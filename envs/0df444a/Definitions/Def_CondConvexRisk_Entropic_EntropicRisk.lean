-- Prove2me | Definitions.Def_CondConvexRisk_Entropic_EntropicRisk
-- name    : CondConvexRisk_Entropic_EntropicRisk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:00:33.200605+00:00
-- url     : https://prove2.me/theorems/df6bdde8-6801-4d51-8b5e-710e7d43f8f9
-- title:
--   Definitions 5.2–5.3 — conditional entropic risk measure and conditional relative entropy
-- statement:
--   Fix $\gamma>0$. With $E_P(\cdot\mid\mathcal G)$ the conditional expectation given the sub-$\sigma$-algebra $\mathcal G$:
--
--   1. The **acceptance set** is $A_\gamma=\{X\in L^\infty : E_P(e^{-\gamma X}\mid\mathcal G)\le 1\}$.
--   2. The **conditional entropic risk measure** is
--   $$\rho_\gamma(X)=\frac1\gamma\log E_P\big(e^{-\gamma X}\mid\mathcal G\big),\qquad X\in L^\infty.$$
--   3. For $Q\in\mathcal P_{\mathcal G}$ with density $\varphi=dQ/dP$, the **conditional relative entropy** is
--   $$H_{\mathcal G}(Q\mid P)=E_P\big(\varphi\log\varphi\mid\mathcal G\big)\in[0,+\infty],$$
--   with the convention $0\log0=0$.
--   4. Auxiliary families: $\{E_Q(Z\mid\mathcal G)-\log E_P(e^Z\mid\mathcal G)\}_{Z\in L^\infty}$ (Lemma 5.5) and $\{-E_Q(X\mid\mathcal G)-\tfrac1\gamma H_{\mathcal G}(Q\mid P)\}_{Q\in\mathcal P_{\mathcal G}}$ (the robust representation with entropic penalty).
--
--   The conditional entropic risk measure is the conditional analogue of the entropic risk measure induced by exponential utility; the conditional relative entropy is its penalty function.
--
--   **Formalization Note** $\varphi$ is the real part of the Radon–Nikodym derivative `Q.rnDeriv P`. Since $\varphi\log\varphi$ need not be integrable, $H_{\mathcal G}$ is a generalized conditional expectation $E_P((\varphi\log\varphi)^+\mid\mathcal G)-E_P((\varphi\log\varphi)^-\mid\mathcal G)$ built from Mathlib's $[0,+\infty]$-valued conditional expectation `condLExp`, valued in `EReal`; the negative part is bounded by $1/e$, so $+\infty-(+\infty)$ never arises and $H_{\mathcal G}=+\infty$ is kept (not collapsed to $0$). In `EReal`, a real number minus $+\infty$ is $-\infty$.
-- source:
--   Detlefsen & Scandolo, Conditional and Dynamic Convex Risk Measures, SFB 649 Discussion Paper 2005-006, p. 12 (Section 5: U_γ, A_γ, ρ_γ; Definition 5.2), p. 13 (Definition 5.3; Lemma 5.5)

import Mathlib
import Definitions.Def_CondConvexRisk_Entropic_Basic

open MeasureTheory

namespace CondConvexRisk.Entropic

/-- Section 5, p. 12: the conditional entropic risk measure with risk aversion `γ`,
`ρ_γ(X) = (1/γ) log E_P(e^{-γX} | G)`, the paper's closed form (Definition 5.2).
`E_P(· | G)` is Mathlib's conditional expectation `P[· | m]`. -/
noncomputable def rhoGamma {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (γ : ℝ) (X : Ω → ℝ) : Ω → ℝ :=
  fun ω => γ⁻¹ * Real.log ((P[fun x => Real.exp (-γ * X x) | m]) ω)

/-- Section 5, p. 12: the acceptance set
`A_γ = {X ∈ L∞ | U_γ(X) ≥ 0} = {X ∈ L∞ | E_P(e^{-γX} | G) ≤ 1}` (inequality `P`-a.s.). -/
def acceptanceSet {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (γ : ℝ) : Set (Ω → ℝ) :=
  {X | MemLp X ⊤ P ∧ (P[fun x => Real.exp (-γ * X x) | m]) ≤ᵐ[P] 1}

/-- Generalized conditional expectation of a real function `f` with values in `[-∞, +∞]`:
`E_μ(f | G) = E_μ(f⁺ | G) - E_μ(f⁻ | G)`, each part being the `[0, +∞]`-valued conditional
expectation `μ⁻[· | m]` of a nonnegative function.  It agrees with the usual conditional
expectation when `f` is `μ`-integrable; it is meaningful whenever the two parts are not both
`+∞` (in `EReal`, `⊤ - ⊤ = ⊥`). -/
noncomputable def condExpExt {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) : Ω → EReal :=
  fun ω => ((μ⁻[fun x => ENNReal.ofReal (f x) | m]) ω : EReal) -
    ((μ⁻[fun x => ENNReal.ofReal (-f x) | m]) ω : EReal)

/-- The real density `φ = dQ/dP` of `Q ∈ P_G` (Radon–Nikodym derivative, a nonnegative real
function; `Q ≪ P`). -/
noncomputable def density {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (Q : PG m P) : Ω → ℝ :=
  fun ω => (Q.1.rnDeriv P ω).toReal

/-- Definition 5.3, p. 13: the conditional relative entropy of `Q ∈ P_G` w.r.t. `P`,
`H_G(Q | P) = E_P(φ log φ | G)` with `φ = dQ/dP` and `0 log 0 = 0`, computed as a generalized
conditional expectation with values in `[-∞, +∞]` (the negative part of `φ log φ` is bounded by
`1/e`, so the value is never `⊤ - ⊤`; it may be `+∞`). -/
noncomputable def condRelEntropy {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (Q : PG m P) : Ω → EReal :=
  condExpExt m P (fun ω => density m P Q ω * Real.log (density m P Q ω))

/-- The family `{E_Q(Z | G) - log E_P(e^Z | G) | Z ∈ L∞}` of Lemma 5.5, p. 13, indexed by
`Z ∈ L∞`. -/
noncomputable def dvFamily {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (Q : PG m P) : LInf P → Ω → EReal :=
  fun Z ω => (((Q.1[Z.1 | m]) ω - Real.log ((P[fun x => Real.exp (Z.1 x) | m]) ω) : ℝ) : EReal)

/-- The family `{-E_Q(X | G) - (1/γ) H_G(Q | P) | Q ∈ P_G}` of the robust representation (3),
p. 5, with the entropic penalty of Proposition 5.4, indexed by `Q ∈ P_G`.  A finite number minus
`+∞` is `-∞` in `EReal`. -/
noncomputable def entropicReprFamily {Ω : Type*} (m : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (X : Ω → ℝ) : PG m P → Ω → EReal :=
  fun Q ω => ((-(Q.1[X | m]) ω : ℝ) : EReal) - ((γ⁻¹ : ℝ) : EReal) * condRelEntropy m P Q ω

end CondConvexRisk.Entropic


