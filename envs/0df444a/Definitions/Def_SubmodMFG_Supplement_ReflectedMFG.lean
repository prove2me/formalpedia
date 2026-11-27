-- Prove2me | Definitions.Def_SubmodMFG_Supplement_ReflectedMFG
-- name    : SubmodMFG_Supplement_ReflectedMFG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:22:38.448954+00:00
-- url     : https://prove2.me/theorems/3654c8cf-40e0-5a0e-b3dc-e5988e573090
-- title:
--   The MFG with reflecting boundary of §6
-- statement:
--   Fix $T>0$, $M>0$, $x_0\in[0,M]$, a compact control set $A\subset\mathbb R$, a Lipschitz $b:[0,T]\times\mathbb R\to\mathbb R$, $\sigma\ge0$, $f,g,c$ satisfying Assumption 5.1, and a lower semicontinuous $l:[0,T]\times\mathbb R\times\mathbb R\to[0,\infty)$, convex in $a$; $\pi=\delta_0+dt+\delta_T$.
--
--   1. $L_M$ is the set of measurable $\mu:[0,T]\to\mathcal P([0,M])$ with $\mu_0=\delta_{x_0}$, ordered $\pi$-a.e. by $\le_{st}$.
--   2. An **admissible relaxed control** is $\rho=(\Omega,\mathcal F,\mathbb F,P,W,\lambda,v,X)$: a Brownian motion $W$ on a filtered probability space with the usual conditions, a $\mathcal P(A)$-valued progressively measurable $\lambda$, and $(v,X)$ solving the reflected equation (6.1): $X_t=x_0+\int_0^t\big(b(s,X_s)+\int_Aa\,\lambda_s(da)\big)ds+\sigma W_t+v_t$, $X_t\in[0,M]$, $\int_0^t\mathbf 1\{X_s\in(0,M)\}\,d|v|_s=0$. It is **strict** if $\lambda_t=\delta_{\alpha_t}$ $P\otimes dt$-a.e. for an $A$-valued progressive $\alpha$.
--   3. $J(\rho,\mu)=E^P\big[\int_0^T\big(f(t,X_t,\mu_t)+\int_Al(t,X_t,a)\lambda_t(da)\big)dt+g(X_T,\mu_T)+\int_0^Tc_t\,d|v|_t\big]$; optimality is over all relaxed controls.
--   4. $\mu\in L_M$ is an **MFG equilibrium** (Definition 6.1) if some strict control is optimal for $\mu$ and $\mu_t=P\circ X_t^{-1}$ for every $t$; the best response (6.4) is $R(\mu)=p(\arg\min_EJ(\cdot,\mu))$ with $p(\nu^\rho)=P\circ(X^\rho)^{-1}$.
--
--   **Formalization Note** §6 does not restate $\sigma$; it is a constant $\sigma\ge0$ as in §5.2.1. The control set is assumed nonempty and convex as well as compact: for a nonconvex $A$ the mean $\int a\,\lambda_t(da)$ of a relaxed control need not lie in $A$, and both Lemma 6.2 (2) and Theorem 6.3 fail (`DISPROOF.md`). (6.1) holds for each $t$ almost surely; $v$ has right-continuous paths of bounded variation. A relaxed control is a pair of a stochastic basis and the processes on it.
-- source:
--   Dianetti, Ferrari, Fischer, Nendel, A Unifying Framework for Submodular Mean Field Games, arXiv:2201.07850v1, §6.1–6.3, pp.25–27 (Definition 6.1, (6.1), (6.4))

import Mathlib
import Definitions.Def_SubmodMFG_Supplement_SubProb
import Definitions.Def_RepairSched_UsualConditions
import Definitions.Def_SubmodMFG_Supplement_Processes
import Definitions.Def_SubmodMFG_Supplement_SingularCommon

open MeasureTheory ProbabilityTheory

namespace SubmodMFG.Supplement

/-- **Data of the MFG with reflecting boundary of §6.**
Dianetti, Ferrari, Fischer, Nendel, *A Unifying Framework for Submodular Mean Field Games*,
arXiv:2201.07850v1, §6.1, pp.25–26: a horizon `T`, a bound `M > 0` (written `Mx`), `x₀ ∈ [0, M]`,
a compact control set `A ⊂ ℝ`, a Lipschitz drift `b : [0, T] × ℝ → ℝ`, a volatility `σ`, the costs
`f, g, c` of §5 under Assumption 5.1 (exponent `p`), and a lower semicontinuous
`l : [0, T] × ℝ × ℝ → [0, ∞)`, convex in `a`. The hypotheses are `Standing`. -/
structure ReflModel where
  T : ℝ
  Mx : ℝ
  x₀ : ℝ
  A : Set ℝ
  b : ℝ → ℝ → ℝ
  σ : ℝ
  p : ℝ
  f : ℝ → ℝ → SubProb → ℝ
  g : ℝ → SubProb → ℝ
  c : ℝ → ℝ
  l : ℝ → ℝ → ℝ → ℝ

namespace ReflModel

variable (D : ReflModel)

/-- `π = δ_0 + dt + δ_T` on `[0, T]` (p.25). -/
noncomputable def π : Measure ℝ :=
  Measure.dirac 0 + volume.restrict (Set.Icc 0 D.T) + Measure.dirac D.T

/-- **Standing assumptions of §6** (pp.25–26).

**Formalization Note.** `σ` is not restated in §6; it is read as a constant `σ ≥ 0` as in §5.2.1.
`A` is required to be nonempty and convex besides compact (see the `Differences` of Lemma 6.2 and
Theorem 6.3: for a nonconvex `A` the mean `∫ a λ_t(da)` of a relaxed control need not lie in `A`).
`l` is lower semicontinuous on `[0, T] × ℝ × ℝ`, nonnegative, and convex in `a` on `ℝ`. -/
structure Standing : Prop where
  T_pos : 0 < D.T
  Mx_pos : 0 < D.Mx
  x₀_mem : D.x₀ ∈ Set.Icc 0 D.Mx
  A_compact : IsCompact D.A
  A_nonempty : D.A.Nonempty
  A_convex : Convex ℝ D.A
  b_lip : ∃ K, LipschitzOnWith K (fun q : ℝ × ℝ => D.b q.1 q.2) (Set.Icc 0 D.T ×ˢ Set.univ)
  σ_nonneg : 0 ≤ D.σ
  a51 : Assumption51 D.T D.p D.f D.g D.c
  l_nonneg : ∀ t ∈ Set.Icc (0 : ℝ) D.T, ∀ x a, 0 ≤ D.l t x a
  l_lsc : LowerSemicontinuousOn (fun q : ℝ × ℝ × ℝ => D.l q.1 q.2.1 q.2.2)
    (Set.Icc 0 D.T ×ˢ Set.univ)
  l_convex : ∀ t ∈ Set.Icc (0 : ℝ) D.T, ∀ x, ConvexOn ℝ Set.univ (D.l t x)

/-- **The flows `L_M`** (p.25): "all measurable functions µ : [0, T] → P([0, M]) with µ₀ = δ_{x₀}",
ordered by `π`-a.e. first-order stochastic dominance. -/
def LM : Type :=
  {μ : ℝ → SubProb // Measurable μ ∧
    (∀ t ∈ Set.Icc (0 : ℝ) D.T, IsProb (μ t) ∧ (μ t).1 (Set.Icc 0 D.Mx)ᶜ = 0) ∧
    (μ 0).1 = Measure.dirac D.x₀}

instance : Preorder D.LM where
  le μ ν := ∀ᵐ t ∂D.π, μ.1 t ≤ ν.1 t
  le_refl μ := Filter.Eventually.of_forall fun t => le_refl _
  le_trans μ ν ρ h₁ h₂ := by filter_upwards [h₁, h₂] with t a b using a.trans b

/-- A filtered probability space with the usual conditions carrying an `𝔽`-Brownian motion `W`
(item (1) of the definition of `E_w`, p.26). The sample space ranges over `Type`. -/
structure Basis where
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  P : Measure Ω
  F : Filtration ℝ mΩ
  W : ℝ → Ω → ℝ
  prob : IsProbabilityMeasure P
  usual : RepairSched.UsualConditions F P
  bm : IsFBMOn P F D.T W

attribute [instance] Basis.mΩ

/-- The total variation `|v|_s` of `v` on `[0, s ∧ T]` (`0` for `s < 0`). -/
noncomputable def tvExt (v : ℝ → ℝ) (s : ℝ) : ℝ :=
  if s < 0 then 0 else (eVariationOn v (Set.Icc 0 (min s D.T))).toReal

/-- **Admissible relaxed control on a basis** (p.26): "(2) λ is a P(A)-valued, progressively
measurable process, (3) the couple (v, X) is a solution to the controlled reflected SDE in the
domain (0, M): (6.1) dX_t = (b(t, X_t) + ∫_A a λ_t(da))dt + σdW_t + dv_t, t ∈ [0, T], X₀ = x₀,
X_t ∈ [0, M], ∫_0^t 1{X_s ∈ (0, M)} d|v|_s = 0, for any t ∈ [0, T], P-a.s., where |v| denotes the
total variation of v."

**Formalization Note.** (6.1) in integrated form, for each `t ∈ [0, T]` P-a.s.; `X` and `v` are
`𝔽`-adapted, and `v` has right-continuous paths of bounded variation on `[0, T]` (needed for
`d|v|`); `∫_0^t 1{X_s ∈ (0,M)} d|v|_s` is the `d|v|`-measure of `{s ∈ [0, t] | X_s ∈ (0, M)}`. -/
structure CtrlOn (β : D.Basis) where
  lam : ℝ → β.Ω → Measure ℝ
  v : ℝ → β.Ω → ℝ
  X : ℝ → β.Ω → ℝ
  lam_prog : ProgMeasOn (fun t => β.F t) D.T lam
  lam_val : ∀ t ∈ Set.Icc (0 : ℝ) D.T, ∀ ω, IsProbabilityMeasure (lam t ω) ∧ lam t ω D.Aᶜ = 0
  v_adapted : ∀ t ∈ Set.Icc (0 : ℝ) D.T, Measurable[β.F t] (v t)
  X_adapted : ∀ t ∈ Set.Icc (0 : ℝ) D.T, Measurable[β.F t] (X t)
  v_rc : ∀ ω, ∀ t ∈ Set.Icc (0 : ℝ) D.T, ContinuousWithinAt (fun s => v s ω) (Set.Icc t D.T) t
  v_bv : ∀ ω, BoundedVariationOn (fun s => v s ω) (Set.Icc 0 D.T)
  X_init : ∀ᵐ ω ∂β.P, X 0 ω = D.x₀
  X_eq : ∀ t ∈ Set.Icc (0 : ℝ) D.T, ∀ᵐ ω ∂β.P,
    X t ω = D.x₀ + (∫ s in (0 : ℝ)..t, (D.b s (X s ω) + ∫ a, a ∂(lam s ω))) +
      D.σ * β.W t ω + v t ω
  X_mem : ∀ t ∈ Set.Icc (0 : ℝ) D.T, ∀ᵐ ω ∂β.P, X t ω ∈ Set.Icc 0 D.Mx
  refl : ∀ t ∈ Set.Icc (0 : ℝ) D.T, ∀ᵐ ω ∂β.P,
    stieltjesMeasure (D.tvExt (fun s => v s ω)) {s | s ∈ Set.Icc 0 t ∧ X s ω ∈ Set.Ioo 0 D.Mx} = 0

/-- The set `E_w` of admissible relaxed controls `ρ = (Ω, 𝓕, 𝔽, P, W, λ, v, X)` (p.26). -/
def Ctrl : Type 1 := Σ β : D.Basis, D.CtrlOn β

/-- **Strict control** (p.26): `λ_t = δ_{α_t}` `P ⊗ dt`-a.e. in `Ω × [0, T]`, for some `A`-valued
progressively measurable process `α`. -/
def IsStrict (ρ : D.Ctrl) : Prop :=
  ∃ α : ℝ → ρ.1.Ω → ℝ, ProgMeasOn (fun t => ρ.1.F t) D.T α ∧ (∀ t ω, α t ω ∈ D.A) ∧
    ∀ᵐ q ∂(ρ.1.P.prod (volume.restrict (Set.Icc (0 : ℝ) D.T))),
      ρ.2.lam q.2 q.1 = Measure.dirac (α q.2 q.1)

/-- **The cost functional** (p.26): `J(ρ, µ) = E^P[∫_0^T (f(t, X_t, µ_t) + ∫_A l(t, X_t, a)
λ_t(da)) dt + g(X_T, µ_T) + ∫_0^T c_t d|v|_t]`.

**Formalization Note.** Value in `[−∞, ∞]`: the part with `f, g, c` is `erealExpect` (its
integrand is bounded, `X_t ∈ [0, M]`), the part with `l ≥ 0` is a lower integral (possibly `∞`). -/
noncomputable def J (ρ : D.Ctrl) (μ : ℝ → SubProb) : EReal :=
  erealExpect ρ.1.P (fun ω => (∫ t in (0 : ℝ)..D.T, D.f t (ρ.2.X t ω) (μ t)) +
      D.g (ρ.2.X D.T ω) (μ D.T) +
      ∫ t in Set.Icc 0 D.T, D.c t ∂(stieltjesMeasure (D.tvExt (fun s => ρ.2.v s ω)))) +
    ((∫⁻ ω, (∫⁻ t in Set.Icc 0 D.T,
        (∫⁻ a, ENNReal.ofReal (D.l t (ρ.2.X t ω) a) ∂(ρ.2.lam t ω))) ∂ρ.1.P : ENNReal) : EReal)

/-- Optimality over all relaxed controls (p.26): `J(ρ, µ) = inf_{E_w} J(·, µ)`. -/
def IsOptimal (ρ : D.Ctrl) (μ : ℝ → SubProb) : Prop := ∀ ρ' : D.Ctrl, D.J ρ μ ≤ D.J ρ' μ

/-- **MFG equilibrium, Definition 6.1** (p.26): "A flow of probabilities µ ∈ L_M is a MFG
equilibrium if (1) there exists a strict optimal control ρ ∈ E_{w,s} for µ, (2) µ_t = P ∘ (X_t)⁻¹
for any t ∈ [0, T]." -/
def IsEquilibrium (μ : D.LM) : Prop :=
  ∃ ρ : D.Ctrl, D.IsStrict ρ ∧ D.IsOptimal ρ μ.1 ∧
    ∀ t ∈ Set.Icc (0 : ℝ) D.T, (μ.1 t).1 = ρ.1.P.map (ρ.2.X t)

/-- **The best-response map (6.4)** (p.27): `R(µ) = p(arg min_E J(·, µ))`, `p(ν^ρ) = P ∘ (X^ρ)⁻¹`:
the flows of `L_M` that agree `π`-a.e. with the marginal laws of an optimal relaxed control. -/
def R (μ : D.LM) : Set D.LM :=
  {m | ∃ ρ : D.Ctrl, D.IsOptimal ρ μ.1 ∧ ∀ᵐ t ∂D.π, (m.1 t).1 = ρ.1.P.map (ρ.2.X t)}

/-- **The set `M` of MFG equilibria** (Theorem 6.3, p.28): the flows of `L_M` that agree `π`-a.e.
with an equilibrium of Definition 6.1. -/
def equilibria : Set D.LM :=
  {m | ∃ m' : D.LM, (∀ᵐ t ∂D.π, m.1 t = m'.1 t) ∧ D.IsEquilibrium m'}

end ReflModel

end SubmodMFG.Supplement


