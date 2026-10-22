-- Prove2me | Definitions.Def_RiskFunctionals_Polyhedral_SinglePeriod
-- name    : RiskFunctionals_Polyhedral_SinglePeriod
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:53:59.999366+00:00
-- url     : https://prove2.me/theorems/12264505-e40f-4221-96d5-e532f1185c11
-- title:
--   Single-period polyhedral probability functionals (2.74), their dual set (2.76), and acceptability functionals (A1)–(A3)
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and $p\in[1,\infty)$; put $\mathcal Y=L_p(\mathcal F,\mathbb R)$. Random variables equal almost surely are identified.
--
--   1. **Data.** Dimensions $k_0,k_1\in\mathbb N$, vectors $c_i,w_i\in\mathbb R^{k_i}$ and sets $V_i\subseteq\mathbb R^{k_i}$, $i\in\{0,1\}$. The data are **polyhedral** if $V_0$ and $V_1$ are non-empty polyhedral sets.
--   2. **The functional (2.74).** For $Y\in\mathcal Y$,
--   $$\mathcal R(Y)=\sup\Bigl\{\langle c_0,v_0\rangle+\mathbb E(\langle c_1,v_1\rangle)\ :\ v_0\in V_0,\ v_1\in L_p(\mathcal F,\mathbb R^{k_1}),\ v_1\in V_1\ \text{a.s.},\ \langle w_0,v_0\rangle+\langle w_1,v_1\rangle=Y\ \text{a.s.}\Bigr\}\in[-\infty,+\infty],$$
--   where $v_0\in\mathbb R^{k_0}$ is deterministic.
--   3. **Complete recourse:** $\langle w_1,V_1\rangle=\{\langle w_1,v\rangle:v\in V_1\}=\mathbb R$.
--   4. **Dual feasibility set:** $D=\{u\in\mathbb R:\ c_0-uw_0\in V_0^*,\ c_1-uw_1\in V_1^*\}$.
--   5. **Dual set (2.76):** with $q$ the exponent conjugate to $p$, $\mathcal Z_*=\{Z\in L_q(\mathcal F,\mathbb R):\ c_0-w_0\mathbb E(Z)\in V_0^*,\ c_1-w_1Z\in V_1^*\ \text{a.s.}\}$.
--   6. A real functional $\mathcal A$ on $\mathcal Y$ is **concave** if $\mathcal A(\lambda Y^{(1)}+(1-\lambda)Y^{(2)})\ge\lambda\mathcal A(Y^{(1)})+(1-\lambda)\mathcal A(Y^{(2)})$ for $Y^{(1)},Y^{(2)}\in\mathcal Y$, $0\le\lambda\le1$; it is **continuous on $\mathcal Y$** for the $L_p$ norm; and it is an **acceptability functional** if it is concave and satisfies (A1) $\mathcal A(Y+c)=\mathcal A(Y)+c$ for constants $c$, and (A3) $Y^{(1)}\le Y^{(2)}$ a.s. implies $\mathcal A(Y^{(1)})\le\mathcal A(Y^{(2)})$.
--   7. **The AV@R parameters of Example 2.70:** for $\alpha\in\mathbb R$, $k_0=1$, $k_1=2$, $w_0=1$, $c_0=1$, $c_1=(-1/\alpha,0)$, $w_1=(-1,1)$, $V_0=\mathbb R$, $V_1=\mathbb R^2_+$.
--
--   The functional (2.74) is the optimal value of a linear two-stage stochastic program whose right-hand side is the random variable being evaluated; the book uses it to generate acceptability functionals with an explicit dual description.
--
--   **Formalization Note** Random variables are functions $\Omega\to\mathbb R$ (or $\Omega\to\mathbb R^{k_1}$) with `MemLp` hypotheses; constraints hold almost surely, so the value does not depend on the version. The supremum (2.74) is taken in `EReal`, so it is $-\infty$ when nothing is feasible and $+\infty$ when unbounded, never a junk value. The properties in item 6 are stated for real-valued functionals and quantify only over $Y\in L_p$; theorems apply them to the real part of $\mathcal R$ after proving finiteness. Continuity is the $\varepsilon$–$\delta$ form with the $L_p$ (semi)norm `eLpNorm`.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 91, Definition 2.66 (Eq. (2.74)); p. 92, Proposition 2.68 (conditions (i)–(ii), Eq. (2.76)) and Example 2.70; pp. 35–36, Definition 2.17

import Mathlib
import Definitions.Def_RiskFunctionals_Polyhedral_Cones

namespace RiskFunctionals.Polyhedral

open MeasureTheory

/-- The parameters of a single-period polyhedral probability functional (Pflug & Römisch,
*Modeling, Measuring and Managing Risk*, World Scientific 2007, p. 91, Definition 2.66):
dimensions `k₀, k₁ ∈ ℕ`, vectors `c_i, w_i ∈ ℝ^{k_i}` and sets `V_i ⊆ ℝ^{k_i}`, `i ∈ {0, 1}`. -/
structure SinglePeriodData where
  /-- The dimension `k₀` of the first-stage (deterministic) variable `v₀`. -/
  k₀ : ℕ
  /-- The dimension `k₁` of the second-stage (random) variable `v₁`. -/
  k₁ : ℕ
  /-- The objective vector `c₀ ∈ ℝ^{k₀}`. -/
  c₀ : Fin k₀ → ℝ
  /-- The objective vector `c₁ ∈ ℝ^{k₁}`. -/
  c₁ : Fin k₁ → ℝ
  /-- The constraint vector `w₀ ∈ ℝ^{k₀}`. -/
  w₀ : Fin k₀ → ℝ
  /-- The constraint vector `w₁ ∈ ℝ^{k₁}`. -/
  w₁ : Fin k₁ → ℝ
  /-- The set `V₀ ⊆ ℝ^{k₀}`. -/
  V₀ : Set (Fin k₀ → ℝ)
  /-- The set `V₁ ⊆ ℝ^{k₁}`. -/
  V₁ : Set (Fin k₁ → ℝ)

namespace SinglePeriodData

/-- The standing requirement of Definition 2.66 (p. 91): `V₀` and `V₁` are non-empty polyhedral
sets. -/
def IsPolyhedral (D : SinglePeriodData) : Prop :=
  IsPolyhedralSet D.V₀ ∧ D.V₀.Nonempty ∧ IsPolyhedralSet D.V₁ ∧ D.V₁.Nonempty

/-- Feasibility of `(v₀, v₁)` for right-hand side `Y` in the program (2.74) (p. 91):
`v₀ ∈ V₀` is a deterministic vector, `v₁ ∈ L_p(ℱ, ℝ^{k₁})`, `v₁(ω) ∈ V₁` almost surely, and
`⟨w₀, v₀⟩ + ⟨w₁, v₁⟩ = Y` almost surely. -/
def Feasible {Ω : Type*} [MeasurableSpace Ω] (D : SinglePeriodData) (P : Measure Ω)
    (p : ENNReal) (Y : Ω → ℝ) (v₀ : Fin D.k₀ → ℝ) (v₁ : Ω → Fin D.k₁ → ℝ) : Prop :=
  MemLp v₁ p P ∧ v₀ ∈ D.V₀ ∧ (∀ᵐ ω ∂P, v₁ ω ∈ D.V₁) ∧
    ∀ᵐ ω ∂P, D.w₀ ⬝ᵥ v₀ + D.w₁ ⬝ᵥ v₁ ω = Y ω

/-- The single-period polyhedral probability functional (2.74) (p. 91, Definition 2.66):
`ℛ(Y) = sup{⟨c₀, v₀⟩ + 𝔼(⟨c₁, v₁⟩) : (v₀, v₁) feasible for Y}`, a supremum in `EReal`
(`−∞` when nothing is feasible, `+∞` when unbounded). -/
noncomputable def functional {Ω : Type*} [MeasurableSpace Ω] (D : SinglePeriodData)
    (P : Measure Ω) (p : ENNReal) (Y : Ω → ℝ) : EReal :=
  sSup {x : EReal | ∃ (v₀ : Fin D.k₀ → ℝ) (v₁ : Ω → Fin D.k₁ → ℝ), D.Feasible P p Y v₀ v₁ ∧
    x = ((D.c₀ ⬝ᵥ v₀ + ∫ ω, D.c₁ ⬝ᵥ v₁ ω ∂P : ℝ) : EReal)}

/-- Complete recourse, condition (i) of Proposition 2.68 (p. 92): `⟨w₁, V₁⟩ = ℝ`. -/
def CompleteRecourse (D : SinglePeriodData) : Prop :=
  (fun v => D.w₁ ⬝ᵥ v) '' D.V₁ = Set.univ

/-- The set `D := {u ∈ ℝ : c₀ − u w₀ ∈ V₀*, c₁ − u w₁ ∈ V₁*}` of condition (ii) of
Proposition 2.68 (p. 92); dual feasibility is `D ≠ ∅`. -/
def dualFeasibleSet (D : SinglePeriodData) : Set ℝ :=
  {u | D.c₀ - u • D.w₀ ∈ polarCone D.V₀ ∧ D.c₁ - u • D.w₁ ∈ polarCone D.V₁}

/-- The dual set (2.76) (p. 92): `𝒵* = {Z ∈ L_q(ℱ, ℝ) : c₀ − w₀𝔼(Z) ∈ V₀*, c₁ − w₁Z ∈ V₁*}`,
the second constraint holding almost surely. -/
def dualSet {Ω : Type*} [MeasurableSpace Ω] (D : SinglePeriodData) (P : Measure Ω)
    (q : ENNReal) : Set (Ω → ℝ) :=
  {Z | MemLp Z q P ∧ D.c₀ - (∫ ω, Z ω ∂P) • D.w₀ ∈ polarCone D.V₀ ∧
    ∀ᵐ ω ∂P, D.c₁ - Z ω • D.w₁ ∈ polarCone D.V₁}

end SinglePeriodData

/-- Concavity on `𝒴 = L_p(ℱ)` of a real functional, property (A2) (p. 36, Definition 2.17):
`𝒜(λY⁽¹⁾ + (1 − λ)Y⁽²⁾) ≥ λ𝒜(Y⁽¹⁾) + (1 − λ)𝒜(Y⁽²⁾)` for `Y⁽¹⁾, Y⁽²⁾ ∈ L_p`, `0 ≤ λ ≤ 1`. -/
def ConcaveOnLp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (p : ENNReal)
    (A : (Ω → ℝ) → ℝ) : Prop :=
  ∀ Y₁ Y₂ : Ω → ℝ, MemLp Y₁ p P → MemLp Y₂ p P → ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 →
    lam * A Y₁ + (1 - lam) * A Y₂ ≤ A (lam • Y₁ + (1 - lam) • Y₂)

/-- Continuity on `𝒴 = L_p(ℱ)` (norm topology) of a real functional: for every `Y ∈ L_p` and
`ε > 0` there is `δ > 0` with `|𝒜(Y') − 𝒜(Y)| < ε` whenever `Y' ∈ L_p` and `‖Y' − Y‖_p < δ`. -/
def ContinuousOnLp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (p : ENNReal)
    (A : (Ω → ℝ) → ℝ) : Prop :=
  ∀ Y : Ω → ℝ, MemLp Y p P → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ Y' : Ω → ℝ, MemLp Y' p P →
    eLpNorm (Y' - Y) p P < ENNReal.ofReal δ → |A Y' - A Y| < ε

/-- An acceptability functional (p. 35–36, Definition 2.17): a real valued mapping `𝒜` on the
linear space `𝒴 = L_p(ℱ)` satisfying, for all `Y, Y⁽¹⁾, Y⁽²⁾ ∈ 𝒴`,
(A1) translation equivariance `𝒜(Y + c) = 𝒜(Y) + c` for all constants `c`,
(A2) concavity, and (A3) monotonicity: `Y⁽¹⁾ ≤ Y⁽²⁾` a.s. implies `𝒜(Y⁽¹⁾) ≤ 𝒜(Y⁽²⁾)`. -/
structure IsAcceptabilityFunctional {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (p : ENNReal) (A : (Ω → ℝ) → ℝ) : Prop where
  /-- (A1) Translation equivariance. -/
  translation : ∀ Y : Ω → ℝ, MemLp Y p P → ∀ c : ℝ, A (fun ω => Y ω + c) = A Y + c
  /-- (A2) Concavity. -/
  concave : ConcaveOnLp P p A
  /-- (A3) Monotonicity. -/
  monotone : ∀ Y₁ Y₂ : Ω → ℝ, MemLp Y₁ p P → MemLp Y₂ p P → (∀ᵐ ω ∂P, Y₁ ω ≤ Y₂ ω) →
    A Y₁ ≤ A Y₂

/-- The parameters of Example 2.70 (p. 92) representing the average value-at-risk at level `α`
in the form (2.74): `k₀ = 1`, `k₁ = 2`, `w₀ = 1`, `c₀ = 1`, `c₁ = (−1/α, 0)`, `w₁ = (−1, 1)`,
`V₀ = ℝ` and `V₁ = ℝ²₊`. -/
noncomputable def avarData (α : ℝ) : SinglePeriodData where
  k₀ := 1
  k₁ := 2
  c₀ := ![1]
  c₁ := ![-1 / α, 0]
  w₀ := ![1]
  w₁ := ![-1, 1]
  V₀ := Set.univ
  V₁ := {v | 0 ≤ v 0 ∧ 0 ≤ v 1}

end RiskFunctionals.Polyhedral


