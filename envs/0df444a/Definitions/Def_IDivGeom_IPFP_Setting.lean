-- Prove2me | Definitions.Def_IDivGeom_IPFP_Setting
-- name    : IDivGeom_IPFP_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:38:30.213685+00:00
-- url     : https://prove2.me/theorems/19f0dcf8-21b3-42a3-8bea-847cd0f21be7
-- title:
--   I-divergence geometry: variation distance, projections, and linear sets
-- statement:
--   On a measurable space $(X,\mathcal X)$, a probability distribution (PD) is a probability measure. For PDs $P,Q,R$, write $I(P\|Q)$ for their extended nonnegative Kullback–Leibler divergence. The definitions in this module specify the paper’s core objects:
--
--   $$
--   |P-Q|=\int\left|\frac{dP}{d(P+Q)}-\frac{dQ}{d(P+Q)}\right|\,d(P+Q),\qquad
--   Q=\operatorname{proj}_{\mathcal E}^{I}(R)\iff Q\in\mathcal E,\ I(Q\|R)<\infty,\ I(Q\|R)\le I(P\|R)\ \forall P\in\mathcal E.
--   $$
--
--   The module also defines convex and variation-closed sets of PDs, algebraic interior points, sets closed under real affine combinations that remain PDs, integrable moment-constraint sets (case (A)), the sets of PDs on a product space with two prescribed marginals (case (B)), membership of a function in the closed linear subspace of $L_1(Q)$ spanned by a family of functions (Theorem 3.1), the extended integral $\int\log q_R\,dP$, and the cyclic I-projection sequence. These definitions support the existence, Pythagorean, and convergence results in this mission.
--
--   **Formalization Note** `klDiv` represents (1.1), including $+\infty$ for singular or divergent cases. The variation formula uses $P+Q$ as a dominating measure; for PDs it has the same value as the paper’s formula using any dominating PD. The extended logarithmic integral uses `ENNReal.log`, so $\log0=-\infty$; its two extended parts are never both infinite under the hypotheses of the theorem items that use it. An I-projection must have finite divergence, matching the paper’s standing requirement that $\mathcal E$ meet $S(R,\infty)$. The cyclic index $n\bmod k$ is zero-based, corresponding to the paper’s $\mathcal E_1,\ldots,\mathcal E_k$.
-- source:
--   Csiszár, I-divergence geometry of probability distributions and minimization problems, Ann. Probab. 3 (1975), pp. 146–155 (PDF pp. 1–10), (1.1)–(1.6), (2.9), the linear-set definition on p. 150, cases (A) and (B) on p. 151, Theorem 3.1 on p. 152, and (3.13) on p. 155

import Mathlib

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal NNReal

namespace IDivGeom.IPFP

variable {X : Type*} [MeasurableSpace X]

/-- The variation distance of (1.6), using `P + Q` as a common dominating measure. -/
noncomputable def varDist (P Q : Measure X) : ℝ :=
  ∫ x, |(P.rnDeriv (P + Q) x).toReal - (Q.rnDeriv (P + Q) x).toReal| ∂(P + Q)

/-- Convexity among probability distributions, with nonnegative weights at most one. -/
def IsConvexPD (ℰ : Set (Measure X)) : Prop :=
  ∀ P ∈ ℰ, ∀ P' ∈ ℰ, ∀ α : ℝ≥0, α ≤ 1 →
    (α : ℝ≥0∞) • P + ((1 - α : ℝ≥0) : ℝ≥0∞) • P' ∈ ℰ

/-- Sequential closure in the variation distance. -/
def IsVarClosed (ℰ : Set (Measure X)) : Prop :=
  ∀ (P : ℕ → Measure X) (Q : Measure X), IsProbabilityMeasure Q →
    (∀ n, P n ∈ ℰ) → Tendsto (fun n => varDist (P n) Q) atTop (𝓝 0) → Q ∈ ℰ

/-- The finite minimizing projection in (1.5). -/
def IsIProjection (R : Measure X) (ℰ : Set (Measure X)) (Q : Measure X) : Prop :=
  Q ∈ ℰ ∧ klDiv Q R ≠ ⊤ ∧ ∀ P ∈ ℰ, klDiv Q R ≤ klDiv P R

/-- Extended integral of `log q_R` against `P`, with `log 0 = -∞`. -/
noncomputable def logDensInt (R Q P : Measure X) : EReal :=
  ((∫⁻ x, (ENNReal.log (Q.rnDeriv R x)).toENNReal ∂P : ℝ≥0∞) : EReal) -
  ((∫⁻ x, (-ENNReal.log (Q.rnDeriv R x)).toENNReal ∂P : ℝ≥0∞) : EReal)

/-- Algebraic interior in the sense of (2.9). -/
def IsAlgInnerPoint (ℰ : Set (Measure X)) (Q : Measure X) : Prop :=
  Q ∈ ℰ ∧ ∀ P ∈ ℰ, ∃ α : ℝ≥0, 0 < α ∧ α < 1 ∧
    ∃ P' ∈ ℰ, Q = (α : ℝ≥0∞) • P + ((1 - α : ℝ≥0) : ℝ≥0∞) • P'

/-- Closure under real affine combinations whenever the combination is a PD. -/
def IsLinearPD (ℰ : Set (Measure X)) : Prop :=
  (∀ P ∈ ℰ, IsProbabilityMeasure P) ∧
  ∀ P ∈ ℰ, ∀ P' ∈ ℰ, ∀ α : ℝ, ∀ M : Measure X,
    IsProbabilityMeasure M →
    (∀ s, MeasurableSet s → M.real s = α * P.real s + (1 - α) * P'.real s) →
    M ∈ ℰ

/-- PDs satisfying the genuine, integrable moment constraints of case (A). -/
def momentSet {ι : Type*} (f : ι → X → ℝ) (a : ι → ℝ) : Set (Measure X) :=
  {P | IsProbabilityMeasure P ∧ ∀ i, Integrable (f i) P ∧ ∫ x, f i x ∂P = a i}

/-- PDs on `X₁ × X₂` with prescribed marginals `P₁` and `P₂` (case (B)). -/
def marginalSet {X₁ X₂ : Type*} [MeasurableSpace X₁] [MeasurableSpace X₂]
    (P₁ : Measure X₁) (P₂ : Measure X₂) : Set (Measure (X₁ × X₂)) :=
  {P | IsProbabilityMeasure P ∧ P.map Prod.fst = P₁ ∧ P.map Prod.snd = P₂}

/-- `g` lies in the closed linear subspace of `L₁(Q)` spanned by the functions `f γ`. -/
def InClosedL1Span {Γ : Type*} (Q : Measure X) (f : Γ → X → ℝ) (g : X → ℝ) : Prop :=
  ∃ (hg : Integrable g Q) (hf : ∀ γ, Integrable (f γ) Q),
    Integrable.toL1 g hg ∈
      (Submodule.span ℝ (Set.range fun γ => Integrable.toL1 (f γ) (hf γ))).topologicalClosure

/-- The zero-based cyclic index for the paper's sets `ℰ₁, ..., ℰₖ`. -/
def cyc (k n : ℕ) (hk : 0 < k) : Fin k := ⟨n % k, Nat.mod_lt n hk⟩

/-- The paper's `Q₀ = R`, with `Qₙ₊₁` projected onto the set indexed by `n % k`. -/
def IsCyclicIProjSeq {k : ℕ} (hk : 0 < k) (ℰ : Fin k → Set (Measure X))
    (R : Measure X) (Qs : ℕ → Measure X) : Prop :=
  Qs 0 = R ∧ ∀ n, IsIProjection (Qs n) (ℰ (cyc k n hk)) (Qs (n + 1))

end IDivGeom.IPFP


