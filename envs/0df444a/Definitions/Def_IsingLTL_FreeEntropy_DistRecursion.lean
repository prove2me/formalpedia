-- Prove2me | Definitions.Def_IsingLTL_FreeEntropy_DistRecursion
-- name    : IsingLTL_FreeEntropy_DistRecursion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:11:09.162924+00:00
-- url     : https://prove2.me/theorems/846b8a0d-cef6-40fc-a230-f4d8c3b2c1bf
-- title:
--   The distributional recursion $h\overset{d}{=}B+\sum_{i=1}^{K-1}\xi(\beta,h_i)$, its iterates and fixed points ((2.6)-(2.7))
-- statement:
--   Let
--   $$\xi(\beta,h)=\operatorname{atanh}[\tanh(\beta)\tanh(h)].$$
--   For a law $Q$ of a real random variable $h$, let $\Phi_{\beta,B,\rho}(Q)$ be the law of
--   $$B+\sum_{i=1}^{K-1}\xi(\beta,h_i),$$
--   where $K$ has distribution $\rho$ and the $h_i$ are i.i.d. with law $Q$, independent of $K$. The sequence $h^{(t)}$ of Lemma 2.3 has $h^{(0)}=0$ and law $\Phi^t(\delta_0)$. A **fixed point** of the recursion (2.6) is a law $Q$ with $\Phi(Q)=Q$; it is **supported on $[0,\infty)$** if $Q([0,\infty))=1$. The fixed point $h^*$ of Lemma 2.3 is the fixed point supported on $[0,\infty)$.
--
--   **Formalization Note** $\Phi(Q)$ is the mixture over $k=K-1$ (weight $\rho_{k+1}$) of the image of $Q^{\otimes k}$ under $h\mapsto B+\sum_{i<k}\xi(\beta,h_i)$; it is proved to be a probability law. The law of $h^*$ is selected by choice among fixed points supported on $[0,\infty)$; under the hypotheses of Lemma 2.3 there is exactly one, and outside them the selected value ($\delta_0$ when none exists) is never used.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, p. 5, Lemma 2.3, (2.6)-(2.7); p. 23, Corollary 6.3

import Mathlib
import Definitions.Def_IsingLTL_FreeEntropy_DegreeDist

namespace IsingLTL.FreeEntropy

open MeasureTheory

/-- `ξ(β, h) = atanh[tanh(β) tanh(h)]` (Dembo–Montanari, *Ising Models on Locally Tree-Like
Graphs*, arXiv:0804.4726v3, p. 5, (2.7)). The argument of `atanh` lies in `(−1, 1)` for real
`β, h`, where Mathlib's `Real.artanh` is the true inverse hyperbolic tangent. -/
noncomputable def xi (β h : ℝ) : ℝ := Real.artanh (Real.tanh β * Real.tanh h)

theorem measurable_xi (β : ℝ) : Measurable (xi β) := by
  have ht : Measurable Real.tanh := by
    rw [show Real.tanh = fun x => Real.sinh x / Real.cosh x from funext Real.tanh_eq_sinh_div_cosh]
    exact Real.continuous_sinh.measurable.div Real.continuous_cosh.measurable
  unfold xi Real.artanh
  fun_prop

/-- The law of `B + ∑_{i=1}^{K−1} ξ(β, h_i)` when `K ∼ ρ` and the `h_i` are i.i.d. with law `Q`,
independent of `K` (the right side of (2.6), p. 5), as a measure: the mixture over `k = K − 1`
(probability `ρ_{k+1}`) of the image of `Q^{⊗k}` under `h ↦ B + ∑_{i<k} ξ(β, h_i)`. -/
noncomputable def recMeasure (β B : ℝ) (D : DegreeDist) (Q : ProbabilityMeasure ℝ) : Measure ℝ :=
  Measure.sum (fun k : ℕ => D.rhoShift k •
    (Measure.pi (fun _ : Fin k => (Q : Measure ℝ))).map
      (fun h : Fin k → ℝ => B + ∑ i, xi β (h i)))

theorem recMeasure_isProbabilityMeasure (β B : ℝ) (D : DegreeDist) (Q : ProbabilityMeasure ℝ) :
    IsProbabilityMeasure (recMeasure β B D Q) := by
  constructor
  rw [recMeasure, Measure.sum_apply _ MeasurableSet.univ]
  have hm : ∀ k : ℕ, Measurable (fun h : Fin k → ℝ => B + ∑ i, xi β (h i)) := fun k => by
    have := measurable_xi β
    fun_prop
  simp only [Measure.smul_apply, smul_eq_mul]
  simp_rw [Measure.map_apply (hm _) MeasurableSet.univ, Set.preimage_univ, measure_univ, mul_one]
  exact PMF.tsum_coe D.rhoShift

/-- The **distributional recursion** (2.6) (p. 5) as a map on laws:
`Φ_{β,B,ρ}(Q) = law of B + ∑_{i=1}^{K−1} ξ(β, h_i)`, `K ∼ ρ`, `h_i` i.i.d. `∼ Q` independent of `K`. -/
noncomputable def recOp (β B : ℝ) (D : DegreeDist) (Q : ProbabilityMeasure ℝ) :
    ProbabilityMeasure ℝ :=
  ⟨recMeasure β B D Q, recMeasure_isProbabilityMeasure β B D Q⟩

/-- The laws of `h^{(t)}` in Lemma 2.3 (p. 5): `h^{(0)} = 0` identically and
`h^{(t+1)} =ᵈ B + ∑_{i=1}^{K−1} ξ(β, h^{(t)}_i)` (2.6). -/
noncomputable def recLaw (β B : ℝ) (D : DegreeDist) : ℕ → ProbabilityMeasure ℝ
  | 0 => ⟨Measure.dirac 0, inferInstance⟩
  | t + 1 => recOp β B D (recLaw β B D t)

/-- `Q` is a **fixed point of the recursion (2.6)** (p. 5; Corollary 6.3, p. 23): `Φ(Q) = Q`. -/
def IsFixedPoint (β B : ℝ) (D : DegreeDist) (Q : ProbabilityMeasure ℝ) : Prop :=
  recOp β B D Q = Q

/-- `Q` is a fixed point of (2.6) **supported on `[0, ∞)`** (Lemma 2.3, p. 5). -/
def IsNonnegFixedPoint (β B : ℝ) (D : DegreeDist) (Q : ProbabilityMeasure ℝ) : Prop :=
  IsFixedPoint β B D Q ∧ (Q : Measure ℝ) (Set.Ici 0) = 1

/-- The law of the fixed point `h*` of Lemma 2.3 (p. 5): a fixed point of (2.6) supported on
`[0, ∞)`, chosen if one exists.

Formalization Note: for `β ≥ 0`, `B > 0` and `ρ` with finite first moment, Lemma 2.3 asserts
that exactly one such law exists, so this is the paper's `h*`. Outside that range (no such fixed
point) the value is the junk law `δ₀`, which no statement of the mission uses. -/
noncomputable def nonnegFixedPoint (β B : ℝ) (D : DegreeDist) : ProbabilityMeasure ℝ := by
  classical
  exact if h : ∃ Q, IsNonnegFixedPoint β B D Q then h.choose else ⟨Measure.dirac 0, inferInstance⟩

end IsingLTL.FreeEntropy


