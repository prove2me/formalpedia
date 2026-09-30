-- Prove2me | Definitions.Def_TraceEstimation_UnitVector_mixingMatrix
-- name    : TraceEstimation_UnitVector_mixingMatrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:36:10.114002+00:00
-- url     : https://prove2.me/theorems/3c4f609b-3b90-4777-a305-5053065b88b9
-- title:
--   Definition 3.5 — the random mixing matrix $\mathcal F = FD$ and $\eta = \max|F_{ij}|^2$
-- statement:
--   Let $n \ge 1$ and let $F \in \mathbb{R}^{n\times n}$ be a fixed orthogonal matrix, the **seed matrix**. A **random mixing matrix** is
--
--   $$\mathcal F = F D ,$$
--
--   where $D$ is a random diagonal matrix whose diagonal entries $D_{11}, \ldots, D_{nn}$ are i.i.d. Rademacher random variables, $\Pr(D_{ii} = \pm 1) = 1/2$. Almost surely $D$, hence $\mathcal F$, is orthogonal. The mixing effectiveness of $\mathcal F$ depends on the quantity
--
--   $$\eta = \max_{i,j} |F_{ij}|^2 .$$
--
--   For an orthogonal seed, $1/n \le \eta \le 1$; Fourier-type seeds (DFT, DCT, Hadamard) have $\eta = \Theta(1/n)$.
--
--   **Formalization Note** The paper allows complex unitary $F$; this mission works over $\mathbb{R}$ (orthogonal $F$), since the estimator uses the transpose $\mathcal F^T$. The file defines `rademacher` (the law $\tfrac12(\delta_1+\delta_{-1})$ on $\mathbb{R}$, with its probability-measure instance), `signMeasure n` (the product of $n$ copies, the law of the diagonal $d$ of $D$), `mixingMatrix F d = F * diagonal d`, and `eta F`, the `Finset.sup'` of $|F_{ij}|^2$ over all index pairs (placeholder $0$ when $n = 0$). Orthogonality of $F$ is a hypothesis of each theorem (`Fᵀ * F = 1`), not part of the definition.
-- source:
--   Avron and Toledo, Randomized algorithms for estimating the trace of an implicit symmetric positive semi-definite matrix, J. ACM 58(2), Article 8 (2011), p. 8:4, Definition 3.5 and the sentence after Definition 3.6

import Mathlib

namespace TraceEstimation.UnitVector

open MeasureTheory Matrix

/-- The Rademacher law on `ℝ`: the values `1` and `-1`, each with probability `1/2`
(Avron–Toledo, Definition 3.5, p. 8:4: `Pr(D_ii = ±1) = 1/2`). -/
noncomputable def rademacher : Measure ℝ :=
  (2⁻¹ : ENNReal) • (Measure.dirac (1 : ℝ) + Measure.dirac (-1 : ℝ))

instance rademacher_isProbabilityMeasure : IsProbabilityMeasure rademacher := by
  constructor
  simp only [rademacher, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- The law of the diagonal `d = (D_11, …, D_nn)` of the random diagonal matrix `D` of
Definition 3.5 (Avron–Toledo, p. 8:4): its `n` entries are i.i.d. Rademacher. -/
noncomputable def signMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ : Fin n => rademacher

/-- The random mixing matrix `𝓕 = F D` of Definition 3.5 (Avron–Toledo, p. 8:4), for the seed
matrix `F` and the diagonal `d` of `D = diag(d)`. -/
noncomputable def mixingMatrix {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  F * Matrix.diagonal d

/-- `η = max_{i,j} |F_ij|²` for the seed matrix `F` (Avron–Toledo, p. 8:4, after Definition 3.6,
and Lemma 8.3, p. 8:13). For `n = 0` the value is the placeholder `0`. -/
noncomputable def eta {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  if h : (Finset.univ : Finset (Fin n × Fin n)).Nonempty then
    Finset.univ.sup' h (fun p => |F p.1 p.2| ^ 2)
  else 0

end TraceEstimation.UnitVector


