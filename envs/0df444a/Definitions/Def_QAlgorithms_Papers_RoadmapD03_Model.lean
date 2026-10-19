-- Prove2me | Definitions.Def_QAlgorithms_Papers_RoadmapD03_Model
-- name    : QAlgorithms_Papers_RoadmapD03_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:23:50.2548+00:00
-- url     : https://prove2.me/theorems/e7671ddd-5333-4f16-b1a8-2da2f2c10a3d
-- title:
--   Multivariate Decoded Quantum Interferometry for Weighted Optimization: supporting definitions
-- statement:
--   Supporting mathematical objects and conventions for the selected original paper results. Exact source hypotheses and labels are documented in the Lean declarations.
-- source:
--   Multivariate Decoded Quantum Interferometry for Weighted Optimization, arXiv:2605.10666v2, https://arxiv.org/abs/2605.10666v2. Exact locators in declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_WeightedDQI
import Definitions.Def_QAlgorithms_Defs_DQI
noncomputable section

open Filter

namespace QAlgorithms.Papers.RoadmapD03

open QAlgorithms.WeightedDQI

/-- The admissible data of Theorem 2, arXiv:2605.10666v2, PDF pp.5–6.
The range `1 ≤ r < p` is recovered from Appendix A, PDF p.30. The degree ratio
is exact; no rounded degrees are substituted for irrational ratios.
The dual-distance condition has the source's strict `2*l + 1 < d^perp` strength. -/
structure WeightedInstance (kappa mu : ℝ) where
  clauses : ClauseDomain
  m : ℕ
  n : ℕ
  blocks : ℕ
  ell : ℕ
  m_pos : 0 < m
  B : Matrix (Fin m) (Fin n) (ZMod clauses.p)
  L : Fin m → Finset (ZMod clauses.p)
  cardinality : ∀ i, (L i).card = clauses.r
  partition : BlockPartition m blocks
  distance : DualDistanceExceeds B (2 * ell + 1)
  kappa_eq : clauseParameters clauses 2 = kappa
  ratio_eq : (ell : ℝ) / m = mu

/-- The optimal signed expectation in (9), PDF p.6: the supremum over unit
multivariate DQI states of total degree at most `ell`. Attainment is a conclusion
of the headline, rather than an assumption on the data. -/
def weightedOptimalValue {kappa mu : ℝ} (I : WeightedInstance kappa mu) : ℝ :=
  letI : NeZero I.clauses.p := ⟨I.clauses.prime.ne_zero⟩
  optimalExpectation I.B I.L I.partition I.ell

/-- The actual Born-rule expectation of the polynomial state, (8), PDF pp.5–6.
Its unit norm is required by the admissibility clauses in the headline. -/
def polynomialExpectation {kappa mu : ℝ} (I : WeightedInstance kappa mu)
    (P : MvPolynomial (Fin I.blocks) ℂ) : ℝ :=
  letI : NeZero I.clauses.p := ⟨I.clauses.prime.ne_zero⟩
  ∑ x, prob (state I.B I.L I.partition P) x * objective I.B I.L I.partition x

/-- The signed remainder of equation (9), PDF p.6. The frozen variationalValue
is precisely Gamma in (10), including the slack budget and allocation endpoints. -/
def residual {kappa mu : ℝ} (I : WeightedInstance kappa mu) : ℝ :=
  weightedOptimalValue I / I.m -
    clauseParameters I.clauses 0 *
      ((I.m : ℝ)⁻¹ * ∑ t, I.partition.weights t * (I.partition.blocks t).card) -
    clauseParameters I.clauses 1 *
      variationalValue I.partition I.m_pos kappa mu (by
        rw [← I.ratio_eq]
        exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- The nonnegative error scale in (9), PDF p.6; the fractional power is real. -/
def errorScale {kappa mu : ℝ} (I : WeightedInstance kappa mu) : ℝ :=
  (I.m : ℝ)⁻¹ * ∑ t, I.partition.weights t *
    ((I.partition.blocks t).card : ℝ) ^ (3 / 4 : ℝ)


end QAlgorithms.Papers.RoadmapD03


