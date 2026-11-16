-- Prove2me | Definitions.Def_BeyondConvexity_APTAS_Supplement_UniformRepresentativeRoundable
-- name    : BeyondConvexity_APTAS_Supplement_UniformRepresentativeRoundable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:15:50.034918+00:00
-- url     : https://prove2.me/theorems/7567f5e5-6e92-4714-9c98-4e30b3b86a38
-- title:
--   Full dimensional uniform representative roundability
-- statement:
--   For every admissible real tuple $\alpha,\beta,\gamma,\eta$ (positive dyadic $\alpha$ and $0<\beta,\gamma,\eta<1$), constants $K$ and $\delta\ge0$ are chosen before the instance and its level-separated partition. Every such real-scale partition of every valid class instance has representative data satisfying all geometric, label, group-count and packing guarantees above.
--
--   For finite rational queries, one finite-alphabet machine accepts the rational tuple, the entire dimensional instance and the full rational level partition. It returns rational representative data satisfying those same guarantees. Computable parameter functions bound the group count, time coefficient and exponent. Its runtime is at most $C(q)\max(2,|\operatorname{enc}(q,I,p)|)^{e(q)}$, including every supplied coordinate, simplex, scale and level assignment. The nonnegative additive allowance depends only on the fixed dimension, class and tuple, never on the instance or number of levels. Correctness holds simultaneously for every feasible comparison count $m$; $m$ and its witness packing are not inputs.
--
--   This expands Definition 5 in dimension $d$, with all analytic real parameters retained and finite rational computation made explicit. No APTAS, bulk estimate, deletion bound or optimizer is built into the assumption.
-- source:
--   Lucas de Oliveira Silva, Elisa Dell'Arriva, Flávio Keidi Miyazawa, STOC 2027 submission #890 (October 2026), Definition 5, printed p.7 / PDF p.8; Section 7, printed p.16 / PDF p.17

import Definitions.Def_BeyondConvexity_APTAS_Supplement_RepresentativeData
import Definitions.Def_BeyondConvexity_APTAS_RationalRoundability

noncomputable section

namespace BeyondConvexity.APTAS.Supplement

/-- Full dimensional Definition 5, with an analytic real-parameter clause and
one uniform rational-input machine. No preprocessing conclusion, bulk estimate,
structured optimizer, or APTAS is included in this hypothesis. -/
def UniformRepresentativeRoundable {d : ℕ} (P : Set (PolyhedralRegion d)) : Prop :=
  (∀ α β γ η : ℝ, PositiveDyadic α →
    0 < β → β < 1 → 0 < γ → γ < 1 → 0 < η → η < 1 →
    ∃ (K : ℕ) (δ : ℝ), 0 ≤ δ ∧
      ∀ (I : Instance d) (p : LevelPartition ℝ), InClass I P →
        LevelValid p I α β γ →
        ∃ R : RepresentativeData d ℝ, R.Correct I p K η δ) ∧
  ∃ (M : BitMachine) (K C exponent : RoundingParameters → ℕ)
      (δ : RoundingParameters → ℝ),
    M.Finite ∧
    Effective encRoundingParameters RSListDecodingCapacity.AllRates.encNat K ∧
    Effective encRoundingParameters RSListDecodingCapacity.AllRates.encNat C ∧
    Effective encRoundingParameters RSListDecodingCapacity.AllRates.encNat exponent ∧
    ∀ q : RoundingParameters, q.Valid → 0 ≤ δ q ∧
      ∀ (I : Instance d) (p : LevelPartition ℚ), InClass I P →
        LevelValid p.Realize I (q.α : ℝ) (q.β : ℝ) (q.γ : ℝ) →
        ∃ R : RepresentativeData d ℚ,
          M.Runs (encRoundingParameters q ++ encInstance I ++ encLevelPartition p)
            (encRepresentativeData R)
            (C q * (max 2 (encRoundingParameters q ++ encInstance I ++
              encLevelPartition p).length) ^ exponent q) ∧
          R.realize.Correct I p.Realize (K q) (q.η : ℝ) (δ q)

end BeyondConvexity.APTAS.Supplement


