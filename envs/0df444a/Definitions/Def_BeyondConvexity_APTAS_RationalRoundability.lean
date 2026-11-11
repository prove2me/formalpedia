-- Prove2me | Definitions.Def_BeyondConvexity_APTAS_RationalRoundability
-- name    : BeyondConvexity_APTAS_RationalRoundability
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:18:22.216418+00:00
-- url     : https://prove2.me/theorems/bb456ae8-7466-49b8-a84e-9e672f8db2f5
-- title:
--   Effective representative rounding on rational finite inputs
-- statement:
--   This is the rational-parameter, rational-scale restriction of the operational guarantee in Definition 5, rather than a replacement definition of uniform representative roundability. The complete source assumption implies this weaker predicate by restricting its queries. A parameter tuple contains dyadic alpha and rational beta, gamma, eta in (0,1). Inputs contain the entire rational scale list, every occurrence's level index, and every polygon boundary.
--
--   One finite-alphabet machine and parameter functions K, C, d and delta precede every instance and partition. K, C and d are computable natural-valued functions. The real nonnegative additive allowance delta need not be computable. On every valid class input and every valid rational-scale partition, that machine returns the finite groups, chosen member maxima and actual rational separate packing checked by RoundingData.Correct, in at most C(q) max(2,|enc(I) enc(p)|)^d(q) steps. Correctness includes exact label coverage, at most K(q) groups per level, containment, and both packing guarantees for every feasible comparison bin count. The comparison packing and its number of bins are not inputs.
--
--   The supplied partition contributes to the runtime base, including any empty levels. There is no bound on its length, no assumed preprocessing result, and no real-valued machine input. The parameters' encoding cost is absorbed in the parameter-dependent coefficient. Restricting a complete source procedure gives these bounds; if the source's polynomial is already measured in polygon length alone, using the larger combined length only relaxes the time requirement. An additive allowance can be enlarged to its maximum with zero. This predicate asserts only the source rounding service; it assumes no structured optimizer, deletion estimate, bulk inequality or APTAS conclusion.
-- source:
--   Lucas de Oliveira Silva, Elisa Dell'Arriva, Flávio Keidi Miyazawa, STOC 2027 submission #890 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/890.pdf, Definitions 4–5, printed pp.6–7 / PDF pp.7–8; rational preprocessing Section 3 and Appendix B.1, printed pp.9–10,18–19 / PDF pp.10–11,19–20; bit runtime Appendix D.9, printed pp.32–33 / PDF pp.33–34.

import Definitions.Def_BeyondConvexity_APTAS_RoundingData

noncomputable section

namespace BeyondConvexity.APTAS

/-- Rational parameters supplied to the uniform representative-rounding machine. -/
structure RoundingParameters where
  α : ℚ
  β : ℚ
  γ : ℚ
  η : ℚ

def RoundingParameters.Valid (q : RoundingParameters) : Prop :=
  PositiveDyadic (q.α : ℝ) ∧ 0 < q.β ∧ q.β < 1 ∧
    0 < q.γ ∧ q.γ < 1 ∧ 0 < q.η ∧ q.η < 1

def encRoundingParameters (q : RoundingParameters) : List Bool :=
  AbelianCayleyHDX.encRat q.α ++ AbelianCayleyHDX.encRat q.β ++
    AbelianCayleyHDX.encRat q.γ ++ AbelianCayleyHDX.encRat q.η

/-- A weaker hypothesis than Definition 5: only rational parameters and rational
scale lists are queried. This is deliberately not named uniform representative
roundability. Every source roundability witness restricts to this finite-input
interface. Theorem 1 below consequently has a more general hypothesis, with the
complete source conclusion. No partition-length bound or optimal packing is an
input promise. The runtime includes the full supplied partition encoding.

K, C and d have computable dependence on the parameters, and the real additive
allowance is fixed before the instance and partition. One machine computes the
very groups and separate rational packing whose correctness is asserted. -/
def RationalRoundability (P : Set Polygon) : Prop :=
  ∃ (M : BitMachine) (K C d : RoundingParameters → ℕ)
      (δ : RoundingParameters → ℝ),
    M.Finite ∧
    Effective encRoundingParameters RSListDecodingCapacity.AllRates.encNat K ∧
    Effective encRoundingParameters RSListDecodingCapacity.AllRates.encNat C ∧
    Effective encRoundingParameters RSListDecodingCapacity.AllRates.encNat d ∧
    ∀ q : RoundingParameters, q.Valid →
      0 ≤ δ q ∧ ∀ (I : Instance) (p : LevelPartition ℚ), I.InClass P →
        p.Realize.Valid I (q.α : ℝ) (q.β : ℝ) (q.γ : ℝ) →
        ∃ R : RoundingData,
          M.Runs (encRoundingParameters q ++ encInstance I ++ encLevelPartition p)
            (encRoundingData R)
            (C q * (max 2 (encInstance I ++ encLevelPartition p).length) ^ d q) ∧
          R.Correct I p.Realize (K q) (q.η : ℝ) (δ q)

end BeyondConvexity.APTAS


