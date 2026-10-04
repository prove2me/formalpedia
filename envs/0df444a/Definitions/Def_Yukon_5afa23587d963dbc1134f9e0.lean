-- Prove2me | Definitions.Def_Yukon_5afa23587d963dbc1134f9e0
-- name    : Yukon_5afa23587d963dbc1134f9e0
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T14:33:07.971149+00:00
-- url     : https://prove2.me/theorems/e61f167a-1a9f-4d83-8f12-bbde471eecdf
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.HFreeDischarge6812.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.HFreeDischarge6812.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/HFreeDischarge6812.lean
--
--   yukon-proof-operation:foundation-direct-d2484c70d5f41debae4a70b015569813189c3fe153a4f3f3316374d158cbd33d
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYWY5ZGU3Y2YzNTYyNTg0M2IxOWQyNDJlNjM0ZWIwOWM0M2YwMTUyNjZmOTFkN2RlMTAyN2UxN2M0YjE2Nzk0NiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWQyNDg0YzcwZDVmNDFkZWJhZTRhNzBiMDE1NTY5ODEzMTg5YzNmZTE1M2E0ZjNmMzMxNjM3NGQxNThjYmQzM2QiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl81YWZhMjM1ODdkOTYzZGJjMTEzNGY5ZTAiLCJ2IjoyfQ]

import Definitions.Def_Yukon_6063c44a017b9098f88bc52e

import Definitions.Def_Yukon_c64d4480230f512d8aedf66b

import Definitions.Def_Yukon_1994a5a4fe112e6c7d911069






































































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-!
Discharge of the H-free stage hypothesis `MovingFiberRetainedStage6811.HFreeStage` through
`HFree6812.hfree_slice_budget`, channel by channel.  One input remains OPEN, isolated as a single
named theorem: `hdefer_gap` (continuity + residual separability at every place of the slice
function field).  `hchar_gap` (pole/zero orders below the characteristic) is proved in
`HFreeChar6812` from the cell's total-degree bound.
-/
namespace ProximityPrize.SubmissionLower.HFree6812
open WithZero MvPolynomial
open RCN002 RCN208 RCN202 RCN135 RCN136 RCN219 RCN341 RCN313 RCN055 RCN095 RCN204
noncomputable section
set_option autoImplicit false

section Gaps
variable {K : Type} [Field K] {E : Type} [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]

/-- hdefer: pieces 3 and 4 (`CrudeBound`, `ResiduallySeparable`) at every place of
`L0` over the slice.  Exactly the `hdefer` input of `hfree_slice_budget`. -/
theorem hdefer_gap (F : MvPolynomial (Fin 4) K) (D : Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime]
    (hHD : surfaceMap (phiE K E) (polyH K F) ∉ D)
    (c : Fin 3 → GenericField K) (i : Fin 3) (hci : c i = 1) (q : Fin 3 → Polynomial K)
    (hq : ∀ m, polynomialEmbedding K (q m) = c m) (hq1 : i = 1 ∨ q 1 = 0)
    (hslice : MvPolynomial.C (sliceValue (GenericField K) E) -
      scalarPolynomialMap (GenericField K) E (∑ m, MvPolynomial.C (c m) * MvPolynomial.X m) ∈ D)
    (N : ℕ) (hN : MvPolynomial.weightedTotalDegree ![0,1,1,1] F ≤ N)
    (hNK : ∀ n : ℕ, 0 < n → n ≤ N → (n : K) ≠ 0) :
    ∀ (F₀ : MvPolynomial (Fin 4) K) [Fact (Irreducible F₀)] (hdvd : F₀ ∣ F)
      (hker : RingHom.ker (sliceMap (K := K) D) = Ideal.span {F₀})
      (ν : RCN026.Place E (CoordinateField E D)) (e : ℕ) (v : Valuation (SliceField F₀) ℤᵐ⁰),
      1 ≤ e → (∃ x, v x = exp (-1)) →
      (∀ x, ν.val (sliceEmbedding D F₀ hker x) = v x ^ e) →
      (∃ C, CrudeBound v (sliceDerivation F F₀ hdvd) C) ∧
      ResiduallySeparable v (sliceDerivation F F₀ hdvd)
        (exp (vpole v (sliceDerivation F F₀ hdvd (sliceLinearL F₀ q)))) :=
  hdefer_holds F D hHD c i hci q hq hq1 hslice N hN hNK

/-- hchar: on a slice component of a surface of total `(Y,Y',Γ)`-degree `≤ N ≤ 9678`, the pole
and zero orders entering the lowest-term argument are below the characteristic (`hchar_holds`).
This is the `hchar` input of `hfree_slice_budget`. -/
theorem hchar_gap [CharP K 2130706433] (F : MvPolynomial (Fin 4) K)
    (D : Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime] (sep : SeparableLiteralCoordinate D)
    (hFD : surfaceMap (phiE K E) F ∈ D) (hHD : surfaceMap (phiE K E) (polyH K F) ∉ D)
    (c : Fin 3 → GenericField K) (i : Fin 3) (hci : c i = 1)
    (hslice : MvPolynomial.C (sliceValue (GenericField K) E) -
      scalarPolynomialMap (GenericField K) E (∑ m, MvPolynomial.C (c m) * MvPolynomial.X m) ∈ D)
    (N : ℕ) (hN : MvPolynomial.weightedTotalDegree ![0,1,1,1] F ≤ N) (hN9 : N ≤ 9678) :
    ∀ ν : RCN026.Place E (CoordinateField E D), ∀ n : ℕ, 0 < n →
      (n : ℤ) ≤ max (flagPole ν.val (coordinate E D) unitAllFlag)
        (RCN026.zeroOrder E (CoordinateField E D) ν
          (SecondJetComponentRoots.coefficientMap (phiE K E) D (polyH K F))) → (n : K) ≠ 0 :=
  hchar_holds F D sep hFD hHD c i hci hslice N hN hN9

end Gaps

section Stage
open MovingFiberRetainedStage6811 CommonLinearChannels6807 LocatorHybridCells
variable {K I : Type} [Field K] [CharP K 2130706433]
  {Gamma : Finset K} {x : I → K} {flag : FlagDegree} {errorCap : ℕ}
  [CharP (GenericField K) 2130706433]

omit [CharP (GenericField K) 2130706433] in
public theorem natCast_ne_zero_K {n : ℕ} (h0 : 0 < n) (hn : n < 2130706433) : (n : K) ≠ 0 := by
  intro h
  exact absurd (Nat.le_of_dvd h0 ((CharP.cast_eq_zero_iff K 2130706433 n).1 h)) (by omega)






end Stage

end
end ProximityPrize.SubmissionLower.HFree6812


