-- Prove2me | Definitions.Def_Yukon_889970ac05654d96eb829360
-- name    : Yukon_889970ac05654d96eb829360
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T10:50:27.418281+00:00
-- url     : https://prove2.me/theorems/7eb88558-252c-4ed1-b553-86354818085c
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.ActualWeightedFirstSlice6807.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.ActualWeightedFirstSlice6807.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/ActualWeightedFirstSlice6807.lean
--
--   yukon-proof-operation:foundation-direct-e75fb8153c2ec2eb8e2a88b9f294552d40b0a9c0dfd4dc8e8a850677e57084e5
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZjI3ZjgyMzIxYjI0NGM0ODY3OTZlMDk3ZmNhNzMyMjYwMmFkZThjMmNjOWUwZDRkMjUwM2YyMGI1NzlhMmZjNyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWU3NWZiODE1M2MyZWMyZWI4ZTJhODhiOWYyOTQ1NTJkNDBiMGE5YzBkZmQ0ZGM4ZThhODUwNjc3ZTU3MDg0ZTUiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl84ODk5NzBhYzA1NjU0ZDk2ZWI4MjkzNjAiLCJ2IjoyfQ]

/-
UNCOMPILED. Per-prime-slice integration of actual Stage multiplicities, generic
embedding points, the frozen helper-root theorem, and the original product formula.
The two remaining budget inputs are PURE FLAG finite-place bounds; they are
provided by PureFlagSliceBudget6807, not a hypothesized first-cut inequality.
-/
import Definitions.Def_Yukon_e9eca0bc79c5bf6a41901a65

import Definitions.Def_Yukon_0bbabd56aca9bc076824eff5

import Definitions.Def_Yukon_9d89c768274d20327591ec1d

import Definitions.Def_Yukon_5ded4664eee963e9eb58f377















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.ActualWeightedFirstSlice6807
open RCN057 (WeightBound)
open RCN204 (flagPole)
open scoped Classical BigOperators WithZero
open RCN002 RCN005 RCN006 RCN007 RCN026 RCN055 RCN074 RCN086 RCN095
open RCN134 RCN135 RCN136 RCN156 RCN208 RCN234 RCN244 RCN248 RCN313 RCN341
open SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open ActualSliceMultiplicity6807 ActualFirstCutPole6807
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 500000
variable {K I E T : Type} [Field K] [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Fintype T] [Nonempty T]
local instance  _root_.ProximityPrize.SubmissionLower.ActualWeightedFirstSlice6807.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.ActualWeightedFirstSlice6807.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}
local notation "Ω" => GenericField K
local notation "PE" => MvPolynomial (Fin 3) E
local notation "w" => RCN326.w

local notation "φE" => RingHom.comp (algebraMap (GenericField K) E) (polynomialEmbedding K)

/-- The per-slice zero count for ANY exponent `e` of the counted function
`baseNumerator/H^e` (denominator `c*H^(e+3)`), given its pole mass. -/
theorem first_cut_on_prime_slice_of
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hproper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1))
    (old : T → FirstTailComponent S)
    (emb : ∀ i, CoordinateField Ω (old i).1 →ₐ[Ω] E)
    (hinj : Function.Injective (fun i => embeddingPoint (old i).1 (emb i)))
    (D : Ideal PE) [D.IsPrime] (sep : SeparableLiteralCoordinate D)
    (hpoint : ∀ i, D ≤ RingHom.ker
      (MvPolynomial.aeval (embeddingPoint (old i).1 (emb i)) : PE →ₐ[E] E).toRingHom)
    (hcarrier : scalarPolynomialMap Ω E S.G ∈ D)
    (hisolated : scalarPolynomialMap Ω E
      (globalTailCut (polynomialEmbedding K) S.F (w+1)) ∉ D)
    (e d cost : ℕ)
    (hpole : surfaceMap φE S.F ∈ D → surfaceMap φE (polyH K S.F) ∉ D →
      (∀ F0 : MvPolynomial (Fin 4) K,
        (∀ i, surfaceMap (polynomialEmbedding K) F0 ∉ (old i).1) → surfaceMap φE F0 ∉ D) →
      ∀ W : Finset (Place E (CoordinateField E D)),
        (d : ℤ) * (∑ nu ∈ W, RCN187.poleOrder nu.val
          (SecondJetComponentRoots.coefficientMap φE D (baseNumerator S.F (w-1))/
            SecondJetComponentRoots.coefficientMap φE D (polyH K S.F)^e)) ≤ cost) :
    d * (∑ i, localMultiplicity S (canonicalLocalDVRFamily S hproper) (old i)) ≤ cost := by
  classical
  let A := CoordinateRing E D
  let Lf := CoordinateField E D
  letI := quotientPolynomialAlgebra E D sep.index
  letI := polynomialBaseAlgebra E D sep.index
  letI := rationalBaseAlgebra E D sep.index sep.transcendental
  letI := quotientBaseScalarTower E D sep.index
  letI := polynomialBaseScalarTower E D sep.index
  letI := quotientFractionScalarTower E D sep.index
  letI := polynomialRationalScalarTower E D sep.index sep.transcendental
  letI := rationalBaseScalarTower E D sep.index sep.transcendental
  letI : FiniteDimensional (RatFunc E) Lf := sep.finite
  letI : Algebra.IsSeparable (RatFunc E) Lf := sep.separable
  let i0 : T := Classical.choice inferInstance
  let ev := SecondJetComponentRoots.coefficientMap φE D
  let evalPoint := fun i => pointHom E D (slicePoint S (old i) (emb i) D (hpoint i))
  let mu := fun i => localMultiplicity S (canonicalLocalDVRFamily S hproper) (old i)
  let a : A := firstTailInSlice S D
  let H : A := originalToSlice (K := K) D (polyH K S.F)
  let c : A := firstTailScalarInSlice (K := K) D
  let b : A := c*H^(e+3)
  let iota : A →+* Lf := algebraMap A Lf
  have hpi : Function.Injective evalPoint := by
    intro i j hh
    have hs := pointHom_injective E D hh
    exact hinj (congrArg Subtype.val hs)
  have hmu : ∀ i, 1 ≤ mu i := fun i => one_le_localMultiplicity S hproper (old i)
  have ha : ∀ i, a ∈ (RingHom.ker (evalPoint i).toRingHom)^(mu i) := by
    intro i
    exact actual_first_tail_mem_point_power S hproper (old i) (emb i) D
      (hpoint i) hcarrier
  have hHpt : ∀ i, evalPoint i H ≠ 0 := fun i =>
    original_H_point_ne_zero S (old i) (emb i) D (hpoint i)
  have hcpt : ∀ i, evalPoint i c ≠ 0 := fun i => firstTailScalar_point_ne_zero D _
  have hb : ∀ i, evalPoint i b ≠ 0 := by
    intro i
    simpa only [b,map_mul,map_pow] using mul_ne_zero (hcpt i) (pow_ne_zero _ (hHpt i))
  have hiota : Function.Injective iota := IsFractionRing.injective A Lf
  have hHi : iota H ≠ 0 := by
    intro hz
    have hH0 : H = 0 := hiota (by simpa only [map_zero] using hz)
    exact hHpt i0 (by rw [hH0,map_zero])
  have hci : iota c ≠ 0 := by
    intro hz
    have hc0 : c = 0 := hiota (by simpa only [map_zero] using hz)
    exact hcpt i0 (by rw [hc0,map_zero])
  have hai : iota a ≠ 0 := by
    intro hz
    exact firstTailInSlice_ne_zero S D hisolated
      (hiota (by simpa only [map_zero] using hz))
  have hbi : iota b ≠ 0 := by
    simpa only [b,map_mul,map_pow] using mul_ne_zero hci (pow_ne_zero _ hHi)
  have hx : iota a / iota b ≠ 0 := div_ne_zero hai hbi
  have hrepr : iota a / iota b = ev (baseNumerator S.F (w-1))/ev (polyH K S.F)^e := by
    have hh := normalized_first_tail_identity iota a
      (originalToSlice (K := K) D (baseNumerator S.F (w-1))) H c e
      (firstTailInSlice_normal_form S D) hHi hci
    have hbv : iota (originalToSlice (K := K) D (baseNumerator S.F (w-1))) =
        ev (baseNumerator S.F (w-1)) := originalToSlice_fraction_value D _
    have hHv : iota H = ev (polyH K S.F) := originalToSlice_fraction_value D _
    exact hh.trans (by rw [hbv, hHv])
  have hnot (F0 : MvPolynomial (Fin 4) K)
      (hn0 : ∀ i, surfaceMap (polynomialEmbedding K) F0 ∉ (old i).1) :
      surfaceMap φE F0 ∉ D := by
    intro hmem
    have hz := RingHom.mem_ker.mp (hpoint i0 hmem)
    change MvPolynomial.eval (embeddingPoint (old i0).1 (emb i0))
      (surfaceMap φE F0) = 0 at hz
    apply GenericSlicePoints6807.scalar_eval_ne_zero (old i0).1 (emb i0)
      (surfaceMap (polynomialEmbedding K) F0) (hn0 i0)
    simpa only [scalar_surfaceMap, MvPolynomial.aeval_eq_eval] using hz
  have hFd : surfaceMap φE S.F ∈ D := by
    rw [← scalar_surfaceMap]
    exact D.mem_of_dvd (map_dvd (scalarPolynomialMap Ω E) S.G_dvd_surface) hcarrier
  have hHd : surfaceMap φE (polyH K S.F) ∉ D :=
    hnot _ (fun i => RCN312.firstTailComponent_regularity_not_mem S (old i))
  apply WeightedZeroMass6807.weighted_affine_points_scaled E Lf A
    evalPoint hpi mu hmu a b ha hb hx d cost
  intro W
  change (d : ℤ) * (∑ nu ∈ W, RCN187.poleOrder nu.val (iota a / iota b)) ≤ (cost : ℤ)
  rw [hrepr]
  exact hpole hFd hHd hnot W

end
end ProximityPrize.SubmissionLower.ActualWeightedFirstSlice6807


