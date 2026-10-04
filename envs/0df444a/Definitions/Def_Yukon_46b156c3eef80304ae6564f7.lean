-- Prove2me | Definitions.Def_Yukon_46b156c3eef80304ae6564f7
-- name    : Yukon_46b156c3eef80304ae6564f7
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T04:12:37.555246+00:00
-- url     : https://prove2.me/theorems/94da6064-50eb-43e1-8c64-136f5e8c2bda
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceRegularRestriction6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceRegularRestriction6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceRegularRestriction6814.lean
--
--   yukon-proof-operation:certificate-b56-9267c858de0febb2b21cf70bcaca03c3e9278614ea44f88af2c99e0a6b48b58f
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYjQwNzAyZDJmMDkzMDdkNWFiYjI2ZDczYzEyZTY5YTEzMDNjZDZjMDQ3MDdlNWVjMzRmNzhiMGI2ZmY1YjdmOSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLWI1Ni05MjY3Yzg1OGRlMGZlYmIyYjIxY2Y3MGJjYWNhMDNjM2U5Mjc4NjE0ZWE0NGY4OGFmMmM5OWUwYTZiNDhiNThmIiwidGFnIjoiYmV0dGVyLWNvZGVzIiwidGFyZ2V0IjoiWXVrb25fNDZiMTU2YzNlZWY4MDMwNGFlNjU2NGY3IiwidiI6Mn0]

import Definitions.Def_Yukon_59d67686b631ae0e4cbc56da














































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Restrict the constructed projections to a smaller regular locus,
without paying their shared budget again. This allows the old Z source's
leading coefficient to be excluded on exactly the counted family. -/
namespace ProximityPrize.SubmissionLower.MovingSourceRegularRestriction6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open scoped BigOperators
open RCN002 RCN046 RCN095 RCN264 RCN341 RCN344

variable {K : Type} [Field K]
    {G M R : MvPolynomial (Fin 3) K}

def forgetExtra (L : MvPolynomial (Fin 3) K)
    (C : RegularComponent K G M (R*L)) : RegularComponent K G M R := by
  classical
  exact ⟨C.1,(mem_regularComponents K).mpr ⟨regularComponent_mem K G M (R*L) C,by
    intro hz
    exact regularComponent_H_not_mem K G M (R*L) C (C.1.mul_mem_right L hz)⟩⟩

theorem forgetExtra_injective (L : MvPolynomial (Fin 3) K) :
    Function.Injective (forgetExtra (G:=G) (M:=M) (R:=R) L) := by
  intro C D h
  exact Subtype.ext (congrArg (fun C0 : RegularComponent K G M R => C0.1) h)

theorem extra_not_mem (L : MvPolynomial (Fin 3) K)
    (C : RegularComponent K G M (R*L)) : L∉C.1 := by
  intro hz
  exact regularComponent_H_not_mem K G M (R*L) C (C.1.mul_mem_left R hz)

public theorem sum_pullback_le {I J : Type} [Fintype I] [Fintype J]
    (f : I → J) (hf : Function.Injective f) (v : J → ℕ) :
    (∑ i, v (f i))≤∑ j, v j := by
  classical
  letI : DecidableEq J := Classical.decEq J
  calc
    _ = ∑ j ∈ Finset.univ.image f, v j := (Finset.sum_image (fun _ _ _ _ h => hf h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

def restrict_projection_family [IsAlgClosed K]
    (base : ∀ C : RegularComponent K G M R, SeparableLiteralCoordinate C.1)
    (p q : FlagDegree) (unit : AdaptiveUnitProjectionFamily base p q)
    (L : MvPolynomial (Fin 3) K) :
    AdaptiveUnitProjectionFamily (fun C => base (forgetExtra L C)) p q where
  zProjection := fun C => unit.zProjection (forgetExtra L C)
  yzProjection := fun C => unit.yzProjection (forgetExtra L C)
  allProjection := fun C => unit.allProjection (forgetExtra L C)
  zValue := fun C => unit.zValue (forgetExtra L C)
  allTranscendental := fun C => unit.allTranscendental (forgetExtra L C)
  zPole_eq := fun C v => unit.zPole_eq (forgetExtra L C) v
  yzPole_eq := fun C v => unit.yzPole_eq (forgetExtra L C) v
  allPole_eq := fun C v => unit.allPole_eq (forgetExtra L C) v
  sum_zDegree_le := (sum_pullback_le (forgetExtra L) (forgetExtra_injective L)
    (fun C => coordinateDegree K (CoordinateField K C.1) (unit.zProjection C))).trans unit.sum_zDegree_le
  sum_yzDegree_le := (sum_pullback_le (forgetExtra L) (forgetExtra_injective L)
    (fun C => coordinateDegree K (CoordinateField K C.1) (unit.yzProjection C))).trans unit.sum_yzDegree_le
  sum_allDegree_le := (sum_pullback_le (forgetExtra L) (forgetExtra_injective L)
    (fun C => coordinateDegree K (CoordinateField K C.1) (unit.allProjection C))).trans unit.sum_allDegree_le




open RCN084 RCN136 RCN207
open MovingFiberThreeSources6811 MovingSourceHybridCount6814

/-- Check the projection restriction and hybrid handoff over an abstract
field, before instantiating the nested generic fields in the packet. -/
theorem restricted_source_point_count
    {K0 : Type} [Field K0] [IsAlgClosed K]
    (phi : Polynomial K0 →+* K) (F : MvPolynomial (Fin 4) K0) (S : Source F)
    (carrier : MvPolynomial (Fin 3) K) (p : FlagDegree)
    (hcarrier : carrier≠0) (hcarrierF : carrier∣surfaceMap phi F) (hp : PolynomialInFlag p carrier)
    (c : ℕ) [CharP K c] (hunit : 2*(p.zOnly+p.yz+p.all)<c)
    (h2 : (2 : K)≠0) (hfact : (S.k.factorial : K)≠0)
    (quadratic A : MvPolynomial (Fin 3) K) (target : K)
    (hquadratic : PolynomialInFlag (2 • unitAllFlag) quadratic) (hA : PolynomialInFlag unitYZFlag A)
    (R : MvPolynomial (Fin 3) K) (hHdiv : surfaceMap phi (RCN313.polyH K0 F)∣R)
    (base : ∀ C : RegularComponent K carrier
      (movingEquation (surfaceMap phi (RCN313.polyH K0 F)) (surfaceMap phi (RCN313.polyG K0 F))
        quadratic A target) R, SeparableLiteralCoordinate C.1)
    (pNew qNew : FlagDegree) (unit : AdaptiveUnitProjectionFamily base pNew qNew)
    (W : FlagDegree) (cut : MvPolynomial (Fin 3) K) (hcut : PolynomialInFlag W cut)
    (points : Finset (Fin 3 → K))
    (hG : ∀ x ∈ points, MvPolynomial.eval x carrier=0)
    (hM : ∀ x ∈ points, MvPolynomial.eval x
      (movingEquation (surfaceMap phi (RCN313.polyH K0 F)) (surfaceMap phi (RCN313.polyG K0 F))
        quadratic A target)=0)
    (hR : ∀ x ∈ points, MvPolynomial.eval x (R*S.leading phi)≠0)
    (hzero : ∀ x ∈ points, MvPolynomial.aeval x cut=0)
    (hisolated : ∀ x ∈ points, IsolatedPoint carrier
      (movingEquation (surfaceMap phi (RCN313.polyH K0 F)) (surfaceMap phi (RCN313.polyG K0 F))
        quadratic A target) cut x) :
    S.d*points.card≤W.zOnly*flagMixed p unitZFlag S.flag+
      S.d*(W.yz*flagMixed pNew qNew unitYZFlag+W.all*flagMixed pNew qNew unitAllFlag) := by
  let M := movingEquation (surfaceMap phi (RCN313.polyH K0 F))
    (surfaceMap phi (RCN313.polyG K0 F)) quadratic A target
  let base' := fun C : RegularComponent K carrier M (R*S.leading phi) =>
    base (forgetExtra (S.leading phi) C)
  let unit' := restrict_projection_family base pNew qNew unit (S.leading phi)
  have hH (C : RegularComponent K carrier M (R*S.leading phi)) :
      surfaceMap phi (RCN313.polyH K0 F)∉C.1 := by
    intro hz
    exact regularComponent_H_not_mem K carrier M (R*S.leading phi) C
      (C.1.mem_of_dvd (dvd_mul_of_dvd_left hHdiv _) hz)
  have hZ := old_z_bound_on_new_projections phi F S carrier p hcarrier hcarrierF hp
    c hunit h2 hfact quadratic A target hquadratic hA (R*S.leading phi)
    hH (extra_not_mem (S.leading phi)) base' pNew qNew unit'
  exact hybrid_isolated_points base' pNew qNew unit' S.d (flagMixed p unitZFlag S.flag)
    hZ W cut hcut points hG hM hR hzero hisolated







end
end ProximityPrize.SubmissionLower.MovingSourceRegularRestriction6814


