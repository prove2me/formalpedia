-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceBundleRadicalAway
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceBundleRadicalAway
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:01.723573+00:00
-- url     : https://prove2.me/theorems/f653a82b-f366-4697-9736-1486aa7d2d17
-- title:
--   PSlice Bundle Radical Away
-- statement:
--   Definitions and structural lemmas for PSlice Bundle Radical Away, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceBundleRadicalAway.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceBundleRadicalAway
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
namespace SliceBundleRadicalAway
variable {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (d : ℕ) (q : Fin n → ℂ) (k : Fin n)
abbrev Base := Localization.Away (Ideal.Quotient.mk J (X k - C (q k)))
def toBase : MvPolynomial (Fin n) ℂ →+* Base J q k :=
  (algebraMap _ (Base J q k)).comp (Ideal.Quotient.mk J)
def rowForm (i : Fin d) : MvPolynomial (Fin d × Fin n) (Base J q k) :=
  ∑ j, X (i, j) * C (toBase J q k (X j - C (q j)))
def coeffMap : MvPolynomial (Fin d × Fin n) ℂ →+* MvPolynomial (Fin d × Fin n) (Base J q k) :=
  eval₂Hom (C.comp ((toBase J q k).comp C)) fun ij =>
    X ij - if ij.2 = k then
      C (IsLocalization.Away.invSelf (Ideal.Quotient.mk J (X k - C (q k)))) * rowForm J d q k ij.1
    else 0
def solveMap :
    MvPolynomial (Fin n) (MvPolynomial (Fin d × Fin n) ℂ) →+* MvPolynomial (Fin d × Fin n) (Base J q k) :=
  eval₂Hom (coeffMap J d q k) fun j => C (toBase J q k (X j))
abbrev Quo := MvPolynomial (Fin n) (MvPolynomial (Fin d × Fin n) ℂ) ⧸ universalSliceIdeal J d q
instance instCommRingQuo : CommRing (Quo J d q) := Ideal.Quotient.commRing _
def uQuo : Quo J d q :=
  algebraMap (MvPolynomial (Fin n) (MvPolynomial (Fin d × Fin n) ℂ)) (Quo J d q) (X k - C (C (q k)))
abbrev Tot := Localization.Away (uQuo J d q k)
def toTot : MvPolynomial (Fin n) (MvPolynomial (Fin d × Fin n) ℂ) →+* Tot J d q k :=
  algebraMap _ _
theorem toTot_apply (x : MvPolynomial (Fin n) (MvPolynomial (Fin d × Fin n) ℂ)) :
    toTot J d q k x = algebraMap (Quo J d q) (Tot J d q k)
      (algebraMap (MvPolynomial (Fin n) (MvPolynomial (Fin d × Fin n) ℂ)) (Quo J d q) x) :=
  IsScalarTower.algebraMap_apply _ _ _ x
theorem toTot_eq_zero {x : MvPolynomial (Fin n) (MvPolynomial (Fin d × Fin n) ℂ)}
    (hx : x ∈ universalSliceIdeal J d q) : toTot J d q k x = 0 := by
  rw [toTot_apply, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
def quotToTot : (MvPolynomial (Fin n) ℂ ⧸ J) →+* Tot J d q k :=
  Ideal.Quotient.lift J ((toTot J d q k).comp (MvPolynomial.map C)) fun a ha =>
    toTot_eq_zero J d q k (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha))
theorem quotToTot_isUnit : IsUnit (quotToTot J d q k (Ideal.Quotient.mk J (X k - C (q k)))) := by
  have e : MvPolynomial.map (C : ℂ →+* MvPolynomial (Fin d × Fin n) ℂ) (X k - C (q k)) =
      X k - C (C (q k)) := by simp
  rw [quotToTot, Ideal.Quotient.lift_mk, RingHom.comp_apply, e, toTot_apply]
  exact IsLocalization.Away.algebraMap_isUnit (S := Tot J d q k) (uQuo J d q k)
def baseToTot : Base J q k →+* Tot J d q k :=
  IsLocalization.Away.lift (R := MvPolynomial (Fin n) ℂ ⧸ J) (S := Base J q k) (P := Tot J d q k)
    (Ideal.Quotient.mk J (X k - C (q k))) (g := quotToTot J d q k) (quotToTot_isUnit J d q k)
def backMap : MvPolynomial (Fin d × Fin n) (Base J q k) →+* Tot J d q k :=
  eval₂Hom (baseToTot J d q k) fun ij => toTot J d q k (C (X ij))
end SliceBundleRadicalAway
end
end GroundTheory.Heights₂.Heights


