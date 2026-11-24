-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartTorsion
-- name    : GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartTorsion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:35.202182+00:00
-- url     : https://prove2.me/theorems/9115131a-5651-49a6-8172-6f476de8e463
-- title:
--   PChart Torsion
-- statement:
--   Definitions and structural lemmas for PChart Torsion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChartTorsion.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
namespace ChartTorsion
variable {D : Type} [CommRing D] {n : ℕ} (k : ℕ) (P : Ideal (MvPolynomial (Fin n) D)) (j : Fin n)
abbrev Base := Localization.Away (Ideal.Quotient.mk P (X j))
def toBase : MvPolynomial (Fin n) D →+* Base P j :=
  (algebraMap (MvPolynomial (Fin n) D ⧸ P) (Base P j)).comp (Ideal.Quotient.mk P)
def solve (i : Fin k) (m : Fin n) : MvPolynomial (Fin k × Fin n) (Base P j) :=
  if m = j then
    -(C (IsLocalization.Away.invSelf (Ideal.Quotient.mk P (X j))) *
      ∑ l ∈ Finset.univ.erase j, C (toBase P j (X l)) * X (i, l))
  else X (i, m)
def toChart : MvPolynomial (Fin n ⊕ (Fin k × Fin n)) D →+* MvPolynomial (Fin k × Fin n) (Base P j) :=
  eval₂Hom (C.comp ((toBase P j).comp C))
    (Sum.elim (fun m => C (toBase P j (X m))) (fun im => solve k P j im.1 im.2))
abbrev Loc := Localization.Away (Ideal.Quotient.mk (incIdeal P k) (X (Sum.inl j)))
def toLoc : MvPolynomial (Fin n ⊕ (Fin k × Fin n)) D →+* Loc k P j :=
  (algebraMap _ (Loc k P j)).comp (Ideal.Quotient.mk (incIdeal P k))
theorem toLoc_mem {g : MvPolynomial (Fin n ⊕ (Fin k × Fin n)) D} (hg : g ∈ incIdeal P k) :
    toLoc k P j g = 0 := by
  simp [toLoc, Ideal.Quotient.eq_zero_iff_mem.2 hg]
def quotToLoc : MvPolynomial (Fin n) D ⧸ P →+* Loc k P j :=
  Ideal.Quotient.lift P ((toLoc k P j).comp (rename Sum.inl).toRingHom) fun _ hp =>
    toLoc_mem k P j (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hp))
theorem quotToLoc_mk (p : MvPolynomial (Fin n) D) :
    quotToLoc k P j (Ideal.Quotient.mk P p) = toLoc k P j (rename Sum.inl p) := rfl
theorem isUnit_quotToLoc : IsUnit (quotToLoc k P j (Ideal.Quotient.mk P (X j))) := by
  rw [quotToLoc_mk, rename_X]
  exact IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk (incIdeal P k) (X (Sum.inl j)))
def baseToLoc : Base P j →+* Loc k P j :=
  IsLocalization.Away.lift _ (isUnit_quotToLoc k P j)
def back : MvPolynomial (Fin k × Fin n) (Base P j) →+* Loc k P j :=
  eval₂Hom (baseToLoc k P j) fun im => toLoc k P j (X (Sum.inr im))
end ChartTorsion
end
end GroundTheory.Heights₂.Heights.Vertical


