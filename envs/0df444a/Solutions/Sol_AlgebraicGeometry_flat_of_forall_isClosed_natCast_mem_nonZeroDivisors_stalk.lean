-- Prove2me | solution 1 for AlgebraicGeometry.flat_of_forall_isClosed_natCast_mem_nonZeroDivisors_stalk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/ed46db9d-ccbe-5e74-b756-a67c8ea8c204

import Mathlib
import Theorems.Thm_AlgebraicGeometry_flat_of_forall_isClosed_germ_mul_eq_zero_of_isDedekindDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_flat_of_forall_isClosed_natCast_mem_nonZeroDivisors_stalk

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem solution
    {q : ℕ} [Fact q.Prime]
    {Y : Scheme.{0}} (πY : Y ⟶ Spec (CommRingCat.of ℤ_[q])) [LocallyOfFiniteType πY]
    (h : ∀ y : Y, IsClosed ({y} : Set Y) → πY y = IsLocalRing.closedPoint ℤ_[q] →
      ((q : ℕ) : Y.presheaf.stalk y) ∈ nonZeroDivisors (Y.presheaf.stalk y)) :
    Flat πY := by
  apply AlgebraicGeometry.flat_of_forall_isClosed_germ_mul_eq_zero_of_isDedekindDomain
  intro y hy hne c z hc hcz

  have hpt : πY y = IsLocalRing.closedPoint ℤ_[q] := by
    apply PrimeSpectrum.ext
    haveI : (πY y).asIdeal.IsPrime := (πY y).isPrime
    exact IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal hne)
  have hq := h y hy hpt

  set φ : ℤ_[q] →+* Y.presheaf.stalk y :=
    ((Scheme.ΓSpecIso (CommRingCat.of ℤ_[q])).inv ≫ πY.appTop ≫ Y.presheaf.germ ⊤ y trivial).hom with hφ
  have hcz' : φ c * z = 0 := hcz

  have key : ∀ w : Y.presheaf.stalk y, φ (q : ℤ_[q]) * w = 0 → w = 0 := by
    intro w hw
    rw [map_natCast] at hw
    exact (mem_nonZeroDivisors_iff.mp hq).1 w hw
  have keyn : ∀ (n : ℕ) (w : Y.presheaf.stalk y), φ (q : ℤ_[q]) ^ n * w = 0 → w = 0 := by
    intro n
    induction n with
    | zero => intro w hw; simpa using hw
    | succ n ih =>
      intro w hw
      rw [pow_succ, mul_assoc] at hw
      exact key w (ih _ hw)

  rw [PadicInt.unitCoeff_spec hc, map_mul, map_pow, mul_assoc] at hcz'
  have hu : IsUnit (φ ((PadicInt.unitCoeff hc : ℤ_[q]ˣ) : ℤ_[q])) := (PadicInt.unitCoeff hc).isUnit.map φ
  exact keyn _ z ((IsUnit.mul_right_eq_zero hu).mp hcz')

end S_AlgebraicGeometry_flat_of_forall_isClosed_natCast_mem_nonZeroDivisors_stalk
end P2MW
export P2MW.S_AlgebraicGeometry_flat_of_forall_isClosed_natCast_mem_nonZeroDivisors_stalk (solution)
