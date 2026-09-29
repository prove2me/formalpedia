-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.exists_algHom_away_apply_ratio_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/75e0e68e-d418-57a0-ae62-9ba32d9fc891

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq

set_option autoImplicit false

universe u v

p2m_open "MvPolynomial HomogeneousLocalization AlgebraicGeometry P2MW.S_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "ProjSpace.ratio ProjSpace.val_algebraMap"
namespace ProjSpace
p2m_export "AlgebraicGeometry.ProjSpace" "ratio val_algebraMap map"
namespace ChartLift
p2m_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ) (i : Fin (n + 1))
  {B : Type v} [CommRing B] [Algebra R B] (b : Fin (n + 1) → B) (hb : b i = 1)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

noncomputable def lift0 : Localization.Away (X i : MvPolynomial (Fin (n + 1)) R) →+* B :=
  IsLocalization.Away.lift (X i : MvPolynomial (Fin (n + 1)) R)
    (g := (MvPolynomial.aeval b : MvPolynomial (Fin (n + 1)) R →ₐ[R] B).toRingHom)
    (by simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, hb]; exact isUnit_one)

theorem lift0_algebraMap (p : MvPolynomial (Fin (n + 1)) R) :
    lift0 R n i b hb (algebraMap _ _ p) = MvPolynomial.aeval b p :=
  IsLocalization.Away.lift_eq _ _ _

noncomputable def liftAway : Away 𝒜 (X i : MvPolynomial (Fin (n + 1)) R) →ₐ[R] B where
  toRingHom := (lift0 R n i b hb).comp (algebraMap (Away 𝒜 (X i : MvPolynomial (Fin (n + 1)) R)) (Localization.Away (X i : MvPolynomial (Fin (n + 1)) R)))
  commutes' r := by
    show lift0 R n i b hb ((algebraMap R (Away 𝒜 (X i : MvPolynomial (Fin (n + 1)) R)) r).val) = algebraMap R B r
    rw [ProjSpace.val_algebraMap, lift0_algebraMap, MvPolynomial.aeval_C]

theorem liftAway_ratio (k : Fin (n + 1)) : liftAway R n i b hb (ProjSpace.ratio R n i k) = b k := by
  show lift0 R n i b hb (ProjSpace.ratio R n i k).val = b k
  rw [ProjSpace.ratio, Away.val_mk, Localization.mk_eq_mk', lift0, IsLocalization.Away.lift, IsLocalization.lift_mk'_spec]

  show MvPolynomial.aeval b (X k) = MvPolynomial.aeval b (X i ^ 1) * b k
  simp [hb]

include hb in
theorem exists_algHom :
    ∃ φ : Away 𝒜 (X i : MvPolynomial (Fin (n + 1)) R) →ₐ[R] B, ∀ k, φ (ProjSpace.ratio R n i k) = b k :=
  ⟨liftAway R n i b hb, liftAway_ratio R n i b hb⟩

end AlgebraicGeometry.ProjSpace.ChartLift

section
attribute [local instance] MvPolynomial.gradedAlgebra
theorem solution
    (R : Type u) [CommRing R] (n : ℕ) (i : Fin (n + 1))
    {B : Type v} [CommRing B] [Algebra R B] (b : Fin (n + 1) → B) (hb : b i = 1) :
    ∃ φ : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) →ₐ[R] B,
      ∀ k, φ (ProjSpace.ratio R n i k) = b k :=
  AlgebraicGeometry.ProjSpace.ChartLift.exists_algHom R n i b hb
end

end S_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq
end P2MW
export P2MW.S_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq (solution)
