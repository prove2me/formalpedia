-- Prove2me | solution 1 for AlgebraicGeometry.map_appTop_mem_nonZeroDivisors_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/45c1090d-7b1a-5e1d-a1a7-a65a45a4d75c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_map_appTop_mem_nonZeroDivisors_of_flat
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite

universe u

theorem solution
    {R : Type u} [CommRing R] {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Flat f]
    (r : R) (hr : r ∈ nonZeroDivisors R) (U : Y.Opens) (hU : IsAffineOpen U) :
    Y.presheaf.map (homOfLE le_top).op (f.appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom r))
      ∈ nonZeroDivisors Γ(Y, U) := by
  have happ : Y.presheaf.map (homOfLE le_top).op (f.appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom r))
      = (f.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (.of R)).inv.hom r) := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    rfl
  rw [happ]
  have hflat : (f.appLE ⊤ U le_top).hom.Flat :=
    HasRingHomProperty.appLE @Flat f inferInstance ⟨⊤, isAffineOpen_top (Spec (.of R))⟩ ⟨U, hU⟩ le_top

  let e : R ≃+* Γ(Spec (.of R), ⊤) := (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm
  let φ : R →+* Γ(Y, U) := (f.appLE ⊤ U le_top).hom.comp e.toRingHom
  have hφflat : φ.Flat := (RingHom.Flat.of_bijective e.bijective).comp hflat
  letI := φ.toAlgebra
  haveI : Module.Flat R Γ(Y, U) := hφflat
  have hreg : IsSMulRegular Γ(Y, U) r := Module.Flat.isSMulRegular_of_nonZeroDivisors hr
  have hφr : φ r = (f.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (.of R)).inv.hom r) := rfl
  rw [← hφr]
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  apply hreg
  show r • x = r • (0 : Γ(Y, U))
  rw [smul_zero, Algebra.smul_def]
  show φ r * x = 0
  rw [mul_comm]; exact hx

end S_AlgebraicGeometry_map_appTop_mem_nonZeroDivisors_of_flat
end P2MW
export P2MW.S_AlgebraicGeometry_map_appTop_mem_nonZeroDivisors_of_flat (solution)
