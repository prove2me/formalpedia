-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.cechFinite_of_affSES_right
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/0f9a26ee-3ded-5655-b072-aed9d5c245bf

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Noetherian.Basic
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Theorems.Thm_Module_Finite_of_ker_le_range_of_isNoetherianRing
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_right

universe u
open AlgebraicGeometry _root_.AlgebraicGeometry.OModulePresheaf in
theorem solution {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
    [IsSeparated π] {F₁ F₂ F₃ : OModulePresheaf π} (S : OModulePresheaf.AffSES F₁ F₂ F₃) (K : V.OrderedAffineCover)
    (h₁ : F₁.CechFinite K) (h₂ : F₂.CechFinite K) : F₃.CechFinite K := by
  obtain ⟨δ₀, δ, h0, hS, -, -⟩ := S.exists_connectingHom K
  refine ⟨?_, fun i => ?_⟩
  · haveI := h₂.1; haveI := h₁.2 0
    exact Module.Finite.of_ker_le_range_of_isNoetherianRing (S.proj.H0Map K) δ₀ h0
  · haveI := h₂.2 i; haveI := h₁.2 (i + 1)
    exact Module.Finite.of_ker_le_range_of_isNoetherianRing (S.proj.HSuccMap K i) (δ i) (hS i)

end S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_right
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_right (solution)
