-- Prove2me | Definitions.Def_AlgebraicGeometry_ProperAffineClosedSubschemes
-- name    : AlgebraicGeometry_ProperAffineClosedSubschemes
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-22T07:13:49.241326+00:00
-- url     : https://prove2.me/theorems/f08e308c-6f4d-4d21-b3ca-5c1009125344
-- title:
--   Noetherian affine models of a closed subscheme
-- statement:
--   Taking schematic images transfers proper Noetherian affine models to a closed subscheme.

import Definitions.Def_AlgebraicGeometry_ClosedSubdiagramLimit
import Definitions.Def_AlgebraicGeometry_SchematicImageLimitIdeal
import Definitions.Def_AlgebraicGeometry_Scheme_ProperAffineModels

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.IdealSheafData


namespace PhilipponProperAffineApproximation

universe u

/-- Schematic images of a closed subscheme in the ambient stages give a
Noetherian proper approximation of the closed subscheme. -/
def AffineModels.closedImmersion {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    {g : Y ⟶ Spec (.of R)} (a : X ⟶ Y) [IsClosedImmersion a] (M : AffineModels g) :
    AffineModels (a ≫ g) := by
  let : Category.{u} M.index := M.category
  let : IsCofiltered M.index := M.cofiltered
  let : ∀ {i j : M.index} (v : i ⟶ j), IsAffineHom (M.ambient.map v) := fun v => M.affine v
  let : ∀ i, IsProper (M.maps.app i) := M.proper
  let : ∀ i, QuasiSeparatedSpace (M.ambient.obj i) := fun i => by
    exact @quasiSeparatedSpace_of_quasiSeparated _ _ (M.maps.app i)
      (inferInstanceAs (QuasiSeparatedSpace (Spec (M.rings.obj (op i))))) inferInstance
  let c : Cone M.ambient := ⟨Y, M.projection⟩
  let K (i : M.index) := (a ≫ c.π.app i).ker
  have hK {i j : M.index} (v : i ⟶ j) : K j ≤ (K i).map (M.ambient.map v) := by
    simp only [K, ← Scheme.Hom.ker_comp, Category.assoc, c.w, le_refl]
  let D := PhilipponClosedSubdiagramLimit.diagram M.ambient K hK
  let ι := PhilipponClosedSubdiagramLimit.inclusion M.ambient K hK
  let d := PhilipponClosedSubdiagramLimit.cone M.ambient K hK c
  let L := PhilipponClosedSubdiagramLimit.limitIdeal M.ambient K c
  have hL : L = a.ker := PhilipponImageLimitIdeal.iSup_kernels_eq M.ambientLimit a
  let r := IsClosedImmersion.lift L.subschemeι a (by rw [ker_subschemeι, hL])
  have hr : r ≫ L.subschemeι = a := IsClosedImmersion.lift_fac ..
  let : IsIso r := IsClosedImmersion.isIso_of_ker_eq a L.subschemeι r hr (by rw [ker_subschemeι, hL])
  let p : (Functor.const M.index).obj X ⟶ D := (Functor.const M.index).map r ≫ d.π
  refine
    { index := M.index
      category := M.category
      cofiltered := M.cofiltered
      rings := M.rings
      noetherian := M.noetherian
      baseInclusion := M.baseInclusion
      baseColimit := M.baseColimit
      ambient := D
      affine := PhilipponClosedSubdiagramLimit.affine_transition M.ambient K hK
      maps := ι ≫ M.maps
      proper i := inferInstanceAs (IsProper ((K i).subschemeι ≫ M.maps.app i))
      projection := p
      ambientLimit := ?_
      commutes := ?_ }
  · let e : X ≅ d.pt := asIso r
    let cX : Cone D := ⟨X, p⟩
    have hCone : d ≅ cX := Cone.ext e.symm (fun i => by
      change d.π.app i = inv r ≫ r ≫ d.π.app i
      rw [IsIso.inv_hom_id_assoc])
    exact (PhilipponClosedSubdiagramLimit.isLimit M.ambient K hK M.ambientLimit).ofIsoLimit hCone
  · intro i
    change (r ≫ d.π.app i) ≫ (ι.app i ≫ M.maps.app i) = _
    have hπ : d.π.app i ≫ ι.app i = L.subschemeι ≫ c.π.app i := by
      simp [d, ι, L, PhilipponClosedSubdiagramLimit.cone, PhilipponClosedSubdiagramLimit.inclusion]
    rw [Category.assoc, ← Category.assoc (d.π.app i), hπ]
    simp only [Category.assoc, reassoc_of% hr, c, M.commutes]

end PhilipponProperAffineApproximation

end

end


