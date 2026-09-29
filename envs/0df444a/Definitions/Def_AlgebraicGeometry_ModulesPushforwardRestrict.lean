-- Prove2me | Definitions.Def_AlgebraicGeometry_ModulesPushforwardRestrict
-- name    : AlgebraicGeometry_ModulesPushforwardRestrict
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/24afcb27-91bc-5579-946e-c1452c2157e5
-- title:
--   Pushforward of sheaves of modules commutes with open restriction
-- statement:
--   Throughout, $g : X \to Y$ is a morphism of schemes and $W$ an open subscheme of $Y$; $g \mid_W : g^{-1}W \to W$ denotes the restriction of $g$ over $W$, and $\iota$ denotes the inclusion of an open subscheme.
--
--   Two isomorphisms are constructed. The first, `restrictPushforwardOpensIso`, is an isomorphism of functors from the opens of $W$ to the opens of $X$: the functor sending $U \subseteq W$ to the image in $X$ of $(g\mid_W)^{-1}U$ under the open immersion $g^{-1}W \hookrightarrow X$ (i.e. `Opens.map (g ∣_ W).base` followed by `(g ⁻¹ᵁ W).ι.opensFunctor`) is isomorphic to the functor sending $U$ to $g^{-1}(\iota_W(U))$ (i.e. `W.ι.opensFunctor` followed by `Opens.map g.base`). Its component at $U$ is the transport along the equality of opens `image_morphismRestrict_preimage g W U`, so the isomorphism is an equality of open sets in each degree.
--
--   The second, `pushforwardRestrictIso`, is the induced isomorphism of functors $X\text{-Modules} \to W\text{-Modules}$ between restriction along the open immersion $g^{-1}W \hookrightarrow X$ followed by pushforward along $g\mid_W$, and pushforward along $g$ followed by restriction along $W \hookrightarrow Y$. Evaluated at an $\mathcal{O}_X$-module $\mathcal{M}$, its forward direction is a map $(g\mid_W)_*(\mathcal{M}|_{g^{-1}W}) \to (g_*\mathcal{M})|_W$ of $\mathcal{O}_W$-modules, natural in $\mathcal{M}$. It is produced from the compatibility of pushforward of sheaves of modules with composition of continuous functors of sites together with the isomorphism above.
--
--   The accompanying lemma `pushforwardRestrictIso_hom_app_app` identifies the construction on sections: for $\mathcal{M}$ and an open $U \subseteq W$, the component of the forward map over $U$ is the restriction map of the presheaf of $\mathcal{M}$ along the equality of opens $g^{-1}(\iota_W(U)) = \iota_{g^{-1}W}((g\mid_W)^{-1}U)$, i.e. the identity under that identification. Since consumers need this explicit identification on sections, the comparison is recorded as data rather than as an existence statement.
--
--   **Relation to Mathlib.** The comparison isomorphism is the project's own; it is built on Mathlib's `Scheme.Modules` pushforward and restriction functors, the pseudofunctoriality of `SheafOfModules.pushforward` along continuous functors of sites (`pushforwardComp`, `pushforwardNatIso`, `pushforwardCongr`) and `image_morphismRestrict_preimage`.
--
--   **Where it is used.** The isomorphism allows assertions about a direct image $g_*\mathcal{M}$ — local freeness, coherence, behaviour under base change — to be checked after restricting to opens, in particular affine opens, of the target, since the construction of $g_*$ is local on the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesPushforwardRestrict.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (W : Y.Opens)

noncomputable def restrictPushforwardOpensIso :
    (Opens.map (g ∣_ W).base ⋙ (g ⁻¹ᵁ W).ι.opensFunctor : W.toScheme.Opens ⥤ X.Opens) ≅
      W.ι.opensFunctor ⋙ Opens.map g.base :=
  NatIso.ofComponents (fun U => eqToIso (image_morphismRestrict_preimage g W U))
    (fun _ => Subsingleton.elim _ _)

set_option maxHeartbeats 400000 in

noncomputable def pushforwardRestrictIso :
    restrictFunctor (g ⁻¹ᵁ W).ι ⋙ pushforward (g ∣_ W) ≅ pushforward g ⋙ restrictFunctor W.ι :=
  letI := CategoryTheory.Functor.isContinuous_comp.{u} (Opens.map (g ∣_ W).base) (g ⁻¹ᵁ W).ι.opensFunctor
    (Opens.grothendieckTopology W) (Opens.grothendieckTopology ↑(g ⁻¹ᵁ W)) (Opens.grothendieckTopology X)
  letI := CategoryTheory.Functor.isContinuous_comp.{u} W.ι.opensFunctor (Opens.map g.base)
    (Opens.grothendieckTopology W) (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
  by
    refine SheafOfModules.pushforwardComp _ _ ≪≫
      SheafOfModules.pushforwardNatIso _ (restrictPushforwardOpensIso g W).symm ≪≫ ?_ ≪≫
      (SheafOfModules.pushforwardComp _ _).symm
    refine SheafOfModules.pushforwardCongr ?_
    ext U x
    simp only [Functor.sheafPushforwardContinuous_obj_obj_obj, sheafCompose_obj_obj, Functor.comp_obj,
      CommRingCat.forgetToRingCat_obj, Hom.toRingCatSheafHom, op_unop, Opens.ι_appIso, Iso.refl_inv,
      Functor.sheafPushforwardContinuousNatTrans, restrictPushforwardOpensIso, Iso.symm_hom, ObjectProperty.ι_obj,
      Category.assoc, ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      TopCat.Presheaf.pushforward_obj_obj, Functor.sheafPushforwardContinuous_map_hom_app, Functor.op_obj,
      NatTrans.op_app, NatIso.ofComponents_inv_app, eqToIso.inv, eqToHom_op, Functor.comp_map, RingCat.hom_comp,
      CommRingCat.forgetToRingCat_map_hom]
    change (X.presheaf.map (eqToHom _)) ((g ∣_ W).app (unop U) x) = g.app (W.ι ''ᵁ unop U) x
    rw [morphismRestrict_app']
    erw [← CategoryTheory.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.appLE_eq_app]
    rfl

lemma pushforwardRestrictIso_hom_app_app (M : X.Modules) (U : W.toScheme.Opens) :
    ((pushforwardRestrictIso g W).hom.app M).app U =
      M.presheaf.map (eqToHom (image_morphismRestrict_preimage g W U).symm).op := by
  first
    | rfl
    | (ext x; simp [pushforwardRestrictIso, restrictPushforwardOpensIso, SheafOfModules.pushforwardCongr,
        SheafOfModules.pushforwardNatIso, SheafOfModules.pushforwardComp, eqToHom_op, Scheme.Modules.Hom.app])

end AlgebraicGeometry.Scheme.Modules


