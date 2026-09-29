-- Prove2me | Definitions.Def_GroupCohomology_RelationHomDefect
-- name    : GroupCohomology_RelationHomDefect
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/5658427e-37f2-5147-be68-c135354cb539
-- title:
--   Precomposition on internal homs; image and cokernel defect modules
-- statement:
--   Over a commutative ring $k$ and a group $G$, [`Rep.preHom`](../def/GroupCohomology_RelationHomDefect.html#L21) turns a morphism $f : A \to A'$ of $k$-linear $G$-representations into the morphism $(\mathrm{ihom}\,A').\mathrm{obj}\,E \to (\mathrm{ihom}\,A).\mathrm{obj}\,E$ of internal homs given by precomposition, $x \mapsto x \circ f$, on the underlying $k$-linear maps; [`Rep.preHom_hom_apply`](../def/GroupCohomology_RelationHomDefect.html#L30) records this formula, [`Rep.preHom_comp`](../def/GroupCohomology_RelationHomDefect.html#L33) the contravariant functoriality $\mathrm{preHom}(f',E) \circ \mathrm{preHom}(f,E)$ (in diagrammatic order $\mathrm{preHom}\,f'\,E$ followed by $\mathrm{preHom}\,f\,E$) $= \mathrm{preHom}(f \circ f', E)$, and [`Rep.preHom_zero`](../def/GroupCohomology_RelationHomDefect.html#L37) that the zero morphism induces zero.
--
--   For $k = \mathbb{Z}$ and $B, E$ in $\mathrm{Rep}\,\mathbb{Z}\,G$ these are applied to the canonical free presentation of $B$: [`Rep.preCover`](../def/GroupCohomology_RelationHomDefect.html#L48) is precomposition with the augmentation [`Rep.freeCover B`](../def/GroupCohomology_RelationModule.html#L15) from the free $\mathbb{Z}[G]$-module on the underlying set of $B$, and [`Rep.preι`](../def/GroupCohomology_RelationHomDefect.html#L50) is precomposition with the inclusion [`Rep.relationModuleInt.ι B`](../def/GroupCohomology_RelationModule.html#L75) of the relation module, i.e. of the kernel of that augmentation (repackaged as an object of $\mathrm{Rep}\,\mathbb{Z}\,G$). [`Rep.preCover_preι`](../def/GroupCohomology_RelationHomDefect.html#L52) states that the composite of these two is zero. [`Rep.defectQ`](../def/GroupCohomology_RelationHomDefect.html#L55) is the subrepresentation of $\mathrm{Hom}(R(B),E)$ that is the range of `preι`, and [`Rep.defectX`](../def/GroupCohomology_RelationHomDefect.html#L57) the quotient of $\mathrm{Hom}(R(B),E)$ by that range. The two short complexes [`Rep.homSeq₁`](../def/GroupCohomology_RelationHomDefect.html#L59) and [`Rep.homSeq₂`](../def/GroupCohomology_RelationHomDefect.html#L64) are $\mathrm{Hom}(B,E) \to \mathrm{Hom}(\mathbb{Z}[G]^{(B)},E) \to \mathrm{defectQ}$ (second map the range restriction of `preι`) and $\mathrm{defectQ} \to \mathrm{Hom}(R(B),E) \to \mathrm{defectX}$.
--
--   Finally, for $\pi : G' \to G$, $E'$ in $\mathrm{Rep}\,\mathbb{Z}\,G'$ and $\varphi : \mathrm{Res}_\pi E \to E'$, the morphisms [`Rep.extInflR`](../def/GroupCohomology_RelationHomDefect.html#L72) and [`Rep.extInflF`](../def/GroupCohomology_RelationHomDefect.html#L76) compare $\mathrm{Res}_\pi \mathrm{Hom}(R_G(B),E)$, respectively $\mathrm{Res}_\pi \mathrm{Hom}(\mathbb{Z}[G]^{(B)},E)$, with the corresponding hom-representation for $\mathrm{Res}_\pi B$ over $G'$ and coefficients $E'$: restriction of the internal hom, then precomposition with the comparison map of relation modules (resp. of free covers), then post-composition with $\varphi$.
--
--   **Relation to Mathlib.** Mathlib supplies the internal hom `ihom` on `Rep k G` and its covariant functoriality in the coefficient variable; [`Rep.preHom`](../def/GroupCohomology_RelationHomDefect.html#L21) adds the contravariant variable. The image and cokernel used here are the project's explicit submodule/quotient models [`GroupCohomology.RepImage.obj`](../def/GroupCohomology_RepImage.html#L14) and [`GroupCohomology.RepCokernel.obj`](../def/GroupCohomology_RepCokernel.html#L13) rather than Mathlib's categorical image and cokernel.
--
--   **Where it is used.** These hom-representations and the two short complexes provide the bookkeeping for computing Ext groups of $B$ with coefficients in $E$ from the canonical free presentation $R(B) \to \mathbb{Z}[G]^{(B)} \to B$, with `defectX` measuring the failure of exactness that obstructs the comparison; `extInflR` and `extInflF` are the maps used to compare these data along a homomorphism $G' \to G$, i.e. between levels of a tower.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_RelationHomDefect.lean

import Mathlib
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RelationModuleRes
import Definitions.Def_GroupCohomology_RepCokernel
import Definitions.Def_GroupCohomology_RepImage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory

noncomputable section

namespace Rep

section generalK

universe u

variable {k G : Type u} [CommRing k] [Group G]

def preHom {A A' : Rep.{u} k G} (f : A ⟶ A') (E : Rep.{u} k G) : (ihom A').obj E ⟶ (ihom A).obj E :=
  Rep.ofHom ⟨LinearMap.lcomp k E f.hom.toLinearMap, fun g => LinearMap.ext fun x => by
    change (((ihom A').obj E).ρ g x) ∘ₗ f.hom.toLinearMap = ((ihom A).obj E).ρ g (x ∘ₗ f.hom.toLinearMap)
    erw [Rep.ihom_obj_ρ_apply, Rep.ihom_obj_ρ_apply]
    apply LinearMap.ext
    intro a
    simp only [LinearMap.coe_comp, Function.comp_apply, Representation.IntertwiningMap.toLinearMap_apply]
    rw [Rep.hom_comm_apply]⟩

theorem preHom_hom_apply {A A' : Rep.{u} k G} (f : A ⟶ A') (E : Rep.{u} k G) (x : (ihom A').obj E) :
    (preHom f E).hom x = (show A' →ₗ[k] E from x) ∘ₗ f.hom.toLinearMap := rfl

theorem preHom_comp {A A' A'' : Rep.{u} k G} (f : A ⟶ A') (f' : A' ⟶ A'') (E : Rep.{u} k G) :
    preHom f' E ≫ preHom f E = preHom (f ≫ f') E :=
  Rep.hom_ext (DFunLike.ext _ _ fun _ => rfl)

theorem preHom_zero {A A' : Rep.{u} k G} (E : Rep.{u} k G) : preHom (0 : A ⟶ A') E = 0 :=
  Rep.hom_ext (DFunLike.ext _ _ fun x => LinearMap.ext fun a => by
    change (show A' →ₗ[k] E from x) ((0 : A ⟶ A').hom a) = (0 : A →ₗ[k] E) a
    simp)

end generalK

section Int

variable {G : Type} [Group G] (B E : Rep ℤ G)

abbrev preCover : (ihom B).obj E ⟶ (ihom (Rep.free ℤ G B)).obj E := preHom (Rep.freeCover B) E

abbrev preι : (ihom (Rep.free ℤ G B)).obj E ⟶ (ihom (Rep.relationModuleInt B)).obj E := preHom (Rep.relationModuleInt.ι B) E

theorem preCover_preι : preCover B E ≫ preι B E = 0 := by
  rw [preHom_comp, Rep.relationModuleInt_ι_comp_freeCover, preHom_zero]

abbrev defectQ : Rep ℤ G := GroupCohomology.RepImage.obj (preι B E)

abbrev defectX : Rep ℤ G := GroupCohomology.RepCokernel.obj (preι B E)

def homSeq₁ : ShortComplex (Rep ℤ G) :=
  ShortComplex.mk (preCover B E) (GroupCohomology.RepImage.toImage (preι B E))
    (Rep.hom_ext (DFunLike.ext _ _ fun x => Subtype.ext
      (congrArg (fun φ : (ihom B).obj E ⟶ (ihom (Rep.relationModuleInt B)).obj E => φ.hom x) (preCover_preι B E))))

abbrev homSeq₂ : ShortComplex (Rep ℤ G) := GroupCohomology.RepImage.seq (preι B E)

end Int

section Infl

variable {G G' : Type} [Group G] [Group G'] (π : G' →* G) (B E : Rep ℤ G) (E' : Rep ℤ G') (φ : Rep.res π E ⟶ E')

abbrev extInflR : Rep.res π ((ihom (Rep.relationModuleInt B)).obj E) ⟶ (ihom (Rep.relationModuleInt (Rep.res π B))).obj E' :=
  Rep.resIhom π (Rep.relationModuleInt B) E ≫ Rep.preHom (Rep.relationModuleInt.resMap π B) (Rep.res π E) ≫
    (ihom (Rep.relationModuleInt (Rep.res π B))).map φ

abbrev extInflF : Rep.res π ((ihom (Rep.free ℤ G B)).obj E) ⟶ (ihom (Rep.free ℤ G' (Rep.res π B))).obj E' :=
  Rep.resIhom π (Rep.free ℤ G B) E ≫ Rep.preHom (Rep.freeResMap π B) (Rep.res π E) ≫ (ihom (Rep.free ℤ G' (Rep.res π B))).map φ

end Infl

end Rep

end


