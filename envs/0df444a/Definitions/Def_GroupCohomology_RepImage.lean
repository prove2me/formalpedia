-- Prove2me | Definitions.Def_GroupCohomology_RepImage
-- name    : GroupCohomology_RepImage
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/4624cc1f-c5bd-53f8-9c07-919609f3c5f3
-- title:
--   Explicit image representation of a morphism of representations
-- statement:
--   Throughout, $k$ is a commutative ring, $G$ a group, and $f : X \to Y$ a morphism of $k$-linear $G$-representations (objects of `Rep k G`). The module gives an explicit model for the image of $f$. The object [`GroupCohomology.RepImage.obj`](../def/GroupCohomology_RepImage.html#L14) is the representation whose underlying module is the range of the $k$-linear map underlying $f$, viewed as a submodule of $Y$, with $Y.\rho$ restricted to it; the restriction is legitimate because $\rho_Y(g)(f(x)) = f(\rho_X(g)x)$, so the range is $G$-stable. Attached to it are two morphisms: `ι`, the inclusion of this subrepresentation into $Y$, acting as the submodule inclusion on elements, and `toImage`, the corestriction of $f$ to its range, so that on elements $\mathrm{toImage}(x)$ has underlying value $f(x)$ in $Y$. The accompanying lemmas record the elementwise descriptions, the factorisation `toImage_ι`, i.e. $f$ equals `toImage` followed by `ι`, and `ι_hom_injective`, the injectivity of the underlying map of `ι`.
--
--   Functoriality is provided by `map`: given a second morphism $f' : X' \to Y'$ and morphisms $\alpha : X \to X'$, $\beta : Y \to Y'$ with $f$ followed by $\beta$ equal to $\alpha$ followed by $f'$, one obtains a morphism of images $\operatorname{im} f \to \operatorname{im} f'$ which on elements is the restriction of $\beta$ (lemma `map_hom_apply_coe`), and which is compatible with the inclusions: `map_ι` states that `map` followed by $\iota_{f'}$ equals $\iota_f$ followed by $\beta$. Finally, `seq` packages the short complex of representations
--   $$\operatorname{im} f \xrightarrow{\ \iota\ } Y \xrightarrow{\ \pi\ } Y/\operatorname{im} f,$$
--   where $\pi$ is the projection onto the explicit cokernel of $f$ built from the quotient of $Y$ by the range of $f$; the required vanishing of the composite holds since elements of the image are exactly those killed by $\pi$.
--
--   **Relation to Mathlib.** The ambient category `Rep k G` and the constructions `Representation.subrepresentation` (restriction of $\rho$ to an invariant submodule) and `Representation.quotient` are Mathlib's; rather than using the categorical image in the abelian category `Rep k G`, this module fixes an explicit carrier, the range of the underlying linear map, together with its inclusion, corestriction and functoriality.
--
--   **Where it is used.** These explicit carriers, together with the companion cokernel construction, supply concrete short exact sequences of $G$-representations from which long exact sequences in group cohomology are obtained in the Galois-cohomological parts of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_RepImage.lean

import Mathlib
import Definitions.Def_GroupCohomology_RepCokernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory

namespace GroupCohomology.RepImage

universe u

variable {k G : Type u} [CommRing k] [Group G] {X Y : Rep.{u} k G} (f : X ⟶ Y)

noncomputable abbrev obj : Rep.{u} k G :=
  Rep.of (Representation.subrepresentation Y.ρ (LinearMap.range f.hom.toLinearMap) fun g => by
    rintro _ ⟨x, rfl⟩
    exact ⟨X.ρ g x, Rep.hom_comm_apply f g x⟩)

noncomputable def ι : obj f ⟶ Y := Rep.ofHom ⟨Submodule.subtype _, fun _ => rfl⟩

theorem ι_hom_apply (y : obj f) : (ι f).hom y = (y : Y) := rfl

noncomputable def toImage : X ⟶ obj f :=
  Rep.ofHom ⟨LinearMap.rangeRestrict f.hom.toLinearMap, fun g => LinearMap.ext fun x => Subtype.ext (Rep.hom_comm_apply f g x)⟩

theorem toImage_hom_apply_coe (x : X) : ((toImage f).hom x : Y) = f.hom x := rfl

theorem toImage_ι : toImage f ≫ ι f = f := Rep.hom_ext (DFunLike.ext _ _ fun _ => rfl)

theorem ι_hom_injective : Function.Injective (ι f).hom := Subtype.coe_injective

noncomputable def map {X' Y' : Rep.{u} k G} (f' : X' ⟶ Y') (α : X ⟶ X') (β : Y ⟶ Y') (w : f ≫ β = α ≫ f') : obj f ⟶ obj f' :=
  Rep.ofHom ⟨LinearMap.codRestrict _ (β.hom.toLinearMap ∘ₗ Submodule.subtype _) (by
      rintro ⟨_, x, rfl⟩
      refine ⟨α.hom x, ?_⟩
      change f'.hom (α.hom x) = β.hom (f.hom x)
      have := congrArg (fun φ : X ⟶ Y' => φ.hom x) w
      exact this.symm),
    fun g => LinearMap.ext fun y => Subtype.ext (Rep.hom_comm_apply β g (y : Y))⟩

theorem map_hom_apply_coe {X' Y' : Rep.{u} k G} (f' : X' ⟶ Y') (α : X ⟶ X') (β : Y ⟶ Y') (w : f ≫ β = α ≫ f') (y : obj f) :
    ((map f f' α β w).hom y : Y') = β.hom (y : Y) := rfl

theorem map_ι {X' Y' : Rep.{u} k G} (f' : X' ⟶ Y') (α : X ⟶ X') (β : Y ⟶ Y') (w : f ≫ β = α ≫ f') :
    map f f' α β w ≫ ι f' = ι f ≫ β := Rep.hom_ext (DFunLike.ext _ _ fun _ => rfl)

noncomputable def seq : ShortComplex (Rep.{u} k G) :=
  ShortComplex.mk (ι f) (GroupCohomology.RepCokernel.π f)
    (Rep.hom_ext (DFunLike.ext _ _ fun y => (GroupCohomology.RepCokernel.π_hom_apply_eq_zero_iff f _).2 y.2))

end GroupCohomology.RepImage


