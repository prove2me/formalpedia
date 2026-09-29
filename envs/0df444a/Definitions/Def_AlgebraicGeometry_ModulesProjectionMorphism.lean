-- Prove2me | Definitions.Def_AlgebraicGeometry_ModulesProjectionMorphism
-- name    : AlgebraicGeometry_ModulesProjectionMorphism
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/7b748387-1ffa-58a7-90c6-21a4dc99b958
-- title:
--   Projection morphism for a morphism of schemes
-- statement:
--   Fix a morphism of schemes $i\colon Z\to X$. Both `Z.Modules` and `X.Modules`, the categories of sheaves of modules over the structure sheaves, carry the symmetric monoidal structure obtained by localising the tensor product of presheaves of modules along sheafification, and the inverse-image functor `Modules.pullback i` is monoidal for these structures; the tensor unit $\mathbb 1_{Z.\mathrm{Modules}}$ is the structure sheaf $\mathcal O_Z$ viewed as a module over itself. Two morphisms are defined, for each $F$ in `X.Modules`.
--
--   First, `projectionMorphismMate i F` is a morphism $i^{*}\bigl(i_{*}\mathcal O_Z\otimes F\bigr)\to i^{*}F$, namely the composite of: the inverse of the monoidal structure isomorphism $\mu$ of `Modules.pullback i` at the pair $(i_{*}\mathcal O_Z, F)$, which identifies $i^{*}(i_{*}\mathcal O_Z\otimes F)$ with $i^{*}i_{*}\mathcal O_Z\otimes i^{*}F$; the right whiskering by $i^{*}F$ of the counit of the adjunction `pullbackPushforwardAdjunction i` evaluated at the unit object, $i^{*}i_{*}\mathcal O_Z\to\mathcal O_Z$; and the left unitor $\mathbb 1\otimes i^{*}F\xrightarrow{\ \sim\ }i^{*}F$.
--
--   Second, `projectionMorphism i F` is the morphism
--   $$i_{*}\mathcal O_Z\otimes_{\mathcal O_X}F\;\longrightarrow\;i_{*}\,i^{*}F$$
--   obtained by transposing the mate across the adjunction $i^{*}\dashv i_{*}$, i.e. the image of `projectionMorphismMate i F` under the hom-equivalence of `pullbackPushforwardAdjunction i`. No assertion is attached: only the morphism is constructed, so that the several statements about it (its transpose identity, its naturality in $F$, and its invertibility under hypotheses on $i$ and $F$) all speak about one and the same map. The remaining two declarations are unfolding lemmas recording these two composites as the definitions of `projectionMorphism` and `projectionMorphismMate`.
--
--   **Relation to Mathlib.** The functors `Modules.pullback`, `Modules.pushforward` and their adjunction are Mathlib's; the monoidal structure on `X.Modules` and the monoidality of `Modules.pullback i` used here come from the project's own development of the tensor product of (pre)sheaves of modules and of pullback as a monoidal functor. The projection morphism itself is the project's definition.
--
--   **Where it is used.** This morphism is the subject of the projection-formula statements used in the project's sheaf-theoretic infrastructure: later modules record that pulling it back and composing with the counit returns the mate, that it is natural in $F$, that it is compatible with restriction to open subschemes, and that it is an isomorphism in favourable cases, the general case being deduced by locality.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesProjectionMorphism.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {Z X : Scheme.{u}} (i : Z ⟶ X)

def projectionMorphismMate (F : X.Modules) :
    (Modules.pullback i).obj ((Modules.pushforward i).obj (𝟙_ Z.Modules) ⊗ F) ⟶ (Modules.pullback i).obj F :=
  (Functor.Monoidal.μIso (Modules.pullback i) ((Modules.pushforward i).obj (𝟙_ Z.Modules)) F).inv ≫
    ((pullbackPushforwardAdjunction i).counit.app (𝟙_ Z.Modules) ▷ (Modules.pullback i).obj F) ≫
    (λ_ ((Modules.pullback i).obj F)).hom

def projectionMorphism (F : X.Modules) :
    (Modules.pushforward i).obj (𝟙_ Z.Modules) ⊗ F ⟶ (Modules.pushforward i).obj ((Modules.pullback i).obj F) :=
  ((pullbackPushforwardAdjunction i).homEquiv _ _) (projectionMorphismMate i F)

theorem projectionMorphism_def (F : X.Modules) :
    projectionMorphism i F = ((pullbackPushforwardAdjunction i).homEquiv _ _) (projectionMorphismMate i F) := rfl

theorem projectionMorphismMate_def (F : X.Modules) :
    projectionMorphismMate i F =
      (Functor.Monoidal.μIso (Modules.pullback i) ((Modules.pushforward i).obj (𝟙_ Z.Modules)) F).inv ≫
        ((pullbackPushforwardAdjunction i).counit.app (𝟙_ Z.Modules) ▷ (Modules.pullback i).obj F) ≫
        (λ_ ((Modules.pullback i).obj F)).hom := rfl

end AlgebraicGeometry.Scheme.Modules

end


