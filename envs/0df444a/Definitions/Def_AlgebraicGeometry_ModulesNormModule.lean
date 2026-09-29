-- Prove2me | Definitions.Def_AlgebraicGeometry_ModulesNormModule
-- name    : AlgebraicGeometry_ModulesNormModule
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/233ed011-04ac-54e6-a681-22a6c1d44a16
-- title:
--   Norm of a sheaf of modules along a scheme morphism
-- statement:
--   For a morphism of schemes $\pi \colon X \to Y$, a natural number $d$ and a sheaf of modules $L$ on $X$, `normModule` is the sheaf of modules on $Y$ given by
--   $$\det\nolimits_d(\pi_* L) \otimes \bigl(\det\nolimits_d(\pi_* \mathcal O_X)\bigr)^{\vee},$$
--   where $\pi_*$ is the pushforward functor on sheaves of modules, $\det_d M$ denotes `det d M`, the $d$-th exterior power obtained by applying the presheaf-level exterior power functor and then sheafifying, $\otimes$ is the monoidal product on sheaves of modules (the sheafification of the presheaf tensor product), the unit $\mathbb 1$ is the structure sheaf viewed as a module over itself, and $A^{\vee}$ is `dual A`, the internal hom $(\mathrm{ihom}\,A)(\mathbb 1)$ for the monoidal closed structure. No hypothesis is imposed on $\pi$, $d$ or $L$: the rank $d$ is an explicit parameter, and the definition is total.
--
--   The module also records the norm as a functor `normModuleFunctor` in the argument $L$, namely $\pi_*$ followed by the $d$-th exterior power followed by tensoring on the right with $(\det_d(\pi_*\mathcal O_X))^{\vee}$; its value on objects is `normModule`, and on a morphism $f$ it is $\Lambda^d(\pi_* f)$ whiskered with the fixed dual factor. From this, `normModuleMapIso` transports isomorphisms $L \cong L'$. A helper `dualCongr` turns an isomorphism $A \cong B$ of sheaves of modules into $A^{\vee} \cong B^{\vee}$ via the `MonoidalClosed.pre` construction. Further isomorphisms compare the norm along the identity morphism with $\det_d L \otimes (\det_d \mathcal O_X)^{\vee}$, and the norms along two morphisms that are equal. Finally, for $L = \mathbb 1$ the norm is $E \otimes E^{\vee}$ with $E = \det_d(\pi_*\mathcal O_X)$, and `normModuleUnitEval` is the evaluation morphism $E \otimes E^{\vee} \to \mathcal O_Y$.
--
--   **Relation to Mathlib.** Mathlib has no norm of a sheaf of modules along a morphism of schemes; it is defined here from Mathlib's sheaves of modules, pushforward and monoidal-closed API together with the project's own exterior power of (pre)sheaves of modules and the project's monoidal and monoidal closed structures on sheaves of modules.
--
--   **Where it is used.** This is the determinant description of the norm of a line bundle along a finite locally free morphism, specialised in the formalisation to maps such as the degeneracy morphisms between modular curves; the properties of the norm (multiplicativity, base change, the unit isomorphism) are established in separate statements built on these definitions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesNormModule.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

def normModule (π : X ⟶ Y) (d : ℕ) (L : X.Modules) : Y.Modules :=
  det d ((pushforward π).obj L) ⊗ dual (det d ((pushforward π).obj (𝟙_ X.Modules)))

theorem normModule_def (π : X ⟶ Y) (d : ℕ) (L : X.Modules) :
    normModule π d L = det d ((pushforward π).obj L) ⊗ dual (det d ((pushforward π).obj (𝟙_ X.Modules))) := rfl

def normModuleFunctor (π : X ⟶ Y) (d : ℕ) : X.Modules ⥤ Y.Modules :=
  (pushforward π ⋙ exteriorPower Y d) ⋙ tensorRight (dual (det d ((pushforward π).obj (𝟙_ X.Modules))))

@[simp] theorem normModuleFunctor_obj (π : X ⟶ Y) (d : ℕ) (L : X.Modules) :
    (normModuleFunctor π d).obj L = normModule π d L := rfl

theorem normModuleFunctor_map (π : X ⟶ Y) (d : ℕ) {L L' : X.Modules} (f : L ⟶ L') :
    (normModuleFunctor π d).map f =
      (exteriorPower Y d).map ((pushforward π).map f) ▷ dual (det d ((pushforward π).obj (𝟙_ X.Modules))) := rfl

def normModuleMapIso (π : X ⟶ Y) (d : ℕ) {L L' : X.Modules} (e : L ≅ L') :
    normModule π d L ≅ normModule π d L' :=
  (normModuleFunctor π d).mapIso e

def dualCongr {A B : Y.Modules} (e : A ≅ B) : dual A ≅ dual B where
  hom := (MonoidalClosed.pre e.inv).app (𝟙_ Y.Modules)
  inv := (MonoidalClosed.pre e.hom).app (𝟙_ Y.Modules)
  hom_inv_id := by
    rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, e.hom_inv_id, MonoidalClosed.pre_id, NatTrans.id_app]
  inv_hom_id := by
    rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, e.inv_hom_id, MonoidalClosed.pre_id, NatTrans.id_app]

def normModuleIdIso (d : ℕ) (L : X.Modules) :
    normModule (𝟙 X) d L ≅ det d L ⊗ dual (det d (𝟙_ X.Modules)) :=
  ((exteriorPower X d).mapIso ((pushforwardId X).app L)) ⊗ᵢ
    dualCongr ((exteriorPower X d).mapIso ((pushforwardId X).app (𝟙_ X.Modules)))

def normModuleCongr {π π' : X ⟶ Y} (h : π = π') (d : ℕ) (L : X.Modules) :
    normModule π d L ≅ normModule π' d L :=
  ((exteriorPower Y d).mapIso ((pushforwardCongr h).app L)) ⊗ᵢ
    dualCongr ((exteriorPower Y d).mapIso ((pushforwardCongr h).app (𝟙_ X.Modules)))

theorem normModule_tensorUnit (π : X ⟶ Y) (d : ℕ) :
    normModule π d (𝟙_ X.Modules) =
      det d ((pushforward π).obj (𝟙_ X.Modules)) ⊗ dual (det d ((pushforward π).obj (𝟙_ X.Modules))) := rfl

def normModuleUnitEval (π : X ⟶ Y) (d : ℕ) : normModule π d (𝟙_ X.Modules) ⟶ 𝟙_ Y.Modules :=
  (ihom.ev (det d ((pushforward π).obj (𝟙_ X.Modules)))).app (𝟙_ Y.Modules)

end AlgebraicGeometry.Scheme.Modules

end


