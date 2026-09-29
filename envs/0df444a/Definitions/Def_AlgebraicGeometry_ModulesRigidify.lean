-- Prove2me | Definitions.Def_AlgebraicGeometry_ModulesRigidify
-- name    : AlgebraicGeometry_ModulesRigidify
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/f1fb2cec-407e-586d-b187-b738cdd505d1
-- title:
--   Rigidification of sheaves of modules along a morphism
-- statement:
--   Throughout, for a scheme $X$ the category `X.Modules` of sheaves of $\mathcal O_X$-modules carries the symmetric monoidal closed structure obtained by localising presheaves of modules, with unit object the structure sheaf; `Scheme.Modules.dual L` is the internal hom $\mathcal Hom(\mathcal L, \mathcal O_X)$, i.e. the value at the unit object of the internal-hom functor with first argument $\mathcal L$.
--
--   Two constructions are made. First, `dualMapIso`: for a scheme $X$ and an isomorphism $e \colon \mathcal L \cong \mathcal L'$ of sheaves of $\mathcal O_X$-modules, an isomorphism $\mathcal L^\vee \cong \mathcal L'^\vee$, obtained by transporting $e^{-1}$ through the contravariant internal-hom functor and evaluating at the unit object. Second, for morphisms of schemes $\sigma \colon T \to P$ and $q \colon P \to T$ and a sheaf of $\mathcal O_P$-modules $\mathcal L$, the rigidification
--   $$\operatorname{rigidify}_{\sigma,q}(\mathcal L) \;=\; \mathcal L \otimes q^{*}\bigl((\sigma^{*}\mathcal L)^{\vee}\bigr),$$
--   again a sheaf of $\mathcal O_P$-modules, where $\sigma^{*}$ and $q^{*}$ denote the pullback functors on sheaves of modules along $\sigma$ and $q$. The lemma `rigidify_def` records this defining formula. No hypothesis relating $\sigma$ and $q$ (such as $\sigma$ being a section of $q$) and no invertibility hypothesis on $\mathcal L$ is imposed at this stage. Finally `rigidifyMapIso` supplies functoriality on isomorphisms: an isomorphism $e \colon \mathcal L \cong \mathcal L'$ of sheaves of $\mathcal O_P$-modules induces $\operatorname{rigidify}_{\sigma,q}(\mathcal L) \cong \operatorname{rigidify}_{\sigma,q}(\mathcal L')$, namely the tensor product of $e$ with the $q$-pullback of the dual isomorphism attached to $\sigma^{*}e$.
--
--   **Relation to Mathlib.** The monoidal, symmetric and monoidal-closed structures on sheaves of $\mathcal O_X$-modules, and hence the dual used here, come from the project's own construction of internal homs for presheaves of modules and its transport along sheafification; the pullback functors on sheaves of modules are Mathlib's. Rigidification itself has no Mathlib counterpart.
--
--   **Where it is used.** Rigidification is the standard device turning an arbitrary line bundle on a $T$-scheme $q \colon P \to T$ with a section $\sigma$ into one whose pullback along $\sigma$ is trivial, and so feeds the definition of the relative Picard functor of rigidified line bundles used in the construction of Jacobians of curves in this development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesRigidify.lean

import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {T P : Scheme.{u}}

def dualMapIso {X : Scheme.{u}} {L L' : X.Modules} (e : L ≅ L') :
    Scheme.Modules.dual L ≅ Scheme.Modules.dual L' :=
  ((MonoidalClosed.internalHom (C := X.Modules)).mapIso e.symm.op).app (𝟙_ X.Modules)

def rigidify (σ : T ⟶ P) (q : P ⟶ T) (L : P.Modules) : P.Modules :=
  L ⊗ (Scheme.Modules.pullback q).obj
    (Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj L))

lemma rigidify_def (σ : T ⟶ P) (q : P ⟶ T) (L : P.Modules) :
    rigidify σ q L = L ⊗ (Scheme.Modules.pullback q).obj
      (Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj L)) := rfl

def rigidifyMapIso (σ : T ⟶ P) (q : P ⟶ T) {L L' : P.Modules} (e : L ≅ L') :
    rigidify σ q L ≅ rigidify σ q L' :=
  e ⊗ᵢ (Scheme.Modules.pullback q).mapIso (dualMapIso ((Scheme.Modules.pullback σ).mapIso e))

end AlgebraicGeometry.Scheme.Modules

end


