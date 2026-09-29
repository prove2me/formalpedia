-- Prove2me | Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
-- name    : AlgebraicGeometry_ModulesTensorPowV2
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/0b5054ff-e4b7-50c4-af0c-6edc572e4c2c
-- title:
--   Tensor powers of a sheaf of modules on a scheme
-- statement:
--   For a scheme $X$, let `X.Modules` denote the category of sheaves of modules over the structure sheaf of $X$, equipped with the symmetric monoidal closed structure set up in the imported definition module: the tensor product is obtained from the tensor product of presheaves of modules by localising at the class of maps that become local isomorphisms of underlying abelian-group presheaves, and the tensor unit $\mathbf 1$ is `SheafOfModules.unit`, i.e. the structure sheaf viewed as a module over itself. In this setting `tensorPow` assigns to a sheaf of modules $\mathcal L$ and a natural number $n$ the object $\mathcal L^{\otimes n}$, defined by recursion on $n$: the value at $0$ is the tensor unit, and the value at $n+1$ is $\mathcal L^{\otimes n}\otimes\mathcal L$, the new factor being appended on the right, so that the bracketing is the left-nested one $(\cdots((\mathbf 1\otimes\mathcal L)\otimes\mathcal L)\cdots)\otimes\mathcal L$.
--
--   Two lemmas record the defining equations as equalities of objects: `tensorPow_zero` states $\mathcal L^{\otimes 0}=\mathbf 1$ and `tensorPow_succ` states $\mathcal L^{\otimes (n+1)}=\mathcal L^{\otimes n}\otimes\mathcal L$; these hold on the nose, not merely up to isomorphism, since the recursion is by definition. Finally `tensorPowOneIso` is the isomorphism $\mathcal L^{\otimes 1}\cong\mathcal L$ in `X.Modules`; as $\mathcal L^{\otimes 1}$ is by definition $\mathbf 1\otimes\mathcal L$, it is the left unitor of the monoidal structure. No invertibility or quasi-coherence hypothesis is imposed on $\mathcal L$: the construction is made for an arbitrary sheaf of modules, so that statements about tensor powers of invertible sheaves are obtained by adding the relevant hypothesis on $\mathcal L$ separately.
--
--   **Relation to Mathlib.** Mathlib supplies the categories `PresheafOfModules` and `SheafOfModules` and the monoidal structure on presheaves of modules; the symmetric monoidal closed structure on sheaves of modules on a scheme used here, including the internal hom of presheaves of modules, is constructed in the project's imported definition modules. The tensor-power recursion itself is the project's own notion.
--
--   **Where it is used.** Tensor powers provide the vocabulary for statements in which a morphism to projective space, or a finiteness or closed-immersion property, is expressed in terms of sections of some power $\mathcal L^{\otimes n}$ of an invertible sheaf; they are used throughout the algebro-geometric layer underlying the treatment of modular curves and their models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesTensorPowV2.lean

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

def tensorPow (L : X.Modules) : ℕ → X.Modules
  | 0 => 𝟙_ X.Modules
  | n + 1 => tensorPow L n ⊗ L

@[simp] theorem tensorPow_zero (L : X.Modules) : L.tensorPow 0 = 𝟙_ X.Modules := rfl

@[simp] theorem tensorPow_succ (L : X.Modules) (n : ℕ) : L.tensorPow (n + 1) = L.tensorPow n ⊗ L := rfl

def tensorPowOneIso (L : X.Modules) : L.tensorPow 1 ≅ L := λ_ L

end AlgebraicGeometry.Scheme.Modules

end


