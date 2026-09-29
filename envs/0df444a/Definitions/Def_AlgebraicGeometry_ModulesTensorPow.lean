-- Prove2me | Definitions.Def_AlgebraicGeometry_ModulesTensorPow
-- name    : AlgebraicGeometry_ModulesTensorPow
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/f996b70a-c715-5e44-b670-cffa7a0b8a17
-- title:
--   Tensor powers of sheaves of modules on a scheme
-- statement:
--   For a scheme $X$, the category `X.Modules` of sheaves of $\mathcal{O}_X$-modules carries a symmetric monoidal structure with unit `SheafOfModules.unit X.ringCatSheaf`, i.e. $\mathcal{O}_X$ itself, obtained by transporting the tensor product of presheaves of modules along the sheafification functor `Scheme.Modules.sheafify X`, which is a localisation with respect to the class of morphisms of presheaves of modules that become local isomorphisms on underlying abelian-group-valued presheaves; that class is shown to be compatible with the monoidal structure, and the resulting monoidal category is symmetric and monoidal closed, the internal hom coming from the internal hom on presheaves of modules, whose sections over $U$ are the families of $\mathcal{O}$-linear maps $\mathcal{F}(V) \to \mathcal{N}(V)$ indexed by the objects over $U$ and natural in $V$. Relative to this structure, the tensor power $\mathcal{L}^{\otimes n}$ of an $\mathcal{O}_X$-module $\mathcal{L}$ is defined by recursion on $n$: `tensorPow L 0` is the monoidal unit $\mathcal{O}_X$, and `tensorPow L (n+1)` is `tensorPow L n ⊗ L`. Thus the recursion multiplies on the right, so $\mathcal{L}^{\otimes n}$ is the left-bracketed product $(\cdots((\mathcal{O}_X \otimes \mathcal{L}) \otimes \mathcal{L}) \cdots) \otimes \mathcal{L}$. The two accompanying equations record the defining clauses as equalities of objects, not merely isomorphisms: `tensorPow_zero` identifies $\mathcal{L}^{\otimes 0}$ with the unit, and `tensorPow_succ` identifies $\mathcal{L}^{\otimes(n+1)}$ with $\mathcal{L}^{\otimes n} \otimes \mathcal{L}$. Finally `tensorPowOneIso` is an isomorphism $\mathcal{L}^{\otimes 1} \cong \mathcal{L}$, namely the left unitor of the monoidal structure applied to $\mathcal{L}$, since $\mathcal{L}^{\otimes 1}$ is by definition $\mathcal{O}_X \otimes \mathcal{L}$. Also provided, for comparison with the presheaf-level tensor product, is the isomorphism identifying the sheafification of $\mathcal{L}.\mathrm{val} \otimes \mathcal{M}.\mathrm{val}$ with $\mathcal{L} \otimes \mathcal{M}$, and the dual $\mathcal{L}^{\vee}$ as the internal hom from $\mathcal{L}$ into the unit.
--
--   **Relation to Mathlib.** Mathlib supplies the categories `PresheafOfModules` and `SheafOfModules` together with the tensor product of presheaves of modules; the monoidal closed structure on presheaves of modules via an internal hom of natural families of linear maps, the transported symmetric monoidal closed structure on sheaves of modules on a scheme, and the tensor power operation are the project's own.
--
--   **Where it is used.** These definitions supply the vocabulary for speaking of $\mathcal{L}^{\otimes n}$ in the sheaf-theoretic geometry used later, for instance in statements about invertible sheaves whose powers have enough sections to produce morphisms to projective space.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesTensorPow.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

end AlgebraicGeometry.Scheme.Modules

end


