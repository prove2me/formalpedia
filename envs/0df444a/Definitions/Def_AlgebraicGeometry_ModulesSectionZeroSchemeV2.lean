-- Prove2me | Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2
-- name    : AlgebraicGeometry_ModulesSectionZeroSchemeV2
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/9aaf0b65-aa43-5843-b2b5-5213750fbfb6
-- title:
--   Zero scheme of a section: V2 interface module
-- statement:
--   This module introduces no new constants: it opens the namespace `AlgebraicGeometry.Scheme.Modules` with a scheme $X$ and a module $M$ over $X$ in context and makes available, in the presence of the V2 monoidal structure on sheaves of modules, the vocabulary of zero schemes of sections together with the ideal-sheaf modules and the rigidified relative Picard presheaf. The notions thereby in scope are the following. For a section $s \colon \mathcal{O}_X \to M$, i.e. a morphism out of the monoidal unit of `X.Modules`, `Scheme.Modules.restrictSection` is the image of $1$ under $s$ over an open $U$, read as a section of the restriction $M|_U$; `coeff` sends a map $\varphi \colon M|_U \to \mathcal{O}_U$ to $\varphi$ applied to that section, an element of $\Gamma(X,U)$; `coeffIdeal` is the ideal of $\Gamma(X,U)$ spanned by all such coefficients; and `zeroSchemeIdeal` is the infimum, in the lattice `X.IdealSheafData`, of those ideal sheaf data $\mathcal{J}$ with $\mathfrak{c}_s(U) \le \mathcal{J}(U)$ for every affine open $U$, with `zeroScheme` the associated closed subscheme. Alongside these: the pullback of a section along a morphism of schemes, the transpose $M^{\vee} \to \mathcal{O}_X$ of a section, and the trivialisation transport showing that a module invertible in the sense of `Scheme.Modules.IsInvertible` (pointwise existence of an open on which the pullback is isomorphic to the unit) is trivial on a basis of affine opens. For an ideal sheaf $\mathcal{I}$ on $X$, `Scheme.IdealSheafData.module` is the kernel of the map from the unit to the pushforward of the unit along the closed immersion of the subscheme, `invModule` its internal dual, and `invModuleSection` the section of that dual obtained by currying the inclusion $\mathcal{I} \to \mathcal{O}_X$. Also in scope are relative effective Cartier divisors and the presheaf of classes of rigidified invertible modules on base changes of a scheme over $\operatorname{Spec} R$.
--
--   **Relation to Mathlib.** Mathlib supplies `SheafOfModules`, `Scheme.IdealSheafData` and the pullback functors used here; the monoidal closed structure on `X.Modules`, the invertibility predicate `Scheme.Modules.IsInvertible`, the coefficient ideals and zero-scheme ideal sheaf, relative effective Cartier divisors and the rigidified relative Picard presheaf are the project's own.
--
--   **Where it is used.** The zero scheme of a section of an invertible module is the mechanism by which sections produce effective divisors, and hence the bridge between invertible modules and relative effective Cartier divisors on curves over a base; this vocabulary feeds the treatment of divisors and of the relative Picard functor used for Jacobians of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2.lean

import Definitions.Def_AlgebraicGeometry_IdealSheafModuleV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {X : Scheme.{u}} {M : X.Modules}

end Scheme.Modules

end AlgebraicGeometry

end


