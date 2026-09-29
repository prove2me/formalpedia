-- Prove2me | Definitions.Def_AlgebraicGeometry_IdealSheafModuleV2
-- name    : AlgebraicGeometry_IdealSheafModuleV2
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/c7b2ec46-9600-5de0-9301-c0108c1c9830
-- title:
--   Ideal sheaf modules and line bundles of relative divisors
-- statement:
--   This module introduces no declarations of its own: it opens the namespaces `AlgebraicGeometry` and `Scheme.IdealSheafData` over a pair of schemes $X, Y$ and collects, through its imports, the notions used to attach sheaves of modules to ideal sheaves and to relative divisors. Those notions are as follows. For a scheme $X$ and quasi-coherent ideal sheaf data $I$ on $X$, with associated closed immersion `I.subschemeι` of the subscheme $Z$ cut out by $I$, `Scheme.IdealSheafData.module` is the kernel, formed in the category `X.Modules` of sheaves of modules over the structure sheaf of $X$, of the canonical map from the unit object $\mathcal O_X$ to the pushforward along `I.subschemeι` of the unit object of $Z$; thus it is the sheaf $\mathcal O_X(-Z) = \ker(\mathcal O_X \to i_*\mathcal O_Z)$. Its inclusion into the monoidal unit is `Scheme.IdealSheafData.moduleι`, and `Scheme.IdealSheafData.invModule` is its dual `Scheme.Modules.dual`, that is, the internal hom from it into the unit, taken for the monoidal closed structure on `X.Modules` obtained by localising the monoidal closed structure on presheaves of modules along sheafification.
--
--   On the divisor side, `RelEffCartierDiv f r g`, for $f : \mathcal C \to S$, $g : T \to S$ and $r \in \mathbb N$, is a structure whose data is ideal sheaf data $I$ on $\mathcal C \times_S T$ together with four properties of the composite of the closed immersion of the subscheme of $I$ with the second projection to $T$: finiteness, flatness, local finite presentation, and the requirement that its flat rank at every point of $T$ equals $r$. For such a $D$, the abbreviations `RelEffCartierDiv.idealModule` and `RelEffCartierDiv.lineBundle` name $\mathcal O(-D)$ and $\mathcal O(D)$, namely the module of $D.I$ and its dual.
--
--   **Relation to Mathlib.** Mathlib supplies `Scheme.IdealSheafData` with its subscheme and closed immersion, the category `SheafOfModules` with sheafification, and the abelian-category kernels used here. The symmetric monoidal closed structure on presheaves and sheaves of modules (built from an explicit internal hom of presheaves of modules and transported along sheafification), the module and dual module of an ideal sheaf, and the structure `RelEffCartierDiv` of relative effective divisors of fixed degree are the project's own.
--
--   **Where it is used.** These constructions provide the line bundles attached to relative effective divisors of fixed degree $r$ on a curve over a base, the setting in which the project formulates universal divisors (`UnivDivisorPack`) and the pullback operation `PullsBackOver` on such divisors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_IdealSheafModuleV2.lean

import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_IdealSheafModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

namespace Scheme.IdealSheafData

end Scheme.IdealSheafData

end AlgebraicGeometry

end


