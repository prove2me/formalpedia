-- Prove2me | Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
-- name    : AlgebraicGeometry_ModulesSectionsTensorV2
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/f695f10a-8353-540d-8be0-3e641da10678
-- title:
--   Sections of tensor products, tensor powers and frames: re-export
-- statement:
--   This module contains no declarations of its own: it fixes a scheme $X$, modules $L, M$ over $X$, opens $U, V$ and a section $s \in \Gamma(M,U)$ in its `variable` lines, and serves to make the section-level tensor calculus for sheaves of modules on a scheme available under one import. The notions it collects are the following. On presheaves of modules over $R \circ \mathrm{forget}_2$ there is an internal hom `ihomObj F N`, whose value at $X$ is the $R(X)$-module of families $\varphi$ assigning to each $f : X \to Y$ an $R(Y)$-linear map $F(Y) \to N(Y)$ subject to the naturality condition $N(g)(\varphi_f x) = \varphi_{f \circ g}(F(g)x)$; currying and uncurrying of maps $F \otimes G \to N$ along pure tensors give an adjunction $F \otimes - \dashv \mathrm{ihom}(F,-)$ and hence a monoidal closed structure. The monoidal, symmetric and closed structures on $X$-modules are obtained by localising the presheaf-level structures along sheafification, with `tensorIsoSheafify` identifying the sheafification of $L.\mathrm{val} \otimes M.\mathrm{val}$ with $L \otimes M$; `dual L` is $\mathrm{ihom}(L, \mathcal O_X)$. Composing the sheafification unit with that isomorphism yields `tensorSectionsHom`, and `tensorSections s t` $\in \Gamma(L \otimes M, U)$ is the image of the pure tensor $s \otimes_{\Gamma(X,U)} t$; it is $\Gamma(X,U)$-bilinear, bundled as `tensorSectionsBilin`, and commutes with restriction. Tensor powers are defined by $L^{\otimes 0} = \mathbf 1$, $L^{\otimes(n+1)} = L^{\otimes n} \otimes L$, with `unitSection U` the unit $1 \in \Gamma(X,U)$ and `tensorPowSection s n` the iterated tensor of $s$ with itself. Finally `IsFrameOn s V` asserts that for every open $W$ with $W \le U$ and $W \le V$ the map $\Gamma(X,W) \to \Gamma(M,W)$, $g \mapsto g \cdot (s|_W)$, is bijective; it is monotone in $V$, unchanged on replacing $V$ by $V \sqcap U$, stable under restricting $s$ and under isomorphisms of modules, and holds for the unit section.
--
--   **Relation to Mathlib.** The underlying `PresheafOfModules`, `SheafOfModules`, sheafification adjunction and the notation $\Gamma(M,U)$ are Mathlib's; the monoidal closed structure on presheaves of modules, the monoidal, symmetric and closed structures on the modules of a scheme obtained by localisation, the tensor product of sections and tensor powers of a section, and the predicate `IsFrameOn`, are the project's own.
--
--   **Where it is used.** These definitions form the basic vocabulary for working with tensor products of sheaves of modules section by section, and with trivialising sections of invertible sheaves, in the algebraic-geometry layer on which the later arithmetic arguments rest.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesSectionsTensorV2.lean

import Mathlib
import Definitions.Def_PresheafOfModules_InternalHom
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory Opposite TensorProduct

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

section Hom

variable (L M : X.Modules)

end Hom

section Sections

variable {L M : X.Modules} {U : X.Opens}

end Sections

section Pow

variable {L : X.Modules} {U : X.Opens}

end Pow

section Frame

variable {M : X.Modules} {U : X.Opens}

namespace IsFrameOn

variable {s : Γ(M, U)} {V : X.Opens}

end IsFrameOn

end Frame

end AlgebraicGeometry.Scheme.Modules

end


