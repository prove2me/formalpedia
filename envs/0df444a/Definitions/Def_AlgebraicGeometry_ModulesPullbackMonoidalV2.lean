-- Prove2me | Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
-- name    : AlgebraicGeometry_ModulesPullbackMonoidalV2
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/3845ab45-f6df-56e5-a4c1-b7952173cc8d
-- title:
--   Monoidal inverse image of modules on schemes, assembled
-- statement:
--   This module introduces no new named notions. It collects, in the namespace `AlgebraicGeometry.Scheme.Modules` and for a morphism of schemes $f : X \to Y$, the monoidal theory of inverse images of (pre)sheaves of modules, and records one definitional identification: the abbreviation `pullback₀ f`, defined as the pullback functor [`PresheafOfModules.PullbackMonoidal.pb`](../def/PresheafOfModules_PullbackMonoidal.html#L225) along the functor $\mathrm{Opens}(Y) \to \mathrm{Opens}(X)$ given by preimage under $f$ together with the comparison map $f.c : \mathcal{O}_Y \to f_*\mathcal{O}_X$, is the same functor as Mathlib's `PresheafOfModules.pullback` taken along the induced morphism of sheaves of rings `f.toRingCatSheafHom.hom`; the two agree on the nose, not merely up to isomorphism.
--
--   The notions thereby made available are: the internal hom of presheaves of modules, whose sections over $X$ are the families assigning to each $f : X \to Y$ an $R(Y)$-linear map $F(Y) \to N(Y)$ subject to the naturality relation $N(g)(\varphi_f x) = \varphi_{f \circ g}(F(g)x)$, with $R(X)$ acting by $(r\cdot\varphi)_f = R(f)(r)\,\varphi_f$, together with the tensor–hom adjunction making presheaves of modules monoidal closed; the statement that for a finite-product-preserving functor $F$ and a map $\varphi : S \to F^{\mathrm{op}} \circ R$ of presheaves of commutative rings the pushforward is lax monoidal and the corresponding pullback is strong monoidal, its oplax structure maps being invertible; the monoidal, symmetric and monoidal-closed structure on sheaves of modules, obtained by localising the presheaf-level structure at the class of morphisms that become isomorphisms after sheafification; and, on schemes, the monoidal structure on `Modules.pullback f` together with the resulting isomorphisms $f^*(L \otimes M) \cong f^*L \otimes f^*M$ and $f^*\mathcal{O}_Y \cong \mathcal{O}_X$.
--
--   **Relation to Mathlib.** The pullback functor on presheaves of modules, the sheafification adjunction and `SheafOfModules.sheafificationCompPullback` are Mathlib's; the internal hom for presheaves of modules, the monoidal structure on sheaves of modules over a scheme, and the strong monoidal structure on the inverse image are supplied by the project's definition modules gathered here.
--
--   **Where it is used.** These structures are what allows pullbacks of tensor products of sheaves of modules, in particular of invertible sheaves, to be identified with tensor products of pullbacks along arbitrary morphisms of schemes, as needed in the geometric treatment of elliptic curves and modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesPullbackMonoidalV2.lean

import Mathlib
import Definitions.Def_PresheafOfModules_InternalHom
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_PresheafOfModules_PullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

example : pullback₀ f = PresheafOfModules.pullback f.toRingCatSheafHom.hom := rfl

end AlgebraicGeometry.Scheme.Modules

end


