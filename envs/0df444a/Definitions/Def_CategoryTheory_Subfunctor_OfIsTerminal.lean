-- Prove2me | Definitions.Def_CategoryTheory_Subfunctor_OfIsTerminal
-- name    : CategoryTheory_Subfunctor_OfIsTerminal
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/82d29aaa-dbc0-5826-be6c-f07db9fa165c
-- title:
--   Subfunctor cut out by a subset at a terminal object
-- statement:
--   Let $\mathcal C$ be a category and $F\colon\mathcal C\to\mathbf{Set}$ a functor to types. The single declaration [`CategoryTheory.Subfunctor.ofIsTerminal`](../def/CategoryTheory_Subfunctor_OfIsTerminal.html#L14) takes an object $X$ of $\mathcal C$ together with a witness `hX` that $X$ is terminal, and a subset $s\subseteq F(X)$, and produces a subfunctor of $F$ in the sense of Mathlib's `CategoryTheory.Subfunctor`: a family of subsets of the values of $F$ stable under the maps of $F$. Its value at an object $U$ is the preimage
--   $$\bigl(F(!_U)\bigr)^{-1}(s)\subseteq F(U),$$
--   where $!_U\colon U\to X$ is the unique morphism to the terminal object, obtained from `hX`. Thus an element $x\in F(U)$ lies in the subfunctor exactly when its image under the structure map to $F(X)$ belongs to $s$; the subfunctor is the fibre of $F$ over $s$ along the canonical transformation to the constant value $F(X)$. The stability condition required by `Subfunctor` is that for every morphism $i\colon U\to V$ the map $F(i)$ carries the subset attached to $U$ into the subset attached to $V$; this holds because $!_U$ factors as $i$ followed by $!_V$ by terminality of $X$, so that $F(!_V)\circ F(i)=F(!_U)$ and the two preimages agree. No condition is imposed on $s$, and no limit or size hypothesis beyond the terminality of $X$ is used; the subfunctor is obtained for an arbitrary subset of $F(X)$, in particular for a singleton $s=\{x\}$, where it is the subfunctor of elements lying over the chosen point $x\in F(X)$.
--
--   **Relation to Mathlib.** Built directly on Mathlib's `CategoryTheory.Subfunctor` structure for functors to `Type w`; it adds this one construction, a subfunctor defined as the fibre of a subset of the value at a terminal object.
--
--   **Where it is used.** The construction is the mechanism by which the functor of lifts of a fixed residual representation is cut out of a functor of representations in deformation theory: on a category of coefficient algebras whose terminal object is the residue field, reduction is the map to the value at the terminal object, and taking $s$ to be the singleton of the residual representation gives the subfunctor of lifts, and similarly the deformation functor inside representations up to strict equivalence.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/Deformations/Subfunctor.lean` — © 2025 Andrew Yang; authors: Andrew Yang). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CategoryTheory_Subfunctor_OfIsTerminal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe w v u

open CategoryTheory

namespace CategoryTheory
namespace Subfunctor

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w)

def ofIsTerminal {X : C} (hX : Limits.IsTerminal X) (s : Set (F.obj X)) :
    Subfunctor F where
  obj U := F.map (hX.from U) ⁻¹' s
  map {U V} i := by
    simp only [← Set.preimage_comp, ← hX.comp_from i, F.map_comp]
    rfl

end Subfunctor
end CategoryTheory


