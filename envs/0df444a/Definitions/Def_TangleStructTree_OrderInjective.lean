-- Prove2me | Definitions.Def_TangleStructTree_OrderInjective
-- name    : TangleStructTree_OrderInjective
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:52:05.573194+00:00
-- url     : https://prove2.me/theorems/1a8943d8-c546-48ae-b890-d19e0873de0c
-- title:
--   Injective order functions on $S$
-- statement:
--   An order function $s\mapsto|s|$ on $S$ is **injective on $S$** if distinct unoriented separations have distinct orders:
--   $$
--   |r|=|s|\ \Longrightarrow\ r=s\qquad(r,s\in S).
--   $$
--
--   Injectivity makes "the separation of minimum order" unique, which is what makes thoroughly ordered tangle structure trees unique.
--
--   **Formalization Note** With `ord : E → ℝ` on oriented separations: if $\mathrm{ord}(x)=\mathrm{ord}(y)$ then $y=x$ or $y=x^*$.
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), §4, p.8 (PDF 19)

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem

namespace TangleStructTree

open SepSystem

variable {E : Type*} [PartialOrder E] [SepSystem E]

/-- The order function is **injective on `S`** (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §4,
p.8 (PDF 19)): distinct unoriented separations have distinct orders.

**Formalization Note** With `ord : E → ℝ` on oriented separations, injectivity on `S` reads: if
`ord x = ord y` then `y` is an orientation of the separation underlying `x` (`y = x` or
`y = x∗`). -/
def OrderInjective (ord : E → ℝ) : Prop :=
  ∀ x y : E, ord x = ord y → y = x ∨ y = rev x

end TangleStructTree


