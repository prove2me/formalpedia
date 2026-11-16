-- Prove2me | Definitions.Def_TangleStructTree_Supplement_IsEfficientTree
-- name    : TangleStructTree_Supplement_IsEfficientTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:06:26.875565+00:00
-- url     : https://prove2.me/theorems/ead5e73c-519d-4578-b000-60c20ffb3774
-- title:
--   Efficient separation trees
-- statement:
--   Given an ordered separation system $\vec S$, a separation tree $(T,r,\beta)$ is **efficient** if for every leaf $\ell$ the set $\beta_\ell$ of labels on the path from the root to $\ell$ is efficient in its closure $\lfloor\beta_\ell\rfloor$: no element $\vec s\in\beta_\ell$ is eclipsed by another element $\vec r\in\lfloor\beta_\ell\rfloor$, where $\vec r$ eclipses $\vec s$ if
--
--   $$\vec r<\vec s\quad\text{and}\quad |r|<|s| .$$
--
--   Efficiency is the part of being thoroughly ordered that survives the contraction of unnecessary edges (Section 5).
--
--   **Formalization Note** "Efficient in" is the published `TangleStructTree.Efficient` (strict in both inequalities), applied at every leaf.
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), §4, p.12 (PDF 23): efficient separation tree

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_sepClosure
import Definitions.Def_TangleStructTree_StronglyEfficient
import Definitions.Def_TangleStructTree_SepTree

namespace TangleStructTree

namespace Supplement

variable {E : Type*} [PartialOrder E] [SepSystem E]

/-- "Given an ordered separation system `S⃗`, we call a separation tree `(T, r, β)` **efficient** if
for every leaf `ℓ` the set `β_ℓ` is efficient in `⌊β_ℓ⌋`" (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §4, p.12 (PDF 23)).

**Formalization Note** "Efficient" is the base mission's `Efficient`: no element of `β_ℓ` is
eclipsed (`r⃗ < s⃗` and `|r| < |s|`, both strict) by another element of `⌊β_ℓ⌋`. -/
def IsEfficientTree (T : SepTree E) (ord : E → ℝ) : Prop :=
  ∀ ℓ : List E, T.IsLeaf ℓ → Efficient ord (labels ℓ) (sepClosure (labels ℓ))

end Supplement

end TangleStructTree


