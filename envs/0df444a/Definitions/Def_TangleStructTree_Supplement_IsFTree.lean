-- Prove2me | Definitions.Def_TangleStructTree_Supplement_IsFTree
-- name    : TangleStructTree_Supplement_IsFTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:08:04.286088+00:00
-- url     : https://prove2.me/theorems/72862924-883a-404f-a2fc-53d890a84fec
-- title:
--   $\mathcal F$-trees
-- statement:
--   An **$\mathcal F$-tree** of $\vec S$ is an $\mathcal F$-tangle structure tree of $\vec S$ all of whose leaves are forbidden, i.e. for every leaf $\ell$ the label set $\beta_\ell$ contains an element of $\mathcal F$.
--
--   $\mathcal F$-trees are the certificates for the non-existence of $\mathcal F$-tangles in the duality theorems 6.5, 7.1 and 7.3.
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), §6, p.19 (PDF 30): F-trees

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_SepTree
import Definitions.Def_TangleStructTree_SepTree_IsTST

namespace TangleStructTree

namespace Supplement

variable {E : Type*} [PartialOrder E] [SepSystem E]

/-- An **`ℱ`-tree** of `S⃗` is an `ℱ`-tangle structure tree of `S⃗` all of whose leaves are
forbidden (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §6, p.19 (PDF 30): "when all their leaves are forbidden. Let us call
such `ℱ`-tangle structure trees `ℱ`-trees"). -/
def IsFTree (T : SepTree E) (ℱ : Set (Set E)) : Prop :=
  T.IsTST ℱ ∧ ∀ ℓ : List E, T.IsLeaf ℓ → T.IsForbiddenLeaf ℱ ℓ

end Supplement

end TangleStructTree


