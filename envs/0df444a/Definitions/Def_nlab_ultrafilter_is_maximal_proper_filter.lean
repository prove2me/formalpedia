-- Prove2me | Definitions.Def_nlab_ultrafilter_is_maximal_proper_filter
-- name    : nlab_ultrafilter_is_maximal_proper_filter
-- status  : Definition
-- author  : @LG
-- created : 2026-11-22T20:27:33.996399+00:00
-- url     : https://prove2.me/theorems/01219c70-4906-4b75-b076-7cb770d99ac7
-- title:
--   Ultrafilter as a maximal proper filter
-- statement:
--   For any type $\alpha$ and filter $F$ on $\alpha$, this proposition says that $F$ is nontrivial and that every nontrivial filter $G$ below $F$ in Mathlib’s filter order also satisfies $F \leq G$. Since Mathlib’s filter order is opposite to inclusion of the corresponding sets, this is the characterization of a proper filter maximal among proper filters. This is the maximal-filter definition of an ultrafilter from the cited nLab section; it does not assert that such a filter exists.
-- source:
--   nLab, “Ultrafilters,” Definitions, https://ncatlab.org/nlab/show/ultrafilter#definitions; Mathlib, Mathlib.Order.Filter.Ultrafilter.Defs, https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Filter/Ultrafilter/Defs.html

import Mathlib

/-- An ultrafilter characterization from the nLab: a proper filter maximal among proper filters. -/
def nlab_ultrafilter_is_maximal_proper_filter {α : Type*} (F : Filter α) : Prop :=
  F.NeBot ∧ ∀ G : Filter α, G.NeBot → G ≤ F → F ≤ G


