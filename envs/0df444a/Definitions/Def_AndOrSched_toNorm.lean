-- Prove2me | Definitions.Def_AndOrSched_toNorm
-- name    : AndOrSched_toNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:30:54.234743+00:00
-- url     : https://prove2.me/theorems/9082a32c-c791-4993-8cdb-245f869cabc5
-- title:
--   Jobs of $I$ as jobs of $I'$
-- statement:
--   The map sending a job $j$ of $I$ to the same job in the normalized instance $I'$, or to nothing if $j\in Z$.
-- source:
--   F. Happach, A. S. Schulz, Approximation Algorithms and LP Relaxations for Scheduling Problems Related to Min-Sum Set Cover, arXiv:2001.07011v1, §2, p.6

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_zeroSet
import Definitions.Def_AndOrSched_normalize
open scoped Classical NNReal

namespace AndOrSched

/-- The job of the normalized instance `normalize I` that corresponds to a job `j` of `I`
(Happach, Schulz, arXiv:2001.07011v1, §2, p.6): `none` if `j ∈ Z` (a disregarded job), and otherwise `j` itself as a job of
`A' = A ∖ Z` or of the first summand of `B' = (B ∖ Z) ⊕ A'`. -/
noncomputable def toNorm (I : Instance) (j : I.N) : Option (normalize I).N :=
  match j with
  | Sum.inl a =>
      if h : Sum.inl a ∈ zeroSet I then none
      else some (Sum.inl (⟨a, h⟩ : {a : I.A // Sum.inl a ∉ zeroSet I}))
  | Sum.inr b =>
      if h : Sum.inr b ∈ zeroSet I then none
      else some (Sum.inr (Sum.inl (⟨b, h⟩ : {b : I.B // Sum.inr b ∉ zeroSet I})))

end AndOrSched


