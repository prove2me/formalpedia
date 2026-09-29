-- Prove2me | Definitions.Def_FCP_InvariantSubspace
-- name    : FCP_InvariantSubspace
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-15T19:06:51.907002+00:00
-- url     : https://prove2.me/theorems/47fa5960-a23b-4921-a3b3-3a7cc4b550c9
-- title:
--   Nontrivial closed invariant subspaces of a bounded operator
-- statement:
--   For a bounded linear operator $T$ on a complex normed space $H$, a **nontrivial closed invariant subspace** is a linear subspace $W \subseteq H$ that is closed in the norm topology, differs from both $\{0\}$ and $H$, and satisfies $T(W) \subseteq W$. The data of such a subspace is packaged as a structure, so that 'there is one' is expressed by that structure being inhabited and 'there is none' by it being empty.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/InvariantSubspaceProblem.lean); https://en.wikipedia.org/wiki/Invariant_subspace_problem

import Mathlib

namespace FCP.InvariantSubspace

/-- A nontrivial closed invariant subspace for a bounded operator `T` on a complex normed space:
a closed linear subspace different from `⊥` and `⊤` mapped into itself by `T`. -/
structure ClosedInvariantSubspace {H : Type} [NormedAddCommGroup H] [Module ℂ H]
    (T : H →L[ℂ] H) where
  toSubspace : Submodule ℂ H
  ne_bot : toSubspace ≠ ⊥
  ne_top : toSubspace ≠ ⊤
  isClosed : IsClosed (toSubspace : Set H)
  isInvariant : toSubspace.map T.toLinearMap ≤ toSubspace

end FCP.InvariantSubspace


