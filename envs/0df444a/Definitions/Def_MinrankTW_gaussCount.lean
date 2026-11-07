-- Prove2me | Definitions.Def_MinrankTW_gaussCount
-- name    : MinrankTW_gaussCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:32:08.247373+00:00
-- url     : https://prove2.me/theorems/50cbb0b2-dd6f-49bd-86df-bc0ea6218663
-- title:
--   Number of $j$-dimensional subspaces $\left[{b\atop j}\right]_q$
-- statement:
--   $\left[{b\atop j}\right]_q$ is the number of $j$-dimensional subspaces of $\mathbb F_q^b$.
--
--   **Formalization Note** Defined as a count of subspaces; the product formula $\prod_{i<j}(q^b-q^i)/(q^j-q^i)$ is a clause of the theorem for Eq. (15), not the definition.
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Section 3.3, p.12, Eq. (15)

import Mathlib

namespace MinrankTW

/-- `[b j]_q`, the number of `j`-dimensional subspaces of `F_q^b` (Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), §3.3, p.12,
"Number of states", Eq. (15)).

**Formalization Note** `Nat.card` of the subtype of submodules of `Fin b → F` of
`Module.finrank` equal to `j`; it is a count, not the product formula (the formula is a clause
of Eq. (15)). -/
noncomputable def gaussCount (F : Type*) [Field F] (b j : ℕ) : ℕ :=
  Nat.card {W : Submodule F (Fin b → F) // Module.finrank F W = j}

end MinrankTW


