-- Prove2me | Definitions.Def_MinrankTW_Nq
-- name    : MinrankTW_Nq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:32:09.374192+00:00
-- url     : https://prove2.me/theorems/ecf3dc09-6f24-4d58-9dc4-b689739bc382
-- title:
--   Number of subspaces $N_q(d)$
-- statement:
--   $N_q(d)$ is the number of subspaces of $\mathbb F_q^d$ (of all dimensions). By (15) it equals $\sum_{j=0}^d\left[{d\atop j}\right]_q=\Theta_q(q^{\lfloor d^2/4\rfloor})$; it is the number of states of a bag of size $d$.
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Section 2.3, p.8 and Eq. (15), p.12

import Mathlib

namespace MinrankTW

/-- `N_q(d)`, the number of subspaces of `F_q^d` (Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), §2.3, p.8; also Eq. (15), p.12,
where it equals `∑_j [d j]_q`).

**Formalization Note** `Nat.card` of the type of submodules of `Fin d → F`, which is finite
for a finite field `F`. -/
noncomputable def Nq (F : Type*) [Field F] (d : ℕ) : ℕ :=
  Nat.card (Submodule F (Fin d → F))

end MinrankTW


