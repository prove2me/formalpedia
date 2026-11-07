-- Prove2me | Definitions.Def_AvgValueAlloc_restrictTo
-- name    : AvgValueAlloc_restrictTo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:10.53689+00:00
-- url     : https://prove2.me/theorems/7e818643-4e3f-4e35-b581-82a46b584507
-- title:
--   Sub-lists and blocks of records
-- statement:
--   For a list $U$ of records and an index set $S$, $U|_S$ is the family of records with index in $S$. For a sequence $Q$ of $T$ items in order $\tau$, the block $\mathrm{seg}(Q,\tau,a,\ell)$ is the $\ell$ items at positions $a,\dots,a+\ell-1$.
--
--   These describe information/service halves and the funding, information and service blocks of the learner's schedules.
--
--   **Formalization Note** Positions beyond the horizon give the zero vector; every use stays inside the horizon.
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §3, p.7; §3.2, p.8

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec

namespace AvgValueAlloc

/-- **Sub-lists of records.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §3.2, p.8: "unordered 2r-record union U = Y ⊎ Z …
The two lists are uniform complementary halves"; §3, p.7: "Its first r live positions form
information list Y , followed by funding M of size r and service Z of size r".

`restrictTo U S` is the family of records `U i`, `i ∈ S`. `seg Q τ start len` is the block of
`len` consecutive positions starting at `start` of the sequence `Q` put in order `τ` (position `i`
holds `Q (τ i)`).

**Formalization Note.** `seg` returns the zero vector at positions beyond the horizon; every use
has `start + len ≤ T`, so that branch is never reached. -/
def restrictTo {n N : ℕ} (U : Fin N → Vec n) (S : Finset (Fin N)) : S → Vec n :=
  fun i => U i.1

/-- A block of consecutive positions of an ordered sequence. -/
def seg {n T : ℕ} (Q : Fin T → Vec n) (τ : Equiv.Perm (Fin T)) (start len : ℕ) :
    Fin len → Vec n :=
  fun i => if h : start + i.val < T then Q (τ ⟨start + i.val, h⟩) else 0

end AvgValueAlloc


