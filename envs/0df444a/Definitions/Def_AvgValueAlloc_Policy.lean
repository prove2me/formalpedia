-- Prove2me | Definitions.Def_AvgValueAlloc_Policy
-- name    : AvgValueAlloc_Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:06.633617+00:00
-- url     : https://prove2.me/theorems/e2e61755-065a-440b-b92e-a8ef32834840
-- title:
--   Deterministic causal policy and its run
-- statement:
--   A **causal policy** maps the list of past live items and the current item to a decision (reject or a buyer). On a live sequence $v_1,\dots,v_T$ it decides $x_t=\pi(v_1,\dots,v_{t-1};v_t)$.
--
--   Policies are the comparators of the causal benchmarks: they may know the law (or the live multiset), but not future draws.
--
--   **Formalization Note** Randomized policies are mixtures of deterministic ones and earn at most the best of them, so deterministic policies give the same benchmark values.
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §1.1, p.2

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec

namespace AvgValueAlloc

/-- **A deterministic causal policy.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §1.1, p.2: "OPT_on(D, T) is optimal expected
welfare of a computationally unbounded causal policy knowing D, not future draws"; "Observe each
live vector in full, then irrevocably assign it to one buyer or reject it".

A policy maps the list of past live items and the current item to a decision (`none` rejects).
`Policy.run π vs t` is its decision at position `t` on the live sequence `vs`.

**Formalization Note.** Knowledge of `D` (or of the live multiset) enters because the benchmark
takes a supremum over all policies for each law; a randomized policy is a mixture of
deterministic ones and earns at most the best of them. -/
abbrev Policy (n : ℕ) : Type := List (Vec n) → Vec n → Option (Fin n)

/-- The decisions of a policy on a live sequence. -/
def Policy.run {n T : ℕ} (π : Policy n) (vs : Fin T → Vec n) : Fin T → Option (Fin n) :=
  fun t => π (List.ofFn fun s : Fin t.val => vs ⟨s.val, lt_trans s.isLt t.isLt⟩) (vs t)

end AvgValueAlloc


