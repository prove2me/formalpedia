-- Prove2me | Definitions.Def_AvgValueAlloc_OPTinv
-- name    : AvgValueAlloc_OPTinv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:39:18.186106+00:00
-- url     : https://prove2.me/theorems/c8e95b6d-1be3-459b-8f1e-0370750b34ed
-- title:
--   Population-known causal benchmark $\mathrm{OPT}_{\mathrm{inv}}(P;S,T)$
-- statement:
--   For a population $P$ of $S+T$ items in uniform order,
--   $$
--   \mathrm{OPT}_{\mathrm{inv}}(P;S,T)=\mathbb E_\pi\ \mathrm{OPT}_{\mathrm{inv}}\bigl(\text{live}_\pi\bigr):
--   $$
--   the comparator knows $P$, subtracts the observed history to know the remaining live multiset, but not its order, and starts the live stream with zero bank.
--
--   It is the "population-known causal" benchmark of Table 1 and of Theorem 1.2(iii)–(iv).
--
--   **Formalization Note** The supremum over policies sits inside the average over the history split.
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §1.1, p.2

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_OPTinvQ
import Definitions.Def_AvgValueAlloc_popAvg

namespace AvgValueAlloc

open scoped ENNReal

/-- **The population-known causal benchmark `OPT_inv(P; S, T)`.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §1.1, p.2: "The population-known causal
OPT_inv(P; S, T) subtracts history to know the remaining multiset, but not its order. It starts the
live stream with zero bank, like the learner."

`OPTinv ρ S T P = E_π OPTinvQ ρ (live part of P under π)`: the population is put in uniform order;
the comparator, knowing `P` and the realized history, knows the live multiset but not its order,
and plays the best causal policy for it from zero surplus.

**Formalization Note.** The supremum over policies sits inside the average over the history
split, because the comparator learns the live multiset before choosing its policy. -/
noncomputable def OPTinv {n : ℕ} (ρ : Fin n → ℚ) (S T : ℕ) (P : Fin (S + T) → Vec n) : ℝ≥0∞ :=
  popAvg S T (fun _ Q => OPTinvQ ρ Q) P

end AvgValueAlloc


