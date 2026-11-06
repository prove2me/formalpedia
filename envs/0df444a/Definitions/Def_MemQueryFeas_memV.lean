-- Prove2me | Definitions.Def_MemQueryFeas_memV
-- name    : MemQueryFeas_memV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:39:13.339273+00:00
-- url     : https://prove2.me/theorems/e2623b93-ed31-43cd-8492-c3008b319a61
-- title:
--   Initial memory $\mathrm{Mem}_v$ of a phase (Definition 1)
-- statement:
--   A fixed deterministic learner is run against the transform oracle. The **start time** $t_{v,0}$ of a phase $v$ is the first round during which the oracle's current leaf (including the leaves it passes through in the while-loop of Algorithm 4, line 3) is a descendant of $v$. The **initial memory** of $v$ is
--   $$
--   \mathrm{Mem}_v=\mathrm{Memory}_{t_{v,0}},
--   $$
--   the learner's memory at the beginning of that round; it is undefined (`none`) if no such round exists.
--
--   **Formalization Note** A leaf skipped within the while-loop of a round counts as held in that round (the reading under which the proof of Theorem 1 counts one query per unskipped leaf).
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Definition 1, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_MemQueryFeas_DetMemAlg_run
import Definitions.Def_MemQueryFeas_skelOracle

namespace MemQueryFeas

open Classical in
/-- **Initial memory `Mem_v` of a phase (Definition 1).** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Definition 1, p.10 (PDF p.11): "The
start … time of phase `v`, denoted `t_{v,0}` … is the first … round `t` when the transform separation
oracle had its internal leaf be a descendant leaf of `v`, i.e. the first round when
`ℓ = v ∥ (1, …, 1)` … if it exists. The initial memory of phase `v`, denoted `Mem_v` is the memory
state of the learner at the beginning of phase `v`, i.e., `Mem_v := Memory_{t_{v,0}}`."

The deterministic learner `alg` is run against the transform oracle `skelOracle d ε P c fin`. With
`n_t` the oracle's leaf index at the beginning of round `t`, the leaves held during round `t` (the
while-loop of Algorithm 4, line 3) are those with index in `[n_t, n_{t+1}]`. `t_{v,0}` is the first
round during which some held leaf is a descendant of `v` (has `v` as a prefix), and
`memV … v = some Memory_{t_{v,0}}`; it is `none` if no such round exists.

**Formalization Note.** Transient-leaf reading of Definition 1: a leaf passed over within the
while-loop of a round counts as held in that round. Rounds are 0-based and the run is infinite
("for `t ≥ 1`"). -/
noncomputable def memV {d M : ℕ} (ε : ℝ) (P : ℕ) (alg : DetMemAlg d M)
    (c : ℕ → List ℕ → ℕ → Op d) (fin : List (Vec d) → Vec d → Option (Vec d)) (v : List ℕ) :
    Option (Fin M → Bool) :=
  let run := alg.run (skelOracle d ε P c fin)
  let n : ℕ → ℕ := fun t => leafIdx (pathOracle (delta d ε P) c) (Np d ε P) P (run t).2
  if h : ∃ t m, n t ≤ m ∧ m ≤ n (t + 1) ∧ m < numLeaves (Np d ε P) P ∧
      v <+: leafOf (Np d ε P) P m then
    some (run (Nat.find h)).1
  else none

end MemQueryFeas


