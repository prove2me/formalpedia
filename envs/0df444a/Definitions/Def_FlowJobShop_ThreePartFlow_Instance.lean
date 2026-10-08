-- Prove2me | Definitions.Def_FlowJobShop_ThreePartFlow_Instance
-- name    : FlowJobShop_ThreePartFlow_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:16:54.655982+00:00
-- url     : https://prove2.me/theorems/ca0cd88d-3989-4fe2-afbf-2671d1e7aa9e
-- title:
--   The three-processor flow shop FS built from a 3-Partition instance, and τ = 2tB (proof of Lemma 4, p. 41)
-- statement:
--   Let $C=(a_1,\dots,a_s,B)$ be an instance of 3-Partition with $s=3t$ numbers and target $B$. The proof of Lemma 4 constructs a flow shop $FS$ with $m=3$ processors and $s+t+2$ jobs, with the following task times $t_{j,i}$ (processor $j$, job $i$):
--
--   1. jobs $i$, $1\le i\le s$: $t_{1,i}=t_{3,i}=a_i$, $t_{2,i}=0$;
--   2. job $s+1$: $t_{1,s+1}=0$, $t_{2,s+1}=2B$, $t_{3,s+1}=B$;
--   3. jobs $s+i+1$, $1\le i\le t-2$: $t_{1,s+i+1}=t_{3,s+i+1}=B$, $t_{2,s+i+1}=2B$;
--   4. job $s+t$: $t_{1,s+t}=B$, $t_{2,s+t}=2B$, $t_{3,s+t}=0$;
--   5. job $s+t+1$: $t_{1,s+t+1}=t_{2,s+t+1}=0$, $t_{3,s+t+1}=B$;
--   6. job $s+t+2$: $t_{1,s+t+2}=B$, $t_{2,s+t+2}=t_{3,s+t+2}=0$.
--
--   The threshold is
--   $$\tau=2tB .$$
--   When $\sum_i a_i=tB$, each of the three processors carries total work exactly $2tB$, so a schedule meeting $\tau$ keeps every processor busy throughout $[0,2tB]$.
--
--   **Formalization Note** The jobs form the type `FSJob t` with constructors `elem i` (the paper's job $i+1$, $i=0,\dots,s-1$), `first` (job $s+1$), `middle k` (job $s+k+2$, $k=0,\dots,t-3$), `last` (job $s+t$), `tail3` (job $s+t+1$) and `tail1` (job $s+t+2$). The construction is meaningful only for $t\ge 2$: for $t<2$ the paper's indices $s+1$ and $s+t$ coincide with conflicting times. The definition is total, but every theorem about it assumes $t\ge 2$. Processors $P_1,P_2,P_3$ are `0, 1, 2`. The instance $C$ is the published `ResourceScheduling.Chain.ThreePartition` (0-based indices, `C.b` $=B$).
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), p. 41, proof of Lemma 4

import Mathlib
import Definitions.Def_FlowJobShop_ThreePartFlow_FlowShop
import Definitions.Def_ResourceScheduling_Chain_ThreePartition

namespace FlowJobShop.ThreePartFlow

open ResourceScheduling.Chain

/-- The `s + t + 2` jobs of the flow shop `FS` built in the proof of Lemma 4
(Gonzalez–Sahni 1978, p. 41), with `s = 3t`. The paper numbers them `1, …, s + t + 2`:
* `elem i` is job `i + 1`, for `i = 0, …, s − 1` (the paper's jobs `1, …, s`);
* `first` is job `s + 1`;
* `middle k` is job `s + k + 2`, for `k = 0, …, t − 3` (the paper's jobs `s + i + 1`,
  `1 ≤ i ≤ t − 2`; there are exactly `t − 2` of them when `t ≥ 2`);
* `last` is job `s + t`;
* `tail3` is job `s + t + 1`;
* `tail1` is job `s + t + 2`.
The construction is meant for `t ≥ 2`; for `t < 2` the paper's indices `s + 1` and `s + t`
collide, and every theorem about this instance assumes `2 ≤ t`. -/
inductive FSJob (t : ℕ) where
  | elem (i : Fin (3 * t))
  | first
  | middle (k : Fin (t - 2))
  | last
  | tail3
  | tail1
  deriving DecidableEq, Fintype

/-- The task times of the flow shop `FS` of Lemma 4 (p. 41), processors `P_1, P_2, P_3` being
`0, 1, 2`, for a 3-Partition instance `C = (a_1, …, a_s, B)` (`C.b = B`):
* `t_{1,i} = t_{3,i} = a_i`, `t_{2,i} = 0` for `1 ≤ i ≤ s`;
* `t_{1,s+1} = 0`, `t_{2,s+1} = 2B`, `t_{3,s+1} = B`;
* `t_{1,s+i+1} = t_{3,s+i+1} = B`, `t_{2,s+i+1} = 2B` for `1 ≤ i ≤ t − 2`;
* `t_{1,s+t} = B`, `t_{2,s+t} = 2B`, `t_{3,s+t} = 0`;
* `t_{1,s+t+1} = t_{2,s+t+1} = 0`, `t_{3,s+t+1} = B`;
* `t_{1,s+t+2} = B`, `t_{2,s+t+2} = t_{3,s+t+2} = 0`. -/
noncomputable def fsTime (C : ThreePartition) : Fin 3 → FSJob C.t → ℝ
  | j, .elem i => ![(C.a i : ℝ), 0, (C.a i : ℝ)] j
  | j, .first => ![0, 2 * (C.b : ℝ), (C.b : ℝ)] j
  | j, .middle _ => ![(C.b : ℝ), 2 * (C.b : ℝ), (C.b : ℝ)] j
  | j, .last => ![(C.b : ℝ), 2 * (C.b : ℝ), 0] j
  | j, .tail3 => ![0, 0, (C.b : ℝ)] j
  | j, .tail1 => ![(C.b : ℝ), 0, 0] j

/-- The three-processor flow shop `FS` constructed from the 3-Partition instance `C` in the
proof of Lemma 4 (p. 41). -/
noncomputable def FS (C : ThreePartition) : FlowShop 3 (FSJob C.t) where
  m_pos := by omega
  t := fsTime C
  t_nonneg := by
    intro j i
    cases i <;> fin_cases j <;> simp [fsTime]

/-- The finish-time threshold `τ = 2tB` of Lemma 4. -/
noncomputable def tau (C : ThreePartition) : ℝ := 2 * (C.t : ℝ) * (C.b : ℝ)

end FlowJobShop.ThreePartFlow


