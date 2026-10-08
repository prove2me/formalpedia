-- Prove2me | Definitions.Def_FlowJobShop_PartitionFlow_Instance
-- name    : FlowJobShop_PartitionFlow_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:15:11.843986+00:00
-- url     : https://prove2.me/theorems/00b91df5-2f73-4014-89fb-83568a77ddeb
-- title:
--   The three-machine flow shop FS of the proof of Lemma 1, built from a PARTITION instance (p. 39)
-- statement:
--   Let $S=\{a_1,\dots,a_n\}$ be a multiset of nonnegative integers and $T=\sum_{i=1}^n a_i$. The flow shop **FS** has $m=3$ processors and $n+2$ jobs, with task times
--   $$t_{1,i}=a_i,\quad t_{2,i}=0,\quad t_{3,i}=a_i\qquad(1\le i\le n),$$
--   $$t_{1,n+1}=T/2,\quad t_{2,n+1}=T,\quad t_{3,n+1}=0,$$
--   $$t_{1,n+2}=0,\quad t_{2,n+2}=T,\quad t_{3,n+2}=T/2 .$$
--   The threshold of the reduction is $\tau=2T$. Every job of FS has at most two nonzero tasks.
--
--   FS is the instance through which the paper reduces PARTITION to the three-machine flow-shop finish-time problem, in both its preemptive and non-preemptive versions. The same quantity $T=\sum_i a_i$ is the scale of the two-processor job shop JS built from $S$ in the proof of Lemma 5 (p. 43, threshold $5T$).
--
--   **Formalization Note** Jobs are `Fin n ⊕ Fin 2`: `Sum.inl i` is job $i+1$, `Sum.inr 0` is job $n+1$, `Sum.inr 1` is job $n+2$. Processors $P_1,P_2,P_3$ are `0, 1, 2`. Times are real numbers, since $T/2$ need not be an integer; $T$ is the real cast of $\sum_i a_i$. The file also contains the two one-line facts $T\ge0$ and $t_{j,i}\ge0$ needed to build the flow shop.
-- source:
--   Gonzalez, Sahni, Flowshop and Jobshop Schedules: Complexity and Approximation, Operations Research 26(1) (1978), p. 39, proof of Lemma 1 (construction of FS)

import Mathlib
import Definitions.Def_FlowJobShop_PartitionFlow_FlowShop

namespace FlowJobShop.PartitionFlow

/-- `T = ∑_{i=1}^n a_i`, as a real number. -/
noncomputable def T {n : ℕ} (a : Fin n → ℕ) : ℝ := ∑ i, (a i : ℝ)

/-- The task times of the flow shop FS of the proof of Lemma 1 (Gonzalez–Sahni 1978, p. 39).
Jobs are `Fin n ⊕ Fin 2`: `Sum.inl i` is job `i + 1` (`1 ≤ i + 1 ≤ n`), `Sum.inr 0` is job
`n + 1` and `Sum.inr 1` is job `n + 2`. Processors `0, 1, 2` are `P_1, P_2, P_3`.
* job `i ≤ n`: `t_{1,i} = a_i`, `t_{2,i} = 0`, `t_{3,i} = a_i`;
* job `n + 1`: `t_{1,n+1} = T/2`, `t_{2,n+1} = T`, `t_{3,n+1} = 0`;
* job `n + 2`: `t_{1,n+2} = 0`, `t_{2,n+2} = T`, `t_{3,n+2} = T/2`. -/
noncomputable def fsTimes {n : ℕ} (a : Fin n → ℕ) : Fin 3 → Fin n ⊕ Fin 2 → ℝ
  | j, Sum.inl i => ![(a i : ℝ), 0, (a i : ℝ)] j
  | j, Sum.inr 0 => ![T a / 2, T a, 0] j
  | j, Sum.inr 1 => ![0, T a, T a / 2] j

theorem T_nonneg {n : ℕ} (a : Fin n → ℕ) : 0 ≤ T a :=
  Finset.sum_nonneg (fun i _ => Nat.cast_nonneg (a i))

theorem fsTimes_nonneg {n : ℕ} (a : Fin n → ℕ) (j : Fin 3) (i : Fin n ⊕ Fin 2) :
    0 ≤ fsTimes a j i := by
  have hT := T_nonneg a
  rcases i with i | k
  · fin_cases j <;> simp [fsTimes]
  · fin_cases k <;> fin_cases j <;> simp [fsTimes] <;> linarith

/-- The three-processor flow shop **FS** built from the PARTITION instance `a` in the proof of
Lemma 1 (p. 39), with `n + 2` jobs and the task times `fsTimes a`. -/
noncomputable def FS {n : ℕ} (a : Fin n → ℕ) : FlowShop 3 (Fin n ⊕ Fin 2) :=
  ⟨fsTimes a, fsTimes_nonneg a, by decide⟩

end FlowJobShop.PartitionFlow


