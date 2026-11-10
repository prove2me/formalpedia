-- Prove2me | Definitions.Def_MMSSevenNinths_Main_ThresholdSearch
-- name    : MMSSevenNinths_Main_ThresholdSearch
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:48:16.543518+00:00
-- url     : https://prove2.me/theorems/a3394e0a-e540-4ba4-adc3-a604b7eeef6e
-- title:
--   Algorithm 14 (threshold search) and the full 7/9-MMS algorithm
-- statement:
--   Algorithm 14 and the algorithm of Theorem 8.1 (§8.1–8.2 and the proof of Theorem 8.1).
--
--   * `initialThresholds V` is $\alpha_i=v_i(M)/n$. `updatedThresholds V α` performs the simultaneous update after the deterministic call `alg1Det V α`: every $i\in F$ gets $\alpha_i\leftarrow b_i$ (`failureBound`, computed from that call's own log), all other thresholds are unchanged.
--   * `thresholdSeq V t` is the threshold vector of call $t=0,1,\dots$, and `searchCall V t` is call $t$ itself: Algorithm 1 restarted on the whole instance at those thresholds.
--   * `tailMax V t i` is the maximum of Lemma 8.4: the largest $\frac97v_i(T)$ over the bundles $T$ that $i$ found unsatisfactory in call $t$ from that call's first tail-filling step onward (`none` if there is none).
--   * `searchCallCount V` is one more than the index of the first successful call, or $0$ if no call succeeds. `thresholdSearchOutput hn V` completes the bundles of the first successful call: each good goes to the agent holding it and every unallocated good to agent $0$ (the least original agent).
--   * `sevenNinthsAllocation hn V` is the full algorithm on an arbitrary instance: if $n>m$, every good goes to agent $0$; otherwise run Algorithm 14 on `orderedInstance V` and convert the result back with `convertBack`. `algorithm1CallCount V` is the number of calls of Algorithm 1 it makes ($0$ when $n>m$).
-- source:
--   Huang and Zhou (2026), A Strongly Polynomial-Time 7/9-Approximation Algorithm for Maximin Share Allocations, held STOC 2027 submission, SHA-256 428b298d196be354cea02bcd3b7278ffac7f04104c4bc290b02b6385aa0e405b, §8.1–8.2 and Algorithm 14, printed pp. 24–25 (PDF 27–28); proof of Theorem 8.1, printed p. 26 (PDF 29)

import Mathlib
import Definitions.Def_MMSSevenNinths_Main_Instance
import Definitions.Def_MMSSevenNinths_Main_OrderedReduction
import Definitions.Def_MMSSevenNinths_Main_Algorithm1

open scoped Classical

namespace MMSSevenNinths.Main

/-! Algorithm 14 (threshold search) and the full algorithm of Theorem 8.1,
Huang and Zhou (2026), §8.1, printed pp. 24–25 (PDF 27–28), and the proof of Theorem 8.1,
printed p. 26 (PDF 29). -/

/-- Initial thresholds: the proportional shares `α_i = v_i(M)/n`. -/
noncomputable def initialThresholds {n m : ℕ} (V : Fin n → Finset (Fin m) → ℝ) : Fin n → ℝ :=
  fun i => V i Finset.univ / n

/-- Simultaneous update after a call at thresholds `α`: every failed agent `i ∈ F` gets
`α_i ← b_i`, computed from the completed call's own test log; other thresholds are unchanged
(after a successful call `F = ∅`, so nothing changes). -/
noncomputable def updatedThresholds {n m : ℕ} (V : Fin n → Finset (Fin m) → ℝ)
    (α : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if i ∈ (alg1Det V α).failed then failureBound V α i else α i

/-- The threshold vector used by the `t`-th call (`t = 0, 1, …`) of Algorithm 14. -/
noncomputable def thresholdSeq {n m : ℕ} (V : Fin n → Finset (Fin m) → ℝ) :
    ℕ → Fin n → ℝ
  | 0 => initialThresholds V
  | t + 1 => updatedThresholds V (thresholdSeq V t)

/-- The `t`-th call of Algorithm 1 made by Algorithm 14: the deterministic implementation run
on the whole (original ordered) instance at thresholds `thresholdSeq V t`. -/
noncomputable def searchCall {n m : ℕ} (V : Fin n → Finset (Fin m) → ℝ) (t : ℕ) :
    CallResult n m :=
  alg1Det V (thresholdSeq V t)

/-- For agent `i` and call `t`: the largest `9 v_i(T)/7` over the bundles `T` that `i` found
unsatisfactory from the first tail-filling step of that call onward (the maximum of
Lemma 8.4); `none` if there is none. -/
noncomputable def tailMax {n m : ℕ} (V : Fin n → Finset (Fin m) → ℝ) (t : ℕ) (i : Fin n) :
    Option ℝ :=
  unsatMax V (thresholdSeq V t) i (searchCall V t).tailLog

/-- Complete the bundles of a successful call: each good goes to the smallest-index agent
holding it, and every unallocated good to agent `0` (the least original agent). -/
noncomputable def completeAllocation {n m : ℕ} (hn : 0 < n) (B : Fin n → Finset (Fin m)) :
    Fin m → Fin n :=
  fun g => ((List.finRange n).find? (fun i => decide (g ∈ B i))).getD ⟨0, hn⟩

/-- Number of calls of Algorithm 1 made by Algorithm 14 on `V`: the index of the first
successful call plus one; `0` if no call ever succeeds (then Algorithm 14 does not halt). -/
noncomputable def searchCallCount {n m : ℕ} (V : Fin n → Finset (Fin m) → ℝ) : ℕ :=
  if h : ∃ t, (searchCall V t).success = true then Nat.find h + 1 else 0

/-- Output of Algorithm 14 on `V`: the completed allocation of the first successful call
(the constant allocation to agent `0` if no call succeeds). -/
noncomputable def thresholdSearchOutput {n m : ℕ} (hn : 0 < n)
    (V : Fin n → Finset (Fin m) → ℝ) : Fin m → Fin n :=
  if h : ∃ t, (searchCall V t).success = true then
    completeAllocation hn (searchCall V (Nat.find h)).bundles
  else fun _ => ⟨0, hn⟩

/-- The full algorithm of Theorem 8.1 on an arbitrary instance: if `n > m`, give every good to
agent `0` (any complete allocation); otherwise build the ordered instance, run Algorithm 14
on it, and convert the result back (Lemma 2.4). -/
noncomputable def sevenNinthsAllocation {n m : ℕ} (hn : 0 < n)
    (V : Fin n → Finset (Fin m) → ℝ) : Fin m → Fin n :=
  if n ≤ m then convertBack V (thresholdSearchOutput hn (orderedInstance V))
  else fun _ => ⟨0, hn⟩

/-- Number of calls of Algorithm 1 made by the full algorithm (none when `n > m`). -/
noncomputable def algorithm1CallCount {n m : ℕ} (V : Fin n → Finset (Fin m) → ℝ) : ℕ :=
  if n ≤ m then searchCallCount (orderedInstance V) else 0

end MMSSevenNinths.Main


