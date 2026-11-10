-- Prove2me | Definitions.Def_MMSSevenNinths_Main_OrderedReduction
-- name    : MMSSevenNinths_Main_OrderedReduction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:47:16.787554+00:00
-- url     : https://prove2.me/theorems/42f0bf0a-d971-4fba-8f5a-b044629e178b
-- title:
--   The ordered instance and the allocation conversion of Lemma 2.4
-- statement:
--   The construction behind Lemma 2.4 ([BK20, §3.1]) as used in the proof of Theorem 8.1.
--
--   * `sortedValues V i` sorts agent $i$'s singleton values $v_i(e_1),\dots,v_i(e_m)$ into nonincreasing order (stable merge sort); `orderedSingleton V i r` is its entry $r$ (the $(r+1)$-st largest value), and `orderedInstance V` is the additive instance $\hat V$ with $\hat v_i(S)=\sum_{r\in S}\hat v_i(\hat e_{r+1})$ on the ranks `Fin m`.
--   * `favourite V a R` is agent $a$'s most valuable good in the finite set $R$ (ties to the smallest index; `none` if $R=\emptyset$), found by one scan.
--   * `convertBack V σ̂` converts an allocation $\hat\sigma$ of the ordered instance into one of the original instance: process the ranks $\hat e_1,\hat e_2,\dots,\hat e_m$ from the most valuable rank down; the owner $\hat\sigma(r)$ of each rank takes her favourite remaining original good. The $m$ steps take every original good, so the fallback in the definition is never used.
-- source:
--   Huang and Zhou (2026), A Strongly Polynomial-Time 7/9-Approximation Algorithm for Maximin Share Allocations, held STOC 2027 submission, SHA-256 428b298d196be354cea02bcd3b7278ffac7f04104c4bc290b02b6385aa0e405b, Lemma 2.4, printed p. 4 (PDF 7), and proof of Theorem 8.1, printed p. 26 (PDF 29)

import Mathlib
import Definitions.Def_MMSSevenNinths_Main_Instance

open scoped Classical

namespace MMSSevenNinths.Main

/-! The ordered-instance construction and allocation conversion of Lemma 2.4
(Huang and Zhou (2026), printed p. 4 / PDF 7, after [BK20, §3.1]; used in the proof of
Theorem 8.1, printed p. 26 / PDF 29). -/

/-- Agent `i`'s singleton values `v_i(e_1), …, v_i(e_m)` sorted in nonincreasing order
(a stable merge sort). -/
noncomputable def sortedValues {n m : ℕ} (V : Fin n → Finset (Fin m) → ℝ) (i : Fin n) :
    List ℝ :=
  (List.ofFn (fun g : Fin m => V i {g})).mergeSort (fun a b => decide (b ≤ a))

/-- `v̂_i(ê_{r+1})`: the `(r+1)`-st largest singleton value of agent `i`. -/
noncomputable def orderedSingleton {n m : ℕ} (V : Fin n → Finset (Fin m) → ℝ) (i : Fin n)
    (r : Fin m) : ℝ :=
  (sortedValues V i).getD r.val 0

/-- The ordered instance `Î = (N, M̂, V̂)`: rank `r : Fin m` is the good `ê_{r+1}`, and
`v̂_i(S) = ∑_{r ∈ S} v̂_i(ê_{r+1})` is additive. -/
noncomputable def orderedInstance {n m : ℕ} (V : Fin n → Finset (Fin m) → ℝ) :
    Fin n → Finset (Fin m) → ℝ :=
  fun i S => ∑ r ∈ S, orderedSingleton V i r

/-- Agent `a`'s most valuable good in the finite set `R`, ties broken towards the smallest
original index; `none` when `R = ∅`. A single left-to-right scan. -/
noncomputable def favourite {n m : ℕ} (V : Fin n → Finset (Fin m) → ℝ) (a : Fin n)
    (R : Finset (Fin m)) : Option (Fin m) :=
  (R.sort (· ≤ ·)).foldl
    (fun best g => match best with
      | none => some g
      | some b => if V a {b} < V a {g} then some g else some b) none

/-- One step of the conversion: the owner `a = σ̂(r)` of rank `r` takes her favourite
remaining original good. The state is (remaining goods, partial owner map). -/
noncomputable def convertStep {n m : ℕ} (V : Fin n → Finset (Fin m) → ℝ) (σh : Fin m → Fin n)
    (st : Finset (Fin m) × (Fin m → Option (Fin n))) (r : Fin m) :
    Finset (Fin m) × (Fin m → Option (Fin n)) :=
  match favourite V (σh r) st.1 with
  | none => st
  | some g => (st.1.erase g, Function.update st.2 g (some (σh r)))

/-- Conversion of an allocation `σ̂` of the ordered instance back to the original instance:
process the ranks `ê_1, ê_2, …, ê_m` from the most valuable rank down, each rank's owner
taking her favourite remaining original good. Every original good is taken by the `m` steps;
the fallback `σh g` in `getD` is never used. -/
noncomputable def convertBack {n m : ℕ} (V : Fin n → Finset (Fin m) → ℝ) (σh : Fin m → Fin n) :
    Fin m → Fin n :=
  let st := (List.finRange m).foldl (convertStep V σh) (Finset.univ, fun _ => none)
  fun g => (st.2 g).getD (σh g)

end MMSSevenNinths.Main


