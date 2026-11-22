-- Prove2me | Definitions.Def_GirvingAKS_LayeredAdapter
-- name    : GirvingAKS_LayeredAdapter
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:31:21.501727+00:00
-- url     : https://prove2.me/theorems/18e3501d-c210-4789-95d4-ac3eaaaeb980
-- title:
--   Greedy layering of sequential comparator networks
-- statement:
--   This file converts a comparator network given as a *sequence* of comparators into an equivalent network of *parallel layers* in the sense of `AKSSorting.Core.ComparatorNetwork`.
--
--   Each comparator $c=(i,j)$ is scheduled greedily: if $w(k)$ denotes the number of the last layer that uses wire $k$, then $c$ is appended to layer $\max(w(i),w(j))+1$ and both wire times are updated. All later layers avoid the wires $i$ and $j$, and disjoint compare-exchange operations commute, so the layered network computes the same function as the sequence. The main facts are
--
--   1. `toLayered_eval`: the layered network evaluates exactly like the sequential one;
--   2. `toLayered_depth`: its number of layers equals the greedy critical-path depth `depth` of the upstream network;
--   3. `toLayered_size`: its number of comparators equals the length of the sequence;
--   4. `toLayered_sorts`: it sorts whenever the sequential network sorts.
--
--   This bridge transfers the $O(\log n)$-depth sorting networks of the ported development to the layered model used by the Ajtai–Komlós–Szemerédi mission.
-- source:
--   Greedy critical-path scheduling of a comparator sequence into disjoint parallel steps; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983), §1

import Definitions.Def_GirvingAKS_Sort_Depth
import Definitions.Def_GirvingAKS_Sort_Monotone
import Definitions.Def_AKSSorting_Core_ComparatorNetwork

/-!
# From sequential comparator networks to layered networks

The upstream development (`girving/aks`) represents a comparator network as a
sequence of comparators and measures its depth by greedy critical-path
scheduling (`depthStep`).  The platform's `AKSSorting.Core.ComparatorNetwork`
is a list of parallel layers of pairwise disjoint comparators.

We run the greedy schedule explicitly: comparator `c` receives the time
`t = max (wt c.i) (wt c.j)` (0-based) and is appended to layer `t`.  Every
later layer avoids both wires of `c`, so moving `c` there does not change the
result of the evaluation.  The number of layers equals the upstream depth and
the total number of comparators is unchanged.
-/

namespace AKSLayered

/-! ## Inserting into a list of layers -/

/-- Append `c` to the layer with index `t`, or add the new layer `[c]` at the end
when there is no such layer. -/
def insertAt {α : Type} : List (List α) → ℕ → α → List (List α)
  | [], _, c => [[c]]
  | M :: L, 0, c => (M ++ [c]) :: L
  | M :: L, t + 1, c => M :: insertAt L t c

theorem length_insertAt {α : Type} (L : List (List α)) (t : ℕ) (c : α)
    (ht : t ≤ L.length) : (insertAt L t c).length = max L.length (t + 1) := by
  induction L generalizing t with
  | nil =>
    simp only [List.length_nil, Nat.le_zero] at ht
    subst ht
    simp [insertAt]
  | cons M L ih =>
    cases t with
    | zero => simp only [insertAt, List.length_cons]; omega
    | succ t =>
      simp only [List.length_cons] at ht
      simp only [insertAt, List.length_cons, ih t (by omega)]
      omega

theorem sum_length_insertAt {α : Type} (L : List (List α)) (t : ℕ) (c : α) :
    ((insertAt L t c).map List.length).sum = (L.map List.length).sum + 1 := by
  induction L generalizing t with
  | nil => simp [insertAt]
  | cons M L ih =>
    cases t with
    | zero => simp only [insertAt, List.map_cons, List.sum_cons, List.length_append,
        List.length_singleton]; omega
    | succ t => simp only [insertAt, List.map_cons, List.sum_cons, ih]; omega

theorem drop_insertAt {α : Type} (L : List (List α)) (t : ℕ) (c : α) :
    (insertAt L t c).drop (t + 1) = L.drop (t + 1) := by
  induction L generalizing t with
  | nil => simp [insertAt]
  | cons M L ih =>
    cases t with
    | zero => simp [insertAt]
    | succ t => simp only [insertAt, List.drop_succ_cons, ih]

theorem mem_drop_of_le {α : Type} {L : List α} {a b : ℕ} (h : b ≤ a) {X : α}
    (hX : X ∈ L.drop a) : X ∈ L.drop b :=
  (List.drop_sublist_drop_left L h).subset hX

theorem mem_drop_insertAt {α : Type} (L : List (List α)) (t m : ℕ) (c : α) {X : List α}
    (hX : X ∈ (insertAt L t c).drop m) {d : α} (hd : d ∈ X) :
    d = c ∨ ∃ Y ∈ L.drop m, d ∈ Y := by
  induction L generalizing t m with
  | nil =>
    have hX' : X ∈ [[c]] := List.mem_of_mem_drop hX
    simp only [List.mem_singleton] at hX'
    subst hX'
    simp only [List.mem_singleton] at hd
    exact Or.inl hd
  | cons M L ih =>
    cases t with
    | zero =>
      cases m with
      | zero =>
        simp only [insertAt, List.drop_zero, List.mem_cons] at hX
        rcases hX with rfl | hX
        · rcases List.mem_append.mp hd with hd | hd
          · exact Or.inr ⟨M, by simp, hd⟩
          · exact Or.inl (List.mem_singleton.mp hd)
        · exact Or.inr ⟨X, by simp [hX], hd⟩
      | succ m =>
        simp only [insertAt, List.drop_succ_cons] at hX
        exact Or.inr ⟨X, by simpa using hX, hd⟩
    | succ t =>
      cases m with
      | zero =>
        simp only [insertAt, List.drop_zero, List.mem_cons] at hX
        rcases hX with rfl | hX
        · exact Or.inr ⟨X, by simp, hd⟩
        · rcases ih t 0 (by simpa using hX) with h | ⟨Y, hY, hdY⟩
          · exact Or.inl h
          · exact Or.inr ⟨Y, by simp at hY ⊢; exact Or.inr hY, hdY⟩
      | succ m =>
        simp only [insertAt, List.drop_succ_cons] at hX
        rcases ih t m hX with h | ⟨Y, hY, hdY⟩
        · exact Or.inl h
        · exact Or.inr ⟨Y, by simpa using hY, hdY⟩

theorem mem_insertAt {α : Type} (L : List (List α)) (t : ℕ) (c : α) {X : List α}
    (hX : X ∈ insertAt L t c) : X ∈ L ∨ X = [c] ∨ ∃ M ∈ L.drop t, X = M ++ [c] := by
  induction L generalizing t with
  | nil =>
    simp only [insertAt, List.mem_singleton] at hX
    exact Or.inr (Or.inl hX)
  | cons M L ih =>
    cases t with
    | zero =>
      simp only [insertAt, List.mem_cons] at hX
      rcases hX with rfl | hX
      · exact Or.inr (Or.inr ⟨M, by simp, rfl⟩)
      · exact Or.inl (by simp [hX])
    | succ t =>
      simp only [insertAt, List.mem_cons] at hX
      rcases hX with rfl | hX
      · exact Or.inl (by simp)
      · rcases ih t hX with h | h | ⟨M', hM', rfl⟩
        · exact Or.inl (by simp [h])
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨M', by simpa using hM', rfl⟩)

/-! ## Commuting disjoint comparators -/

variable {n : ℕ}

/-- `c` and `d` share no wire. -/
def Apart (c d : Comparator n) : Prop :=
  (c.i ≠ d.i ∧ c.i ≠ d.j) ∧ (c.j ≠ d.i ∧ c.j ≠ d.j)

theorem apply_comm {α : Type} [LinearOrder α] (c d : Comparator n) (h : Apart c d)
    (y : Fin n → α) : c.apply (d.apply y) = d.apply (c.apply y) := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  have hc : c.i ≠ c.j := c.h.ne
  have hd : d.i ≠ d.j := d.h.ne
  funext k
  simp only [Comparator.apply]
  split_ifs <;> simp_all [Ne.symm]

/-- Evaluate a list of comparators in order. -/
def evalSeq {α : Type} [LinearOrder α] (cs : List (Comparator n)) (x : Fin n → α) :
    Fin n → α :=
  cs.foldl (fun y c => c.apply y) x

/-- Evaluate a list of layers in order. -/
def evalL {α : Type} [LinearOrder α] (L : List (List (Comparator n))) (x : Fin n → α) :
    Fin n → α :=
  L.foldl (fun y M => evalSeq M y) x

theorem evalSeq_apply_comm {α : Type} [LinearOrder α] (c : Comparator n)
    (M : List (Comparator n)) (hM : ∀ d ∈ M, Apart c d) (y : Fin n → α) :
    evalSeq M (c.apply y) = c.apply (evalSeq M y) := by
  induction M generalizing y with
  | nil => rfl
  | cons d M ih =>
    simp only [evalSeq, List.foldl_cons] at ih ⊢
    rw [← apply_comm c d (hM d (by simp)) y]
    exact ih (fun d' hd' => hM d' (by simp [hd'])) _

theorem evalL_apply_comm {α : Type} [LinearOrder α] (c : Comparator n)
    (L : List (List (Comparator n))) (hL : ∀ X ∈ L, ∀ d ∈ X, Apart c d) (y : Fin n → α) :
    evalL L (c.apply y) = c.apply (evalL L y) := by
  induction L generalizing y with
  | nil => rfl
  | cons M L ih =>
    simp only [evalL, List.foldl_cons] at ih ⊢
    rw [evalSeq_apply_comm c M (hL M (by simp))]
    exact ih (fun X hX => hL X (by simp [hX])) _

theorem evalL_insertAt {α : Type} [LinearOrder α] (L : List (List (Comparator n))) (t : ℕ)
    (c : Comparator n) (hav : ∀ X ∈ L.drop t, ∀ d ∈ X, Apart c d) (x : Fin n → α) :
    evalL (insertAt L t c) x = c.apply (evalL L x) := by
  induction L generalizing t x with
  | nil => rfl
  | cons M L ih =>
    cases t with
    | zero =>
      simp only [insertAt, evalL, List.foldl_cons]
      have h1 : evalSeq (M ++ [c]) x = c.apply (evalSeq M x) := by
        simp [evalSeq, List.foldl_append]
      rw [h1]
      exact evalL_apply_comm c L (fun X hX => hav X (by simp [hX])) _
    | succ t =>
      simp only [insertAt, evalL, List.foldl_cons]
      exact ih t (fun X hX => hav X (by simpa using hX)) _

/-! ## The greedy schedule -/

/-- Scheduling state: the layers built so far and, for every wire, the number of
the last layer that uses it (0 if none). -/
abbrev State (n : ℕ) := List (List (Comparator n)) × (Fin n → ℕ)

/-- Schedule one comparator: it goes to layer `max (wt c.i) (wt c.j)`. -/
def schedStep (s : State n) (c : Comparator n) : State n :=
  (insertAt s.1 (max (s.2 c.i) (s.2 c.j)) c,
    Function.update (Function.update s.2 c.i (max (s.2 c.i) (s.2 c.j) + 1)) c.j
      (max (s.2 c.i) (s.2 c.j) + 1))

/-- Invariant of the schedule. -/
structure Inv (s : State n) : Prop where
  le_len : ∀ k, s.2 k ≤ s.1.length
  avoid : ∀ k, ∀ X ∈ s.1.drop (s.2 k), ∀ d ∈ X, k ≠ d.i ∧ k ≠ d.j
  disj : ∀ X ∈ s.1, (X.flatMap fun d => [d.i, d.j]).Nodup

theorem inv_init : Inv (([], fun _ => 0) : State n) where
  le_len := fun _ => le_rfl
  avoid := by simp
  disj := by simp

theorem apart_of_inv {s : State n} (hs : Inv s) (c : Comparator n) :
    ∀ X ∈ s.1.drop (max (s.2 c.i) (s.2 c.j)), ∀ d ∈ X, Apart c d := by
  intro X hX d hd
  have hi := hs.avoid c.i X (mem_drop_of_le (le_max_left _ _) hX) d hd
  have hj := hs.avoid c.j X (mem_drop_of_le (le_max_right _ _) hX) d hd
  exact ⟨hi, hj⟩

theorem inv_schedStep {s : State n} (hs : Inv s) (c : Comparator n) :
    Inv (schedStep s c) := by
  obtain ⟨L, wt⟩ := s
  set t := max (wt c.i) (wt c.j) with ht_def
  have hci : wt c.i ≤ t := le_max_left _ _
  have hcj : wt c.j ≤ t := le_max_right _ _
  have htlen : t ≤ L.length := max_le (hs.le_len c.i) (hs.le_len c.j)
  have hne : c.i ≠ c.j := c.h.ne
  refine ⟨?_, ?_, ?_⟩
  · intro k
    simp only [schedStep]
    rw [length_insertAt L t c htlen]
    have hk := hs.le_len k
    simp only [Function.update_apply]
    split_ifs <;> simp_all <;> omega
  · intro k X hX d hd
    simp only [schedStep] at hX
    by_cases hk : k = c.j ∨ k = c.i
    · have hwk : (Function.update (Function.update wt c.i (t + 1)) c.j (t + 1)) k = t + 1 := by
        rcases hk with rfl | rfl
        · simp
        · simp [hne]
      rw [hwk, drop_insertAt] at hX
      have hle : wt k ≤ t + 1 := by rcases hk with rfl | rfl <;> omega
      exact hs.avoid k X (mem_drop_of_le hle hX) d hd
    · push Not at hk
      have hwk : (Function.update (Function.update wt c.i (t + 1)) c.j (t + 1)) k = wt k := by
        simp [hk.1, hk.2]
      rw [hwk] at hX
      rcases mem_drop_insertAt L t (wt k) c hX hd with rfl | ⟨Y, hY, hdY⟩
      · exact ⟨hk.2, hk.1⟩
      · exact hs.avoid k Y hY d hdY
  · intro X hX
    simp only [schedStep] at hX
    rcases mem_insertAt L t c hX with h | rfl | ⟨M, hM, rfl⟩
    · exact hs.disj X h
    · simp [hne]
    · rw [List.flatMap_append, List.nodup_append]
      refine ⟨hs.disj M (List.mem_of_mem_drop hM), by simp [hne], ?_⟩
      intro a ha b hb
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hb
      obtain ⟨d, hdM, had⟩ := List.mem_flatMap.mp ha
      have h1 := hs.avoid c.i M (mem_drop_of_le hci hM) d hdM
      have h2 := hs.avoid c.j M (mem_drop_of_le hcj hM) d hdM
      simp only [List.mem_cons, List.not_mem_nil, or_false] at had
      rcases hb with rfl | rfl <;> rcases had with rfl | rfl
      · exact h1.1.symm
      · exact h1.2.symm
      · exact h2.1.symm
      · exact h2.2.symm

/-- Running the schedule over a list of comparators preserves the invariant and the
semantics. -/
theorem fold_spec {α : Type} [LinearOrder α] (cs : List (Comparator n)) (s : State n)
    (hs : Inv s) :
    Inv (cs.foldl schedStep s) ∧
      ∀ x : Fin n → α, evalL (cs.foldl schedStep s).1 x = evalSeq cs (evalL s.1 x) := by
  induction cs generalizing s with
  | nil => exact ⟨hs, fun _ => rfl⟩
  | cons c cs ih =>
    obtain ⟨h1, h2⟩ := ih (schedStep s c) (inv_schedStep hs c)
    refine ⟨h1, fun x => ?_⟩
    simp only [List.foldl_cons]
    rw [h2 x]
    simp only [evalSeq, List.foldl_cons]
    congr 1
    exact evalL_insertAt s.1 _ c (apart_of_inv hs c) x

theorem fold_inv (cs : List (Comparator n)) (s : State n) (hs : Inv s) :
    Inv (cs.foldl schedStep s) := by
  induction cs generalizing s with
  | nil => exact hs
  | cons c cs ih => exact ih _ (inv_schedStep hs c)

/-- The schedule tracks exactly the state of upstream `depthStep`. -/
theorem fold_depth (cs : List (Comparator n)) (s : State n) (hs : Inv s) :
    cs.foldl depthStep (s.2, s.1.length) =
      ((cs.foldl schedStep s).2, (cs.foldl schedStep s).1.length) := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldl_cons]
    rw [← ih (schedStep s c) (inv_schedStep hs c)]
    congr 1
    have htlen : max (s.2 c.i) (s.2 c.j) ≤ s.1.length :=
      max_le (hs.le_len c.i) (hs.le_len c.j)
    simp only [depthStep, schedStep, length_insertAt _ _ _ htlen]
    all_goals (try congr 1)
    all_goals omega

theorem fold_size (cs : List (Comparator n)) (s : State n) :
    ((cs.foldl schedStep s).1.map List.length).sum = (s.1.map List.length).sum + cs.length := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldl_cons, ih, schedStep, sum_length_insertAt, List.length_cons]
    omega

/-! ## The layered network -/

/-- The layers produced by the greedy schedule. -/
def schedule (net : ComparatorNetwork n) : List (List (Comparator n)) :=
  (net.comparators.foldl schedStep ([], fun _ => 0)).1

theorem schedule_inv (net : ComparatorNetwork n) :
    Inv (net.comparators.foldl schedStep (([], fun _ => 0) : State n)) :=
  fold_inv _ _ inv_init

/-- The layered network obtained from an upstream sequential network. -/
def toLayered (net : ComparatorNetwork n) : AKSSorting.Core.ComparatorNetwork n where
  layers := (schedule net).map (List.map fun c => (c.i, c.j))
  ne := by
    intro L hL p hp
    simp only [List.mem_map] at hL
    obtain ⟨X, -, rfl⟩ := hL
    simp only [List.mem_map] at hp
    obtain ⟨c, -, rfl⟩ := hp
    exact c.h.ne
  disjoint := by
    intro L hL
    simp only [List.mem_map] at hL
    obtain ⟨X, hX, rfl⟩ := hL
    rw [List.flatMap_map]
    exact (schedule_inv net).disj X hX

theorem compareExchange_eq_apply {α : Type} [LinearOrder α] (c : Comparator n)
    (y : Fin n → α) : AKSSorting.Core.compareExchange c.i c.j y = c.apply y := by
  have hne : c.j ≠ c.i := c.h.ne'
  funext k
  simp only [AKSSorting.Core.compareExchange, Comparator.apply, Function.update_apply]
  by_cases hj : k = c.j
  · subst hj; simp [hne]
  · by_cases hi : k = c.i
    · subst hi; simp [hj]
    · simp [hi, hj]

theorem toLayered_eval {α : Type} [LinearOrder α] (net : ComparatorNetwork n)
    (x : Fin n → α) : (toLayered net).eval x = net.exec x := by
  have h := (fold_spec (α := α) net.comparators (([], fun _ => 0) : State n) inv_init).2 x
  have h1 : (toLayered net).eval x = evalL (schedule net) x := by
    simp only [AKSSorting.Core.ComparatorNetwork.eval, toLayered, List.foldl_map, evalL]
    congr 1
    funext y M
    simp only [AKSSorting.Core.ComparatorNetwork.evalLayer, List.foldl_map, evalSeq]
    congr 1
    funext z c
    exact compareExchange_eq_apply c z
  rw [h1]
  exact h

theorem toLayered_sorts (net : ComparatorNetwork n) (h : ComparatorNetwork.Sorts.{0} net) :
    (toLayered net).Sorts := by
  intro α _ x
  rw [show (toLayered net).eval x = net.exec x from toLayered_eval net x]
  exact h α x

theorem toLayered_depth (net : ComparatorNetwork n) :
    (toLayered net).depth = net.depth := by
  have h := fold_depth net.comparators (([], fun _ => 0) : State n) inv_init
  simp only [List.length_nil] at h
  simp only [AKSSorting.Core.ComparatorNetwork.depth, toLayered, List.length_map, schedule,
    ComparatorNetwork.depth, h]

theorem toLayered_size (net : ComparatorNetwork n) :
    (toLayered net).size = net.size := by
  have h := fold_size net.comparators (([], fun _ => 0) : State n)
  simp only [List.map_nil, List.sum_nil, zero_add] at h
  simp only [AKSSorting.Core.ComparatorNetwork.size, toLayered, List.map_map, schedule,
    ComparatorNetwork.size]
  rw [← h]
  congr 1
  apply List.map_congr_left
  intro X _
  simp

end AKSLayered


