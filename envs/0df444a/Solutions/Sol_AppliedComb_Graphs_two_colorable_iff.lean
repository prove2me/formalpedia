-- Prove2me | solution 1 for AppliedComb.Graphs.two_colorable_iff
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T02:28:17.60972+00:00
-- url     : https://prove2.me/submissions/5c75ed0f-38ff-4e78-af73-f695d7bed8c1

import Mathlib
import Definitions.Def_AppliedComb_Graphs_IsCycle

open SimpleGraph

namespace TwoColAux

/-- A closed walk of length `n`, given as a function `ℕ → V`. -/
def ClosedWalk {V : Type*} (G : SimpleGraph V) (f : ℕ → V) (n : ℕ) : Prop :=
  f n = f 0 ∧ ∀ i < n, G.Adj (f i) (f (i + 1))

/-- Splitting a closed walk at a repeated vertex `f i = f j` (`1 ≤ i < j ≤ n`) gives two closed
walks, of lengths `j - i` and `n - (j - i)`. -/
lemma split_left {V : Type*} {G : SimpleGraph V} {f : ℕ → V} {n i j : ℕ}
    (hf : ClosedWalk G f n) (hij : i < j) (hj : j ≤ n) (heq : f i = f j) :
    ClosedWalk G (fun k => f (i + k)) (j - i) := by
  refine ⟨?_, fun k hk => ?_⟩
  · simp only [add_zero]
    have : i + (j - i) = j := by omega
    rw [this, heq]
  · have := hf.2 (i + k) (by omega)
    simpa [add_assoc] using this

lemma split_right {V : Type*} {G : SimpleGraph V} {f : ℕ → V} {n i j : ℕ}
    (hf : ClosedWalk G f n) (hij : i < j) (hj : j ≤ n) (heq : f i = f j) :
    ClosedWalk G (fun k => if k ≤ i then f k else f (k + (j - i))) (n - (j - i)) := by
  have hkey : ∀ k, i ≤ k → (if k ≤ i then f k else f (k + (j - i))) = f (k + (j - i)) := by
    intro k hk
    by_cases h : k ≤ i
    · have : k = i := le_antisymm h hk
      subst this
      have : k + (j - k) = j := by omega
      simp [this, heq]
    · simp [h]
  refine ⟨?_, fun k hk => ?_⟩
  · dsimp only
    have h1 : i ≤ n - (j - i) := by omega
    rw [hkey _ h1]
    have : n - (j - i) + (j - i) = n := by omega
    rw [this]
    simp [hf.1]
  · dsimp only
    by_cases hk1 : k + 1 ≤ i
    · have h1 : k ≤ i := by omega
      simp only [h1, hk1, if_true]
      exact hf.2 k (by omega)
    · by_cases hk2 : k ≤ i
      · have : k = i := by omega
        subst this
        simp only [le_refl, if_true, hk1, if_false]
        have e : k + 1 + (j - k) = (j) + 1 := by omega
        rw [e, heq]
        exact hf.2 j (by omega)
      · rw [hkey k (by omega)]
        simp only [hk1, if_false]
        have e : k + 1 + (j - i) = (k + (j - i)) + 1 := by omega
        rw [e]
        exact hf.2 _ (by omega)

/-- An odd closed walk, without repeated vertices among `f 1, …, f n`, gives an odd cycle. -/
lemma oddCycle_of_injective {V : Type*} {G : SimpleGraph V} {f : ℕ → V} {n : ℕ}
    (hf : ClosedWalk G f n) (hodd : Odd n)
    (hinj : ∀ i j, 1 ≤ i → i < j → j ≤ n → f i ≠ f j) :
    AppliedComb.Graphs.ContainsOddCycle G := by
  have hn1 : n ≠ 1 := by
    rintro rfl
    have h := hf.2 0 (by omega)
    have h1 : f 1 = f 0 := hf.1
    rw [h1] at h
    exact G.loopless.irrefl _ h
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact absurd hodd (by decide)
  have hn3 : 3 ≤ n := by
    have := Nat.odd_iff.mp hodd
    omega
  refine ⟨(List.range n).map (fun k => f (k + 1)), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa using hn3
  · refine List.Nodup.map_on ?_ (List.nodup_range)
    intro x hx y hy hxy
    simp only [List.mem_range] at hx hy
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact hinj (x + 1) (y + 1) (by omega) (by omega) (by omega) hxy
    · exact hinj (y + 1) (x + 1) (by omega) (by omega) (by omega) hxy.symm
  · rw [List.isChain_map, List.isChain_iff_getElem]
    intro i hi
    simp only [List.length_range] at hi
    simp only [List.getElem_range]
    exact hf.2 (i + 1) (by omega)
  · refine ⟨f 1, f n, ?_, ?_, ?_⟩
    · rw [List.head?_map, List.head?_range]
      simp [hn0]
    · rw [List.getLast?_map, List.getLast?_range]
      simp only [hn0, if_false, Option.map_some]
      congr 2
      omega
    · have h := hf.2 0 (by omega)
      rw [hf.1]
      exact h.symm
  · simpa using hodd

/-- An odd closed walk yields an odd cycle. -/
lemma oddCycle_of_closedWalk {V : Type*} (G : SimpleGraph V) :
    ∀ (n : ℕ) (f : ℕ → V), ClosedWalk G f n → Odd n → AppliedComb.Graphs.ContainsOddCycle G := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f hf hodd
    by_cases hinj : ∀ i j, 1 ≤ i → i < j → j ≤ n → f i ≠ f j
    · exact oddCycle_of_injective hf hodd hinj
    · push Not at hinj
      obtain ⟨i, j, hi, hij, hj, heq⟩ := hinj
      have hL := split_left hf hij hj heq
      have hR := split_right hf hij hj heq
      have hsum : (j - i) + (n - (j - i)) = n := by omega
      rcases Nat.even_or_odd (j - i) with he | ho
      · have hodd' : Odd (n - (j - i)) := by
          have h1 := Nat.even_iff.mp he
          have h2 := Nat.odd_iff.mp hodd
          exact Nat.odd_iff.mpr (by omega)
        exact ih (n - (j - i)) (by omega) _ hR hodd'
      · exact ih (j - i) (by omega) _ hL ho

/-- Colour parity along a chain in a proper Boolean colouring. -/
lemma chain_color {V : Type*} {G : SimpleGraph V} (c : G.Coloring Bool) :
    ∀ (l : List V) (a : V), List.IsChain G.Adj (a :: l) →
      ∀ b, (a :: l).getLast? = some b → (c a = c b ↔ Even l.length) := by
  intro l
  induction l with
  | nil =>
    intro a _ b hb
    simp only [List.getLast?_singleton, Option.some.injEq] at hb
    subst hb
    simp
  | cons x l' ih =>
    intro a hch b hb
    rw [List.isChain_cons_cons] at hch
    have hax : c a ≠ c x := c.valid hch.1
    have h1 := ih x hch.2 b (by simpa [List.getLast?_cons_cons] using hb)
    simp only [List.length_cons, Nat.even_add_one]
    revert hax h1
    cases c a <;> cases c x <;> cases c b <;> simp

lemma not_containsOddCycle_of_colorable {V : Type*} {G : SimpleGraph V}
    (h : G.chromaticNumber ≤ 2) : ¬ AppliedComb.Graphs.ContainsOddCycle G := by
  rintro ⟨xs, ⟨hlen, hnd, hchain, a, b, ha, hb, hab⟩, hodd⟩
  obtain ⟨c0⟩ := chromaticNumber_le_iff_colorable.mp h
  let c : G.Coloring Bool := recolorOfEquiv G finTwoEquiv c0
  cases xs with
  | nil => simp at hlen
  | cons x l =>
    simp only [List.head?_cons, Option.some.injEq] at ha
    subst ha
    have := chain_color c l x hchain b hb
    have hev : Even l.length := by
      have h1 := Nat.odd_iff.mp hodd
      simp only [List.length_cons] at h1
      exact Nat.even_iff.mpr (by omega)
    exact c.valid hab (this.mpr hev)

lemma even_of_noOddCycle {V : Type*} {G : SimpleGraph V}
    (h : ¬ AppliedComb.Graphs.ContainsOddCycle G) {u : V} (p : G.Walk u u) :
    Even p.length := by
  by_contra hne
  have hodd : Odd p.length := Nat.not_even_iff_odd.mp hne
  refine h (oddCycle_of_closedWalk G p.length p.getVert ⟨?_, fun i hi => p.adj_getVert_succ hi⟩ hodd)
  rw [p.getVert_length, p.getVert_zero]

lemma colorable_two_of_noOddCycle {V : Type*} {G : SimpleGraph V}
    (h : ¬ AppliedComb.Graphs.ContainsOddCycle G) : G.chromaticNumber ≤ 2 := by
  classical
  have hrep : ∀ C : G.ConnectedComponent, ∃ r : V, G.connectedComponentMk r = C :=
    fun C => Quot.exists_rep C
  choose rep hrep using hrep
  let col : V → Bool := fun v =>
    decide (Odd (G.dist (rep (G.connectedComponentMk v)) v))
  have hvalid : ∀ {u v : V}, G.Adj u v → col u ≠ col v := by
    intro u v huv
    have hC : G.connectedComponentMk u = G.connectedComponentMk v :=
      ConnectedComponent.connectedComponentMk_eq_of_adj huv
    have hru : G.Reachable (rep (G.connectedComponentMk u)) u :=
      ConnectedComponent.eq.mp (hrep _)
    have hrv : G.Reachable (rep (G.connectedComponentMk u)) v :=
      ConnectedComponent.eq.mp ((hrep _).trans hC)
    obtain ⟨p, hp⟩ := hru.exists_walk_length_eq_dist
    obtain ⟨q, hq⟩ := hrv.exists_walk_length_eq_dist
    have hev := even_of_noOddCycle h (p.append (Walk.cons huv q.reverse))
    simp only [Walk.length_append, Walk.length_cons, Walk.length_reverse, hp, hq] at hev
    intro hcol
    simp only [col] at hcol
    rw [← hC] at hcol
    simp only [decide_eq_decide] at hcol
    have h1 := Nat.even_iff.mp hev
    by_cases ho : Odd (G.dist (rep (G.connectedComponentMk u)) u)
    · have ho' := hcol.mp ho
      have := Nat.odd_iff.mp ho
      have := Nat.odd_iff.mp ho'
      omega
    · have ho' : ¬ Odd (G.dist (rep (G.connectedComponentMk u)) v) := fun h' => ho (hcol.mpr h')
      have := Nat.not_odd_iff.mp ho
      have := Nat.not_odd_iff.mp ho'
      omega
  let c : G.Coloring Bool := Coloring.mk col (fun {u v} huv => hvalid huv)
  have hc : G.Colorable 2 := by
    simpa using (recolorOfEquiv G finTwoEquiv.symm c).colorable
  exact hc.chromaticNumber_le

end TwoColAux

theorem solution {V : Type*} [Fintype V] (G : SimpleGraph V) :
    G.chromaticNumber ≤ 2 ↔ ¬ AppliedComb.Graphs.ContainsOddCycle G :=
  ⟨TwoColAux.not_containsOddCycle_of_colorable, TwoColAux.colorable_two_of_noOddCycle⟩
