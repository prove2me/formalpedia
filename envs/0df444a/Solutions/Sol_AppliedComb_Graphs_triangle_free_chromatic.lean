-- Prove2me | solution 1 for AppliedComb.Graphs.triangle_free_chromatic
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T02:45:37.796813+00:00
-- url     : https://prove2.me/submissions/f5b77573-7456-4a73-9ccc-c9439018fdcc

import Mathlib

namespace MycAux

/-- The adjacency relation of the Mycielskian on `Option (V × Bool)`: `some (v, false)` is the
original vertex `v`, `some (v, true)` its twin, and `none` the apex. -/
def Madj {V : Type*} (G : SimpleGraph V) : Option (V × Bool) → Option (V × Bool) → Prop
  | some (a, false), some (b, false) => G.Adj a b
  | some (a, true), some (b, false) => G.Adj a b
  | some (a, false), some (b, true) => G.Adj a b
  | some (_, true), none => True
  | none, some (_, true) => True
  | _, _ => False

/-- The Mycielskian of a graph. -/
def myc {V : Type*} (G : SimpleGraph V) : SimpleGraph (Option (V × Bool)) where
  Adj := Madj G
  symm := ⟨by
    intro x y h
    rcases x with _ | ⟨a, _ | _⟩ <;> rcases y with _ | ⟨b, _ | _⟩ <;>
      simp only [Madj] at h ⊢ <;> exact h.symm⟩
  loopless := ⟨by
    intro x h
    rcases x with _ | ⟨a, _ | _⟩ <;> simp only [Madj] at h
    exact G.loopless.irrefl a h⟩

lemma myc_adj {V : Type*} (G : SimpleGraph V) (x y : Option (V × Bool)) :
    (myc G).Adj x y ↔ Madj G x y := Iff.rfl

/-- No triangles. -/
def TriFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c → False

lemma myc_triFree {V : Type*} {G : SimpleGraph V} (h : TriFree G) : TriFree (myc G) := by
  intro a b c hab hac hbc
  rw [myc_adj] at hab hac hbc
  rcases a with _ | ⟨x, _ | _⟩ <;> rcases b with _ | ⟨y, _ | _⟩ <;>
    rcases c with _ | ⟨z, _ | _⟩ <;> simp only [Madj] at hab hac hbc <;>
    exact h _ _ _ hab hac hbc

lemma myc_colorable {V : Type*} {G : SimpleGraph V} {k : ℕ} (h : G.Colorable k) :
    (myc G).Colorable (k + 1) := by
  obtain ⟨c⟩ := h
  refine ⟨SimpleGraph.Coloring.mk
    (fun x : Option (V × Bool) => x.elim (Fin.last k) (fun p => (c p.1).castSucc)) ?_⟩
  intro x y hxy
  rw [myc_adj] at hxy
  rcases x with _ | ⟨a, _ | _⟩ <;> rcases y with _ | ⟨b, _ | _⟩ <;> simp only [Madj] at hxy <;>
    first
    | exact (Fin.castSucc_lt_last _).ne
    | exact (Fin.castSucc_lt_last _).ne.symm
    | simpa using c.valid hxy

lemma myc_colorable_rev {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (h : (myc G).Colorable (k + 1)) : G.Colorable k := by
  classical
  obtain ⟨d⟩ := h
  set m : Fin (k + 1) := d none with hm
  have hcopy : ∀ v, d (some (v, true)) ≠ m := fun v =>
    d.valid ((myc_adj G _ _).2 (by simp [Madj]))
  let c : V → {x : Fin (k + 1) // x ≠ m} := fun v =>
    if h : d (some (v, false)) ≠ m then ⟨d (some (v, false)), h⟩ else ⟨d (some (v, true)), hcopy v⟩
  have hc : ∀ {v w : V}, G.Adj v w → c v ≠ c w := by
    intro v w hvw
    have h1 : d (some (v, false)) ≠ d (some (w, false)) := d.valid ((myc_adj G _ _).2 hvw)
    have h2 : d (some (v, true)) ≠ d (some (w, false)) := d.valid ((myc_adj G _ _).2 hvw)
    have h3 : d (some (v, false)) ≠ d (some (w, true)) := d.valid ((myc_adj G _ _).2 hvw)
    by_cases hv : d (some (v, false)) = m <;> by_cases hw : d (some (w, false)) = m
    · exact absurd (hv.trans hw.symm) h1
    · intro heq
      simp only [c, hv, hw, ne_eq, not_true_eq_false, not_false_eq_true, dif_neg, dif_pos,
        Subtype.mk.injEq] at heq
      exact h2 heq
    · intro heq
      simp only [c, hv, hw, ne_eq, not_true_eq_false, not_false_eq_true, dif_neg, dif_pos,
        Subtype.mk.injEq] at heq
      exact h3 heq
    · intro heq
      simp only [c, hv, hw, ne_eq, not_false_eq_true, dif_pos, Subtype.mk.injEq] at heq
      exact h1 heq
  have hcol := (SimpleGraph.Coloring.mk c (fun {v w} hvw => hc hvw)).colorable
  have hcard : Fintype.card {x : Fin (k + 1) // x ≠ m} = k := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
    simp
  rwa [hcard] at hcol

lemma cliqueNum_eq_two {V : Type*} [Finite V] (G : SimpleGraph V) (h : TriFree G) {a b : V}
    (hab : G.Adj a b) : G.cliqueNum = 2 := by
  classical
  apply le_antisymm
  · obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
    by_contra hlt
    have h3 : 3 ≤ s.card := by rw [hs.card_eq]; omega
    obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq h3
    have ht : G.IsNClique 3 t := ⟨hs.isClique.subset (by exact_mod_cast hts), htc⟩
    obtain ⟨x, y, z, hxy, hxz, hyz, _⟩ := SimpleGraph.is3Clique_iff.1 ht
    exact h x y z hxy hxz hyz
  · have hcl : G.IsClique (↑({a, b} : Finset V) : Set V) := by
      rw [Finset.coe_pair, SimpleGraph.isClique_pair]
      exact fun _ => hab
    have := SimpleGraph.IsClique.card_le_cliqueNum (G := G) (t := {a, b}) (tc := hcl)
    rwa [Finset.card_pair hab.ne] at this

/-- Mycielski induction: a triangle-free graph with an edge that needs exactly `k + 2` colours. -/
lemma exists_graph (k : ℕ) :
    ∃ (W : Type) (_ : Fintype W) (G : SimpleGraph W),
      G.Colorable (k + 2) ∧ ¬ G.Colorable (k + 1) ∧ TriFree G ∧ ∃ a b, G.Adj a b := by
  induction k with
  | zero =>
    refine ⟨Bool, inferInstance, ⊤, ?_, ?_, ?_, true, false, by decide⟩
    · simpa using SimpleGraph.colorable_of_fintype (⊤ : SimpleGraph Bool)
    · intro hc
      rw [zero_add, SimpleGraph.colorable_one_iff] at hc
      have := congrArg (fun H : SimpleGraph Bool => H.Adj true false) hc
      simp at this
    · intro a b c hab hac hbc
      revert a b c
      decide
  | succ k ih =>
    obtain ⟨W, hW, G, h1, h2, h3, a, b, hab⟩ := ih
    refine ⟨Option (W × Bool), inferInstance, myc G, myc_colorable h1, ?_, myc_triFree h3,
      some (a, false), some (b, false), (myc_adj G _ _).2 hab⟩
    intro hc
    exact h2 (myc_colorable_rev hc)

end MycAux

/-- For every `t ≥ 3` there is a triangle-free-clique graph with chromatic number `t`. -/
theorem solution (t : ℕ) (ht : 3 ≤ t) :
    ∃ (N : ℕ) (G : SimpleGraph (Fin N)), G.chromaticNumber = t ∧ G.cliqueNum = 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 2 := ⟨t - 2, by omega⟩
  obtain ⟨W, hW, G, h1, h2, h3, a, b, hab⟩ := MycAux.exists_graph k
  let e : Fin (Fintype.card W) ≃ W := (Fintype.equivFin W).symm
  refine ⟨Fintype.card W, G.comap e, ?_, ?_⟩
  · rw [SimpleGraph.chromaticNumber_congr (SimpleGraph.Iso.comap e G)]
    have : ((k + 2 : ℕ) : ℕ∞) = ((k + 1 : ℕ) : ℕ∞) + 1 := by push_cast; ring
    rw [this]
    exact SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable.2 ⟨h1, h2⟩
  · refine MycAux.cliqueNum_eq_two (G.comap e) ?_ (a := e.symm a) (b := e.symm b) ?_
    · intro x y z hxy hxz hyz
      exact h3 (e x) (e y) (e z) hxy hxz hyz
    · simpa [SimpleGraph.comap_adj] using hab
