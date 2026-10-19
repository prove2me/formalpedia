-- Prove2me | solution 1 for AngelDevil.connectedSquares_perimeter
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-18T13:54:02.471821+00:00
-- url     : https://prove2.me/submissions/700b1bdf-1d4f-4089-8f8e-7005b53c9d6e

import Definitions.Def_AngelDevil_SquareBoundary

namespace AngelDevil

inductive GluedSquares : Finset Point → Prop
  | singleton (v : Point) : GluedSquares {v}
  | insert {s : Finset Point} {v : Point} : GluedSquares s → v ∉ s →
      (∃ u ∈ s, SquareAdjacent u v) → GluedSquares (insert v s)

theorem sideNeighbor_opposite (v : Point) (d : SquareSide) :
    sideNeighbor (sideNeighbor v d) (oppositeSide d) = v := by
  rcases v with ⟨x,y⟩
  rcases d with ⟨a,b⟩
  cases a <;> cases b <;> simp [sideNeighbor, oppositeSide]

theorem sideNeighbor_ne (v : Point) (d : SquareSide) : sideNeighbor v d ≠ v := by
  rcases v with ⟨x,y⟩
  rcases d with ⟨a,b⟩
  cases a <;> cases b <;> simp [sideNeighbor]

theorem exposedSides_antitone {s t : Finset Point} (hst : s ⊆ t) (v : Point) :
    exposedSides t v ⊆ exposedSides s v := by
  intro d hd
  simp only [exposedSides, Finset.mem_filter, Finset.mem_univ, true_and] at *
  exact fun h => hd (hst h)

theorem exposedSides_card_le (s : Finset Point) (v : Point) :
    (exposedSides s v).card ≤ 4 := by
  have h := Finset.card_le_card (Finset.subset_univ (exposedSides s v))
  simpa using h

theorem squarePerimeter_singleton (v : Point) : squarePerimeter {v} = 4 := by
  have h : exposedSides {v} v = Finset.univ := by
    ext d
    simp [exposedSides, sideNeighbor_ne]
  simp [squarePerimeter, h]

theorem squarePerimeter_insert {s : Finset Point} {u v : Point}
    (hu : u ∈ s) (hv : v ∉ s) (hadj : SquareAdjacent u v) :
    squarePerimeter (insert v s) ≤ squarePerimeter s + 2 := by
  obtain ⟨d, hd⟩ := hadj
  have hold : d ∈ exposedSides s u := by simp [exposedSides, hd, hv]
  have hnew : d ∉ exposedSides (insert v s) u := by simp [exposedSides, hd]
  have hstrict : (exposedSides (insert v s) u).card < (exposedSides s u).card := by
    apply Finset.card_lt_card
    exact Finset.ssubset_iff_subset_ne.mpr
      ⟨exposedSides_antitone (Finset.subset_insert v s) u,
        fun heq => hnew (heq.symm ▸ hold)⟩
  have hreverse : sideNeighbor v (oppositeSide d) = u := by
    rw [← hd]
    exact sideNeighbor_opposite u d
  have hmissing : oppositeSide d ∉ exposedSides (insert v s) v := by
    simp [exposedSides, hreverse, hu]
  have hthree : (exposedSides (insert v s) v).card ≤ 3 := by
    have hlt : (exposedSides (insert v s) v).card < (Finset.univ : Finset SquareSide).card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨Finset.subset_univ _, fun heq => hmissing (heq.symm ▸ Finset.mem_univ _)⟩)
    have hc : (Finset.univ : Finset SquareSide).card = 4 := by decide
    omega
  have hsum : (∑ w ∈ s.erase u, (exposedSides (insert v s) w).card) ≤
      ∑ w ∈ s.erase u, (exposedSides s w).card := by
    apply Finset.sum_le_sum
    intro w _
    exact Finset.card_le_card (exposedSides_antitone (Finset.subset_insert v s) w)
  have heq1 := Finset.sum_erase_add s (fun w => (exposedSides (insert v s) w).card) hu
  have heq2 := Finset.sum_erase_add s (fun w => (exposedSides s w).card) hu
  simp only [squarePerimeter, Finset.sum_insert hv]
  omega

theorem gluedSquares_perimeter {s : Finset Point} (h : GluedSquares s) :
    squarePerimeter s ≤ 2 * s.card + 2 := by
  induction h with
  | singleton v => simp [squarePerimeter_singleton]
  | @insert s v h hv hadj ih =>
    obtain ⟨u, hu, huv⟩ := hadj
    have hb := squarePerimeter_insert hu hv huv
    rw [Finset.card_insert_of_notMem hv]
    omega

theorem squarePath_crossing {s t : Finset Point} {a b : Point}
    (hpath : Relation.ReflTransGen
      (fun u v => u ∈ s ∧ v ∈ s ∧ SquareAdjacent u v) a b)
    (ha : a ∈ t) (hb : b ∉ t) :
    ∃ u ∈ t, ∃ v ∈ s, v ∉ t ∧ SquareAdjacent u v := by
  induction hpath with
  | refl => exact False.elim (hb ha)
  | @tail b c hpath hstep ih =>
    by_cases hbt : b ∈ t
    · exact ⟨b, hbt, c, hstep.2.1, hb, hstep.2.2⟩
    · exact ih hbt

theorem gluedSquares_nonempty {s : Finset Point} (h : GluedSquares s) : s.Nonempty := by
  cases h with
  | singleton v => exact ⟨v, Finset.mem_singleton_self v⟩
  | @insert s v _ _ _ => exact ⟨v, Finset.mem_insert_self v s⟩

theorem extend_gluedSquares (s t : Finset Point) (hconn : SquaresConnected s)
    (hsub : t ⊆ s) (hglue : GluedSquares t) : GluedSquares s := by
  classical
  by_cases heq : t = s
  · exact heq ▸ hglue
  · have hex : ∃ b ∈ s, b ∉ t := by
      by_contra h
      apply heq
      apply Finset.Subset.antisymm hsub
      intro b hb
      by_contra hbt
      exact h ⟨b, hb, hbt⟩
    obtain ⟨b, hbs, hbt⟩ := hex
    obtain ⟨a, hat⟩ := gluedSquares_nonempty hglue
    obtain ⟨u, hut, v, hvs, hvt, huv⟩ :=
      squarePath_crossing (hconn.2 a (hsub hat) b hbs) hat hbt
    have hsub' : insert v t ⊆ s := Finset.insert_subset hvs hsub
    exact extend_gluedSquares s (insert v t) hconn hsub'
      (GluedSquares.insert hglue hvt ⟨u, hut, huv⟩)
termination_by s.card - t.card
decreasing_by
  have hc := Finset.card_le_card hsub'
  rw [Finset.card_insert_of_notMem hvt] at *
  omega

theorem connectedSquares_glued {s : Finset Point} (h : SquaresConnected s) :
    GluedSquares s := by
  obtain ⟨a, ha⟩ := h.1
  exact extend_gluedSquares s {a} h (Finset.singleton_subset_iff.mpr ha)
    (GluedSquares.singleton a)

/-- Mathe, Claim 4.2: a nonempty side-connected set of n squares has at most
2n+2 boundary unit sides. No simple-connectivity assumption is needed. -/
theorem connectedSquares_perimeter {s : Finset Point} (h : SquaresConnected s) :
    squarePerimeter s ≤ 2 * s.card + 2 :=
  gluedSquares_perimeter (connectedSquares_glued h)

theorem mem_boundaryWalls (s : Finset Point) (v : Point) (d : SquareSide) :
    (v, d) ∈ boundaryWalls s ↔ v ∈ s ∧ sideNeighbor v d ∉ s := by
  simp [boundaryWalls, exposedSides]

theorem boundaryWalls_card (s : Finset Point) :
    (boundaryWalls s).card = squarePerimeter s := by
  unfold boundaryWalls
  rw [Finset.card_biUnion]
  · unfold squarePerimeter
    apply Finset.sum_congr rfl
    intro v _
    exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)
  · intro u _ v _ huv
    apply Finset.disjoint_left.mpr
    intro w hw1 hw2
    obtain ⟨d, _, hd⟩ := Finset.mem_image.mp hw1
    obtain ⟨e, _, he⟩ := Finset.mem_image.mp hw2
    exact huv (Prod.mk.inj (hd.trans he.symm)).1

theorem distinct_boundaryWalls_bound {s : Finset Point} (h : SquaresConnected s)
    (walls : Finset (Point × SquareSide)) (hw : walls ⊆ boundaryWalls s) :
    walls.card ≤ 2 * s.card + 2 := by
  have hc := Finset.card_le_card hw
  rw [boundaryWalls_card] at hc
  exact hc.trans (connectedSquares_perimeter h)

end AngelDevil

theorem solution {s : Finset AngelDevil.Point} (h : AngelDevil.SquaresConnected s) :
    AngelDevil.squarePerimeter s ≤ 2 * s.card + 2 :=
  AngelDevil.connectedSquares_perimeter h
