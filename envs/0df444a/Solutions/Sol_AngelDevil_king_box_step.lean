-- Prove2me | solution 1 for AngelDevil.king_box_step
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-19T13:22:34.521608+00:00
-- url     : https://prove2.me/submissions/3737259d-c150-4d52-9591-1aa190addda5

import Definitions.Def_AngelDevil_KingGuard
import Definitions.Def_AngelDevil_FiniteGame
import Mathlib.Tactic.FinCases
import Theorems.Thm_AngelDevil_kingGuard_five_origin

set_option maxRecDepth 2000
set_option maxHeartbeats 2000000

namespace AngelDevil

theorem kingOffset_bounds (i : Fin 3) : -1 ≤ kingOffset i ∧ kingOffset i ≤ 1 := by
  unfold kingOffset
  have := i.isLt
  omega

theorem kingOffset_exhaustive (z : Int) (h : -1 ≤ z ∧ z ≤ 1) :
    ∃ i : Fin 3, kingOffset i = z := by
  refine ⟨⟨(z+1).toNat, by omega⟩, ?_⟩
  change ((z+1).toNat : Int) - 1 = z
  omega

theorem guardSquare_bounds (x : Int) (i : Fin 11) :
    x-5 ≤ guardSquare x i ∧ guardSquare x i ≤ x+5 := by
  unfold guardSquare
  have := i.isLt
  omega

theorem kingGuard_mono (n : Nat) (x : Int) {B C : Finset Int}
    (hBC : B ⊆ C) (h : KingGuard n x B) : KingGuard n x C := by
  induction n generalizing x B C with
  | zero =>
    obtain ⟨i, hi⟩ := h
    exact ⟨i, fun j => Finset.insert_subset_insert _ hBC (hi j)⟩
  | succ n ih =>
    obtain ⟨i, hi⟩ := h
    exact ⟨i, fun j => ih _ (Finset.insert_subset_insert _ hBC) (hi j)⟩

theorem triple_has_guard {x : Int} {B : Finset Int}
    (h : ∀ i : Fin 3, x + kingOffset i ∈ B) (j : Fin 3) :
    KingGuard 0 (x + kingOffset j) B := by
  let a : Fin 11 := ⟨(5 + kingOffset j).toNat, by
    have := kingOffset_bounds j
    omega⟩
  refine ⟨a, ?_⟩
  intro k
  have hj := kingOffset_bounds j
  have hk := kingOffset_bounds k
  by_cases hs : -1 ≤ kingOffset j + kingOffset k ∧ kingOffset j + kingOffset k ≤ 1
  · obtain ⟨i, hi⟩ := kingOffset_exhaustive _ hs
    apply Finset.mem_insert_of_mem
    convert h i using 1 <;> omega
  · apply Finset.mem_insert.mpr
    left
    dsimp [guardSquare, a]
    omega

theorem kingGuard_translate (n : Nat) (x t : Int) {B C : Finset Int}
    (hBC : ∀ b ∈ B, b+t ∈ C) (h : KingGuard n x B) :
    KingGuard n (x+t) C := by
  induction n generalizing x B C with
  | zero =>
    obtain ⟨i, hi⟩ := h
    refine ⟨i, ?_⟩
    intro j
    have hh := hi j
    simp only [Finset.mem_insert] at hh ⊢
    rcases hh with hh | hh
    · left
      dsimp [guardSquare] at *
      omega
    · right
      convert hBC _ hh using 1 <;> omega
  | succ n ih =>
    obtain ⟨i, hi⟩ := h
    refine ⟨i, ?_⟩
    intro j
    have hh := ih (x+kingOffset j) (B := insert (guardSquare x i) B)
      (C := insert (guardSquare (x+t) i) C) (by
        intro b hb
        simp only [Finset.mem_insert] at hb ⊢
        rcases hb with hb | hb
        · left
          dsimp [guardSquare] at *
          omega
        · exact Or.inr (hBC b hb)) (hi j)
    convert hh using 1 <;> omega

theorem kingGuard_step (n : Nat) (x : Int) (B : Finset Int)
    (h : KingGuard n x B) :
    ∃ z, x-5 ≤ z ∧ z ≤ x+5 ∧
      (n = 0 → ∀ j : Fin 3, x + kingOffset j ∈ insert z B) ∧
      ∀ j : Fin 3, KingGuard (n-1) (x+kingOffset j) (insert z B) := by
  cases n with
  | zero =>
    obtain ⟨i, hi⟩ := h
    exact ⟨guardSquare x i, (guardSquare_bounds x i).1,
      (guardSquare_bounds x i).2, fun _ => hi, triple_has_guard hi⟩
  | succ n =>
    obtain ⟨i, hi⟩ := h
    exact ⟨guardSquare x i, (guardSquare_bounds x i).1,
      (guardSquare_bounds x i).2, by omega, hi⟩

theorem kingBoard_mem (p : Point) : p ∈ kingBoard ↔
    -100 ≤ p.1 ∧ p.1 ≤ 100 ∧ -100 ≤ p.2 ∧ p.2 ≤ 100 := by
  unfold kingBoard
  constructor
  · intro h
    obtain ⟨⟨a,b⟩, _, hab⟩ := Finset.mem_image.mp h
    have ha := a.isLt
    have hb := b.isLt
    cases hab
    dsimp
    omega
  · intro h
    apply Finset.mem_image.mpr
    refine ⟨(⟨(p.1+100).toNat, by omega⟩, ⟨(p.2+100).toNat, by omega⟩),
      Finset.mem_univ _, ?_⟩
    apply Prod.ext <;> dsimp <;> omega

theorem king_wall_coordinates (s : Fin 4) (x : Int) :
    kingNormal s (kingWallPoint s x) = 100 ∧
    kingTangent s (kingWallPoint s x) = x := by
  fin_cases s <;> simp [kingNormal, kingTangent, kingWallPoint]

theorem king_wall_inverse (s : Fin 4) (p : Point) (h : kingNormal s p = 100) :
    kingWallPoint s (kingTangent s p) = p := by
  fin_cases s <;> simp [kingNormal, kingTangent, kingWallPoint] at * <;>
    apply Prod.ext <;> dsimp <;> omega

theorem kingLineBurns_mem (s : Fin 4) (B : Finset Point) (x : Int) :
    x ∈ kingLineBurns s B ↔ kingWallPoint s x ∈ B := by
  constructor
  · intro h
    obtain ⟨p,hp,hx⟩ := Finset.mem_image.mp h
    obtain ⟨hp, hn⟩ := Finset.mem_filter.mp hp
    rw [← hx, king_wall_inverse s p hn]
    exact hp
  · intro h
    exact Finset.mem_image.mpr ⟨_, Finset.mem_filter.mpr
      ⟨h, (king_wall_coordinates s x).1⟩, (king_wall_coordinates s x).2⟩

theorem kingLineBurns_mono (s : Fin 4) {B C : Finset Point} (h : B ⊆ C) :
    kingLineBurns s B ⊆ kingLineBurns s C := by
  intro x hx
  exact (kingLineBurns_mem s C x).mpr (h ((kingLineBurns_mem s B x).mp hx))

theorem kingLineBurns_insert (s : Fin 4) (B : Finset Point) (z : Int) :
    insert z (kingLineBurns s B) ⊆ kingLineBurns s (insert (kingWallPoint s z) B) := by
  intro x hx
  rw [kingLineBurns_mem]
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem ((kingLineBurns_mem s B x).mp hx)

theorem kingCorners_length : kingCorners.length = 56 := by decide

theorem kingCorners_cover (s : Fin 4) (x : Int)
    (h : (-100 ≤ x ∧ x ≤ -94) ∨ (94 ≤ x ∧ x ≤ 100)) :
    kingWallPoint s x ∈ kingCorners := by
  apply List.mem_flatMap.mpr
  refine ⟨s, by simp, ?_⟩
  change kingWallPoint s x ∈ (List.range 7).flatMap (fun (k : Nat) =>
    [kingWallPoint s (-100+(k:Int)), kingWallPoint s (100-(k:Int))])
  apply List.mem_flatMap.mpr
  rcases h with h | h
  · refine ⟨(x+100).toNat, List.mem_range.mpr (show (x+100).toNat < 7 by omega), ?_⟩
    have hx : -100+((x+100).toNat:Int) = x := by omega
    simp only [List.mem_cons, List.not_mem_nil, or_false, hx]
    simp
  · refine ⟨(100-x).toNat, List.mem_range.mpr (show (100-x).toNat < 7 by omega), ?_⟩
    have hx : 100-((100-x).toNat:Int) = x := by omega
    simp only [List.mem_cons, List.not_mem_nil, or_false, hx]
    simp

theorem kingGuard_five (x : Int) (B : Finset Int) : KingGuard 4 x B := by
  simpa using kingGuard_translate 4 0 x (B := ∅) (C := B)
    (by simp) kingGuard_five_origin

theorem kingLineReady_far (s : Fin 4) (p : Point) (B : Finset Point)
    (h : kingNormal s p ≤ 95) : KingLineReady s p B :=
  ⟨4, by omega, by omega, kingGuard_five _ _⟩

theorem king_coordinates_jump (s : Fin 4) {p q : Point} (h : Jump 1 p q) :
    -1 ≤ kingNormal s q - kingNormal s p ∧ kingNormal s q - kingNormal s p ≤ 1 ∧
    -1 ≤ kingTangent s q - kingTangent s p ∧ kingTangent s q - kingTangent s p ≤ 1 := by
  fin_cases s <;> simp [kingNormal, kingTangent] <;> unfold Jump at h <;> omega

theorem king_wall_in_board (s : Fin 4) (x : Int) (h : -100 ≤ x ∧ x ≤ 100) :
    kingWallPoint s x ∈ kingBoard := by
  rw [kingBoard_mem]
  fin_cases s <;> simp [kingWallPoint] <;> omega

theorem king_inside_board (p : Point) (h : ∀ s : Fin 4, kingNormal s p < 100) :
    p ∈ kingBoard := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp [kingNormal] at h0 h1 h2 h3
  rw [kingBoard_mem]
  omega

theorem king_two_fronts_corner (p : Point) (s t : Fin 4)
    (hne : t ≠ s) (hs : 95 ≤ kingNormal s p) (ht : 95 ≤ kingNormal t p)
    (hin : ∀ u : Fin 4, kingNormal u p < 100) :
    (-99 ≤ kingTangent s p ∧ kingTangent s p ≤ -95) ∨
    (95 ≤ kingTangent s p ∧ kingTangent s p ≤ 99) := by
  have h0 := hin 0
  have h1 := hin 1
  have h2 := hin 2
  have h3 := hin 3
  fin_cases s <;> fin_cases t <;>
    simp [kingNormal, kingTangent] at * <;> omega

theorem king_unique_front_tangent (p : Point) (s : Fin 4)
    (hu : ∀ t : Fin 4, 95 ≤ kingNormal t p → t = s) :
    -94 ≤ kingTangent s p ∧ kingTangent s p ≤ 94 := by
  have h0 := hu 0
  have h1 := hu 1
  have h2 := hu 2
  have h3 := hu 3
  fin_cases s <;> simp [kingNormal, kingTangent] at * <;> omega

theorem king_corner_triple (p : Point) (s t : Fin 4) (B : Finset Point)
    (hB : ∀ z ∈ kingCorners, z ∈ B)
    (hne : t ≠ s) (hs : 95 ≤ kingNormal s p) (ht : 95 ≤ kingNormal t p)
    (hin : ∀ u : Fin 4, kingNormal u p < 100) :
    ∀ j : Fin 3, kingTangent s p + kingOffset j ∈ kingLineBurns s B := by
  intro j
  rw [kingLineBurns_mem]
  apply hB
  apply kingCorners_cover
  have hh := king_two_fronts_corner p s t hne hs ht hin
  have hj := kingOffset_bounds j
  omega

theorem king_triple_no_cross (s : Fin 4) (p q : Point) (B : Finset Point)
    (hin : kingNormal s p < 100) (hj : Jump 1 p q) (hq : q ∉ B)
    (ht : ∀ j : Fin 3, kingTangent s p + kingOffset j ∈ kingLineBurns s B) :
    kingNormal s q < 100 := by
  have hc := king_coordinates_jump s hj
  by_contra hh
  have he : kingNormal s q = 100 := by omega
  obtain ⟨j,hj⟩ := kingOffset_exhaustive _ hc.2.2
  have hb := (kingLineBurns_mem s B _).mp (ht j)
  have hx : kingTangent s p + kingOffset j = kingTangent s q := by omega
  rw [hx, king_wall_inverse s q he] at hb
  exact hq hb

theorem kingBoxReady_mono (p : Point) {B C : Finset Point} (hBC : B ⊆ C)
    (h : KingBoxReady p B) : KingBoxReady p C := by
  refine ⟨fun z hz => hBC (h.1 z hz), h.2.1, ?_⟩
  intro s
  obtain ⟨n,hn,hd,hg⟩ := h.2.2 s
  exact ⟨n,hn,hd,kingGuard_mono n _ (kingLineBurns_mono s hBC) hg⟩

theorem king_box_step (p : Point) (B : Finset Point) (h : KingBoxReady p B) :
    ∃ z ∈ kingBoard, ∀ q, Jump 1 p q → q ∉ insert z B → KingBoxReady q (insert z B) := by
  classical
  by_cases hu : ∃ s : Fin 4, 95 ≤ kingNormal s p ∧
      ∀ t : Fin 4, 95 ≤ kingNormal t p → t = s
  · obtain ⟨s,hs,hu⟩ := hu
    obtain ⟨n,hn,hd,hg⟩ := h.2.2 s
    obtain ⟨z,hzl,hzr,htr,hnext⟩ := kingGuard_step n _ _ hg
    have htan := king_unique_front_tangent p s hu
    refine ⟨kingWallPoint s z, king_wall_in_board s z (by omega), ?_⟩
    intro q hj hq
    have hc := king_coordinates_jump s hj
    obtain ⟨j,hj'⟩ := kingOffset_exhaustive _ hc.2.2
    have ht : kingTangent s p + kingOffset j = kingTangent s q := by omega
    have hsnew : kingNormal s q < 100 := by
      by_cases hn0 : n = 0
      · apply king_triple_no_cross s p q _ (h.2.1 s) hj hq
        intro k
        exact kingLineBurns_insert s B z (htr hn0 k)
      · omega
    have hin : ∀ t : Fin 4, kingNormal t q < 100 := by
      intro t
      by_cases hts : t = s
      · simpa [hts] using hsnew
      · have hfar : kingNormal t p < 95 := by
          by_contra hh
          exact hts (hu t (by omega))
        have := king_coordinates_jump t hj
        omega
    refine ⟨fun v hv => Finset.mem_insert_of_mem (h.1 v hv), hin, ?_⟩
    intro t
    by_cases hts : t = s
    · subst t
      refine ⟨n-1, by omega, by omega, ?_⟩
      rw [← ht]
      exact kingGuard_mono _ _ (kingLineBurns_insert s B z) (hnext j)
    · apply kingLineReady_far
      have hfar : kingNormal t p < 95 := by
        by_contra hh
        exact hts (hu t (by omega))
      have := king_coordinates_jump t hj
      omega
  · have triple : ∀ s : Fin 4, 95 ≤ kingNormal s p →
        ∀ j : Fin 3, kingTangent s p + kingOffset j ∈ kingLineBurns s B := by
      intro s hs
      have hex : ∃ t : Fin 4, 95 ≤ kingNormal t p ∧ t ≠ s := by
        by_contra hh
        apply hu
        refine ⟨s,hs,?_⟩
        intro t ht
        by_contra hts
        exact hh ⟨t,ht,hts⟩
      obtain ⟨t,ht,hts⟩ := hex
      exact king_corner_triple p s t B h.1 hts hs ht h.2.1
    refine ⟨origin, (kingBoard_mem origin).mpr (by decide), ?_⟩
    intro q hj hq
    have hbq : q ∉ B := fun hh => hq (Finset.mem_insert_of_mem hh)
    have hin : ∀ s : Fin 4, kingNormal s q < 100 := by
      intro s
      by_cases hs : 95 ≤ kingNormal s p
      · exact king_triple_no_cross s p q B (h.2.1 s) hj hbq (triple s hs)
      · have := king_coordinates_jump s hj
        omega
    refine ⟨fun v hv => Finset.mem_insert_of_mem (h.1 v hv), hin, ?_⟩
    intro s
    by_cases hs : 95 ≤ kingNormal s p
    · refine ⟨0, by omega, by have := hin s; omega, ?_⟩
      have hc := king_coordinates_jump s hj
      obtain ⟨j,hj'⟩ := kingOffset_exhaustive _ hc.2.2
      have ht : kingTangent s p + kingOffset j = kingTangent s q := by omega
      rw [← ht]
      exact kingGuard_mono _ _ (kingLineBurns_mono s (Finset.subset_insert _ _))
        (triple_has_guard (triple s hs) j)
    · apply kingLineReady_far
      have := king_coordinates_jump s hj
      omega

end AngelDevil

theorem solution (p : AngelDevil.Point) (B : Finset AngelDevil.Point)
    (h : AngelDevil.KingBoxReady p B) :
    ∃ z ∈ AngelDevil.kingBoard, ∀ q, AngelDevil.Jump 1 p q →
      q ∉ insert z B → AngelDevil.KingBoxReady q (insert z B) :=
  AngelDevil.king_box_step p B h
