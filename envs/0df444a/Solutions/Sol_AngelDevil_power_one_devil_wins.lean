-- Prove2me | solution 1 for AngelDevil.power_one_devil_wins
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-19T13:22:41.36008+00:00
-- url     : https://prove2.me/submissions/7cc072a7-5bf9-4c69-8a97-d69d1af8b32f

import Definitions.Def_AngelDevil_KingGuard
import Definitions.Def_AngelDevil_FiniteGame
import Mathlib.Tactic.FinCases
import Theorems.Thm_AngelDevil_kingGuard_five_origin
import Theorems.Thm_AngelDevil_king_box_step

set_option maxRecDepth 2000
set_option maxHeartbeats 2000000

namespace AngelDevil

theorem jump_self (p : Nat) (v : Point) : Jump p v v := by
  unfold Jump
  omega

theorem jump_add {p q : Nat} {u v w : Point}
    (h : Jump p u v) (h' : Jump q v w) : Jump (p+q) u w := by
  unfold Jump at *
  omega

theorem play_lengths (A : AngelStrategy) (D : DevilStrategy) (n : Nat) :
    (play A D n).visited.length = n+1 ∧ (play A D n).burned.length = n := by
  induction n with
  | zero => simp [play, initial]
  | succ n ih => simp_all [play, step, List.length_append, Nat.add_assoc]

theorem current_succ (A : AngelStrategy) (D : DevilStrategy) (n : Nat) :
    current (play A D (n+1)) =
      A (play A D n).visited ((play A D n).burned ++ [D (play A D n).visited]) := by
  simp [play, step, current]

theorem safeFor_mono (p : Nat) (A : AngelStrategy) (D : DevilStrategy)
    (n k : Nat) (hk : k ≤ n) (hs : SafeFor p A D n) : SafeFor p A D k :=
  fun m hm => hs m (by omega)

theorem badMove_spec (p n : Nat) (s : State) (hn : ¬ Viable p (n+1) s) :
    ∀ v, Jump p (current s) v → some v ∉ s.burned ++ [badMove p n s] →
      ¬ Viable p n (advance s (badMove p n s) v) := by
  classical
  have hex : ∃ d : Option Point, ∀ v, Jump p (current s) v →
      some v ∉ s.burned ++ [d] → ¬ Viable p n (advance s d v) := by
    by_contra hh
    apply hn
    intro d
    by_contra hd
    exact hh ⟨d, fun v hj hb hv => hd ⟨v, hj, hb, hv⟩⟩
  simp only [badMove, hex, ↓reduceDIte]
  exact Classical.choose_spec hex

theorem simulatedBurns_append (choose : State → Option Point) (h : List Point)
    (hne : h ≠ []) (v : Point) :
    simulatedBurns choose (h ++ [v]) =
      simulatedBurns choose h ++ [choose ⟨h, simulatedBurns choose h⟩] := by
  rw [simulatedBurns]
  simp [hne]

theorem simulatedBurns_play (choose : State → Option Point) (A : AngelStrategy)
    (n : Nat) : simulatedBurns choose (play A (historyDevil choose) n).visited =
      (play A (historyDevil choose) n).burned := by
  induction n with
  | zero => simp [play, initial, simulatedBurns]
  | succ n ih =>
      change simulatedBurns choose ((play A (historyDevil choose) n).visited ++ [_]) = _
      have hne : (play A (historyDevil choose) n).visited ≠ [] := by
        have := (play_lengths A (historyDevil choose) n).1
        intro hh
        simp [hh] at this
      rw [simulatedBurns_append choose _ hne]
      change _ = (play A (historyDevil choose) n).burned ++
        [choose ⟨(play A (historyDevil choose) n).visited,
          simulatedBurns choose (play A (historyDevil choose) n).visited⟩]
      rw [ih]

theorem historyDevil_at_play (choose : State → Option Point) (A : AngelStrategy)
    (n : Nat) : historyDevil choose (play A (historyDevil choose) n).visited =
      choose (play A (historyDevil choose) n) := by
  change choose ⟨(play A (historyDevil choose) n).visited,
    simulatedBurns choose (play A (historyDevil choose) n).visited⟩ = _
  rw [simulatedBurns_play]

theorem not_viable_forces_failure (p T : Nat) (hv : ¬ Viable p T initial) :
    ∀ A, ¬ SafeFor p A (finiteDevil p T) T := by
  intro A hs
  let D := finiteDevil p T
  have inv : ∀ n, n ≤ T → SafeFor p A D n →
      ¬ Viable p (T-n) (play A D n) := by
    intro n
    induction n with
    | zero =>
        intro _ _
        simpa only [Nat.sub_zero, play] using hv
    | succ n ih =>
        intro hn hsafe
        have hprev := ih (by omega) (safeFor_mono p A D (n+1) n (by omega) hsafe)
        have hlen := (play_lengths A D n).1
        have hr : T-n = T-(play A D n).visited.length+1 := by omega
        rw [hr] at hprev
        have hc := badMove_spec p (T-(play A D n).visited.length) (play A D n) hprev
        have hd : D (play A D n).visited =
            badMove p (T-(play A D n).visited.length) (play A D n) :=
          historyDevil_at_play (fun s => badMove p (T-s.visited.length) s) A n
        rw [← hd] at hc
        have hstep := hsafe n (by omega)
        rw [current_succ] at hstep
        have hnxt := hc _ hstep.1 hstep.2
        simpa only [hlen, play, step, advance] using hnxt
  have hh := inv T (by omega) hs
  simp only [Nat.sub_self, Viable, not_true_eq_false] at hh

theorem kingGuard_mono (n : Nat) (x : Int) {B C : Finset Int}
    (hBC : B ⊆ C) (h : KingGuard n x B) : KingGuard n x C := by
  induction n generalizing x B C with
  | zero =>
    obtain ⟨i, hi⟩ := h
    exact ⟨i, fun j => Finset.insert_subset_insert _ hBC (hi j)⟩
  | succ n ih =>
    obtain ⟨i, hi⟩ := h
    exact ⟨i, fun j => ih _ (Finset.insert_subset_insert _ hBC) (hi j)⟩

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

theorem kingCorners_length : kingCorners.length = 56 := by decide

theorem kingGuard_five (x : Int) (B : Finset Int) : KingGuard 4 x B := by
  simpa using kingGuard_translate 4 0 x (B := ∅) (C := B)
    (by simp) kingGuard_five_origin

theorem kingLineReady_far (s : Fin 4) (p : Point) (B : Finset Point)
    (h : kingNormal s p ≤ 95) : KingLineReady s p B :=
  ⟨4, by omega, by omega, kingGuard_five _ _⟩

theorem king_inside_board (p : Point) (h : ∀ s : Fin 4, kingNormal s p < 100) :
    p ∈ kingBoard := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp [kingNormal] at h0 h1 h2 h3
  rw [kingBoard_mem]
  omega

theorem kingBoxReady_mono (p : Point) {B C : Finset Point} (hBC : B ⊆ C)
    (h : KingBoxReady p B) : KingBoxReady p C := by
  refine ⟨fun z hz => hBC (h.1 z hz), h.2.1, ?_⟩
  intro s
  obtain ⟨n,hn,hd,hg⟩ := h.2.2 s
  exact ⟨n,hn,hd,kingGuard_mono n _ (kingLineBurns_mono s hBC) hg⟩

theorem kingBurned_mem (s : State) (p : Point) : p ∈ kingBurned s ↔ some p ∈ s.burned := by
  simp [kingBurned]

theorem kingBurned_advance (s : State) (z q : Point) :
    kingBurned (advance s (some z) q) = insert z (kingBurned s) := by
  ext p
  simp [kingBurned_mem, advance, eq_comm, or_comm]

theorem king_current_advance (s : State) (d : Option Point) (q : Point) :
    current (advance s d q) = q := by simp [current, advance]

theorem king_box_fresh_step (p : Point) (B : Finset Point) (h : KingBoxReady p B)
    (hex : (kingBoard \ B).Nonempty) :
    ∃ z ∈ kingBoard \ B, ∀ q, Jump 1 p q → q ∉ insert z B → KingBoxReady q (insert z B) := by
  obtain ⟨z,hz,hstep⟩ := king_box_step p B h
  by_cases hb : z ∈ B
  · obtain ⟨w,hw⟩ := hex
    refine ⟨w,hw,?_⟩
    intro q hj hq
    have hqB : q ∉ B := fun hh => hq (Finset.mem_insert_of_mem hh)
    have hh := hstep q hj (by simpa [Finset.insert_eq_of_mem hb] using hqB)
    rw [Finset.insert_eq_of_mem hb] at hh
    exact kingBoxReady_mono q (Finset.subset_insert _ _) hh
  · exact ⟨z,Finset.mem_sdiff.mpr ⟨hz,hb⟩,hstep⟩

theorem king_trap_not_viable (n : Nat) (s : State)
    (hr : KingBoxReady (current s) (kingBurned s))
    (hc : (kingBoard \ kingBurned s).card < n) : ¬ Viable 1 n s := by
  induction n generalizing s with
  | zero => omega
  | succ n ih =>
    intro hv
    by_cases he : (kingBoard \ kingBurned s).Nonempty
    · obtain ⟨z,hz,hstep⟩ := king_box_fresh_step _ _ hr he
      obtain ⟨q,hj,hq,hv'⟩ := hv (some z)
      have hqb : q ∉ insert z (kingBurned s) := by
        rw [← kingBurned_advance s z q, kingBurned_mem]
        exact hq
      have hr' := hstep q hj hqb
      apply ih (advance s (some z) q)
      · simpa [king_current_advance, kingBurned_advance] using hr'
      · rw [kingBurned_advance]
        have hid : kingBoard \ insert z (kingBurned s) =
            (kingBoard \ kingBurned s).erase z := by
          ext v
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
          tauto
        rw [hid, Finset.card_erase_of_mem hz]
        have := Finset.card_pos.mpr he
        omega
      · exact hv'
    · obtain ⟨z,_,hstep⟩ := king_box_step _ _ hr
      obtain ⟨q,hj,hq,_⟩ := hv (some z)
      have hqb : q ∉ insert z (kingBurned s) := by
        rw [← kingBurned_advance s z q, kingBurned_mem]
        exact hq
      have hr' := hstep q hj hqb
      exact he ⟨q, Finset.mem_sdiff.mpr ⟨king_inside_board q hr'.2.1,
        fun hh => hqb (Finset.mem_insert_of_mem hh)⟩⟩

theorem viable_burn_prefix (L : List Point) (T : Nat) (s : State)
    (hv : Viable 1 (L.length+T) s) :
    ∃ s', Viable 1 T s' ∧ kingBurned s' = L.toFinset ∪ kingBurned s ∧
      Jump L.length (current s) (current s') := by
  induction L generalizing s with
  | nil =>
    exact ⟨s, by simpa using hv, by simp, jump_self 0 _⟩
  | cons z L ih =>
    have hh : Viable 1 ((L.length+T)+1) s := by simpa [Nat.add_assoc, Nat.add_comm] using hv
    obtain ⟨q,hj,_,hv'⟩ := hh (some z)
    obtain ⟨s',hs',hb,hjump⟩ := ih (advance s (some z) q) hv'
    refine ⟨s',hs',?_,?_⟩
    · rw [hb, kingBurned_advance]
      ext v
      simp only [List.toFinset_cons, Finset.mem_union, Finset.mem_insert]
      tauto
    · rw [king_current_advance] at hjump
      simpa [Nat.add_comm] using jump_add hj hjump

theorem power_one_finite_obstruction :
    ¬ Viable 1 (56 + (kingBoard.card+1)) initial := by
  intro hv
  have hv' : Viable 1 (kingCorners.length+(kingBoard.card+1)) initial := by
    simpa [kingCorners_length] using hv
  obtain ⟨s,hs,hb,hj⟩ := viable_burn_prefix kingCorners (kingBoard.card+1) initial hv'
  have hcorners : ∀ z ∈ kingCorners, z ∈ kingBurned s := by
    intro z hz
    rw [hb]
    exact Finset.mem_union_left _ (List.mem_toFinset.mpr hz)
  have hbound : -56 ≤ (current s).1 ∧ (current s).1 ≤ 56 ∧
      -56 ≤ (current s).2 ∧ (current s).2 ≤ 56 := by
    simpa [kingCorners_length, Jump, current, initial, origin] using hj
  have hnorm : ∀ t : Fin 4, kingNormal t (current s) ≤ 56 := by
    intro t
    fin_cases t <;> simp [kingNormal] <;> omega
  have hr : KingBoxReady (current s) (kingBurned s) :=
    ⟨hcorners, fun t => by have := hnorm t; omega,
      fun t => kingLineReady_far t _ _ (by have := hnorm t; omega)⟩
  apply king_trap_not_viable (kingBoard.card+1) s hr _ hs
  have := Finset.card_le_card (Finset.sdiff_subset (s := kingBoard) (t := kingBurned s))
  omega

theorem power_one_bounded_capture : ∃ D : DevilStrategy,
    ∀ A, ¬ SafeFor 1 A D (56 + (kingBoard.card+1)) :=
  ⟨finiteDevil 1 (56 + (kingBoard.card+1)),
    not_viable_forces_failure 1 _ power_one_finite_obstruction⟩

theorem power_one_devil_wins : ∃ D : DevilStrategy, ∀ A, ¬ Survives 1 A D := by
  obtain ⟨D,hD⟩ := power_one_bounded_capture
  exact ⟨D, fun A hA => hD A (fun n _ => hA n)⟩

theorem power_one_not_wins : ¬ AngelWins 1 := by
  obtain ⟨D,hD⟩ := power_one_devil_wins
  rintro ⟨A,hA⟩
  exact hD A (hA D)

end AngelDevil

theorem solution : ∃ D : AngelDevil.DevilStrategy, ∀ A, ¬ AngelDevil.Survives 1 A D :=
  AngelDevil.power_one_devil_wins
