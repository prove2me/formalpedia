-- Prove2me | solution 1 for AngelDevil.finite_game_determined
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-18T13:37:32.006659+00:00
-- url     : https://prove2.me/submissions/3d322903-a7e1-4217-862a-3e6127177f79

import Mathlib.Combinatorics.Compactness
import Definitions.Def_AngelDevil_FiniteGame

namespace AngelDevil

theorem jump_self (p : Nat) (v : Point) : Jump p v v := by
  unfold Jump
  omega

theorem jump_mono {p q : Nat} (hpq : p ≤ q) {u v : Point}
    (h : Jump p u v) : Jump q u v := by
  unfold Jump at *
  omega

theorem jump_symm {p : Nat} {u v : Point} (h : Jump p u v) : Jump p v u := by
  unfold Jump at *
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

theorem pass_is_nice (p : Nat) : Nice p (fun _ => none) := by
  intro h hj z hz
  contradiction

/- Proposition 4.3's final numerical contradiction. The geometric estimates
are hypotheses here; establishing them remains open. -/
theorem wall_budget_contradiction (t d a N perimeter : Int)
    (hd : d ≤ t) (ha : 2*t-1 ≤ a)
    (hlower : a+2*N+5 ≤ perimeter)
    (hupper : perimeter ≤ 2*(N+d)+2) : False := by
  omega

theorem nice_wins_excludes_confinement {p N : Nat} (h : NiceAngelWins p) :
    ¬ NiceCanConfine p N := by
  intro hc
  obtain ⟨A, hA⟩ := h
  obtain ⟨D, hn, hD⟩ := hc
  obtain ⟨hs, he⟩ := hA D hn
  obtain ⟨n, hn'⟩ := he N
  exact hn' (hD A n (fun m _ => hs m))

/- A proved logical assembly lemma, NOT a proof of either paper milestone. -/
theorem nice_escape_and_reduction_imply_win {p : Nat}
    (reduction : ¬ AngelWins p → ∃ N, 0 < N ∧ NiceCanConfine p N)
    (escape : NiceAngelWins p) : AngelWins p := by
  apply Classical.byContradiction
  intro h
  obtain ⟨N, _, hN⟩ := reduction h
  exact nice_wins_excludes_confinement escape hN

theorem current_zero (A : AngelStrategy) (D : DevilStrategy) :
    current (play A D 0) = origin := rfl

theorem current_succ (A : AngelStrategy) (D : DevilStrategy) (n : Nat) :
    current (play A D (n+1)) =
      A (play A D n).visited ((play A D n).burned ++ [D (play A D n).visited]) := by
  simp [play, step, current]


theorem safeFor_mono (p : Nat) (A : AngelStrategy) (D : DevilStrategy)
    (n k : Nat) (hk : k ≤ n) (hs : SafeFor p A D n) : SafeFor p A D k :=
  fun m hm => hs m (by omega)

theorem survives_iff_all_safeFor (p : Nat) (A : AngelStrategy) (D : DevilStrategy) :
    Survives p A D ↔ ∀ n, SafeFor p A D n := by
  constructor
  · intro hs n m _
    exact hs m
  · intro hs m
    exact hs (m+1) m (by omega)

theorem safeFor_inBox (p : Nat) (A : AngelStrategy) (D : DevilStrategy)
    (n : Nat) (hs : SafeFor p A D n) : InBox (n*p) (current (play A D n)) := by
  induction n with
  | zero => simpa only [Nat.zero_mul, current_zero, InBox] using jump_self 0 origin
  | succ n ih =>
      have hh := jump_add (ih (safeFor_mono p A D (n+1) n (by omega) hs))
        (hs n (by omega)).1
      simpa only [Nat.succ_mul, InBox] using hh

/- Once a fixed Devil forces failure by a uniform finite deadline, bounded
speed supplies a positive box for every safe prefix (Claim 2.1's final step). -/
theorem bounded_failure_confines (p T : Nat) (D : DevilStrategy)
    (hD : ∀ A, ¬ SafeFor p A D T) :
    ∀ A n, SafeFor p A D n → InBox (T*p+1) (current (play A D n)) := by
  intro A n hs
  have hn : n < T := by
    apply Classical.byContradiction
    intro h
    exact hD A (safeFor_mono p A D n T (by omega) hs)
  have hbound : n*p ≤ T*p+1 := by
    have := Nat.mul_le_mul_right p (Nat.le_of_lt hn)
    omega
  exact jump_mono hbound (safeFor_inBox p A D n hs)

theorem decodeMove_legal (p : Nat) (h : List Point) (d : BoundedMove p) :
    Jump p (h.getLastD origin) (decodeMove p h d) := by
  have hx := d.1.isLt
  have hy := d.2.isLt
  unfold Jump decodeMove
  dsimp only
  omega

theorem decode_encode_legal (p : Nat) (A : AngelStrategy) (h : List Point)
    (b : List (Option Point)) (hj : Jump p (h.getLastD origin) (A h b)) :
    boundedAngel p (encodeAngel p A) h b = A h b := by
  simp only [boundedAngel, encodeAngel, hj, ↓reduceDIte, decodeMove]
  apply Prod.ext <;> dsimp only
  all_goals unfold Jump at hj; omega

/- Finite play depends only on the strategy inputs actually visited. -/
theorem play_eq_of_agreement (A B : AngelStrategy) (D : DevilStrategy) (n : Nat)
    (h : ∀ m, m < n →
      B (play A D m).visited ((play A D m).burned ++ [D (play A D m).visited]) =
      A (play A D m).visited ((play A D m).burned ++ [D (play A D m).visited])) :
    play B D n = play A D n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change step B D (play B D n) = step A D (play A D n)
      rw [ih (fun m hm => h m (by omega))]
      simp only [step, h n (by omega)]

theorem encode_play_eq (p : Nat) (A : AngelStrategy) (D : DevilStrategy) (n : Nat)
    (hs : SafeFor p A D n) :
    play (boundedAngel p (encodeAngel p A)) D n = play A D n := by
  apply play_eq_of_agreement
  intro m hm
  apply decode_encode_legal
  have hj := (hs m hm).1
  rw [current_succ] at hj
  exact hj

theorem encode_safeFor (p : Nat) (A : AngelStrategy) (D : DevilStrategy) (n : Nat)
    (hs : SafeFor p A D n) : SafeFor p (boundedAngel p (encodeAngel p A)) D n := by
  intro m hm
  rw [encode_play_eq p A D m (safeFor_mono p A D n m (by omega) hs),
      encode_play_eq p A D (m+1) (safeFor_mono p A D n (m+1) (by omega) hs)]
  exact hs m hm

theorem finiteAngelWins_bounded (p n : Nat) (h : FiniteAngelWins p n) :
    ∃ f : Observation → BoundedMove p, ∀ D, SafeFor p (boundedAngel p f) D n := by
  obtain ⟨A, hA⟩ := h
  exact ⟨encodeAngel p A, fun D => encode_safeFor p A D n (hA D)⟩


theorem finiteAngel_spec (p T : Nat) (s : State) (d : Option Point)
    (hv : Viable p (T-s.visited.length+1) s) :
    let v := finiteAngel p T s.visited (s.burned ++ [d])
    Jump p (current s) v ∧ some v ∉ s.burned ++ [d] ∧
      Viable p (T-s.visited.length) (advance s d v) := by
  have hex := hv d
  unfold finiteAngel
  simp only [current, advance] at hex ⊢
  simp only [hex, ↓reduceDIte]
  exact Classical.choose_spec hex

theorem viable_has_strategy (p T : Nat) (hv : Viable p T initial) :
    FiniteAngelWins p T := by
  refine ⟨finiteAngel p T, ?_⟩
  intro D
  let A := finiteAngel p T
  have inv : ∀ n, n ≤ T → SafeFor p A D n ∧ Viable p (T-n) (play A D n) := by
    intro n
    induction n with
    | zero =>
        intro _
        exact ⟨fun m hm => by omega, by simpa only [Nat.sub_zero, play] using hv⟩
    | succ n ih =>
        intro hn
        obtain ⟨hs, hvi⟩ := ih (by omega)
        have hlen := (play_lengths A D n).1
        have hr : T-n = T-(play A D n).visited.length+1 := by omega
        rw [hr] at hvi
        have hc := finiteAngel_spec p T (play A D n) (D (play A D n).visited) hvi
        have hstep : Jump p (current (play A D n)) (current (play A D (n+1))) ∧
            some (current (play A D (n+1))) ∉ (play A D (n+1)).burned := by
          rw [current_succ]
          exact ⟨hc.1, hc.2.1⟩
        constructor
        · intro m hm
          by_cases hmn : m < n
          · exact hs m hmn
          · have : m = n := by omega
            subst m
            exact hstep
        · simpa only [hlen, play, step, advance, A] using hc.2.2
  exact (inv T (by omega)).1

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

theorem finite_game_determined (p T : Nat) :
    FiniteAngelWins p T ∨ ∃ D, ∀ A, ¬ SafeFor p A D T := by
  classical
  by_cases hv : Viable p T initial
  · exact Or.inl (viable_has_strategy p T hv)
  · exact Or.inr ⟨finiteDevil p T, not_viable_forces_failure p T hv⟩

/- Exact original platform target: Claim 2.1 plus the determinacy observation. -/

end AngelDevil

open AngelDevil
theorem solution (p T : Nat) :
    FiniteAngelWins p T ∨ ∃ D, ∀ A, ¬ SafeFor p A D T := by
  exact AngelDevil.finite_game_determined p T
