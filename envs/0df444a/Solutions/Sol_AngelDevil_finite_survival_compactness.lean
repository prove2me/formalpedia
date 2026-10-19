-- Prove2me | solution 1 for AngelDevil.finite_survival_compactness
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-18T13:37:30.273734+00:00
-- url     : https://prove2.me/submissions/eea2d952-0175-46ea-9bfd-7196e1130416

import Mathlib.Combinatorics.Compactness
import Definitions.Def_AngelDevil_FiniteHorizon

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


/- The limit-strategy step in the proof of Claim 2.1. Rado selection is applied
to finite observations, not to an unjustified finite set of Devil choices. -/
theorem finite_survival_compactness (p : Nat)
    (hf : ∀ n, FiniteAngelWins p n) : AngelWins p := by
  classical
  let f : Nat → Observation → BoundedMove p :=
    fun n => Classical.choose (finiteAngelWins_bounded p n (hf n))
  have hsafe : ∀ n D, SafeFor p (boundedAngel p (f n)) D n := by
    intro n
    exact Classical.choose_spec (finiteAngelWins_bounded p n (hf n))
  let horizon : Finset Observation → Nat := fun s => s.sup (fun o => o.1.length)
  let g : Finset Observation → Observation → BoundedMove p := fun s => f (horizon s)
  obtain ⟨χ, hχ⟩ := Finset.rado_selection g
  refine ⟨boundedAngel p χ, ?_⟩
  intro D n
  let A := boundedAngel p χ
  let obs : Nat → Observation := fun m =>
    ((play A D m).visited, (play A D m).burned ++ [D (play A D m).visited])
  let s : Finset Observation := (Finset.range (n+1)).image obs
  obtain ⟨t, hst, ht⟩ := hχ s
  have hmem : ∀ m, m ≤ n → obs m ∈ s := by
    intro m hm
    exact Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr (by omega), rfl⟩
  have hn : n < horizon t := by
    have hbound : (obs n).1.length ≤ horizon t :=
      Finset.le_sup (f := fun o : Observation => o.1.length) (hst (hmem n (by omega)))
    have hlen : (obs n).1.length = n+1 := (play_lengths A D n).1
    omega
  have hagree : ∀ m, m ≤ n →
      boundedAngel p (g t) (play A D m).visited
        ((play A D m).burned ++ [D (play A D m).visited]) =
      A (play A D m).visited
        ((play A D m).burned ++ [D (play A D m).visited]) := by
    intro m hm
    have he := ht (obs m) (hmem m hm)
    change decodeMove p _ (g t (obs m)) = decodeMove p _ (χ (obs m))
    rw [he]
  have heq : ∀ k, k ≤ n+1 → play (boundedAngel p (g t)) D k = play A D k := by
    intro k hk
    exact play_eq_of_agreement A (boundedAngel p (g t)) D k
      (fun m hm => hagree m (by omega))
  have hs := hsafe (horizon t) D n hn
  change Jump p (current (play (boundedAngel p (g t)) D n))
      (current (play (boundedAngel p (g t)) D (n+1))) ∧
    some (current (play (boundedAngel p (g t)) D (n+1))) ∉
      (play (boundedAngel p (g t)) D (n+1)).burned at hs
  rw [heq n (by omega), heq (n+1) (by omega)] at hs
  exact hs

theorem no_win_has_finite_obstruction (p : Nat) (h : ¬ AngelWins p) :
    ∃ n, ¬ FiniteAngelWins p n := by
  classical
  by_contra hn
  apply h
  apply finite_survival_compactness p
  simpa using hn


end AngelDevil

open AngelDevil
theorem solution (p : Nat)
    (hf : ∀ n, FiniteAngelWins p n) : AngelWins p := by
  exact AngelDevil.finite_survival_compactness p hf
