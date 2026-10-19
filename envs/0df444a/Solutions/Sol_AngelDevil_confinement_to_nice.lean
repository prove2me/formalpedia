-- Prove2me | solution 1 for AngelDevil.confinement_to_nice
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-18T13:18:23.91702+00:00
-- url     : https://prove2.me/submissions/42cf9ad1-e809-4fe5-8895-07f5d7aa31c4

import Definitions.Def_AngelDevil_NiceReduction
import Theorems.Thm_AngelDevil_reducedJourney_allowed

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

theorem visited_get (A : AngelStrategy) (D : DevilStrategy) (n i : Nat)
    (hi : i ≤ n) :
    (play A D n).visited[i]? = some (current (play A D i)) := by
  induction n with
  | zero =>
      have : i = 0 := by omega
      subst i
      rfl
  | succ n ih =>
      by_cases hin : i ≤ n
      · change ((play A D n).visited ++ [_])[i]? = _
        rw [List.getElem?_append_left (by have := (play_lengths A D n).1; omega)]
        exact ih hin
      · have : i = n+1 := by omega
        subst i
        change ((play A D n).visited ++ [_])[n+1]? = _
        rw [List.getElem?_append_right (by rw [(play_lengths A D n).1]; omega)]
        simp [(play_lengths A D n).1, current_succ]

theorem safe_prefix_journey (p : Nat) (A : AngelStrategy) (D : DevilStrategy) (n : Nat)
    (safe : ∀ m, m < n →
      Jump p (current (play A D m)) (current (play A D (m+1)))) :
    Journey p (play A D n).visited := by
  constructor
  · have h := visited_get A D n 0 (Nat.zero_le n)
    simpa only [List.head?_eq_getElem?, current_zero] using h
  · intro i u v hu hv
    have hiv := (List.getElem?_eq_some_iff.mp hv).1
    have hil : i+1 < (play A D n).visited.length := hiv
    rw [(play_lengths A D n).1] at hil
    have hi : i < n := by omega
    rw [visited_get A D n i (by omega)] at hu
    rw [visited_get A D n (i+1) (by omega)] at hv
    cases hu
    cases hv
    exact safe i hi

theorem survives_journey {p : Nat} {A : AngelStrategy} {D : DevilStrategy}
    (safe : Survives p A D) (n : Nat) : Journey p (play A D n).visited :=
  safe_prefix_journey p A D n (fun m _ => (safe m).1)

theorem nice_does_not_eat_current (p : Nat) (A : AngelStrategy)
    (D : DevilStrategy) (nice : Nice p D) (n : Nat)
    (safe : ∀ m, m < n → Jump p (current (play A D m)) (current (play A D (m+1)))) :
    D (play A D n).visited ≠ some (current (play A D n)) := by
  intro eaten
  have hprotected := nice _ (safe_prefix_journey p A D n safe) _ eaten
  cases n with
  | zero => exact hprotected.1 rfl
  | succ n =>
      have mem : current (play A D n) ∈ (play A D (n+1)).visited.dropLast := by
        simpa [play, step] using List.mem_of_getElem? (visited_get A D n n (by omega))
      exact hprotected.2 _ mem (safe n (by omega))

def stationary : AngelStrategy := fun _ _ => origin

theorem stationary_current (D : DevilStrategy) (n : Nat) :
    current (play stationary D n) = origin := by
  cases n with
  | zero => rfl
  | succ n => simp [current_succ, stationary]

theorem stationary_journey (p : Nat) (D : DevilStrategy) (n : Nat) :
    Journey p (play stationary D n).visited := by
  apply safe_prefix_journey
  intro m hm
  simp only [stationary_current]
  exact jump_self p origin

theorem stationary_not_burned (p : Nat) (D : DevilStrategy) (nice : Nice p D)
    (n : Nat) : some origin ∉ (play stationary D n).burned := by
  induction n with
  | zero => simp [play, initial]
  | succ n ih =>
      have h : D (play stationary D n).visited ≠ some origin := by
        intro e
        exact (nice _ (stationary_journey p D n) origin e).1 rfl
      simpa [play, step] using And.intro ih (Ne.symm h)

/- The source explicitly distinguishes survival from escape against Nice Devils:
staying at the origin survives, but is not the Theorem 4.5 target. -/
theorem stationary_survives_nice (p : Nat) (D : DevilStrategy) (nice : Nice p D) :
    Survives p stationary D := by
  intro n
  simp only [stationary_current]
  exact ⟨jump_self p origin, stationary_not_burned p D nice (n+1)⟩

theorem stationary_does_not_escape (D : DevilStrategy) : ¬ Escapes stationary D := by
  intro h
  obtain ⟨n, hn⟩ := h 0
  apply hn
  simp only [stationary_current, InBox]
  exact jump_self 0 origin

theorem reducedJourney_endpoint (p : Nat) (h : List Point) (hne : h ≠ []) :
    (reducedJourney p h).getLastD origin = h.getLastD origin := by
  rw [reducedJourney]
  simp only [hne, ↓reduceDIte]
  split
  · rename_i he
    simpa using he.symm
  · split <;> simp

theorem take_last (h : List Point) (i : Nat) (hi : i < h.length) :
    (h.take (i+1)).getLastD origin = h[i] := by
  simp [List.getLastD_eq_getLast?, List.getLast?_take,
    List.getElem?_eq_getElem hi]

theorem niceReduction_eq_some_iff (p : Nat) (D : DevilStrategy)
    (h : List Point) (z : Point) :
    niceReduction p D h = some z ↔
      D (reducedJourney p h) = some z ∧ NiceEligible p h z := by
  unfold niceReduction
  cases he : D (reducedJourney p h) with
  | none => simp
  | some w =>
    by_cases hw : NiceEligible p h w
    · simp [hw]
      intro hh
      subst z
      exact hw
    · simp [hw]
      intro hh
      subst z
      exact hw

theorem niceReduction_is_nice (p : Nat) (D : DevilStrategy) :
    Nice p (niceReduction p D) := by
  intro h _ z hz
  exact ((niceReduction_eq_some_iff p D h z).mp hz).2

theorem visited_take (A : AngelStrategy) (D : DevilStrategy) (n k : Nat)
    (hk : k ≤ n) : (play A D n).visited.take (k+1) = (play A D k).visited := by
  induction n with
  | zero =>
      have : k = 0 := by omega
      subst k
      rfl
  | succ n ih =>
      by_cases hkn : k ≤ n
      · change List.take (k+1) ((play A D n).visited ++ [_]) = _
        rw [List.take_append_of_le_length (by rw [(play_lengths A D n).1]; omega)]
        exact ih hkn
      · have : k = n+1 := by omega
        subst k
        rw [← (play_lengths A D (n+1)).1, List.take_length]

theorem past_devil_move_mem (A : AngelStrategy) (D : DevilStrategy) (n i : Nat)
    (hi : i < n) : D (play A D i).visited ∈ (play A D n).burned := by
  induction n with
  | zero => omega
  | succ n ih =>
      change D (play A D i).visited ∈ (play A D n).burned ++ [_]
      by_cases hin : i < n
      · exact List.mem_append_left _ (ih hin)
      · have : i = n := by omega
        subst i
        exact List.mem_append_right _ (by simp)

/- Connect the finite-history formulation to every safe prefix of the original
strategy semantics; no assumption of infinite survival is made. -/
theorem safe_prefix_allowed (p : Nat) (A : AngelStrategy) (D : DevilStrategy)
    (n : Nat) (safe : ∀ m, m < n →
      Jump p (current (play A D m)) (current (play A D (m+1))) ∧
      some (current (play A D (m+1))) ∉ (play A D (m+1)).burned) :
    Allowed p D (play A D n).visited := by
  refine ⟨safe_prefix_journey p A D n (fun m hm => (safe m hm).1), ?_⟩
  intro i j z hij hz he
  have hjn : j ≤ n := by
    have hl := (List.getElem?_eq_some_iff.mp hz).1
    rw [(play_lengths A D n).1] at hl
    omega
  rw [visited_get A D n j hjn] at hz
  cases hz
  rw [visited_take A D n i (by omega)] at he
  have heaten := past_devil_move_mem A D j i hij
  rw [he] at heaten
  have hj : j-1+1 = j := by omega
  have hs := (safe (j-1) (by omega)).2
  rw [hj] at hs
  exact hs heaten


def scriptedAngel (h : List Point) : AngelStrategy := fun visited _ =>
  h[visited.length]?.getD origin

theorem scripted_visited (p : Nat) (h : List Point) (hj : Journey p h)
    (D : DevilStrategy) (n : Nat) (hn : n < h.length) :
    (play (scriptedAngel h) D n).visited = h.take (n+1) := by
  induction n with
  | zero =>
      change [origin] = h.take 1
      simp [List.take_one, hj.1]
  | succ n ih =>
      change (play (scriptedAngel h) D n).visited ++
        [h[(play (scriptedAngel h) D n).visited.length]?.getD origin] = _
      rw [(play_lengths (scriptedAngel h) D n).1, ih (by omega)]
      rw [List.getElem?_eq_getElem hn]
      simp only [Option.getD_some]
      exact (List.take_succ_eq_append_getElem hn).symm

theorem scripted_current (p : Nat) (h : List Point) (hj : Journey p h)
    (D : DevilStrategy) (n : Nat) (hn : n < h.length) :
    current (play (scriptedAngel h) D n) = h[n] := by
  unfold current
  rw [scripted_visited p h hj D n hn, take_last h n hn]

theorem burned_mem_iff (A : AngelStrategy) (D : DevilStrategy)
    (n : Nat) (z : Option Point) :
    z ∈ (play A D n).burned ↔ ∃ i, i < n ∧ D (play A D i).visited = z := by
  induction n with
  | zero => simp [play, initial]
  | succ n ih =>
      change z ∈ (play A D n).burned ++ [D (play A D n).visited] ↔ _
      rw [List.mem_append, List.mem_singleton, ih]
      constructor
      · intro hh
        rcases hh with ⟨i, hi, he⟩ | he
        · exact ⟨i, by omega, he⟩
        · exact ⟨n, by omega, he.symm⟩
      · rintro ⟨i, hi, he⟩
        by_cases hin : i < n
        · exact Or.inl ⟨i, hin, he⟩
        · have : i = n := by omega
          subst i
          exact Or.inr he.symm

theorem allowed_scripted_safe (p : Nat) (D : DevilStrategy) (h : List Point)
    (ha : Allowed p D h) (m : Nat) (hm : m+1 < h.length) :
    Jump p (current (play (scriptedAngel h) D m))
      (current (play (scriptedAngel h) D (m+1))) ∧
    some (current (play (scriptedAngel h) D (m+1))) ∉
      (play (scriptedAngel h) D (m+1)).burned := by
  rw [scripted_current p h ha.1 D m (by omega), scripted_current p h ha.1 D (m+1) hm]
  constructor
  · exact ha.1.2 m _ _ (List.getElem?_eq_getElem (by omega))
      (List.getElem?_eq_getElem hm)
  · intro hz
    obtain ⟨i, hi, he⟩ := (burned_mem_iff (scriptedAngel h) D (m+1) _).mp hz
    rw [scripted_visited p h ha.1 D i (by omega)] at he
    exact ha.2 i (m+1) _ hi (List.getElem?_eq_getElem hm) he

/- Finite-history confinement is equivalent to confinement of all safe plays. -/
theorem confinement_iff_allowed (p N : Nat) (D : DevilStrategy) :
    (∀ A n, (∀ m, m < n →
      Jump p (current (play A D m)) (current (play A D (m+1))) ∧
      some (current (play A D (m+1))) ∉ (play A D (m+1)).burned) →
      InBox N (current (play A D n))) ↔
    (∀ h, Allowed p D h → InBox N (h.getLastD origin)) := by
  constructor
  · intro hc h ha
    have hne : h ≠ [] := by
      intro he
      have hh := ha.1.1
      simp [he] at hh
    have hl := List.length_pos_iff.mpr hne
    have hs := hc (scriptedAngel h) (h.length-1)
      (fun m hm => allowed_scripted_safe p D h ha m (by omega))
    unfold current at hs
    rw [scripted_visited p h ha.1 D (h.length-1) (by omega),
      show h.length-1+1 = h.length by omega, List.take_length] at hs
    exact hs
  · intro hc A n hs
    exact hc _ (safe_prefix_allowed p A D n hs)

/- Theorem 2.4, with the same finite-prefix confinement semantics as the mission.
Positivity is unnecessary for this reduction alone. -/
theorem confinement_to_nice (p N : Nat) (D : DevilStrategy)
    (hc : ∀ A n, (∀ m, m < n →
      Jump p (current (play A D m)) (current (play A D (m+1))) ∧
      some (current (play A D (m+1))) ∉ (play A D (m+1)).burned) →
      InBox N (current (play A D n))) : NiceCanConfine p N := by
  refine ⟨niceReduction p D, niceReduction_is_nice p D, ?_⟩
  apply (confinement_iff_allowed p N (niceReduction p D)).mpr
  intro h ha
  have hne : h ≠ [] := by
    intro he
    have hh := ha.1.1
    simp [he] at hh
  have hh := (confinement_iff_allowed p N D).mp hc _ (reducedJourney_allowed p D h ha)
  rw [reducedJourney_endpoint p h hne] at hh
  exact hh


end AngelDevil

open AngelDevil
theorem solution (p N : Nat) (D : DevilStrategy)
    (hc : ∀ A n, (∀ m, m < n →
      Jump p (current (play A D m)) (current (play A D (m+1))) ∧
      some (current (play A D (m+1))) ∉ (play A D (m+1)).burned) →
      InBox N (current (play A D n))) : NiceCanConfine p N  := by
  exact AngelDevil.confinement_to_nice p N D hc
