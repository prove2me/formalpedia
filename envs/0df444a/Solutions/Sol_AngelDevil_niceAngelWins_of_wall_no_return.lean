-- Prove2me | solution 1 for AngelDevil.niceAngelWins_of_wall_no_return
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-18T14:14:45.027109+00:00
-- url     : https://prove2.me/submissions/05d1a48d-8270-4a2a-ad1a-2c0319e2d981

import Definitions.Def_AngelDevil_WallWalk

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
        rw [List.getElem?_append_right (by rw [(play_lengths A D n).1])]
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

theorem sideNeighbor_opposite (v : Point) (d : SquareSide) :
    sideNeighbor (sideNeighbor v d) (oppositeSide d) = v := by
  rcases v with ⟨x,y⟩
  rcases d with ⟨a,b⟩
  cases a <;> cases b <;> simp [sideNeighbor, oppositeSide]


theorem tangentSide_twice (d : SquareSide) :
    tangentSide (tangentSide d) = oppositeSide d := by
  rcases d with ⟨a,b⟩
  cases a <;> cases b <;> rfl

theorem tangentSide_opposite (d : SquareSide) :
    tangentSide (oppositeSide d) = oppositeSide (tangentSide d) := by
  rcases d with ⟨a,b⟩
  cases a <;> cases b <;> rfl

theorem oppositeSide_twice (d : SquareSide) : oppositeSide (oppositeSide d) = d := by
  rcases d with ⟨a,b⟩
  cases b <;> rfl

theorem sideNeighbor_commute (v : Point) (d e : SquareSide) :
    sideNeighbor (sideNeighbor v d) e = sideNeighbor (sideNeighbor v e) d := by
  rcases v with ⟨x,y⟩
  rcases d with ⟨a,b⟩
  rcases e with ⟨c,f⟩
  cases a <;> cases b <;> cases c <;> cases f <;>
    simp [sideNeighbor]

theorem nextWall_boundary {B : Set Point} {w : Wall} (h : IsBoundaryWall B w) :
    IsBoundaryWall B (nextWall B w) := by
  classical
  unfold nextWall
  dsimp only
  split
  · exact ⟨h.1, ‹_ ∉ B›⟩
  · split
    · exact ⟨by simpa using ‹¬ _ ∉ B›, ‹_ ∉ B›⟩
    · constructor
      · simpa using ‹¬ _ ∉ B›
      · unfold wallOutside
        dsimp only
        rw [sideNeighbor_commute (sideNeighbor w.1 _) w.2 _, sideNeighbor_opposite]
        exact h.2

theorem nextWall_jump {B : Set Point} (w : Wall) :
    Jump 1 (wallOutside w) (wallOutside (nextWall B w)) := by
  classical
  unfold nextWall
  dsimp only
  split
  · rcases w with ⟨⟨x,y⟩,a,b⟩
    cases a <;> cases b <;> simp [wallOutside, sideNeighbor, tangentSide, Jump]
  · split
    · rcases w with ⟨⟨x,y⟩,a,b⟩
      cases a <;> cases b <;> simp [wallOutside, sideNeighbor, tangentSide, Jump]
    · rcases w with ⟨⟨x,y⟩,a,b⟩
      cases a <;> cases b <;> simp [wallOutside, sideNeighbor, tangentSide, oppositeSide, Jump]

theorem previousWall_next_of_extension {B C : Set Point} (hBC : B ⊆ C)
    {w : Wall} (hw : IsBoundaryWall B w) (hout : wallOutside w ∉ C) :
    previousWall C (nextWall B w) = w := by
  classical
  rcases w with ⟨u,d⟩
  have hu : u ∈ C := hBC hw.1
  change sideNeighbor u d ∉ C at hout
  unfold nextWall
  dsimp only
  split
  · simp [previousWall, tangentSide_twice, oppositeSide_twice, hout]
  · rename_i ha
    have haC : sideNeighbor u (tangentSide d) ∈ C := hBC (by simpa using ha)
    split
    · simp [previousWall, sideNeighbor_opposite, hu, hout]
    · simp [previousWall, tangentSide_opposite, tangentSide_twice,
        oppositeSide_twice, sideNeighbor_opposite, haC, hu]

theorem nextWall_injective {B : Set Point} {v w : Wall}
    (hv : IsBoundaryWall B v) (hw : IsBoundaryWall B w)
    (heq : nextWall B v = nextWall B w) : v = w := by
  have h := congrArg (previousWall B) heq
  rw [previousWall_next_of_extension (fun _ h => h) hv hv.2,
    previousWall_next_of_extension (fun _ h => h) hw hw.2] at h
  exact h

/-- The old side-neighbor supplies the middle square in a concave turn. -/
theorem nextWall_support_path {B : Set Point} {w : Wall} (hw : IsBoundaryWall B w) :
    Relation.ReflTransGen (fun u v => u ∈ B ∧ v ∈ B ∧ SquareAdjacent u v)
      w.1 (nextWall B w).1 := by
  classical
  unfold nextWall
  dsimp only
  split
  · exact Relation.ReflTransGen.refl
  · rename_i ha
    have haB : sideNeighbor w.1 (tangentSide w.2) ∈ B := by simpa using ha
    have first : Relation.ReflTransGen
        (fun u v => u ∈ B ∧ v ∈ B ∧ SquareAdjacent u v)
        w.1 (sideNeighbor w.1 (tangentSide w.2)) :=
      Relation.ReflTransGen.single ⟨hw.1, haB, tangentSide w.2, rfl⟩
    split
    · exact first
    · rename_i hb
      exact first.tail ⟨haB, by simpa using hb, w.2, rfl⟩

/-- A first repeated wall is the initial wall, even while the obstacle set grows.
The preservation of earlier empty squares is an explicit hypothesis here. -/
theorem first_wall_repeat_is_initial (B : Nat → Set Point) (w : Nat → Wall)
    (hmono : Monotone B) (hwall : ∀ n, IsBoundaryWall (B n) (w n))
    (hstep : ∀ n, w (n+1) = nextWall (B n) (w n))
    (hprotect : ∀ i j, i ≤ j → wallOutside (w i) ∉ B j)
    {i j : Nat} (hij : i < j) (heq : w i = w j)
    (hinj : ∀ a b, a < j → b < j → w a = w b → a = b) : i = 0 := by
  cases i with
  | zero => rfl
  | succ k =>
    have hj : j = (j-1)+1 := by omega
    have hk : k ≤ j-1 := by omega
    have hjstep : w j = nextWall (B (j-1)) (w (j-1)) := by
      calc
        w j = w ((j-1)+1) := congrArg w hj
        _ = _ := hstep (j-1)
    have hprev := congrArg (previousWall (B (j-1))) heq
    rw [hstep k, hjstep] at hprev
    rw [previousWall_next_of_extension (hmono hk) (hwall k) (hprotect k (j-1) hk),
      previousWall_next_of_extension (fun _ h => h) (hwall (j-1))
        (hprotect (j-1) (j-1) (Nat.le_refl _))] at hprev
    have he := hinj k (j-1) (by omega) (by omega) hprev
    omega

theorem two_wall_steps_legal {B : Set Point} {w : Wall} (hw : IsBoundaryWall B w) :
    IsBoundaryWall B (nextWall B (nextWall B w)) ∧
      Jump 2 (wallOutside w) (wallOutside (nextWall B (nextWall B w))) := by
  exact ⟨nextWall_boundary (nextWall_boundary hw),
    jump_add (nextWall_jump w) (nextWall_jump (nextWall B w))⟩

theorem wall_determined_by_outside_normal {v w : Wall}
    (hp : wallOutside v = wallOutside w) (hd : v.2 = w.2) : v = w := by
  apply Prod.ext _ hd
  calc
    v.1 = sideNeighbor (wallOutside v) (oppositeSide v.2) :=
      (sideNeighbor_opposite v.1 v.2).symm
    _ = sideNeighbor (wallOutside w) (oppositeSide w.2) := by rw [hp, hd]
    _ = w.1 := sideNeighbor_opposite w.1 w.2


theorem wallHistory_nil : wallHistory [] = initialWall := by
  rw [wallHistory]
  simp

theorem wallHistory_append (b : List (Option Point)) (d : Option Point) :
    wallHistory (b ++ [d]) =
      nextWall (wallObstacles (b ++ [d]))
        (nextWall (wallObstacles (b ++ [d])) (wallHistory b)) := by
  rw [wallHistory]
  simp

theorem wall_current (D : DevilStrategy) (n : Nat) :
    current (play wallAngel D n) = wallOutside (wallHistory (play wallAngel D n).burned) := by
  cases n with
  | zero => simp [play, initial, current, wallHistory_nil, initialWall, wallOutside, sideNeighbor, origin]
  | succ n => rw [current_succ]; rfl

theorem wallObstacles_mono {b c : List (Option Point)} (h : ∀ x ∈ b, x ∈ c) :
    wallObstacles b ⊆ wallObstacles c := by
  intro v hv
  rcases hv with hv | hv
  · exact Or.inl hv
  · exact Or.inr (h _ hv)

theorem wall_play_invariant (D : DevilStrategy) (hnice : Nice 2 D) (n : Nat) :
    IsBoundaryWall (wallObstacles (play wallAngel D n).burned)
      (wallHistory (play wallAngel D n).burned) ∧
    ∀ m, m < n → Jump 2 (current (play wallAngel D m))
      (current (play wallAngel D (m+1))) := by
  induction n with
  | zero =>
    constructor
    · simp [play, initial, wallHistory_nil, IsBoundaryWall, initialWall,
        wallOutside, sideNeighbor, wallObstacles]
    · intro m hm
      omega
  | succ n ih =>
    let b := (play wallAngel D n).burned
    let d := D (play wallAngel D n).visited
    have hnot : d ≠ some (wallOutside (wallHistory b)) := by
      simpa only [wall_current] using nice_does_not_eat_current 2 wallAngel D hnice n ih.2
    have hext : wallObstacles b ⊆ wallObstacles (b ++ [d]) :=
      wallObstacles_mono (fun x hx => List.mem_append_left _ hx)
    have hbefore : IsBoundaryWall (wallObstacles (b ++ [d])) (wallHistory b) := by
      refine ⟨hext ih.1.1, ?_⟩
      intro heaten
      rcases heaten with hleft | hburn
      · exact ih.1.2 (Or.inl hleft)
      · rcases List.mem_append.mp hburn with hprior | hlast
        · exact ih.1.2 (Or.inr hprior)
        · exact hnot (List.mem_singleton.mp hlast).symm
    have htwo := two_wall_steps_legal hbefore
    have hboundary : IsBoundaryWall (wallObstacles (play wallAngel D (n+1)).burned)
        (wallHistory (play wallAngel D (n+1)).burned) := by
      simpa only [play, step, wallHistory_append] using htwo.1
    have hjump : Jump 2 (current (play wallAngel D n))
        (current (play wallAngel D (n+1))) := by
      rw [wall_current, wall_current]
      change Jump 2 (wallOutside (wallHistory b)) (wallOutside (wallHistory (b ++ [d])))
      rw [wallHistory_append]
      exact htwo.2
    refine ⟨hboundary, ?_⟩
    intro m hm
    by_cases hmn : m = n
    · simpa only [hmn] using hjump
    · exact ih.2 m (by omega)

theorem wallAngel_survives_nice (D : DevilStrategy) (hnice : Nice 2 D) :
    Survives 2 wallAngel D := by
  intro n
  have h := wall_play_invariant D hnice (n+1)
  refine ⟨h.2 n (by omega), ?_⟩
  rw [wall_current]
  exact fun hb => h.1.2 (Or.inr hb)

theorem play_burned_mono (A : AngelStrategy) (D : DevilStrategy) {n m : Nat}
    (hnm : n ≤ m) : ∀ x ∈ (play A D n).burned, x ∈ (play A D m).burned := by
  induction m, hnm using Nat.le_induction with
  | base => exact fun _ h => h
  | succ m _ ih =>
    intro x hx
    exact List.mem_append_left _ (ih x hx)

theorem nice_neighborhood_persistent {p : Nat} {A : AngelStrategy} {D : DevilStrategy}
    (hnice : Nice p D) (hsafe : Survives p A D) (n : Nat) (z : Point)
    (hjump : Jump p (current (play A D n)) z)
    (hclear : some z ∉ (play A D (n+1)).burned) :
    ∀ m, n+1 ≤ m → some z ∉ (play A D m).burned := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact hclear
  | succ m hnm ih =>
    have hne : D (play A D m).visited ≠ some z := by
      intro he
      have hp := (hnice _ (survives_journey hsafe m) z he).2
      have hmem : current (play A D n) ∈ (play A D m).visited.dropLast := by
        cases m with
        | zero => omega
        | succ k =>
          simpa only [play, step, List.dropLast_concat] using
            List.mem_of_getElem? (visited_get A D k n (by omega))
      exact hp _ hmem hjump
    intro he
    change some z ∈ (play A D m).burned ++ [D (play A D m).visited] at he
    rcases List.mem_append.mp he with hold | hlast
    · exact ih hold
    · exact hne (List.mem_singleton.mp hlast).symm

theorem wall_before_turn (D : DevilStrategy) (hnice : Nice 2 D) (n : Nat) :
    IsBoundaryWall (wallObstacles (play wallAngel D (n+1)).burned)
      (wallHistory (play wallAngel D n).burned) := by
  have hi := wall_play_invariant D hnice n
  have hne := nice_does_not_eat_current 2 wallAngel D hnice n hi.2
  rw [wall_current] at hne
  constructor
  · exact wallObstacles_mono (play_burned_mono wallAngel D (Nat.le_succ n)) hi.1.1
  · intro he
    rcases he with hleft | hburn
    · exact hi.1.2 (Or.inl hleft)
    · change some _ ∈ (play wallAngel D n).burned ++ [_] at hburn
      rcases List.mem_append.mp hburn with hold | hlast
      · exact hi.1.2 (Or.inr hold)
      · exact hne (List.mem_singleton.mp hlast).symm

theorem traceObstacles_even (D : DevilStrategy) (n : Nat) :
    traceObstacles D (2*n) = wallObstacles (play wallAngel D (n+1)).burned := by
  unfold traceObstacles
  congr 3; omega

theorem traceObstacles_odd (D : DevilStrategy) (n : Nat) :
    traceObstacles D (2*n+1) = wallObstacles (play wallAngel D (n+1)).burned := by
  unfold traceObstacles
  congr 3; omega

theorem wallTrace_even (D : DevilStrategy) (n : Nat) :
    wallTrace D (2*n) = wallHistory (play wallAngel D n).burned := by
  induction n with
  | zero => simp [wallTrace, play, initial, wallHistory_nil]
  | succ n ih =>
    rw [show 2*(n+1) = (2*n+1)+1 by omega, wallTrace, wallTrace,
      traceObstacles_odd, traceObstacles_even, ih]
    change _ = wallHistory ((play wallAngel D n).burned ++ [_])
    rw [wallHistory_append]
    rfl

theorem wallTrace_odd (D : DevilStrategy) (n : Nat) :
    wallTrace D (2*n+1) = nextWall (wallObstacles (play wallAngel D (n+1)).burned)
      (wallHistory (play wallAngel D n).burned) := by
  rw [wallTrace, traceObstacles_even, wallTrace_even]

theorem wallTrace_boundary (D : DevilStrategy) (hnice : Nice 2 D) (i : Nat) :
    IsBoundaryWall (traceObstacles D i) (wallTrace D i) := by
  have hcases : ∃ n, i = 2*n ∨ i = 2*n+1 := ⟨i/2, by omega⟩
  obtain ⟨n, h | h⟩ := hcases
  · subst i
    rw [traceObstacles_even, wallTrace_even]
    exact wall_before_turn D hnice n
  · subst i
    rw [traceObstacles_odd, wallTrace_odd]
    exact nextWall_boundary (wall_before_turn D hnice n)

theorem wallTrace_near_round (D : DevilStrategy) (i : Nat) :
    Jump 2 (current (play wallAngel D (i/2))) (wallOutside (wallTrace D i)) := by
  have hcases : ∃ n, i = 2*n ∨ i = 2*n+1 := ⟨i/2, by omega⟩
  obtain ⟨n, h | h⟩ := hcases
  · subst i
    rw [show 2*n/2 = n by omega, wallTrace_even, wall_current]
    exact jump_self 2 _
  · subst i
    rw [show (2*n+1)/2 = n by omega, wallTrace_odd, wall_current]
    exact jump_mono (by omega) (nextWall_jump _)

theorem traceObstacles_monotone (D : DevilStrategy) : Monotone (traceObstacles D) := by
  intro i j hij
  exact wallObstacles_mono (play_burned_mono wallAngel D (by omega))

theorem wallTrace_protected (D : DevilStrategy) (hnice : Nice 2 D)
    (i j : Nat) (hij : i ≤ j) : wallOutside (wallTrace D i) ∉ traceObstacles D j := by
  have hc := (wallTrace_boundary D hnice i).2
  have hp := nice_neighborhood_persistent hnice (wallAngel_survives_nice D hnice)
    (i/2) (wallOutside (wallTrace D i)) (wallTrace_near_round D i)
    (fun hb => hc (Or.inr hb)) (j/2+1) (by omega)
  intro he
  rcases he with hleft | hburn
  · exact hc (Or.inl hleft)
  · exact hp hburn

theorem wallTrace_first_repeat (D : DevilStrategy) (hnice : Nice 2 D)
    {i j : Nat} (hij : i < j) (heq : wallTrace D i = wallTrace D j)
    (hinj : ∀ a b, a < j → b < j → wallTrace D a = wallTrace D b → a = b) :
    i = 0 :=
  first_wall_repeat_is_initial (traceObstacles D) (wallTrace D)
    (traceObstacles_monotone D) (wallTrace_boundary D hnice) (fun _ => rfl)
    (wallTrace_protected D hnice) hij heq hinj

theorem wallTrace_injective_of_no_return (D : DevilStrategy) (hnice : Nice 2 D)
    (hreturn : ∀ n, 0 < n → wallTrace D n ≠ initialWall) :
    Function.Injective (wallTrace D) := by
  have distinct : ∀ j i, i < j → wallTrace D i ≠ wallTrace D j := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro i hij heq
      have hfirst := wallTrace_first_repeat D hnice hij heq (by
        intro a b ha hb hab
        rcases lt_trichotomy a b with hlt | he | hgt
        · exact False.elim (ih b hb a hlt hab)
        · exact he
        · exact False.elim (ih a ha b hgt hab.symm))
      subst i
      exact hreturn j (by omega) heq.symm
  intro i j heq
  rcases lt_trichotomy i j with hlt | he | hgt
  · exact False.elim (distinct j i hlt heq)
  · exact he
  · exact False.elim (distinct i j hgt heq.symm)

def boxCode (N : Nat) (v : Point) (h : InBox N v) : Fin (2*N+1) × Fin (2*N+1) :=
  (⟨(v.1 + N).toNat, by unfold InBox Jump origin at h; dsimp at h; omega⟩,
   ⟨(v.2 + N).toNat, by unfold InBox Jump origin at h; dsimp at h; omega⟩)

theorem boxCode_injective {N : Nat} {u v : Point} (hu : InBox N u) (hv : InBox N v)
    (heq : boxCode N u hu = boxCode N v hv) : u = v := by
  have hx := congrArg (fun c => c.1.val) heq
  have hy := congrArg (fun c => c.2.val) heq
  unfold boxCode at hx hy
  dsimp only at hx hy
  unfold InBox Jump origin at hu hv
  apply Prod.ext <;> omega

theorem wallAngel_escapes_of_no_return (D : DevilStrategy) (hnice : Nice 2 D)
    (hreturn : ∀ n, 0 < n → wallTrace D n ≠ initialWall) : Escapes wallAngel D := by
  classical
  intro N
  by_contra hbound
  have hb : ∀ n, InBox N (current (play wallAngel D n)) := by simpa using hbound
  have ht : ∀ i, InBox (N+2) (wallOutside (wallTrace D i)) := by
    intro i
    exact jump_add (hb (i/2)) (wallTrace_near_round D i)
  let code (i : Nat) : (Fin (2*(N+2)+1) × Fin (2*(N+2)+1)) × SquareSide :=
    (boxCode (N+2) (wallOutside (wallTrace D i)) (ht i), (wallTrace D i).2)
  have hc : Function.Injective code := by
    intro i j he
    apply wallTrace_injective_of_no_return D hnice hreturn
    apply wall_determined_by_outside_normal
    · exact boxCode_injective (ht i) (ht j) (congrArg Prod.fst he)
    · exact (congrArg Prod.snd he : (code i).2 = (code j).2)
  exact Finite.false (Finite.of_injective code hc)

/-- The remaining geometric no-return obligation suffices for the original
Nice-Angel target with its single strategy and universal Devil quantifier. -/
theorem niceAngelWins_of_wall_no_return
    (hreturn : ∀ D, Nice 2 D → ∀ n, 0 < n → wallTrace D n ≠ initialWall) :
    NiceAngelWins 2 := by
  refine ⟨wallAngel, ?_⟩
  intro D hnice
  exact ⟨wallAngel_survives_nice D hnice,
    wallAngel_escapes_of_no_return D hnice (hreturn D hnice)⟩


end AngelDevil

theorem solution
    (hreturn : ∀ D, AngelDevil.Nice 2 D → ∀ n, 0 < n →
      AngelDevil.wallTrace D n ≠ AngelDevil.initialWall) :
    AngelDevil.NiceAngelWins 2 :=
  AngelDevil.niceAngelWins_of_wall_no_return hreturn
