-- Prove2me | solution 1 for AngelDevil.wallTrace_never_returns
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-18T14:37:27.949487+00:00
-- url     : https://prove2.me/submissions/52287fc3-ae4a-4382-a8cb-380bb94d7fd3

import Definitions.Def_AngelDevil_WallWalk
import Theorems.Thm_AngelDevil_connectedSquares_perimeter

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


/-- Initial vertex of the unit segment oriented with its occupied square on the left. -/
def wallStart (w : Wall) : Point :=
  let x := w.1.1
  let y := w.1.2
  if w.2.1 then
    if w.2.2 then (x,y) else (x+1,y+1)
  else if w.2.2 then (x,y+1) else (x+1,y)

def wallEnd (w : Wall) : Point := sideNeighbor (wallStart w) (tangentSide w.2)

theorem wallStart_initial : wallStart initialWall = origin := rfl

theorem nextWall_start (B : Set Point) (w : Wall) :
    wallStart (nextWall B w) = wallEnd w := by
  classical
  unfold nextWall
  dsimp only
  split
  · rcases w with ⟨⟨x,y⟩,a,b⟩
    cases a <;> cases b <;>
      simp [wallStart, wallEnd, tangentSide, sideNeighbor]
  · split
    · rcases w with ⟨⟨x,y⟩,a,b⟩
      cases a <;> cases b <;>
        simp [wallStart, wallEnd, tangentSide, sideNeighbor]
    · rcases w with ⟨⟨x,y⟩,a,b⟩
      cases a <;> cases b <;>
        simp [wallStart, wallEnd, tangentSide, sideNeighbor, oppositeSide]

theorem wallTrace_end_start (D : DevilStrategy) (i : Nat) :
    wallEnd (wallTrace D i) = wallStart (wallTrace D (i+1)) := by
  rw [wallTrace, nextWall_start]

/-- Freezing later obstacles preserves a past transition when both outside
squares remain empty. -/
theorem nextWall_stable {B C : Set Point} (hBC : B ⊆ C) (w : Wall)
    (hnext : wallOutside (nextWall B w) ∉ C) : nextWall C w = nextWall B w := by
  classical
  unfold nextWall at *
  dsimp only at *
  split at hnext
  · rename_i ha
    change sideNeighbor w.1 (tangentSide w.2) ∉ C at hnext
    simp only [if_pos ha, if_pos hnext]
  · rename_i ha
    have haC : sideNeighbor w.1 (tangentSide w.2) ∈ C := hBC (by simpa using ha)
    split at hnext
    · rename_i hb
      change sideNeighbor (sideNeighbor w.1 (tangentSide w.2)) w.2 ∉ C at hnext
      simp only [if_neg ha, if_neg (not_not.mpr haC), if_pos hb, if_pos hnext]
    · rename_i hb
      have hbC : sideNeighbor (sideNeighbor w.1 (tangentSide w.2)) w.2 ∈ C :=
        hBC (by simpa using hb)
      simp only [if_neg ha, if_neg hb, if_neg (not_not.mpr haC), if_neg (not_not.mpr hbC)]

theorem wallTrace_frozen_step (D : DevilStrategy) (hnice : Nice 2 D)
    (i j : Nat) (hij : i < j) :
    nextWall (traceObstacles D j) (wallTrace D i) = wallTrace D (i+1) := by
  rw [wallTrace]
  apply nextWall_stable (traceObstacles_monotone D (Nat.le_of_lt hij))
  change wallOutside (wallTrace D (i+1)) ∉ traceObstacles D j
  exact wallTrace_protected D hnice (i+1) j (by omega)

theorem boundary_halfplane_support {B : Set Point}
    (hleft : ∀ v : Point, v.1 < 0 → v ∈ B) {w : Wall} (hw : IsBoundaryWall B w) :
    -1 ≤ w.1.1 ∧ 0 ≤ (wallOutside w).1 := by
  have hout : 0 ≤ (wallOutside w).1 := by
    by_contra hn
    exact hw.2 (hleft _ (by omega))
  refine ⟨?_, hout⟩
  rcases w with ⟨⟨x,y⟩,a,b⟩
  cases a <;> cases b <;> simp [wallOutside, sideNeighbor] at hout ⊢ <;> omega

theorem boundary_halfplane_start_nonneg {B : Set Point}
    (hleft : ∀ v : Point, v.1 < 0 → v ∈ B) {w : Wall} (hw : IsBoundaryWall B w) :
    0 ≤ (wallStart w).1 := by
  have hout := (boundary_halfplane_support hleft hw).2
  rcases w with ⟨⟨x,y⟩,a,b⟩
  cases a <;> cases b <;> simp [wallOutside, sideNeighbor, wallStart] at hout ⊢ <;> omega

noncomputable def staticWall (B : Set Point) (w : Wall) : Nat → Wall
  | 0 => w
  | n+1 => nextWall B (staticWall B w n)

theorem staticWall_boundary {B : Set Point} {w : Wall} (hw : IsBoundaryWall B w)
    (n : Nat) : IsBoundaryWall B (staticWall B w n) := by
  induction n with
  | zero => exact hw
  | succ n ih => exact nextWall_boundary ih

theorem staticWall_cancel {B : Set Point} {w : Wall} (hw : IsBoundaryWall B w)
    {i j : Nat} (hij : i ≤ j) (heq : staticWall B w i = staticWall B w j) :
    w = staticWall B w (j-i) := by
  induction i generalizing j with
  | zero => simpa only [Nat.sub_zero, staticWall] using heq
  | succ i ih =>
    cases j with
    | zero => omega
    | succ j =>
      have he := nextWall_injective (staticWall_boundary hw i) (staticWall_boundary hw j) heq
      simpa only [Nat.add_sub_add_right] using ih (by omega) he

theorem staticWall_mem_boundary {s : Finset Point} {w : Wall}
    (hw : IsBoundaryWall (s : Set Point) w) (n : Nat) :
    staticWall (s : Set Point) w n ∈ boundaryWalls s := by
  have h := staticWall_boundary hw n
  generalize staticWall (s : Set Point) w n = v at *
  rcases v with ⟨u,d⟩
  exact (mem_boundaryWalls s u d).mpr h

theorem staticWall_returns {s : Finset Point} {w : Wall}
    (hw : IsBoundaryWall (s : Set Point) w) :
    ∃ n, 0 < n ∧ staticWall (s : Set Point) w n = w := by
  classical
  by_contra hreturn
  let f (n : Nat) : {v // v ∈ boundaryWalls s} :=
    ⟨staticWall (s : Set Point) w n, staticWall_mem_boundary hw n⟩
  have hf : Function.Injective f := by
    intro i j he
    have heq := congrArg Subtype.val he
    rcases lt_trichotomy i j with hlt | he | hgt
    · exact False.elim (hreturn ⟨j-i, by omega,
        (staticWall_cancel hw (Nat.le_of_lt hlt) heq).symm⟩)
    · exact he
    · exact False.elim (hreturn ⟨i-j, by omega,
        (staticWall_cancel hw (Nat.le_of_lt hgt) heq.symm).symm⟩)
  exact Finite.false (Finite.of_injective f hf)

/-- The least positive return is a simple directed-wall cycle. -/
theorem staticWall_cycle_bound {s : Finset Point} {w : Wall}
    (hw : IsBoundaryWall (s : Set Point) w) :
    ∃ L, 0 < L ∧ staticWall (s : Set Point) w L = w ∧
      (∀ i j, i < L → j < L → staticWall (s : Set Point) w i =
        staticWall (s : Set Point) w j → i = j) ∧ L ≤ squarePerimeter s := by
  classical
  have hex := staticWall_returns hw
  let L := Nat.find hex
  have hL : 0 < L ∧ staticWall (s : Set Point) w L = w := Nat.find_spec hex
  have hmin : ∀ k, 0 < k → k < L → staticWall (s : Set Point) w k ≠ w := by
    intro k hk hkL he
    have h := Nat.find_min' hex ⟨hk, he⟩
    omega
  have hi : ∀ i j, i < L → j < L → staticWall (s : Set Point) w i =
      staticWall (s : Set Point) w j → i = j := by
    intro i j hi hj he
    rcases lt_trichotomy i j with hlt | heq | hgt
    · exact False.elim (hmin (j-i) (by omega) (by omega)
        (staticWall_cancel hw (Nat.le_of_lt hlt) he).symm)
    · exact heq
    · exact False.elim (hmin (i-j) (by omega) (by omega)
        (staticWall_cancel hw (Nat.le_of_lt hgt) he.symm).symm)
  refine ⟨L, hL.1, hL.2, hi, ?_⟩
  have hsub : (Finset.range L).image (staticWall (s : Set Point) w) ⊆ boundaryWalls s := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact staticWall_mem_boundary hw i
  have hcard : ((Finset.range L).image (staticWall (s : Set Point) w)).card = L := by
    rw [Finset.card_image_iff.mpr]
    · exact Finset.card_range L
    · intro i hi' j hj' he
      exact hi i j (Finset.mem_range.mp hi') (Finset.mem_range.mp hj') he
  have hb := Finset.card_le_card hsub
  rw [hcard, boundaryWalls_card] at hb
  exact hb

theorem connected_staticWall_cycle_bound {s : Finset Point} {w : Wall}
    (hconn : SquaresConnected s) (hw : IsBoundaryWall (s : Set Point) w) :
    ∃ L, 0 < L ∧ staticWall (s : Set Point) w L = w ∧ L ≤ 2*s.card+2 := by
  obtain ⟨L, hL, hreturn, _, hbound⟩ := staticWall_cycle_bound hw
  exact ⟨L, hL, hreturn, hbound.trans (connectedSquares_perimeter hconn)⟩

theorem staticWall_shift (B : Set Point) (w : Wall) (n : Nat) :
    staticWall B w (n+1) = staticWall B (nextWall B w) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change nextWall B (staticWall B w (n+1)) = nextWall B (staticWall B (nextWall B w) n)
    rw [ih]

theorem staticWall_orbit_predecessor {B : Set Point} {w v : Wall} {L : Nat}
    (hw : IsBoundaryWall B w) (hv : IsBoundaryWall B v) (hL : 0 < L)
    (hreturn : staticWall B w L = w)
    (hnext : ∃ k, k < L ∧ nextWall B v = staticWall B w k) :
    ∃ k, k < L ∧ v = staticWall B w k := by
  obtain ⟨k, hk, he⟩ := hnext
  cases k with
  | zero =>
    have hlast : nextWall B (staticWall B w (L-1)) = w := by
      have h := hreturn
      conv_lhs at h => rw [show L = (L-1)+1 by omega]
      exact h
    refine ⟨L-1, by omega, ?_⟩
    apply nextWall_injective hv (staticWall_boundary hw (L-1))
    exact he.trans hlast.symm
  | succ k =>
    exact ⟨k, by omega, nextWall_injective hv (staticWall_boundary hw k) he⟩

theorem staticWall_reaches_orbit {B : Set Point} {w v : Wall} {L : Nat}
    (hw : IsBoundaryWall B w) (hv : IsBoundaryWall B v) (hL : 0 < L)
    (hreturn : staticWall B w L = w) (m : Nat)
    (hreach : ∃ k, k < L ∧ staticWall B v m = staticWall B w k) :
    ∃ k, k < L ∧ v = staticWall B w k := by
  induction m generalizing v with
  | zero => exact hreach
  | succ m ih =>
    simp only [staticWall_shift] at hreach
    exact staticWall_orbit_predecessor hw hv hL hreturn
      (ih (nextWall_boundary hv) hreach)

theorem wall_northwest_potential (w : Wall) :
    (wallEnd w).2 - (wallEnd w).1 ≤ (wallStart w).2 - (wallStart w).1 + 1 := by
  rcases w with ⟨⟨x,y⟩,a,b⟩
  cases a <;> cases b <;> simp [wallEnd, wallStart, sideNeighbor, tangentSide] <;> omega

theorem wall_southeast_potential (w : Wall) :
    (wallEnd w).1 - (wallEnd w).2 ≤ (wallStart w).1 - (wallStart w).2 + 1 := by
  rcases w with ⟨⟨x,y⟩,a,b⟩
  cases a <;> cases b <;> simp [wallEnd, wallStart, sideNeighbor, tangentSide] <;> omega

theorem staticWall_potential_bound (B : Set Point) (w : Wall) (f : Point → Int)
    (hf : ∀ v : Wall, f (wallEnd v) ≤ f (wallStart v) + 1)
    {i j : Nat} (hij : i ≤ j) :
    f (wallStart (staticWall B w j)) - f (wallStart (staticWall B w i)) ≤ (j-i : Nat) := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    have hs := hf (staticWall B w j)
    have he : wallStart (staticWall B w (j+1)) = wallEnd (staticWall B w j) :=
      nextWall_start B _
    rw [he]
    omega


abbrev SquarePath (s : Finset Point) (u v : Point) : Prop :=
  Relation.ReflTransGen (fun a b => a ∈ s ∧ b ∈ s ∧ SquareAdjacent a b) u v

noncomputable def squareComponent (s : Finset Point) (root : Point) : Finset Point := by
  classical
  exact s.filter (SquarePath s root)

theorem squareAdjacent_symm {u v : Point} (h : SquareAdjacent u v) : SquareAdjacent v u := by
  obtain ⟨d, rfl⟩ := h
  exact ⟨oppositeSide d, sideNeighbor_opposite u d⟩

theorem squarePath_reverse {s : Finset Point} {u v : Point} (h : SquarePath s u v) :
    SquarePath s v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.head ⟨hstep.2.1, hstep.1, squareAdjacent_symm hstep.2.2⟩

theorem mem_squareComponent (s : Finset Point) (r v : Point) :
    v ∈ squareComponent s r ↔ v ∈ s ∧ SquarePath s r v := by
  classical
  simp [squareComponent]

theorem squareComponent_subset (s : Finset Point) (r : Point) : squareComponent s r ⊆ s := by
  intro v hv
  exact ((mem_squareComponent s r v).mp hv).1

theorem squareComponent_root {s : Finset Point} {r : Point} (hr : r ∈ s) :
    r ∈ squareComponent s r :=
  (mem_squareComponent s r r).mpr ⟨hr, Relation.ReflTransGen.refl⟩

theorem squareComponent_path {s : Finset Point} {r v : Point}
    (hp : SquarePath s r v) : SquarePath (squareComponent s r) r v := by
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | @tail u v hpath hstep ih =>
    have hu := (mem_squareComponent s r u).mpr ⟨hstep.1, hpath⟩
    have hv := (mem_squareComponent s r v).mpr ⟨hstep.2.1, hpath.tail hstep⟩
    exact ih.tail ⟨hu, hv, hstep.2.2⟩

theorem squareComponent_connected {s : Finset Point} {r : Point} (hr : r ∈ s) :
    SquaresConnected (squareComponent s r) := by
  refine ⟨⟨r, squareComponent_root hr⟩, ?_⟩
  intro u hu v hv
  have hp := squareComponent_path ((mem_squareComponent s r u).mp hu).2
  have hq := squareComponent_path ((mem_squareComponent s r v).mp hv).2
  exact (squarePath_reverse hp).trans hq

theorem squareComponent_adjacent {s : Finset Point} {r u v : Point}
    (hu : u ∈ squareComponent s r) (hv : v ∈ s) (h : SquareAdjacent u v) :
    v ∈ squareComponent s r := by
  obtain ⟨hus, hp⟩ := (mem_squareComponent s r u).mp hu
  exact (mem_squareComponent s r v).mpr ⟨hv, hp.tail ⟨hus, hv, h⟩⟩

theorem nextWall_component {s : Finset Point} {r : Point} {w : Wall}
    (hw : w.1 ∈ squareComponent s r) :
    nextWall (squareComponent s r : Set Point) w = nextWall (s : Set Point) w := by
  classical
  unfold nextWall
  dsimp only
  by_cases ha : sideNeighbor w.1 (tangentSide w.2) ∈ s
  · have haC := squareComponent_adjacent hw ha ⟨tangentSide w.2, rfl⟩
    by_cases hb : sideNeighbor (sideNeighbor w.1 (tangentSide w.2)) w.2 ∈ s
    · have hbC := squareComponent_adjacent haC hb ⟨w.2, rfl⟩
      simp [ha, haC, hb, hbC]
    · have hbC : sideNeighbor (sideNeighbor w.1 (tangentSide w.2)) w.2 ∉ squareComponent s r :=
        fun h => hb (squareComponent_subset s r h)
      simp [ha, haC, hb, hbC]
  · have haC : sideNeighbor w.1 (tangentSide w.2) ∉ squareComponent s r :=
      fun h => ha (squareComponent_subset s r h)
    simp [ha, haC]

theorem staticWall_component {s : Finset Point} {w : Wall}
    (hw : IsBoundaryWall (s : Set Point) w) (n : Nat) :
    staticWall (squareComponent s w.1 : Set Point) w n = staticWall (s : Set Point) w n := by
  have hc : IsBoundaryWall (squareComponent s w.1 : Set Point) w :=
    ⟨squareComponent_root hw.1, fun h => hw.2 (squareComponent_subset s w.1 h)⟩
  induction n with
  | zero => rfl
  | succ n ih =>
    change nextWall _ (staticWall _ w n) = nextWall _ (staticWall _ w n)
    rw [nextWall_component (staticWall_boundary hc n).1, ih]

/-- Even if the whole obstacle set is disconnected, this corner convention
keeps the walk on one side-connected component. -/
theorem finite_staticWall_cycle_bound {s : Finset Point} {w : Wall}
    (hw : IsBoundaryWall (s : Set Point) w) :
    ∃ L, 0 < L ∧ staticWall (s : Set Point) w L = w ∧ L ≤ 2*s.card+2 := by
  have hc : IsBoundaryWall (squareComponent s w.1 : Set Point) w :=
    ⟨squareComponent_root hw.1, fun h => hw.2 (squareComponent_subset s w.1 h)⟩
  obtain ⟨L, hL, heq, hb⟩ := connected_staticWall_cycle_bound
    (squareComponent_connected hw.1) hc
  rw [staticWall_component hw] at heq
  have hcard := Finset.card_le_card (squareComponent_subset s w.1)
  exact ⟨L, hL, heq, by omega⟩


def preColumn (N : Nat) : Finset Point :=
  (Finset.range N).image (fun k : Nat => ((-1 : Int), (k : Int)))

def quadrantBurns (b : List (Option Point)) : Finset Point :=
  (b.filterMap id).toFinset.filter (fun v => 0 ≤ v.1 ∧ 0 ≤ v.2)

def frozenSquares (N : Nat) (b : List (Option Point)) : Finset Point :=
  preColumn N ∪ quadrantBurns b

theorem mem_preColumn (N : Nat) (v : Point) :
    v ∈ preColumn N ↔ v.1 = -1 ∧ 0 ≤ v.2 ∧ v.2 < (N : Int) := by
  constructor
  · intro h
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
    have hkN := Finset.mem_range.mp hk
    exact ⟨rfl, by omega, by omega⟩
  · intro h
    apply Finset.mem_image.mpr
    refine ⟨v.2.toNat, Finset.mem_range.mpr (by omega), ?_⟩
    apply Prod.ext <;> dsimp <;> omega

theorem mem_quadrantBurns (b : List (Option Point)) (v : Point) :
    v ∈ quadrantBurns b ↔ 0 ≤ v.1 ∧ 0 ≤ v.2 ∧ some v ∈ b := by
  simp [quadrantBurns, List.mem_filterMap, and_comm, and_assoc]

theorem mem_frozenSquares (N : Nat) (b : List (Option Point)) (v : Point) :
    v ∈ frozenSquares N b ↔
      (v.1 = -1 ∧ 0 ≤ v.2 ∧ v.2 < (N : Int)) ∨
      (0 ≤ v.1 ∧ 0 ≤ v.2 ∧ some v ∈ b) := by
  simp only [frozenSquares, Finset.mem_union, mem_preColumn, mem_quadrantBurns]

theorem frozenSquares_card (N : Nat) (b : List (Option Point)) :
    (frozenSquares N b).card ≤ N + b.length := by
  have hcol : (preColumn N).card ≤ N := by
    have h := Finset.card_image_le (s := Finset.range N)
      (f := fun k => ((-1 : Int), (k : Int)))
    simpa only [preColumn, Finset.card_range] using h
  have hburn : (quadrantBurns b).card ≤ b.length :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans
      ((List.toFinset_card_le _).trans (List.length_filterMap_le id b))
  have h := Finset.card_union_le (preColumn N) (quadrantBurns b)
  unfold frozenSquares
  omega

theorem frozenSquares_agree (N : Nat) (b : List (Option Point)) (v : Point)
    (hx : -1 ≤ v.1) (hy : 0 ≤ v.2) (hN : v.2 < (N : Int)) :
    v ∈ frozenSquares N b ↔ v ∈ wallObstacles b := by
  rw [mem_frozenSquares]
  change _ ↔ v.1 < 0 ∨ some v ∈ b
  constructor
  · rintro (h | h)
    · exact Or.inl (by omega)
    · exact Or.inr h.2.2
  · rintro (h | h)
    · exact Or.inl ⟨by omega, hy, hN⟩
    · by_cases hv : v.1 < 0
      · exact Or.inl ⟨by omega, hy, hN⟩
      · exact Or.inr ⟨by omega, hy, h⟩

theorem frozenSquares_nonnegative_y {N : Nat} {b : List (Option Point)} {v : Point}
    (hv : v ∈ frozenSquares N b) : 0 ≤ v.2 := by
  rcases (mem_frozenSquares N b v).mp hv with h | h <;> exact h.2.1

theorem frozenSquares_left_bound {N : Nat} {b : List (Option Point)} {v : Point}
    (hv : v ∈ frozenSquares N b) : -1 ≤ v.1 := by
  rcases (mem_frozenSquares N b v).mp hv with h | h <;> omega

theorem frozenSquares_height {N : Nat} {b : List (Option Point)}
    (htall : ∀ v, some v ∈ b → v.2 < (N : Int)) {v : Point}
    (hv : v ∈ frozenSquares N b) : v.2 < (N : Int) := by
  rcases (mem_frozenSquares N b v).mp hv with h | h
  · exact h.2.2
  · exact htall v h.2.2

theorem frozenSquares_initial_boundary {N : Nat} (hN : 0 < N)
    {b : List (Option Point)} (hclear : some origin ∉ b) :
    IsBoundaryWall (frozenSquares N b : Set Point) initialWall := by
  constructor
  · apply (mem_frozenSquares N b (-1,0)).mpr
    exact Or.inl ⟨rfl, by omega, by omega⟩
  · change origin ∉ frozenSquares N b
    rw [mem_frozenSquares]
    simp [origin] at hclear ⊢
    exact hclear

theorem frozenSquares_cycle_budget {N : Nat} (hN : 0 < N)
    {b : List (Option Point)} (hclear : some origin ∉ b) :
    ∃ L, 0 < L ∧ staticWall (frozenSquares N b : Set Point) initialWall L = initialWall ∧
      L ≤ 2*(N+b.length)+2 := by
  obtain ⟨L, hL, heq, hb⟩ := finite_staticWall_cycle_bound
    (frozenSquares_initial_boundary hN hclear)
  have hc := frozenSquares_card N b
  exact ⟨L, hL, heq, by omega⟩

def columnWest (k : Nat) : Wall := ((-1, (k : Int)), (false, true))
def columnBottom : Wall := ((-1,0), (true,true))
def columnTop (N : Nat) : Wall := ((-1, (N : Int)-1), (true,false))

theorem columnWest_zero_next (N : Nat) (b : List (Option Point)) :
    nextWall (frozenSquares N b : Set Point) (columnWest 0) = columnBottom := by
  simp [nextWall, columnWest, columnBottom, tangentSide, sideNeighbor,
    mem_frozenSquares]

theorem columnWest_succ_next (N k : Nat) (hk : k < N) (b : List (Option Point)) :
    nextWall (frozenSquares N b : Set Point) (columnWest (k+1)) = columnWest k := by
  have hcol : ((-1, (k : Int)) : Point) ∈ frozenSquares N b :=
    (mem_frozenSquares N b _).mpr (Or.inl ⟨rfl, by omega, by omega⟩)
  have hout : ((-2, (k : Int)) : Point) ∉ frozenSquares N b := by
    simp [mem_frozenSquares]
  simp [nextWall, columnWest, tangentSide, sideNeighbor, hcol, hout]

theorem columnBottom_next (N : Nat) (b : List (Option Point))
    (hclear : some origin ∉ b) :
    nextWall (frozenSquares N b : Set Point) columnBottom = initialWall := by
  have h : ((0,0) : Point) ∉ frozenSquares N b := by
    have hc : some ((0,0) : Point) ∉ b := hclear
    simp [mem_frozenSquares, hc]
  simp [nextWall, columnBottom, initialWall, tangentSide, sideNeighbor, h]

theorem columnTop_next (N : Nat) (hN : 0 < N) (b : List (Option Point)) :
    nextWall (frozenSquares N b : Set Point) (columnTop N) = columnWest (N-1) := by
  have h : ((-2, (N : Int)-1) : Point) ∉ frozenSquares N b := by
    simp [mem_frozenSquares]
  have hc : ((N-1 : Nat) : Int) = (N : Int)-1 := by omega
  simp [nextWall, columnTop, columnWest, tangentSide, sideNeighbor, h, hc]

theorem columnTop_boundary (N : Nat) (hN : 0 < N) (b : List (Option Point)) :
    IsBoundaryWall (frozenSquares N b : Set Point) (columnTop N) := by
  constructor
  · apply (mem_frozenSquares N b _).mpr
    exact Or.inl ⟨rfl, by dsimp [columnTop]; omega, by dsimp [columnTop]; omega⟩
  · simp [wallOutside, columnTop, sideNeighbor, mem_frozenSquares]

theorem columnWest_reaches_initial (N k : Nat) (hk : k < N)
    (b : List (Option Point)) (hclear : some origin ∉ b) :
    staticWall (frozenSquares N b : Set Point) (columnWest k) (k+2) = initialWall := by
  induction k with
  | zero =>
    rw [staticWall_shift, columnWest_zero_next]
    exact columnBottom_next N b hclear
  | succ k ih =>
    rw [show k+1+2 = (k+2)+1 by omega, staticWall_shift, columnWest_succ_next N k (by omega)]
    exact ih (by omega)

theorem columnTop_reaches_initial (N : Nat) (hN : 0 < N)
    (b : List (Option Point)) (hclear : some origin ∉ b) :
    staticWall (frozenSquares N b : Set Point) (columnTop N) (N+2) = initialWall := by
  rw [show N+2 = ((N-1)+2)+1 by omega, staticWall_shift, columnTop_next N hN]
  exact columnWest_reaches_initial N (N-1) (by omega) b hclear

theorem columnTop_in_initial_cycle {N L : Nat} (hN : 0 < N)
    {b : List (Option Point)} (hclear : some origin ∉ b) (hL : 0 < L)
    (hreturn : staticWall (frozenSquares N b : Set Point) initialWall L = initialWall) :
    ∃ k, k < L ∧ staticWall (frozenSquares N b : Set Point) initialWall k = columnTop N := by
  obtain ⟨k, hk, he⟩ := staticWall_reaches_orbit
    (frozenSquares_initial_boundary hN hclear) (columnTop_boundary N hN b)
    hL hreturn (N+2) ⟨0, hL, columnTop_reaches_initial N hN b hclear⟩
  exact ⟨k, hk, he.symm⟩

/-- Claim 4.4's lower count, with the first-contact geometry made explicit. -/
theorem frozenSquares_return_lower {N L j : Nat} (hN : 0 < N)
    {b : List (Option Point)} (hclear : some origin ∉ b) (hL : 0 < L)
    (hreturn : staticWall (frozenSquares N b : Set Point) initialWall L = initialWall)
    (x : Int) (hx : 1 ≤ x)
    (heast : wallStart (staticWall (frozenSquares N b : Set Point) initialWall (j+1)) = (x+1,0))
    (hprefix : ∀ i, i ≤ j →
      (wallStart (staticWall (frozenSquares N b : Set Point) initialWall i)).2 < (N : Int)) :
    j + 2*N + 5 ≤ L := by
  let B : Set Point := frozenSquares N b
  obtain ⟨k, hk, htop⟩ := columnTop_in_initial_cycle hN hclear hL hreturn
  have htopstart : wallStart (staticWall B initialWall k) = (0, (N : Int)) := by
    rw [htop]
    simp [wallStart, columnTop]
  have hjk : j < k := by
    by_contra h
    have hp := hprefix k (by omega)
    rw [htop] at hp
    simp [wallStart, columnTop] at hp
  have htopnext : wallStart (staticWall B initialWall (k+1)) = (-1, (N : Int)) := by
    change wallStart (nextWall B (staticWall B initialWall k)) = _
    rw [nextWall_start, htop]
    simp [wallEnd, wallStart, columnTop, tangentSide, sideNeighbor]
  have hfinish : wallStart (staticWall B initialWall L) = (0,0) := by
    rw [hreturn]
    rfl
  have hn := staticWall_potential_bound B initialWall (fun v => v.2-v.1)
    wall_northwest_potential (show j+1 ≤ k by omega)
  have hs := staticWall_potential_bound B initialWall (fun v => v.1-v.2)
    wall_southeast_potential (show k+1 ≤ L by omega)
  rw [htopstart, heast] at hn
  rw [hfinish, htopnext] at hs
  dsimp only at hn hs
  omega


noncomputable def traceHeight (D : DevilStrategy) (j : Nat) : Nat :=
  (Finset.range (j+1)).sup (fun i => (wallTrace D i).1.2.toNat) + 3

theorem traceHeight_pos (D : DevilStrategy) (j : Nat) : 0 < traceHeight D j := by
  unfold traceHeight
  omega

theorem traceHeight_bound (D : DevilStrategy) {i j : Nat} (hij : i ≤ j) :
    (wallTrace D i).1.2 + 2 < (traceHeight D j : Int) := by
  have h := Finset.le_sup (f := fun i => (wallTrace D i).1.2.toNat)
    (Finset.mem_range.mpr (show i < j+1 by omega))
  unfold traceHeight
  omega

theorem wallStart_height (w : Wall) : (wallStart w).2 ≤ w.1.2+1 := by
  rcases w with ⟨⟨x,y⟩,a,b⟩
  cases a <;> cases b <;> simp [wallStart]

theorem wall_tests_in_strip (w : Wall) (hx : 0 ≤ (wallOutside w).1)
    (hy : 0 ≤ (wallStart w).2) (he : 0 < (wallEnd w).2) :
    let a := sideNeighbor w.1 (tangentSide w.2)
    let b := sideNeighbor a w.2
    (-1 ≤ a.1 ∧ 0 ≤ a.2 ∧ a.2 ≤ w.1.2+1) ∧
      (-1 ≤ b.1 ∧ 0 ≤ b.2 ∧ b.2 ≤ w.1.2+1) := by
  rcases w with ⟨⟨x,y⟩,a,b⟩
  cases a <;> cases b <;>
    simp [wallOutside, wallStart, wallEnd, sideNeighbor, tangentSide] at * <;> omega

theorem nextWall_congr_tests (B C : Set Point) (w : Wall)
    (ha : sideNeighbor w.1 (tangentSide w.2) ∈ B ↔
      sideNeighbor w.1 (tangentSide w.2) ∈ C)
    (hb : sideNeighbor (sideNeighbor w.1 (tangentSide w.2)) w.2 ∈ B ↔
      sideNeighbor (sideNeighbor w.1 (tangentSide w.2)) w.2 ∈ C) :
    nextWall B w = nextWall C w := by
  classical
  simp only [nextWall, ha, hb]

theorem nice_origin_not_burned {D : DevilStrategy} (hnice : Nice 2 D) (n : Nat) :
    some origin ∉ (play wallAngel D n).burned := by
  induction n with
  | zero => simp [play, initial]
  | succ n ih =>
    have hne : D (play wallAngel D n).visited ≠ some origin := by
      intro he
      exact (hnice _ (survives_journey (wallAngel_survives_nice D hnice) n) origin he).1 rfl
    change some origin ∉ (play wallAngel D n).burned ++ [_]
    simpa using And.intro ih (Ne.symm hne)

theorem trace_frozen_prefix (D : DevilStrategy) (hnice : Nice 2 D) {j : Nat}
    (hpositive : ∀ k, 0 < k → k < j → 0 < (wallStart (wallTrace D k)).2) :
    ∀ i, i < j →
      staticWall (frozenSquares (traceHeight D j)
        (play wallAngel D ((j-1)/2+1)).burned : Set Point) initialWall i = wallTrace D i := by
  let N := traceHeight D j
  let b := (play wallAngel D ((j-1)/2+1)).burned
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hij
    change nextWall (frozenSquares N b : Set Point) (staticWall _ initialWall i) = _
    rw [ih (by omega)]
    have hw := wallTrace_boundary D hnice i
    have hx : 0 ≤ (wallOutside (wallTrace D i)).1 :=
      (boundary_halfplane_support (fun _ h => Or.inl h) hw).2
    have hy : 0 ≤ (wallStart (wallTrace D i)).2 := by
      by_cases hi : i = 0
      · subst i; exact Int.le_refl 0
      · exact le_of_lt (hpositive i (by omega) (by omega))
    have he : 0 < (wallEnd (wallTrace D i)).2 := by
      rw [wallTrace_end_start]
      exact hpositive (i+1) (by omega) hij
    have ht := wall_tests_in_strip (wallTrace D i) hx hy he
    have hheight := traceHeight_bound D (show i ≤ j by omega)
    have heq : nextWall (frozenSquares N b : Set Point) (wallTrace D i) =
        nextWall (traceObstacles D (j-1)) (wallTrace D i) := by
      apply nextWall_congr_tests
      · exact frozenSquares_agree N b _ ht.1.1 ht.1.2.1 (by dsimp [N]; omega)
      · exact frozenSquares_agree N b _ ht.2.1 ht.2.2.1 (by dsimp [N]; omega)
    rw [heq]
    exact wallTrace_frozen_step D hnice i (j-1) (by omega)

theorem wall_down_to_axis (w : Wall) (hx : 0 ≤ (wallOutside w).1)
    (hy : 0 < (wallStart w).2) (he : (wallEnd w).2 ≤ 0) :
    ∃ x : Int, 1 ≤ x ∧ w = ((x,0),(false,true)) := by
  rcases w with ⟨⟨x,y⟩,a,b⟩
  cases a <;> cases b <;>
    simp [wallOutside, wallStart, wallEnd, sideNeighbor, tangentSide] at hx hy he ⊢
  all_goals omega

theorem wallTrace_no_first_axis_contact (D : DevilStrategy) (hnice : Nice 2 D)
    {j : Nat} (hj : 0 < j)
    (hpositive : ∀ k, 0 < k → k < j → 0 < (wallStart (wallTrace D k)).2)
    (hcontact : (wallStart (wallTrace D j)).2 ≤ 0) : False := by
  have hone : wallStart (wallTrace D 1) = (0,1) := by
    rw [← wallTrace_end_start D 0]
    rfl
  have hj2 : 1 < j := by
    by_contra h
    have hjeq : j = 1 := by omega
    rw [hjeq, hone] at hcontact
    dsimp at hcontact
    omega
  let N := traceHeight D j
  let t := (j-1)/2+1
  let b := (play wallAngel D t).burned
  let B : Set Point := frozenSquares N b
  have hN : 0 < N := traceHeight_pos D j
  have hclear : some origin ∉ b := nice_origin_not_burned hnice t
  have hbefore := hpositive (j-1) (by omega) (by omega)
  have hend : (wallEnd (wallTrace D (j-1))).2 ≤ 0 := by
    rw [wallTrace_end_start, show j-1+1 = j by omega]
    exact hcontact
  have hout : 0 ≤ (wallOutside (wallTrace D (j-1))).1 :=
    (boundary_halfplane_support (fun _ h => Or.inl h) (wallTrace_boundary D hnice (j-1))).2
  obtain ⟨x, hx, hwall⟩ := wall_down_to_axis (wallTrace D (j-1)) hout hbefore hend
  have hpast : staticWall B initialWall (j-1) = wallTrace D (j-1) :=
    trace_frozen_prefix D hnice hpositive (j-1) (by omega)
  have hjwall : staticWall B initialWall j = ((x,0),(true,true)) := by
    conv_lhs => rw [show j = (j-1)+1 by omega]
    change nextWall B (staticWall B initialWall (j-1)) = _
    rw [hpast, hwall]
    simp [B, nextWall, tangentSide, sideNeighbor, mem_frozenSquares]
  have heast : wallStart (staticWall B initialWall (j+1)) = (x+1,0) := by
    change wallStart (nextWall B (staticWall B initialWall j)) = _
    rw [nextWall_start, hjwall]
    simp [wallEnd, wallStart, tangentSide, sideNeighbor]
  have hprefix : ∀ i, i ≤ j → (wallStart (staticWall B initialWall i)).2 < (N : Int) := by
    intro i hij
    by_cases heq : i = j
    · subst i
      rw [hjwall]
      simp only [wallStart]
      dsimp
      omega
    · have hi : i < j := by omega
      rw [trace_frozen_prefix D hnice hpositive i hi]
      have ht := traceHeight_bound D hij
      have hs := wallStart_height (wallTrace D i)
      dsimp [N]
      omega
  obtain ⟨L, hL, hreturn, hupper⟩ := frozenSquares_cycle_budget hN hclear
  have hlower := frozenSquares_return_lower hN hclear hL hreturn x hx heast hprefix
  have hlen : b.length = t := (play_lengths wallAngel D t).2
  have hbudget : 2*t-1 ≤ j := by dsimp [t]; omega
  omega

theorem wallTrace_above_axis (D : DevilStrategy) (hnice : Nice 2 D)
    (n : Nat) (hn : 0 < n) : 0 < (wallStart (wallTrace D n)).2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_contra h
    exact wallTrace_no_first_axis_contact D hnice hn
      (fun k hk hkn => ih k hkn hk) (by omega)

theorem wallTrace_never_returns (D : DevilStrategy) (hnice : Nice 2 D)
    (n : Nat) (hn : 0 < n) : wallTrace D n ≠ initialWall := by
  intro heq
  have h := wallTrace_above_axis D hnice n hn
  rw [heq, wallStart_initial] at h
  change 0 < (0 : Int) at h
  omega


end AngelDevil

theorem solution (D : AngelDevil.DevilStrategy) (hnice : AngelDevil.Nice 2 D)
    (n : Nat) (hn : 0 < n) : AngelDevil.wallTrace D n ≠ AngelDevil.initialWall :=
  AngelDevil.wallTrace_never_returns D hnice n hn
