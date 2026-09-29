-- Prove2me | Definitions.Def_KServer_park_shadow
-- name    : KServer_park_shadow
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T15:14:11.565045+00:00
-- url     : https://prove2.me/theorems/7972439b-4752-4bd9-872d-9b15066c9a56
-- title:
--   Park-aware shadow evaders and bail-cost domination
-- statement:
--   In the coin phase of the BCR race, the advancing side's requests are united with the passive side's frozen parking set. Let $\pi : Y \to X$ be nonexpansive, $G$ a request transformation with $\pi(G(S)) \subseteq S$, and $P \subseteq Y$ a parking set separated from every transformed request: $d(y, z) \ge s$ for all $y \in G(S)$, $z \in P$. An online evader $E$ on $Y$ facing the park-united requests $G(S) \cup P$ induces a park-aware shadow on $X$: it follows $\pi$ while $E$ serves from the transformed copy, and serves by a chosen point once $E$ parks. With the induced online bail rule (transported bail, or the first parked position) at escape price $p_e$, the shadow's bail-aware cost is dominated by $E$'s: $$\mathrm{bailCost}_{\mathrm{shadow}}(h, \chi, p_e) \le \mathrm{bailCost}_{E}(h_0 + \theta(h), \theta(\chi), p'),$$ provided $\mathrm{diam}(X) + p_e \le s$, the start position is $s$-far from the park, the chunk's sets are nonempty, and $p_e \le p'$. The park bail is financed geometrically: entering the park costs $E$ at least the separation $s$, which covers the shadow's final repositioning jump (at most $\mathrm{diam}(X)$) plus the escape price. The file also provides first-firing characterizations of online bail times.
-- source:
--   BCR randomized k-server lower bound, stage construction layer

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_bail_append
import Definitions.Def_KServer_shadow

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

namespace KServer

/-! ### Shadow evaders with parking options

In the coin phase of the BCR race, the advancing side's requests are
united with the passive side's frozen parking set.  An online evader on
the level step facing such requests induces an online evader for the
advancing side's system: it follows the nonexpansive projection while the
evader serves from the advancing copy, and *bails* — at the level-`w`
escape price — once the evader first serves from the park.  The bail is
financed by the geometric separation: entering the park costs at least
`sep`, which dominates the shadow's final repositioning jump (bounded by
the diameter of the small space) plus the escape price. -/

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- Requests with a parking option. -/
def parkMap (G : Set X → Set Y) (Pk : Set Y) (l : List (Set X)) : List (Set Y) :=
  l.map (fun S => G S ∪ Pk)

theorem parkMap_append (G : Set X → Set Y) (Pk : Set Y) (l l' : List (Set X)) :
    parkMap G Pk (l ++ l') = parkMap G Pk l ++ parkMap G Pk l' := by
  unfold parkMap
  rw [List.map_append]

theorem parkMap_take (G : Set X → Set Y) (Pk : Set Y) (l : List (Set X)) (n : ℕ) :
    parkMap G Pk (l.take n) = (parkMap G Pk l).take n := by
  unfold parkMap
  rw [List.map_take]

theorem parkMap_length (G : Set X → Set Y) (Pk : Set Y) (l : List (Set X)) :
    (parkMap G Pk l).length = l.length := by
  unfold parkMap
  rw [List.length_map]

open Classical in
/-- The park-aware shadow: project through `π` while the evader is out of
the park; serve via a chosen point once it parks. -/
noncomputable def parkShadow (π : Y → X) (G : Set X → Set Y) (Pk : Set Y)
    (hG : ∀ S : Set X, ∀ y ∈ G S, π y ∈ S)
    (hGne : ∀ S : Set X, S.Nonempty → (G S).Nonempty)
    (E : EvaderAlgorithm Y) (h₀ : List (Set Y)) : EvaderAlgorithm X where
  pos l :=
    if E.pos (h₀ ++ parkMap G Pk l) ∈ Pk then
      match l.getLast? with
      | some S => if hS : S.Nonempty then hS.choose
          else π (E.pos (h₀ ++ parkMap G Pk l))
      | none => π (E.pos (h₀ ++ parkMap G Pk l))
    else π (E.pos (h₀ ++ parkMap G Pk l))
  serves l S hS := by
    have hlast : (l ++ [S]).getLast? = some S := by
      rw [List.getLast?_concat]
    by_cases hp : E.pos (h₀ ++ parkMap G Pk (l ++ [S])) ∈ Pk
    · simp only [hp, if_pos, hlast]
      rw [dif_pos hS]
      exact hS.choose_spec
    · simp only [hp, if_neg, not_false_iff]
      have hserve := E.serves (h₀ ++ parkMap G Pk l) (G S ∪ Pk)
        (Set.Nonempty.inl (hGne S hS))
      have he : h₀ ++ parkMap G Pk (l ++ [S])
          = (h₀ ++ parkMap G Pk l) ++ [G S ∪ Pk] := by
        rw [parkMap_append, List.append_assoc]
        rfl
      rw [← he] at hserve
      rcases hserve with hin | hin
      · exact hG S _ hin
      · exact absurd hin hp


section ParkBound

variable (π : Y → X) (G : Set X → Set Y) (Pk : Set Y)
variable (E : EvaderAlgorithm Y) (h₀ : List (Set Y)) (h χ : List (Set X))

/-- The step-space position after `q` requests of the chunk. -/
noncomputable def posY (q : ℕ) : Y :=
  E.pos ((h₀ ++ parkMap G Pk h) ++ (parkMap G Pk χ).take q)

theorem theta_align (q : ℕ) :
    h₀ ++ parkMap G Pk (h ++ χ.take q)
      = (h₀ ++ parkMap G Pk h) ++ (parkMap G Pk χ).take q := by
  rw [parkMap_append, parkMap_take, ← List.append_assoc]

theorem take_succ_park {q : ℕ} (hq : q < χ.length) :
    (parkMap G Pk χ).take (q + 1)
      = (parkMap G Pk χ).take q ++ [G χ[q] ∪ Pk] := by
  have hq' : q < (parkMap G Pk χ).length := by
    rw [parkMap_length]
    exact hq
  rw [List.take_add_one, List.getElem?_eq_getElem hq']
  simp only [Option.toList_some]
  congr 1
  simp [parkMap]

theorem take_succ_chunk {q : ℕ} (hq : q < χ.length) :
    χ.take (q + 1) = χ.take q ++ [χ[q]] := by
  rw [List.take_add_one]
  congr 1
  rw [List.getElem?_eq_getElem hq]
  rfl

/-- Serving discipline: after request `q`, the evader is in the request. -/
theorem posY_mem (hGne : ∀ S : Set X, S.Nonempty → (G S).Nonempty)
    {q : ℕ} (hq : q < χ.length) (hSne : (χ[q] : Set X).Nonempty) :
    posY G Pk E h₀ h χ (q + 1) ∈ G χ[q] ∪ Pk := by
  unfold posY
  rw [take_succ_park G Pk χ hq, ← List.append_assoc]
  exact E.serves _ _ (Set.Nonempty.inl (hGne _ hSne))

open Classical in
/-- The shadow's position while the evader is out of the park. -/
theorem parkShadow_pos_out
    (hG : ∀ S : Set X, ∀ y ∈ G S, π y ∈ S)
    (hGne : ∀ S : Set X, S.Nonempty → (G S).Nonempty)
    {q : ℕ} (hout : posY G Pk E h₀ h χ q ∉ Pk) :
    (parkShadow π G Pk hG hGne E h₀).pos (h ++ χ.take q)
      = π (posY G Pk E h₀ h χ q) := by
  unfold parkShadow
  show (if E.pos (h₀ ++ parkMap G Pk (h ++ χ.take q)) ∈ Pk then _ else _) = _
  rw [theta_align G Pk h₀ h χ q]
  rw [if_neg (show ¬ _ by exact hout)]
  rfl

open Classical in
/-- The shadow's position at a parked step: the chosen serving point. -/
theorem parkShadow_pos_in
    (hG : ∀ S : Set X, ∀ y ∈ G S, π y ∈ S)
    (hGne : ∀ S : Set X, S.Nonempty → (G S).Nonempty)
    {q : ℕ} (hq : q < χ.length)
    (hSne : (χ[q] : Set X).Nonempty)
    (hin : posY G Pk E h₀ h χ (q + 1) ∈ Pk) :
    (parkShadow π G Pk hG hGne E h₀).pos (h ++ χ.take (q + 1))
      = hSne.choose := by
  unfold parkShadow
  show (if E.pos (h₀ ++ parkMap G Pk (h ++ χ.take (q + 1))) ∈ Pk then _ else _) = _
  rw [theta_align G Pk h₀ h χ (q + 1)]
  rw [if_pos (show _ by exact hin)]
  have hlast : (h ++ χ.take (q + 1)).getLast? = some (χ[q] : Set X) := by
    rw [take_succ_chunk χ hq, ← List.append_assoc, List.getLast?_concat]
  rw [hlast]
  show (if hS : (χ[q] : Set X).Nonempty then hS.choose else _) = _
  rw [dif_pos hSne]

theorem chunk_choose_mem {q : ℕ} (hq : q < χ.length)
    (hSne : (χ[q] : Set X).Nonempty) : hSne.choose ∈ (χ[q] : Set X) :=
  hSne.choose_spec

end ParkBound


section BailFacts

variable {X : Type*}

theorem find?_first {α : Type*} {l : List α} {p : α → Bool} {b : α}
    (h : l.find? p = some b) :
    ∃ i : ℕ, ∃ hi : i < l.length, l[i] = b ∧ p b = true
      ∧ ∀ j (hj : j < i), p (l[j]'(by omega)) = false := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rw [List.find?_cons] at h
    by_cases hpa : p a
    · rw [hpa] at h
      obtain rfl := Option.some_inj.mp h
      exact ⟨0, by simp, rfl, hpa, fun j hj => absurd hj (by omega)⟩
    · rw [Bool.not_eq_true] at hpa
      rw [hpa] at h
      obtain ⟨i, hi, hget, hpb, hbefore⟩ := ih h
      refine ⟨i + 1, by simpa using Nat.succ_lt_succ hi, by simpa using hget,
        hpb, ?_⟩
      intro j hj
      rcases j with _ | j'
      · simpa using hpa
      · have := hbefore j' (by omega)
        simpa using this

theorem bailTime_none_iff {bail : List (Set X) → Bool} {h χ : List (Set X)} :
    bailTime bail h χ = none
      ↔ ∀ q, q < χ.length → bail (h ++ χ.take q) = false := by
  unfold bailTime
  rw [List.find?_eq_none]
  constructor
  · intro hall q hq
    have := hall q (List.mem_range.mpr hq)
    simpa using this
  · intro hall q hq
    rw [List.mem_range] at hq
    simp [hall q hq]

theorem bailTime_some_first {bail : List (Set X) → Bool} {h χ : List (Set X)}
    {q : ℕ} (hq : bailTime bail h χ = some q) :
    q < χ.length ∧ bail (h ++ χ.take q) = true
      ∧ ∀ q', q' < q → bail (h ++ χ.take q') = false := by
  unfold bailTime at hq
  obtain ⟨i, hi, hget, hpb, hbefore⟩ := find?_first hq
  rw [List.length_range] at hi
  rw [List.getElem_range] at hget
  subst hget
  refine ⟨hi, hpb, ?_⟩
  intro q' hq'
  have := hbefore q' hq'
  rwa [List.getElem_range] at this

theorem bailTime_some_intro {bail : List (Set X) → Bool} {h χ : List (Set X)}
    {q : ℕ} (hq : q < χ.length) (hfire : bail (h ++ χ.take q) = true)
    (hbef : ∀ q', q' < q → bail (h ++ χ.take q') = false) :
    bailTime bail h χ = some q := by
  unfold bailTime
  rw [List.find?_eq_some_iff_append]
  refine ⟨by simpa using hfire, List.range q,
    (List.range χ.length).drop (q + 1), ?_, ?_⟩
  · have hqr : q < (List.range χ.length).length := by
      rw [List.length_range]
      exact hq
    have h1 : List.range χ.length
        = (List.range χ.length).take q ++ (List.range χ.length).drop q :=
      (List.take_append_drop _ _).symm
    have h2 : (List.range χ.length).drop q
        = q :: (List.range χ.length).drop (q + 1) := by
      rw [List.drop_eq_getElem_cons hqr, List.getElem_range]
    conv_lhs => rw [h1, h2]
    rw [List.take_range, min_eq_left (le_of_lt hq)]
  · intro a ha
    rw [List.mem_range] at ha
    simp [hbef a ha]

end BailFacts


section ParkMain

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

theorem costOn_nil (E : EvaderAlgorithm Y) (h : List (Set Y)) :
    E.costOn h [] = 0 := by
  unfold EvaderAlgorithm.costOn
  rw [List.append_nil, sub_self]

theorem costOn_nilX (E : EvaderAlgorithm X) (h : List (Set X)) :
    E.costOn h [] = 0 := by
  unfold EvaderAlgorithm.costOn
  rw [List.append_nil, sub_self]

open Classical in
/-- **Park-shadow bail-cost domination**: against park-united requests, the
park-aware shadow with the transported-or-parked bail rule is dominated by
the original evader, the park bail financed by the separation. -/
theorem park_shadow_bailCost_le
    (π : Y → X) (G : Set X → Set Y) (Pk : Set Y)
    (hπ : ∀ y z : Y, dist (π y) (π z) ≤ dist y z)
    (hG : ∀ S : Set X, ∀ y ∈ G S, π y ∈ S)
    (hGne : ∀ S : Set X, S.Nonempty → (G S).Nonempty)
    (E : EvaderAlgorithm Y) (bail' : List (Set Y) → Bool)
    (h₀ : List (Set Y)) (h χ : List (Set X)) {pe p' sep J : ℝ}
    (hpe0 : 0 ≤ pe) (hpe : pe ≤ p') (hsep0 : 0 < sep)
    (hsep : ∀ (S : Set X) (y z : Y), y ∈ G S → z ∈ Pk → sep ≤ dist y z)
    (hstart : ∀ z ∈ Pk, sep ≤ dist (posY G Pk E h₀ h χ 0) z)
    (hdiam : ∀ x₁ x₂ : X, dist x₁ x₂ ≤ J)
    (harith : J + pe ≤ sep)
    (hchunk : ∀ q : ℕ, (hq : q < χ.length) → (χ[q] : Set X).Nonempty) :
    (parkShadow π G Pk hG hGne E h₀).bailCost
        (fun l => bail' (h₀ ++ parkMap G Pk l)
          || decide (E.pos (h₀ ++ parkMap G Pk l) ∈ Pk)) h χ pe
      ≤ E.bailCost bail' (h₀ ++ parkMap G Pk h) (parkMap G Pk χ) p' := by
  set SH := parkShadow π G Pk hG hGne E h₀ with hSH_def
  set bailI : List (Set X) → Bool := fun l => bail' (h₀ ++ parkMap G Pk l)
    || decide (E.pos (h₀ ++ parkMap G Pk l) ∈ Pk) with hbailI_def
  set PY : ℕ → Y := posY G Pk E h₀ h χ with hPY_def
  -- basic facts
  have hp'0 : 0 ≤ p' := le_trans hpe0 hpe
  have hpos0 : PY 0 ∉ Pk := by
    intro hmem
    have h1 := hstart _ hmem
    rw [dist_self] at h1
    linarith
  have hlenP : (parkMap G Pk χ).length = χ.length := parkMap_length G Pk χ
  -- the bail components at aligned prefixes
  have hbailI_at : ∀ q : ℕ, bailI (h ++ χ.take q)
      = (bail' ((h₀ ++ parkMap G Pk h) ++ (parkMap G Pk χ).take q)
        || decide (PY q ∈ Pk)) := by
    intro q
    rw [hbailI_def]
    show (bail' (h₀ ++ parkMap G Pk (h ++ χ.take q))
      || decide (E.pos (h₀ ++ parkMap G Pk (h ++ χ.take q)) ∈ Pk)) = _
    rw [theta_align G Pk h₀ h χ q]
    rfl
  -- membership of out-of-park positions in the mapped sets
  have hposG : ∀ q : ℕ, (hq : q < χ.length) → PY (q + 1) ∉ Pk →
      PY (q + 1) ∈ G (χ[q]'hq) := by
    intro q hq hout
    have := posY_mem G Pk E h₀ h χ hGne hq (hchunk q hq)
    exact this.resolve_right hout
  -- the E-side step expansion
  have hEstep : ∀ q : ℕ, (hq : q < χ.length) →
      E.costOn (h₀ ++ parkMap G Pk h) ((parkMap G Pk χ).take (q + 1))
        = E.costOn (h₀ ++ parkMap G Pk h) ((parkMap G Pk χ).take q)
          + dist (PY q) (PY (q + 1)) := by
    intro q hq
    rw [take_succ_park G Pk χ hq, E.costOn_concat]
    have h2 : E.pos ((h₀ ++ parkMap G Pk h) ++ (parkMap G Pk χ).take q
        ++ [G (χ[q]'hq) ∪ Pk]) = PY (q + 1) := by
      rw [List.append_assoc, ← take_succ_park G Pk χ hq]
      rfl
    rw [h2]
    rfl
  -- the shadow-side step expansion
  have hSstep : ∀ q : ℕ, q < χ.length →
      SH.costOn h (χ.take (q + 1))
        = SH.costOn h (χ.take q)
          + dist (SH.pos (h ++ χ.take q)) (SH.pos (h ++ χ.take (q + 1))) := by
    intro q hq
    rw [take_succ_chunk χ hq, SH.costOn_concat]
    congr 2
    rw [List.append_assoc, ← take_succ_chunk χ hq]
  -- entry steps are expensive
  have hentry : ∀ q : ℕ, q < χ.length → PY q ∉ Pk → PY (q + 1) ∈ Pk →
      sep ≤ dist (PY q) (PY (q + 1)) := by
    intro q hq hout hin
    rcases Nat.eq_zero_or_pos q with rfl | hqpos
    · exact hstart _ hin
    · obtain ⟨q', rfl⟩ : ∃ q'', q = q'' + 1 := ⟨q - 1, by omega⟩
      have hinG : PY (q' + 1) ∈ G χ[q'] := hposG q' (by omega) hout
      exact hsep _ _ _ hinG hin
  -- master prefix domination
  have hmaster : ∀ n : ℕ, n ≤ χ.length →
      (∀ q, 1 ≤ q → q < n → PY q ∉ Pk) →
      SH.costOn h (χ.take n)
        ≤ E.costOn (h₀ ++ parkMap G Pk h) ((parkMap G Pk χ).take n) := by
    intro n
    induction n with
    | zero =>
      intro _ _
      rw [List.take_zero, List.take_zero, costOn_nilX, costOn_nil]
    | succ n ih =>
      intro hn hint
      have hnlt : n < χ.length := by omega
      have hleft : PY n ∉ Pk := by
        rcases Nat.eq_zero_or_pos n with rfl | hnpos
        · exact hpos0
        · exact hint n hnpos (by omega)
      have hIH := ih (by omega) (fun q h1 h2 => hint q h1 (by omega))
      rw [hSstep n hnlt, hEstep n hnlt]
      have hposout := parkShadow_pos_out π G Pk E h₀ h χ hG hGne hleft
      by_cases hinq : PY (n + 1) ∈ Pk
      · -- final step parks: choice-jump ≤ J ≤ sep ≤ E-step
        have hSpos := parkShadow_pos_in π G Pk E h₀ h χ hG hGne hnlt
          (hchunk n hnlt) hinq
        rw [hposout, hSpos]
        have h1 : dist (π (PY n)) (hchunk n hnlt).choose ≤ J := hdiam _ _
        have h2 := hentry n hnlt hleft hinq
        have h3 : (J : ℝ) ≤ sep := by linarith
        linarith
      · have hSpos' := parkShadow_pos_out π G Pk E h₀ h χ hG hGne
          (q := n + 1) hinq
        rw [hposout, hSpos']
        have h1 := hπ (PY n) (PY (n + 1))
        linarith
  -- cost monotonicity on the E side
  have hEmono : ∀ q q' : ℕ, q ≤ q' →
      E.costOn (h₀ ++ parkMap G Pk h) ((parkMap G Pk χ).take q)
        ≤ E.costOn (h₀ ++ parkMap G Pk h) ((parkMap G Pk χ).take q') := by
    intro q q' hqq
    have hsplit : (parkMap G Pk χ).take q' = ((parkMap G Pk χ).take q').take q
        ++ (((parkMap G Pk χ).take q').drop q) := (List.take_append_drop _ _).symm
    rw [List.take_take, min_eq_left hqq] at hsplit
    rw [hsplit, E.costOn_append]
    have := E.costOn_nonneg ((h₀ ++ parkMap G Pk h) ++ (parkMap G Pk χ).take q)
      (((parkMap G Pk χ).take q').drop q)
    linarith
  -- the main case analysis
  unfold EvaderAlgorithm.bailCost
  rcases hQI : bailTime bailI h χ with _ | q
  · -- induced never bails
    have hall := bailTime_none_iff.mp hQI
    have hEnone : bailTime bail' (h₀ ++ parkMap G Pk h) (parkMap G Pk χ)
        = none := by
      rw [bailTime_none_iff]
      intro q hq
      rw [hlenP] at hq
      have h1 := hall q hq
      rw [hbailI_at q] at h1
      exact (Bool.or_eq_false_iff.mp h1).1
    rw [hEnone]
    have hint : ∀ q, 1 ≤ q → q < χ.length → PY q ∉ Pk := by
      intro q h1 h2
      have := hall q h2
      rw [hbailI_at q] at this
      have h3 := (Bool.or_eq_false_iff.mp this).2
      simpa using h3
    have := hmaster χ.length (le_refl _)  hint
    rw [List.take_length] at this
    rw [show (parkMap G Pk χ).take χ.length = parkMap G Pk χ by
      rw [← hlenP, List.take_length]] at this
    exact this
  · -- induced bails at q
    obtain ⟨hqlen, hfire, hbefore⟩ := bailTime_some_first hQI
    have hint : ∀ q', 1 ≤ q' → q' < q → PY q' ∉ Pk := by
      intro q' h1 h2
      have := hbefore q' h2
      rw [hbailI_at q'] at this
      have h3 := (Bool.or_eq_false_iff.mp this).2
      simpa using h3
    have hbefore' : ∀ q', q' < q →
        bail' ((h₀ ++ parkMap G Pk h) ++ (parkMap G Pk χ).take q') = false := by
      intro q' h2
      have := hbefore q' h2
      rw [hbailI_at q'] at this
      exact (Bool.or_eq_false_iff.mp this).1
    rw [hbailI_at q] at hfire
    rcases Bool.or_eq_true_iff.mp hfire with hb' | hpk
    · -- the transported bail fires at q: aligned resolution
      have hEfire : bailTime bail' (h₀ ++ parkMap G Pk h) (parkMap G Pk χ)
          = some q := by
        refine bailTime_some_intro (by rw [hlenP]; exact hqlen) hb' ?_
        intro q' h2
        exact hbefore' q' h2
      rw [hEfire]
      have hmq := hmaster q (le_of_lt hqlen) hint
      linarith
    · -- the park fires at q
      have hqpos : 1 ≤ q := by
        rcases Nat.eq_zero_or_pos q with rfl | h1
        · exact absurd (of_decide_eq_true hpk) hpos0
        · exact h1
      have hinPk : PY q ∈ Pk := of_decide_eq_true hpk
      have hleft : PY (q - 1) ∉ Pk := by
        rcases Nat.eq_zero_or_pos (q - 1) with h0 | h1
        · rw [h0]
          exact hpos0
        · exact hint (q - 1) h1 (by omega)
      -- induced cost: prefix (q-1) + jump + pe ≤ E-prefix (q-1) + sep ≤ E(take q)
      have hq1len : q - 1 < χ.length := by omega
      have hmq1 := hmaster (q - 1) (by omega) (fun a h1 h2 => hint a h1 (by omega))
      have hSsplit := hSstep (q - 1) hq1len
      rw [show q - 1 + 1 = q by omega] at hSsplit
      have hEsplit := hEstep (q - 1) hq1len
      rw [show q - 1 + 1 = q by omega] at hEsplit
      have hjump : dist (SH.pos (h ++ χ.take (q - 1))) (SH.pos (h ++ χ.take q))
          ≤ J := by
        have hposout := parkShadow_pos_out π G Pk E h₀ h χ hG hGne hleft
        have hSpos := parkShadow_pos_in π G Pk E h₀ h χ hG hGne hq1len
          (hchunk _ hq1len) (by rw [show q - 1 + 1 = q by omega]; exact hinPk)
        rw [show q - 1 + 1 = q by omega] at hSpos
        rw [hposout, hSpos]
        exact hdiam _ _
      have hcross : sep ≤ dist (PY (q - 1)) (PY q) := by
        have := hentry (q - 1) hq1len hleft
          (by rw [show q - 1 + 1 = q by omega]; exact hinPk)
        rwa [show q - 1 + 1 = q by omega] at this
      -- E side resolves at some q'' ≥ q or never; either way ≥ costOn(take q)
      have hEge : E.costOn (h₀ ++ parkMap G Pk h) ((parkMap G Pk χ).take q)
          ≤ E.bailCost bail' (h₀ ++ parkMap G Pk h) (parkMap G Pk χ) p' := by
        unfold EvaderAlgorithm.bailCost
        rcases hE : bailTime bail' (h₀ ++ parkMap G Pk h) (parkMap G Pk χ)
          with _ | q''
        · have h1 := hEmono q χ.length (le_of_lt hqlen)
          rw [show (parkMap G Pk χ).take χ.length = parkMap G Pk χ by
            rw [← hlenP, List.take_length]] at h1
          exact h1
        · obtain ⟨hq''len, hfire'', hbefore''⟩ := bailTime_some_first hE
          have hq''ge : q ≤ q'' := by
            by_contra hcon
            push_neg at hcon
            have := hbefore' q'' hcon
            rw [this] at hfire''
            exact absurd hfire'' (by simp)
          have h1 := hEmono q q'' hq''ge
          linarith
      unfold EvaderAlgorithm.bailCost at hEge
      calc SH.costOn h (χ.take q) + pe
          = SH.costOn h (χ.take (q - 1))
            + dist (SH.pos (h ++ χ.take (q - 1))) (SH.pos (h ++ χ.take q))
            + pe := by rw [← hSsplit]
        _ ≤ E.costOn (h₀ ++ parkMap G Pk h) ((parkMap G Pk χ).take (q - 1))
            + J + pe := by linarith
        _ ≤ E.costOn (h₀ ++ parkMap G Pk h) ((parkMap G Pk χ).take (q - 1))
            + sep := by linarith
        _ ≤ E.costOn (h₀ ++ parkMap G Pk h) ((parkMap G Pk χ).take q) := by
            rw [hEsplit]
            linarith
        _ ≤ E.bailCost bail' (h₀ ++ parkMap G Pk h) (parkMap G Pk χ) p' := hEge

end ParkMain

end KServer


