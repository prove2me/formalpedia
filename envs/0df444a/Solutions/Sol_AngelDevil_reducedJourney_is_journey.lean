-- Prove2me | solution 1 for AngelDevil.reducedJourney_is_journey
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-18T12:58:56.906056+00:00
-- url     : https://prove2.me/submissions/b5e68d92-4b5a-41c1-bd2c-27a41a0c3b4d

import Definitions.Def_AngelDevil_ReducedJourney

namespace AngelDevil

theorem reducedJourney_nil (p : Nat) : reducedJourney p [] = [] := by
  rw [reducedJourney]
  simp

theorem reducedJourney_return (p : Nat) (h : List Point) (hne : h ≠ [])
    (hend : h.getLastD origin = origin) : reducedJourney p h = [origin] := by
  rw [reducedJourney]
  simp only [hne, ↓reduceDIte, hend, ↓reduceIte]

theorem reducedJourney_nonempty (p : Nat) (h : List Point) (hne : h ≠ []) :
    reducedJourney p h ≠ [] := by
  rw [reducedJourney]
  simp only [hne, ↓reduceDIte]
  split
  · simp
  · split <;> simp

theorem reducedJourney_endpoint (p : Nat) (h : List Point) (hne : h ≠ []) :
    (reducedJourney p h).getLastD origin = h.getLastD origin := by
  rw [reducedJourney]
  simp only [hne, ↓reduceDIte]
  split
  · rename_i he
    simpa using he.symm
  · split <;> simp

theorem firstReachable_jump (p : Nat) (h : List Point) (z : Point)
    (hi : firstReachable p h z < h.length) :
    Jump p h[firstReachable p h z] z := by
  exact of_decide_eq_true (List.findIdx_getElem (w := hi))

theorem firstReachable_minimal (p : Nat) (h : List Point) (z : Point) (j : Nat)
    (hj : j < firstReachable p h z) :
    ¬ Jump p (h[j]'(Nat.lt_of_lt_of_le hj List.findIdx_le_length)) z := by
  have hfalse := List.not_of_lt_findIdx hj
  simpa using hfalse

theorem last_lookup (h : List Point) (hne : h ≠ []) :
    h[h.length-1]? = some (h.getLastD origin) := by
  rw [← List.getLast?_eq_getElem?]
  simp only [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne,
    Option.getD_some]

theorem journey_take (p : Nat) (h : List Point) (hj : Journey p h)
    (k : Nat) (hk : 0 < k) : Journey p (h.take k) := by
  constructor
  · simpa [List.head?_take, Nat.ne_of_gt hk] using hj.1
  · intro i u v hu hv
    have hi : i+1 < k := by
      apply Classical.byContradiction
      intro hn
      simp [List.getElem?_take, hn] at hv
    rw [List.getElem?_take, if_pos (by omega)] at hu
    rw [List.getElem?_take, if_pos hi] at hv
    exact hj.2 i u v hu hv

theorem journey_dropLast (p : Nat) (h : List Point) (hj : Journey p h)
    (hl : 1 < h.length) : Journey p h.dropLast := by
  constructor
  · simpa [List.head?_dropLast, hl] using hj.1
  · intro i u v hu hv
    have hi : i+1 < h.length-1 := by
      apply Classical.byContradiction
      intro hn
      simp [hn] at hv
    rw [List.getElem?_dropLast, if_pos (by omega)] at hu
    rw [List.getElem?_dropLast, if_pos hi] at hv
    exact hj.2 i u v hu hv

theorem journey_append (p : Nat) (h : List Point) (hj : Journey p h) (z : Point)
    (hjump : Jump p (h.getLastD origin) z) : Journey p (h ++ [z]) := by
  have hne : h ≠ [] := by intro e; have hh := hj.1; rw [e] at hh; contradiction
  have hpos := List.length_pos_iff.mpr hne
  constructor
  · simp [List.head?_append, hj.1]
  · intro i u v hu hv
    have hil : i+1 < (h ++ [z]).length := (List.getElem?_eq_some_iff.mp hv).1
    simp only [List.length_append, List.length_singleton] at hil
    by_cases hin : i+1 < h.length
    · rw [List.getElem?_append_left (by omega)] at hu
      rw [List.getElem?_append_left hin] at hv
      exact hj.2 i u v hu hv
    · have he : i+1 = h.length := by omega
      have hei : i = h.length-1 := by omega
      rw [List.getElem?_append_left (by omega), hei, last_lookup h hne] at hu
      rw [List.getElem?_append_right (by omega), he] at hv
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hv
      cases hu
      subst v
      exact hjump

theorem journey_last_has_predecessor (p : Nat) (h : List Point) (hj : Journey p h)
    (hz : h.getLastD origin ≠ origin) :
    firstReachable p h.dropLast (h.getLastD origin) < h.dropLast.length := by
  have hne : h ≠ [] := by intro e; have hh := hj.1; rw [e] at hh; contradiction
  have hpos := List.length_pos_iff.mpr hne
  have hl : 1 < h.length := by
    apply Classical.byContradiction
    intro hn
    have he : h.length = 1 := by omega
    have hlast := last_lookup h hne
    have hfirst := hj.1
    rw [List.head?_eq_getElem?] at hfirst
    simp only [he, Nat.sub_self] at hlast
    rw [hfirst] at hlast
    exact hz (Option.some.inj hlast).symm
  let j := h.length-2
  have hjl : j < h.length := by omega
  have hpred : h[j]? = some h[j] := List.getElem?_eq_getElem hjl
  have hlast : h[j+1]? = some (h.getLastD origin) := by
    have : j+1 = h.length-1 := by omega
    rw [this]; exact last_lookup h hne
  have hstep := hj.2 j h[j] _ hpred hlast
  apply List.findIdx_lt_length_of_exists
  refine ⟨h[j], ?_, by simpa using hstep⟩
  apply List.mem_of_getElem? (i := j)
  rw [List.getElem?_dropLast, if_pos (by omega)]
  exact hpred

theorem take_last (h : List Point) (i : Nat) (hi : i < h.length) :
    (h.take (i+1)).getLastD origin = h[i] := by
  simp [List.getLastD_eq_getLast?, List.getLast?_take,
    List.getElem?_eq_getElem hi]

theorem reducedJourney_is_journey (p : Nat) (h : List Point) (hj : Journey p h) :
    Journey p (reducedJourney p h) := by
  induction h using reducedJourney.induct p with
  | case1 => simp [Journey] at hj
  | case2 h hne z hz =>
      rw [reducedJourney_return p h hne hz]
      constructor
      · rfl
      · intro i u v hu hv
        have := (List.getElem?_eq_some_iff.mp hv).1
        simp at this
  | case3 h hne z hz prior i hi ih =>
      dsimp only [z, prior, i] at hz hi ih
      have hl : 1 < h.length := by
        have : 0 < h.dropLast.length := Nat.lt_of_le_of_lt (Nat.zero_le _) hi
        simp only [List.length_dropLast] at this
        omega
      have hprior := journey_take p h.dropLast (journey_dropLast p h hj hl)
        (firstReachable p h.dropLast (h.getLastD origin)+1) (by omega)
      have hpriorne : h.dropLast.take (firstReachable p h.dropLast (h.getLastD origin)+1) ≠ [] := by
        intro e
        have hh := hprior.1
        rw [e] at hh
        contradiction
      rw [reducedJourney]
      simp only [hne, ↓reduceDIte, hz, ↓reduceIte, hi]
      apply journey_append p _ (ih hprior)
      rw [reducedJourney_endpoint _ _ hpriorne, take_last _ _ hi]
      exact firstReachable_jump p _ _ hi
  | case4 h hne z hz prior i hbad =>
      exact False.elim (hbad (journey_last_has_predecessor p h hj hz))

end AngelDevil


theorem solution (p : Nat) (h : List AngelDevil.Point) (hj : AngelDevil.Journey p h) : AngelDevil.Journey p (AngelDevil.reducedJourney p h) := AngelDevil.reducedJourney_is_journey p h hj
