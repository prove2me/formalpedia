-- Prove2me | solution 1 for AngelDevil.reducedJourney_allowed
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-18T13:16:52.667424+00:00
-- url     : https://prove2.me/submissions/97eeb292-fd7e-40ce-9b4b-c045518e225a

import Definitions.Def_AngelDevil_NiceReduction
import Theorems.Thm_AngelDevil_reducedJourney_is_journey

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

theorem reducedJourney_sublist (p : Nat) (h : List Point) :
    (reducedJourney p h).Sublist h := by
  induction h using reducedJourney.induct p with
  | case1 => simp [reducedJourney_nil]
  | case2 h hne z hz =>
      rw [reducedJourney_return p h hne hz]
      apply List.singleton_sublist.mpr
      dsimp only [z] at hz
      have hh := List.mem_of_getElem? (last_lookup h hne)
      simpa only [hz] using hh
  | case3 h hne z hz prior i hi ih =>
      dsimp only [z, prior, i] at hz hi ih
      rw [reducedJourney]
      simp only [hne, ↓reduceDIte, hz, ↓reduceIte, hi]
      have hs := (ih.trans (List.take_sublist _ _)).append_right [h.getLastD origin]
      have he : h.dropLast ++ [h.getLastD origin] = h := by
        simpa [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
          using List.dropLast_concat_getLast hne
      rw [he] at hs
      exact hs
  | case4 h hne z hz prior i hbad =>
      dsimp only [z, prior, i] at hz hbad
      rw [reducedJourney]
      simp only [hne, ↓reduceDIte, hz, ↓reduceIte, hbad]
      exact List.singleton_sublist.mpr (List.mem_of_getElem? (last_lookup h hne))

theorem reducedJourney_length_le (p : Nat) (h : List Point) :
    (reducedJourney p h).length ≤ h.length :=
  (reducedJourney_sublist p h).length_le

/- No vertex strictly before the selected predecessor can reach the endpoint.
This is the exclusion needed when the Nice filter could suppress a Devil move. -/
theorem firstReachable_excludes_earlier (p : Nat) (h : List Point) (z v : Point)
    (hv : v ∈ h.take (firstReachable p h z)) : ¬ Jump p v z := by
  obtain ⟨j, hj, he⟩ := List.mem_take_iff_getElem.mp hv
  have hh := firstReachable_minimal p h z j (by omega)
  simpa only [he] using hh

theorem take_dropLast_of_le (h : List Point) (k : Nat) (hk : k ≤ h.length-1) :
    h.dropLast.take k = h.take k := by
  rw [List.dropLast_eq_take, List.take_take, Nat.min_eq_left hk]

/- Every nonempty reduced prefix is itself the reduction of an original prefix.
The witness is an index in the original history, not a reduced-list index. -/
theorem reducedJourney_prefix (p : Nat) (h : List Point) (s : Nat)
    (hs : s < (reducedJourney p h).length) :
    ∃ k, k < h.length ∧
      reducedJourney p (h.take (k+1)) = (reducedJourney p h).take (s+1) := by
  induction h using reducedJourney.induct p generalizing s with
  | case1 => simp [reducedJourney_nil] at hs
  | case2 h hne z hz =>
      have hr := reducedJourney_return p h hne hz
      rw [hr] at hs ⊢
      have : s = 0 := by simpa using hs
      subst s
      have hl := List.length_pos_iff.mpr hne
      refine ⟨h.length-1, by omega, ?_⟩
      rw [show h.length-1+1 = h.length by omega, List.take_length, hr]
      rfl
  | case3 h hne z hz prior i hi ih =>
      dsimp only [z, prior, i] at hz hi ih
      let q := h.dropLast.take (firstReachable p h.dropLast (h.getLastD origin)+1)
      have hr : reducedJourney p h = reducedJourney p q ++ [h.getLastD origin] := by
        rw [reducedJourney]
        simp only [hne, ↓reduceDIte, hz, ↓reduceIte, hi, q]
      rw [hr] at hs ⊢
      by_cases hs' : s < (reducedJourney p q).length
      · obtain ⟨k, hk, he⟩ := ih s hs'
        simp only [List.length_take] at hk
        have hk' : k+1 ≤ firstReachable p h.dropLast (h.getLastD origin)+1 := by
          omega
        have hlen : firstReachable p h.dropLast (h.getLastD origin) < h.length-1 := by
          simpa only [List.length_dropLast] using hi
        refine ⟨k, by omega, ?_⟩
        rw [List.take_append_of_le_length (by omega)]
        simpa only [List.take_take, Nat.min_eq_left hk',
          take_dropLast_of_le h (k+1) (by omega)] using he
      · have hl := List.length_pos_iff.mpr hne
        have he : s+1 = (reducedJourney p q ++ [h.getLastD origin]).length := by
          simp only [List.length_append, List.length_singleton] at hs ⊢
          omega
        refine ⟨h.length-1, by omega, ?_⟩
        rw [show h.length-1+1 = h.length by omega, List.take_length, hr, he,
          List.take_length]
  | case4 h hne z hz prior i hbad =>
      dsimp only [z, prior, i] at hz hbad
      have hr : reducedJourney p h = [h.getLastD origin] := by
        rw [reducedJourney]
        simp only [hne, ↓reduceDIte, hz, ↓reduceIte, hbad]
      rw [hr] at hs ⊢
      have : s = 0 := by simpa using hs
      subst s
      have hl := List.length_pos_iff.mpr hne
      refine ⟨h.length-1, by omega, ?_⟩
      rw [show h.length-1+1 = h.length by omega, List.take_length, hr]
      rfl


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

theorem allowed_take (p : Nat) (D : DevilStrategy) (h : List Point)
    (ha : Allowed p D h) (k : Nat) (hk : 0 < k) : Allowed p D (h.take k) := by
  refine ⟨journey_take p h ha.1 k hk, ?_⟩
  intro i j z hij hz
  have hjk : j < k := by
    apply Classical.byContradiction
    intro hn
    simp [List.getElem?_take, hn] at hz
  rw [List.getElem?_take, if_pos hjk] at hz
  simpa only [List.take_take, Nat.min_eq_left (by omega : i+1 ≤ k)]
    using ha.2 i j z hij hz

theorem endpoint_eligible_at_earlier_prefix (p : Nat) (h : List Point)
    (hz : h.getLastD origin ≠ origin) (k : Nat)
    (hi : firstReachable p h.dropLast (h.getLastD origin) < h.dropLast.length)
    (hk : k ≤ firstReachable p h.dropLast (h.getLastD origin)) :
    NiceEligible p (h.take (k+1)) (h.getLastD origin) := by
  refine ⟨hz, ?_⟩
  intro v hv
  have hlen : firstReachable p h.dropLast (h.getLastD origin) < h.length-1 := by
    simpa only [List.length_dropLast] using hi
  rw [List.dropLast_take (by omega : k+1 < h.length)] at hv
  simp only [Nat.add_sub_cancel] at hv
  apply firstReachable_excludes_earlier p h.dropLast (h.getLastD origin) v
  rw [take_dropLast_of_le h _ (by omega)]
  exact (List.take_sublist_take_left hk).subset hv

/- Mathe Claim 2.6: the transformed Devil preserves legality on reduction. -/
theorem reducedJourney_allowed (p : Nat) (D : DevilStrategy) (h : List Point)
    (ha : Allowed p (niceReduction p D) h) : Allowed p D (reducedJourney p h) := by
  induction h using reducedJourney.induct p with
  | case1 => simp [Allowed, Journey] at ha
  | case2 h hne z hz =>
      refine ⟨reducedJourney_is_journey p h ha.1, ?_⟩
      rw [reducedJourney_return p h hne hz]
      intro s t v hst hv
      have ht := (List.getElem?_eq_some_iff.mp hv).1
      simp only [List.length_singleton] at ht
      omega
  | case3 h hne z hz prior i hi ih =>
      dsimp only [z, prior, i] at hz hi ih
      let a := firstReachable p h.dropLast (h.getLastD origin)
      let q := h.dropLast.take (a+1)
      have hlen : a < h.length-1 := by
        simpa only [List.length_dropLast] using hi
      have hq : q = h.take (a+1) := take_dropLast_of_le h _ (by omega)
      have haq : Allowed p (niceReduction p D) q := by
        rw [hq]
        exact allowed_take p _ h ha (a+1) (by omega)
      have hred : Allowed p D (reducedJourney p q) := ih haq
      have hr : reducedJourney p h = reducedJourney p q ++ [h.getLastD origin] := by
        rw [reducedJourney]
        simp only [hne, ↓reduceDIte, hz, ↓reduceIte, hi, q, a]
      refine ⟨reducedJourney_is_journey p h ha.1, ?_⟩
      rw [hr]
      intro s t v hst hv he
      have ht := (List.getElem?_eq_some_iff.mp hv).1
      simp only [List.length_append, List.length_singleton] at ht
      by_cases ht' : t < (reducedJourney p q).length
      · rw [List.getElem?_append_left ht'] at hv
        rw [List.take_append_of_le_length (by omega)] at he
        exact hred.2 s t v hst hv he
      · have hte : t = (reducedJourney p q).length := by omega
        rw [List.getElem?_append_right (by omega), hte] at hv
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hv
        subst v
        obtain ⟨k, hk, hprefix⟩ := reducedJourney_prefix p q s (by omega)
        have hkbound : k ≤ a := by
          have : q.length ≤ a+1 := by
            dsimp only [q]
            rw [List.length_take]
            exact Nat.min_le_left _ _
          omega
        have hprefix' : reducedJourney p (h.take (k+1)) =
            (reducedJourney p q).take (s+1) := by
          rw [hq, List.take_take, Nat.min_eq_left (by omega : k+1 ≤ a+1)] at hprefix
          simpa only [hq] using hprefix
        rw [List.take_append_of_le_length (by omega), ← hprefix'] at he
        have hn : niceReduction p D (h.take (k+1)) = some (h.getLastD origin) := by
          apply (niceReduction_eq_some_iff p D _ _).mpr
          exact ⟨he, endpoint_eligible_at_earlier_prefix p h hz k hi hkbound⟩
        exact ha.2 k (h.length-1) (h.getLastD origin) (by omega)
          (last_lookup h hne) hn
  | case4 h hne z hz prior i hbad =>
      exact False.elim (hbad (journey_last_has_predecessor p h ha.1 hz))


end AngelDevil

open AngelDevil
theorem solution (p : Nat) (D : DevilStrategy) (h : List Point)
    (ha : Allowed p (niceReduction p D) h) : Allowed p D (reducedJourney p h)  := by
  exact AngelDevil.reducedJourney_allowed p D h ha
