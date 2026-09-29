-- Prove2me | solution 1 for AGT.single_parameter_characterization
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-13T14:31:58.385449+00:00
-- url     : https://prove2.me/submissions/97279304-ec1e-4d4e-9a87-2ec4b79e02f7

import Definitions.Def_agt_mechanism
import Mathlib.Tactic.Linarith
import Mathlib.Order.Interval.Set.Basic

/-!
# Theorem 9.36: characterization of truthful single-parameter mechanisms
-/

namespace SPHelp

open AGT

variable {A ι : Type*} [DecidableEq ι]
variable {W : ι → Set A} {t0 t1 : ℝ} {f : (ι → ℝ) → A} {p : ι → (ι → ℝ) → ℝ}

omit [DecidableEq ι] in
lemma spValue_win {i : ι} {x : ℝ} {a : A} (h : a ∈ W i) : spValue W i x a = x := by
  simp [spValue, h]

omit [DecidableEq ι] in
lemma spValue_lose {i : ι} {x : ℝ} {a : A} (h : a ∉ W i) : spValue W i x a = 0 := by
  simp [spValue, h]

lemma update_mem {t : ι → ℝ} (ht : ∀ j, t j ∈ Set.Icc t0 t1) (i : ι) {s : ℝ}
    (hs : s ∈ Set.Icc t0 t1) : ∀ j, Function.update t i s j ∈ Set.Icc t0 t1 := by
  intro j
  by_cases hj : j = i
  · subst hj; simpa [Function.update_apply] using hs
  · simpa [Function.update_apply, hj] using ht j

lemma update_self_eq (t : ι → ℝ) (i : ι) : Function.update t i (t i) = t := by
  funext j
  by_cases hj : j = i <;> simp [Function.update_apply, hj]

lemma update_update (t : ι → ℝ) (i : ι) (x s : ℝ) :
    Function.update (Function.update t i x) i s = Function.update t i s := by
  funext j
  by_cases hj : j = i <;> simp [Function.update_apply, hj]

/-- Incentive compatibility applied at an arbitrary true value `x` for player `i`,
with the other players' bids fixed by `t`. -/
lemma ic_apply (hIC : SPIncentiveCompatible W t0 t1 f p) {t : ι → ℝ}
    (ht : ∀ j, t j ∈ Set.Icc t0 t1) (i : ι) {x s : ℝ}
    (hx : x ∈ Set.Icc t0 t1) (hs : s ∈ Set.Icc t0 t1) :
    spValue W i x (f (Function.update t i s)) - p i (Function.update t i s) ≤
      spValue W i x (f (Function.update t i x)) - p i (Function.update t i x) := by
  have h := hIC (Function.update t i x) (update_mem ht i hx) i s hs
  have hxi : (Function.update t i x) i = x := by simp
  rw [hxi, update_update] at h
  exact h

end SPHelp

open SPHelp AGT

/-- **Theorem 9.36.** A normalized mechanism on a single-parameter domain is
incentive compatible iff the rule is monotone and winners pay the critical
value. -/
theorem solution {A ι : Type*} [Fintype ι]
    [DecidableEq ι] (W : ι → Set A) (t0 t1 : ℝ) (h01 : t0 ≤ t1)
    (f : (ι → ℝ) → A) (p : ι → (ι → ℝ) → ℝ)
    (hnorm : SPNormalized W t0 t1 f p) :
    SPIncentiveCompatible W t0 t1 f p ↔
      SPMonotone W t0 t1 f ∧ SPCriticalPayments W t0 t1 f p := by
  constructor
  · intro hIC
    refine ⟨?_, ?_⟩
    · -- monotonicity
      intro t ht i s hs s' hs' hss hwin
      by_contra hlose
      have hp' : p i (Function.update t i s') = 0 :=
        hnorm _ (update_mem ht i hs') i hlose
      have h1 := ic_apply hIC ht i hs' hs
      rw [spValue_win hwin, spValue_lose hlose, hp'] at h1
      have h2 := ic_apply hIC ht i hs hs'
      rw [spValue_lose hlose, spValue_win hwin, hp'] at h2
      have hEq : s = s' := le_antisymm hss (by linarith)
      rw [hEq] at hwin
      exact hlose hwin
    · -- critical payments
      intro t ht i
      by_cases hW : ∃ s ∈ Set.Icc t0 t1, f (Function.update t i s) ∈ W i
      · obtain ⟨s0, hs0, hw0⟩ := hW
        have key : ∀ s ∈ Set.Icc t0 t1, f (Function.update t i s) ∈ W i →
            p i (Function.update t i s) = p i (Function.update t i s0) := by
          intro s hs hws
          have h1 := ic_apply hIC ht i hs hs0
          rw [spValue_win hw0, spValue_win hws] at h1
          have h2 := ic_apply hIC ht i hs0 hs
          rw [spValue_win hws, spValue_win hw0] at h2
          linarith
        refine ⟨p i (Function.update t i s0), key, ?_⟩
        intro hL
        -- `c ≤ s0` : a winner never pays more than their bid
        obtain ⟨r0, hr0, hrl0⟩ := hL
        have hpr0 : p i (Function.update t i r0) = 0 :=
          hnorm _ (update_mem ht i hr0) i hrl0
        have hle : ∀ s ∈ Set.Icc t0 t1, f (Function.update t i s) ∈ W i →
            p i (Function.update t i s) ≤ s := by
          intro s hs hws
          have h := ic_apply hIC ht i hs hr0
          rw [spValue_lose hrl0, spValue_win hws, hpr0] at h
          linarith
        constructor
        · rintro r ⟨hr, hrl⟩
          have hpr : p i (Function.update t i r) = 0 :=
            hnorm _ (update_mem ht i hr) i hrl
          have h := ic_apply hIC ht i hr hs0
          rw [spValue_win hw0, spValue_lose hrl, hpr] at h
          linarith
        · intro u hu
          by_contra hlt
          push_neg at hlt
          -- `u < c`; pick `m` strictly between
          set c := p i (Function.update t i s0) with hc
          have hu0 : t0 ≤ u := le_trans hr0.1 (hu ⟨hr0, hrl0⟩)
          have hcs0 : c ≤ s0 := hle s0 hs0 hw0
          have hm : (u + c) / 2 ∈ Set.Icc t0 t1 :=
            ⟨by linarith, by linarith [hs0.2]⟩
          have hmwin : f (Function.update t i ((u + c) / 2)) ∈ W i := by
            by_contra hml
            have : (u + c) / 2 ≤ u := hu ⟨hm, hml⟩
            linarith
          have := hle _ hm hmwin
          rw [key _ hm hmwin] at this
          linarith
      · push_neg at hW
        refine ⟨t1, ?_, ?_⟩
        · intro s hs hws
          exact absurd hws (hW s hs)
        · intro _
          have hset : {s | s ∈ Set.Icc t0 t1 ∧ f (Function.update t i s) ∉ W i}
              = Set.Icc t0 t1 := by
            ext s
            exact ⟨fun h => h.1, fun h => ⟨h, hW s h⟩⟩
          rw [hset]
          exact isLUB_Icc h01
  · rintro ⟨hmono, hcrit⟩
    intro t ht i s hs
    obtain ⟨c, hcwin, hclub⟩ := hcrit t ht i
    have hx : t i ∈ Set.Icc t0 t1 := ht i
    have hself := update_self_eq t i
    by_cases hws : f (Function.update t i s) ∈ W i <;>
      by_cases hwx : f t ∈ W i
    · -- both win
      have h1 : p i (Function.update t i s) = c := hcwin s hs hws
      have h2 : p i t = c := by
        have := hcwin (t i) hx (by rw [hself]; exact hwx)
        rwa [hself] at this
      rw [spValue_win hws, spValue_win hwx, h1, h2]
    · -- misreport wins, truth loses
      have h1 : p i (Function.update t i s) = c := hcwin s hs hws
      have h2 : p i t = 0 := hnorm t ht i hwx
      have hlub : IsLUB {s | s ∈ Set.Icc t0 t1 ∧ f (Function.update t i s) ∉ W i} c := by
        refine hclub ⟨t i, hx, ?_⟩
        rw [hself]; exact hwx
      have : t i ≤ c := hlub.1 ⟨hx, by rw [hself]; exact hwx⟩
      rw [spValue_win hws, spValue_lose hwx, h1, h2]
      linarith
    · -- misreport loses, truth wins
      have h1 : p i (Function.update t i s) = 0 :=
        hnorm _ (update_mem ht i hs) i hws
      have h2 : p i t = c := by
        have := hcwin (t i) hx (by rw [hself]; exact hwx)
        rwa [hself] at this
      have hlub : IsLUB {s | s ∈ Set.Icc t0 t1 ∧ f (Function.update t i s) ∉ W i} c :=
        hclub ⟨s, hs, hws⟩
      have hub : t i ∈ upperBounds
          {s | s ∈ Set.Icc t0 t1 ∧ f (Function.update t i s) ∉ W i} := by
        rintro r ⟨hr, hrl⟩
        by_contra hlt
        push_neg at hlt
        exact hrl (hmono t ht i (t i) hx r hr (le_of_lt hlt) (by rw [hself]; exact hwx))
      have : c ≤ t i := hlub.2 hub
      rw [spValue_lose hws, spValue_win hwx, h1, h2]
      linarith
    · -- both lose
      have h1 : p i (Function.update t i s) = 0 :=
        hnorm _ (update_mem ht i hs) i hws
      have h2 : p i t = 0 := hnorm t ht i hwx
      rw [spValue_lose hws, spValue_lose hwx, h1, h2]