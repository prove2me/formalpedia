-- Prove2me | Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseKOneHolds
-- name    : Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseKOneHolds
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:14:25.703917+00:00
-- url     : https://prove2.me/theorems/c5580d44-8dba-4d97-aeea-0a7de5d1e6c7
-- title:
--   Base Case KOne Holds
-- statement:
--   Definitions and structural lemmas for Base Case KOne Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusBaseCase/FrobeniusBaseCaseProofs/BaseCaseKOneHolds.lean

import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
namespace Formalism.BaseCaseIdentities
noncomputable section
open Classical
def ratVal (l : ℕ) [Fact l.Prime] : AddValuation ℚ (WithTop ℝ) :=
  AddValuation.of (fun x => if x = 0 then ⊤ else ((padicValRat l x : ℝ) : WithTop ℝ))
    (by simp) (by simp)
    (by
      intro x y
      by_cases hx : x = 0
      · simp [hx]
      by_cases hy : y = 0
      · simp [hy]
      by_cases hxy : x + y = 0
      · simp [hxy]
      simp only [hx, hy, hxy, if_false]
      have h := padicValRat.min_le_padicValRat_add (p := l) hxy
      rcases le_total (padicValRat l x) (padicValRat l y) with h1 | h1
      · rw [min_eq_left h1] at h
        refine le_trans (min_le_left _ _) ?_
        exact_mod_cast h
      · rw [min_eq_right h1] at h
        refine le_trans (min_le_right _ _) ?_
        exact_mod_cast h)
    (by
      intro x y
      by_cases hx : x = 0
      · simp [hx]
      by_cases hy : y = 0
      · simp [hy]
      simp only [hx, hy, mul_eq_zero, or_self, if_false]
      rw [padicValRat.mul hx hy]
      push_cast
      rfl)
theorem ratVal_apply (l : ℕ) [Fact l.Prime] {x : ℚ} (hx : x ≠ 0) :
    ratVal l x = ((padicValRat l x : ℝ) : WithTop ℝ) := by
  simp [ratVal, hx]
theorem ratVal_l (l : ℕ) [hl : Fact l.Prime] : ratVal l (l : ℚ) = 1 := by
  rw [ratVal_apply l (by exact_mod_cast hl.out.ne_zero)]
  simp [padicValRat.self hl.out.one_lt]
theorem ratVal_l_inv (l : ℕ) [hl : Fact l.Prime] : ratVal l (l : ℚ)⁻¹ = ((-1 : ℝ) : WithTop ℝ) := by
  have h0 : (l : ℚ) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  rw [ratVal_apply l (inv_ne_zero h0), padicValRat.inv, padicValRat.self hl.out.one_lt]
  simp
def exData (l i : ℕ) (hl : l.Prime) (hl3 : 3 ≤ l) (hi : Odd i) : Data ℚ Unit (Fin 2) :=
  haveI : Fact l.Prime := ⟨hl⟩
  { v := ratVal l
    l := l
    l_prime := hl
    l_ge := hl3
    v_l := ratVal_l l
    i := i
    i_odd := hi
    good := fun _ => True
    lev := fun c => c.val
    pure_good := fun _ _ => trivial
    ι := fun _ => 0
    ι_inj := fun _ _ _ => rfl
    ι_lev := fun _ => rfl
    al := fun c j b => if c = 0 ∧ j = 2 ∧ b = 1 then (l : ℚ)⁻¹ else 0
    g := fun c b => if c = 0 ∧ b = 1 then 1 else 0
    lam := fun _ _ => 0
    al_all := by
      intro c j b
      split_ifs with h
      · obtain ⟨_, rfl, _⟩ := h
        rw [ratVal_l_inv]
        exact_mod_cast (by norm_num : (-((2 : ℕ) : ℝ)) ≤ -1)
      · simp
    al_good := by
      intro c _ j b _
      split_ifs with h
      · obtain ⟨_, rfl, _⟩ := h
        rw [ratVal_l_inv]
        exact_mod_cast (by norm_num : (-(((2 : ℕ) : ℝ) - 1)) ≤ -1)
      · simp
    al_one := by
      intro c _ b
      simp
    al_two := by
      intro c _ b
      by_cases h : c = 0 ∧ b = 1
      · simp [h]
      · have : ¬ (c = 0 ∧ 2 = 2 ∧ b = 1) := by tauto
        simp [h]
    g_int := by
      intro c b
      split_ifs <;> simp
    lam_int := by
      intro c b
      simp
    g_supp := by
      intro c _ b hb
      by_cases h : c = 0 ∧ b = 1
      · obtain ⟨rfl, rfl⟩ := h
        exact absurd rfl hb
      · simp [h] }
end
end Formalism.BaseCaseIdentities


