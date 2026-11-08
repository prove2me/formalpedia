-- Prove2me | solution 1 for AssignToSeatRM.supported_choice_no_loss
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:32:30.760204+00:00
-- url     : https://prove2.me/submissions/05eb6096-fe2a-49ee-b567-96f691d681c3

import Mathlib
import Definitions.Def_AssignToSeatRM_Basic
import Definitions.Def_AssignToSeatRM_DynamicPrimal
import Definitions.Def_AssignToSeatRM_Dynamic

set_option autoImplicit false
open Classical
open scoped BigOperators


open AssignToSeatRM in
theorem solution {M : ℕ} (p : ℕ → ℕ → ℝ) (hp : IsPriceVec M p)
    (A : ℕ → ℕ → ℕ) (d : ℕ → ℕ → ℝ) (hd : ∀ ij ∈ itins M, 0 ≤ d ij.1 ij.2)
    (γ : Idx4 → ℝ) (hγ : IsOptimalOPT M p (fun u v => (A u v : ℝ)) d 0 γ)
    (o : Idx4) (ho : o ∈ gammaIdx M) (h1 : 1 ≤ γ o) :
    OPT M p (fun u v => (A u v : ℝ)) d (Pi.single o 1) =
      OPT M p (fun u v => (A u v : ℝ)) d 0 := by
  have hfeas : ∀ γ', IsFeasOPT M (fun u v => (A u v : ℝ)) d (Pi.single o 1) γ' →
      IsFeasOPT M (fun u v => (A u v : ℝ)) d 0 γ' := by
    rintro γ' ⟨a, b, c, e⟩
    refine ⟨a, b, fun c' hc' => ?_, e⟩
    have hc := c c' hc'
    have h0 : (0 : ℝ) ≤ (Pi.single o (1 : ℝ) : Idx4 → ℝ) c' := by
      rw [Pi.single_apply]; split_ifs <;> norm_num
    show (0 : ℝ) ≤ γ' c'
    linarith
  have hγs : IsFeasOPT M (fun u v => (A u v : ℝ)) d (Pi.single o 1) γ := by
    obtain ⟨a, b, c, e⟩ := hγ.1
    refine ⟨a, b, fun c' hc' => ?_, e⟩
    rw [Pi.single_apply]
    split_ifs with h
    · rw [h]; exact h1
    · exact c c' hc'
  unfold OPT
  have e1 : sSup (dpObjective M p '' {γ' | IsFeasOPT M (fun u v => (A u v : ℝ)) d
      (Pi.single o 1) γ'}) = dpObjective M p γ := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨γ, hγs, rfl⟩, ?_⟩
    rintro _ ⟨γ', hγ', rfl⟩
    exact hγ.2 γ' (hfeas γ' hγ')
  have e2 : sSup (dpObjective M p '' {γ' | IsFeasOPT M (fun u v => (A u v : ℝ)) d
      0 γ'}) = dpObjective M p γ := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨γ, hγ.1, rfl⟩, ?_⟩
    rintro _ ⟨γ', hγ', rfl⟩
    exact hγ.2 γ' hγ'
  rw [e1, e2]
