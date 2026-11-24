-- Prove2me | solution 1 for AAInvW.collapse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:31:27.34075+00:00
-- url     : https://prove2.me/submissions/cd4e432c-4356-484a-93ae-92fd78ea502f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAAv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CauchyBinet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open AAInvW
namespace AAInvW
theorem _root_.solution {A : Type*} [AddCommGroup A] [Module ℂ A] {N r m : ℕ} (hm : m ≤ r)
    (φ : Fin r → Fin N) (hφ : Function.Injective φ) (w : Fin N → Fin N → ℂ)
    (hw : ∀ (a : Fin r) (i : Fin N), (∀ b : Fin r, b.val < a.val → i ≠ φ b) →
      w i (φ a) = if i = φ a then 1 else 0)
    (q : (Fin m → Fin N) → A) (hq : ∀ c : Fin m → Fin N, ¬ Function.Injective c → q c = 0) :
    ∑ c : Fin m → Fin N, (∏ j, w (c j) (φ (Fin.castLE hm j))) • q c =
      q (fun j => φ (Fin.castLE hm j)) := by
  have hone : ∀ j : Fin m, w (φ (Fin.castLE hm j)) (φ (Fin.castLE hm j)) = 1 := by
    intro j
    have h := hw (Fin.castLE hm j) (φ (Fin.castLE hm j)) (fun b hb hb' => by
      have := hφ hb'
      rw [this] at hb
      exact lt_irrefl _ hb)
    rw [h, if_pos rfl]
  rw [Finset.sum_eq_single (fun j => φ (Fin.castLE hm j))]
  · simp only [hone, Finset.prod_const_one, one_smul]
  · intro c _ hc
    by_cases hinj : Function.Injective c
    · have hex : ∃ j, w (c j) (φ (Fin.castLE hm j)) = 0 := by
        by_contra hall
        push_neg at hall
        apply hc
        funext j
        obtain ⟨k, hk⟩ := j
        revert hk
        refine Nat.strong_induction_on k ?_
        intro k ih hk
        by_cases hex : ∃ b : Fin r, b.val < k ∧ c ⟨k, hk⟩ = φ b
        · obtain ⟨b, hbk, hb⟩ := hex
          have hbm : b.val < m := lt_trans hbk hk
          have e1 : c ⟨b.val, hbm⟩ = φ (Fin.castLE hm ⟨b.val, hbm⟩) := ih b.val hbk hbm
          have e2 : Fin.castLE hm ⟨b.val, hbm⟩ = b := Fin.ext rfl
          rw [e2] at e1
          have e3 := hinj (e1.trans hb.symm)
          have e4 : b.val = k := congrArg Fin.val e3
          omega
        · push_neg at hex
          have hw' := hw (Fin.castLE hm ⟨k, hk⟩) (c ⟨k, hk⟩) (fun b hb => hex b hb)
          have hne := hall ⟨k, hk⟩
          rw [hw'] at hne
          by_contra hcon
          exact hne (if_neg hcon)
      obtain ⟨j, hj⟩ := hex
      rw [Finset.prod_eq_zero (Finset.mem_univ j) hj, zero_smul]
    · rw [hq c hinj, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
end AAInvW
