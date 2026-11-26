-- Prove2me | solution 1 for Arxiv2405_10327.weak_form_decouples_forward_operator
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T00:44:59.292059+00:00
-- url     : https://prove2.me/submissions/65b83e5c-076e-437f-9f2b-15dcd944fc60

import Mathlib
import Definitions.Def_Arxiv2405_10327_Basic

set_option autoImplicit false

namespace S74WD
open Arxiv2405_10327

lemma grad_aff {n : ℕ} (c a : ℝ) (g : Vec n → ℝ) (x : Vec n) :
    gradient (fun y => c + a * g y) x = a • gradient g x := by
  unfold gradient
  have : (fun y => c + a * g y) = fun y => c + (a • g) y := by
    funext y; simp [smul_eq_mul]
  rw [this, fderiv_const_add, fderiv_const_smul_field]
  simp

end S74WD

open Arxiv2405_10327 S74WD in
theorem solution {d m p M : ℕ} {C : Type*}
    (hM : 0 < M) (σ γ : ℝ) (hσ : 0 < σ) (hγ : 0 < γ)
    (F : Vec d → Vec m) (yobs : Vec m)
    (fInv : Vec d → C → Vec d) (ybar : C) (hfInv : ∀ c, Function.Bijective (fun u => fInv u c))
    (h : Vec p → Vec d → Vec d) (hh : ∀ φ, Function.Bijective (h φ) ∧ Differentiable ℝ (h φ))
    (z : Fin M → Vec d) :
    (∀ (x : Fin M → Vec d) (φ : Vec p),
      weakObjective σ γ F yobs fInv ybar h z x φ =
        (1 / (M : ℝ)) * (∑ i, dataMisfit σ F yobs (x i))
          + (1 / (M : ℝ)) * innerLoss γ fInv ybar h z x φ) ∧
    (∀ (x : Fin M → Vec d) (φ : Vec p),
      gradient (fun φ' => weakObjective σ γ F yobs fInv ybar h z x φ') φ =
        (1 / (M : ℝ)) • gradient (fun φ' => innerLoss γ fInv ybar h z x φ') φ) ∧
    (∀ (x : Fin M → Vec d) (φ : Vec p),
      (∀ φ', weakObjective σ γ F yobs fInv ybar h z x φ ≤ weakObjective σ γ F yobs fInv ybar h z x φ') ↔
        (∀ φ', innerLoss γ fInv ybar h z x φ ≤ innerLoss γ fInv ybar h z x φ')) ∧
    (∀ (x : Fin M → Vec d) (φ : Vec p) (i : Fin M),
      gradient (fun v => weakObjective σ γ F yobs fInv ybar h z (Function.update x i v) φ) (x i) =
        (1 / (M : ℝ)) • gradient (outerLoss σ γ F yobs fInv ybar (h φ) (z i)) (x i)) := by
  have hsplit : ∀ (x : Fin M → Vec d) (φ : Vec p),
      weakObjective σ γ F yobs fInv ybar h z x φ =
        (1 / (M : ℝ)) * (∑ i, dataMisfit σ F yobs (x i))
          + (1 / (M : ℝ)) * innerLoss γ fInv ybar h z x φ := by
    intro x φ
    unfold weakObjective innerLoss
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => by ring)
  have hMpos : (0:ℝ) < 1 / (M : ℝ) := by
    have : (0:ℝ) < M := by exact_mod_cast hM
    positivity
  refine ⟨hsplit, fun x φ => ?_, fun x φ => ?_, fun x φ i => ?_⟩
  · have : (fun φ' => weakObjective σ γ F yobs fInv ybar h z x φ') =
        fun φ' => (1 / (M : ℝ)) * (∑ i, dataMisfit σ F yobs (x i)) +
          (1 / (M : ℝ)) * innerLoss γ fInv ybar h z x φ' := by
      funext φ'; exact hsplit x φ'
    rw [this, grad_aff]
  · simp only [hsplit]
    constructor
    · intro hle φ'
      have := hle φ'
      have := le_of_mul_le_mul_left (by linarith : (1 / (M:ℝ)) * innerLoss γ fInv ybar h z x φ ≤
        (1 / (M:ℝ)) * innerLoss γ fInv ybar h z x φ') hMpos
      exact this
    · intro hle φ'
      have := mul_le_mul_of_nonneg_left (hle φ') hMpos.le
      linarith
  · set K : ℝ := (1 / (M : ℝ)) * ((∑ j ∈ Finset.univ.erase i, (dataMisfit σ F yobs (x j)
        + ‖x j - corrected fInv ybar (h φ) (z j)‖ ^ 2 / (2 * γ ^ 2)
        + latentTerm (h φ) (z j))) + latentTerm (h φ) (z i)) with hK
    have : (fun v => weakObjective σ γ F yobs fInv ybar h z (Function.update x i v) φ) =
        fun v => K + (1 / (M : ℝ)) * outerLoss σ γ F yobs fInv ybar (h φ) (z i) v := by
      funext v
      unfold weakObjective outerLoss
      rw [hK, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self]
      have : ∑ j ∈ Finset.univ.erase i, (dataMisfit σ F yobs (Function.update x i v j)
          + ‖Function.update x i v j - corrected fInv ybar (h φ) (z j)‖ ^ 2 / (2 * γ ^ 2)
          + latentTerm (h φ) (z j)) =
          ∑ j ∈ Finset.univ.erase i, (dataMisfit σ F yobs (x j)
          + ‖x j - corrected fInv ybar (h φ) (z j)‖ ^ 2 / (2 * γ ^ 2)
          + latentTerm (h φ) (z j)) := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      rw [this]
      ring
    rw [this, grad_aff]
