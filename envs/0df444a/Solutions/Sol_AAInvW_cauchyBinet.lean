-- Prove2me | solution 1 for AAInvW.cauchyBinet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:29:34.442608+00:00
-- url     : https://prove2.me/submissions/9d12f36e-75da-4232-a4ed-e1b8d1631dd4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAAv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CauchyBinet
import Theorems.Thm_AAInvW_grouping
import Theorems.Thm_AAInvW_det_mul_expand

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
theorem _root_.solution {m N : ℕ} (κ : Fin N → ℕ) (hκ : Function.Injective κ)
    (X : Matrix (Fin m) (Fin N) ℂ) (Y : Matrix (Fin N) (Fin m) ℂ) :
    (X * Y).det = ∑ C : Fin m → Fin N,
      if StrictMono (fun l => κ (C l)) then
        (Matrix.of fun a l => X a (C l)).det * (Matrix.of fun i l => Y (C i) l).det else 0 := by
  have hF : ∀ (d : Fin m → Fin N) (τ : Equiv.Perm (Fin m)),
      (Matrix.of fun a l => X a ((d ∘ τ) l)).det =
        ((Equiv.Perm.sign τ : ℤ) : ℂ) * (Matrix.of fun a l => X a (d l)).det := by
    intro d τ
    exact Matrix.det_permute' τ (Matrix.of fun a l => X a (d l))
  have hF0 : ∀ d : Fin m → Fin N, ¬ Function.Injective d → (Matrix.of fun a l => X a (d l)).det = 0 := by
    intro d hd
    simp only [Function.Injective, not_forall] at hd
    obtain ⟨p, q, hpq, hne⟩ := hd
    exact Matrix.det_zero_of_column_eq hne (fun a => by simp [hpq])
  rw [det_mul_expand X Y]
  rw [grouping κ hκ (fun d => (Matrix.of fun a l => X a (d l)).det) hF hF0 (fun d => ∏ l, Y (d l) l)]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  split_ifs with h
  · rw [smul_eq_mul, mul_comm]
    congr 1
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    simp [Units.smul_def, zsmul_eq_mul]
  · rfl
end AAInvW
