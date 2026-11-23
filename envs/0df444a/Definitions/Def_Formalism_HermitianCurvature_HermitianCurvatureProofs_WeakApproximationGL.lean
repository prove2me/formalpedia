-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:46:58.811923+00:00
-- url     : https://prove2.me/theorems/db024e40-89ef-4c99-8397-007f382364e3
-- title:
--   Weak Approximation GL
-- statement:
--   Definitions and structural lemmas for Weak Approximation GL, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakApproximationGL.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G1_card_UT
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_card_UT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
namespace Formalism.FourierDecayAlt.P.WeakApproximationGL
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G5
abbrev FinalTheorems (m : ℕ) : Type := Fin (m + 1) ⊕ UT (m + 2)
abbrev Tgt (m : ℕ) : Type := Unit ⊕ (Fin m ⊕ (UT (m + 1) ⊕ Fin (m + 1)))
def cls {m : ℕ} (i : Fin (m + 1)) (j : Fin (m + 2)) (h : i.succ ≤ j) : FinalTheorems m :=
  if h' : i.succ = j then Sum.inl i else Sum.inr ⟨(i.succ, j), lt_of_le_of_ne h h'⟩
theorem succ_le_castSucc {m : ℕ} {i j : Fin (m + 1)} (h : i < j) : i.succ ≤ j.castSucc := by
  rw [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc]
  exact h
def idx (m : ℕ) : Tgt m → FinalTheorems m
  | Sum.inl _ => Sum.inr ⟨(0, Fin.last (m + 1)), Fin.last_pos⟩
  | Sum.inr (Sum.inl k) => Sum.inr ⟨(0, k.succ.castSucc), by
      rw [Fin.lt_def]; simp⟩
  | Sum.inr (Sum.inr (Sum.inl q)) => cls q.1.1 q.1.2.castSucc (succ_le_castSucc q.2)
  | Sum.inr (Sum.inr (Sum.inr i)) => cls i (Fin.last (m + 1)) (Fin.le_last _)
theorem idx_surjective (m : ℕ) : Function.Surjective (idx m) := by
  rintro (i | ⟨⟨a, b⟩, hab⟩)
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | rfl
    · refine ⟨Sum.inr (Sum.inr (Sum.inl ⟨(k.castSucc, k.succ), Fin.castSucc_lt_succ⟩)), ?_⟩
      show cls k.castSucc k.succ.castSucc (succ_le_castSucc Fin.castSucc_lt_succ) = Sum.inl k.castSucc
      unfold cls
      exact dif_pos rfl
    · exact ⟨Sum.inr (Sum.inr (Sum.inr (Fin.last m))), by simp [idx, cls]⟩
  · rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨i, rfl⟩
    · rcases Fin.eq_castSucc_or_eq_last b with ⟨c, rfl⟩ | rfl
      · rcases Fin.eq_zero_or_eq_succ c with rfl | ⟨k, rfl⟩
        · simp at hab
        · exact ⟨Sum.inr (Sum.inl k), rfl⟩
      · exact ⟨Sum.inl (), rfl⟩
    · rcases Fin.eq_castSucc_or_eq_last b with ⟨c, rfl⟩ | rfl
      · have hic : i < c := by
          rw [Fin.lt_def] at hab ⊢
          simp only [Fin.val_succ, Fin.val_castSucc] at hab
          omega
        exact ⟨Sum.inr (Sum.inr (Sum.inl ⟨(i, c), hic⟩)), by simp [idx, cls, ne_of_lt hab]⟩
      · exact ⟨Sum.inr (Sum.inr (Sum.inr i)), by simp [idx, cls, ne_of_lt hab]⟩
theorem card_eq (m : ℕ) : Fintype.card (Tgt m) = Fintype.card (FinalTheorems m) := by
  simp only [Tgt, FinalTheorems, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin,
    Formalism.FourierDecayAlt.P.G5.card_UT, Finset.sum_range_succ]
  ring
theorem idx_bijective (m : ℕ) : Function.Bijective (idx m) :=
  (Fintype.bijective_iff_surjective_and_card _).mpr ⟨idx_surjective m, card_eq m⟩
noncomputable def idxE (m : ℕ) : Tgt m ≃ FinalTheorems m := Equiv.ofBijective (idx m) (idx_bijective m)
def split (m : ℕ) (v : Tgt m → ℂ) : RedCoord m :=
  (v (Sum.inl ()), fun k => v (Sum.inr (Sum.inl k)), fun q => v (Sum.inr (Sum.inr (Sum.inl q))),
    fun i => v (Sum.inr (Sum.inr (Sum.inr i))))
end Formalism.FourierDecayAlt.P.WeakApproximationGL
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.WeakApproximationGL
end Formalism.FourierDecayAlt.P


