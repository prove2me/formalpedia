-- Prove2me | solution 1 for AlgoPrinciplesMulticlass.NoEnvelope.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T09:53:00.129245+00:00
-- url     : https://prove2.me/submissions/f358bd41-a944-42b4-99ae-bed8e7fdf896

import Mathlib
import Theorems.Thm_AlgoPrinciplesMulticlass_NoEnvelope_lemma_3_2
import Theorems.Thm_AlgoPrinciplesMulticlass_NoEnvelope_learnable_ds_finite
import Theorems.Thm_AlgoPrinciplesMulticlass_NoEnvelope_pac_learner_image_ds_infinite

section
namespace AlgoPrinciplesMulticlass

theorem chk_theorem_3_1 :
    ∃ (X : Type) (Y : Type) (Hc : Set (X → Y)), NoEnvelope.PACLearnable Hc ∧
      ∀ Hprop : Set (X → Y), Hc ⊆ Hprop → ¬ NoEnvelope.ProperlyPACLearnable Hprop := by
  refine ⟨NoEnvelope.Pt, NoEnvelope.Label, NoEnvelope.H, ?_, ?_⟩
  · refine ⟨NoEnvelope.refLearner, ?_⟩
    intro ε δ hε hε1 hδ hδ1
    refine ⟨⌈-Real.log δ / ε⌉₊ + 1, ?_⟩
    intro m hm hstar hH D hD
    have hm1 : 1 ≤ m := by omega
    refine (NoEnvelope.lemma_3_2 hstar hH D hD ε hε hε1 m hm1).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have h1 : -Real.log δ / ε ≤ (m : ℝ) := by
      have := Nat.le_ceil (-Real.log δ / ε)
      have h2 : ((⌈-Real.log δ / ε⌉₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
      push_cast at h2; linarith
    have h3 : -Real.log δ ≤ m * ε := by
      rw [div_le_iff₀ hε] at h1; exact h1
    calc Real.exp (-((m : ℝ) * ε)) ≤ Real.exp (Real.log δ) := by
          apply Real.exp_le_exp.2; linarith
      _ = δ := Real.exp_log hδ
  · intro Hprop hsub ⟨A, hprop, hpac⟩
    have hAH : NoEnvelope.PACLearns A NoEnvelope.H := by
      intro ε δ h1 h2 h3 h4
      obtain ⟨n, hn⟩ := hpac ε δ h1 h2 h3 h4
      exact ⟨n, fun m hm hstar hH D hD => hn m hm hstar (hsub hH) D hD⟩
    have hinf := (NoEnvelope.pac_learner_image_ds_infinite.{0}.2 A hAH)
    have hfin := NoEnvelope.learnable_ds_finite Hprop ⟨A, hpac⟩
    have hsubset : A.image ⊆ Hprop := by
      rintro f ⟨m, S, rfl⟩; exact hprop m S
    have mono : MulticlassDS.Compress.dsDim A.image ≤ MulticlassDS.Compress.dsDim Hprop := by
      unfold MulticlassDS.Compress.dsDim
      refine iSup_le fun n => iSup_le fun S => iSup_le fun hS => ?_
      obtain ⟨B, hB, hpc⟩ := hS
      refine le_iSup_of_le n (le_iSup_of_le S (le_iSup_of_le ⟨B, ?_, hpc⟩ le_rfl))
      refine hB.trans ?_
      rintro _ ⟨f, hf, rfl⟩
      exact ⟨f, hsubset hf, rfl⟩
    rw [hinf] at mono
    exact absurd (top_le_iff.1 mono) hfin.ne
end AlgoPrinciplesMulticlass
end

theorem solution : type_of% @AlgoPrinciplesMulticlass.chk_theorem_3_1 := @AlgoPrinciplesMulticlass.chk_theorem_3_1
