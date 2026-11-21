-- Prove2me | solution 1 for AlgoPrinciplesMulticlass.NoEnvelope.pac_learner_image_ds_infinite
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T09:53:00.009029+00:00
-- url     : https://prove2.me/submissions/9ac2b64d-67bb-45bd-be8d-bf5e033fc6f9

import Mathlib
import Theorems.Thm_AlgoPrinciplesMulticlass_NoEnvelope_lemma_3_3
import Theorems.Thm_AlgoPrinciplesMulticlass_NoEnvelope_condition1_ds_ge
import Theorems.Thm_AlgoPrinciplesMulticlass_NoEnvelope_condition2_impossible
universe u

section
namespace AlgoPrinciplesMulticlass
open NoEnvelope MeasureTheory


instance : Countable Pt := by
  have : Function.Injective (fun x : Pt => (⟨x.d, (x.v, x.j)⟩ : Σ d : ℕ, List (Fin d → Bool) × Fin d)) := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    simp only [Sigma.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [heq_eq_eq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  exact this.countable

theorem rand_ds_top (R : RandLearner.{u} Pt Label) (hR : R.PACLearns H) :
    MulticlassDS.Compress.dsDim R.image = ⊤ := by
  by_contra hne
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hne
  have h1 : 1 ≤ n + 1 := by omega
  rcases NoEnvelope.lemma_3_3 R.image (n + 1) h1 with hc | hc
  · have := NoEnvelope.condition1_ds_ge R.image (n + 1) h1 hc
    rw [← hn] at this
    exact absurd (by exact_mod_cast this : n + 1 ≤ n) (by omega)
  · exact NoEnvelope.condition2_impossible R hR (n + 1) h1 hc

theorem chk_pac_learner_image_ds_infinite :
    (∀ R : RandLearner.{u} Pt Label, R.PACLearns H →
      MulticlassDS.Compress.dsDim R.image = ⊤) ∧
    (∀ A : Learner Pt Label, PACLearns A H →
      MulticlassDS.Compress.dsDim A.image = ⊤) := by
  refine ⟨rand_ds_top, fun A hA => ?_⟩
  have himg : (RandLearner.ofLearner A).image = A.image := by
    ext f; constructor
    · rintro ⟨_, m, S, rfl⟩; exact ⟨m, S, rfl⟩
    · rintro ⟨m, S, rfl⟩; exact ⟨(), m, S, rfl⟩
  rw [← himg]
  refine rand_ds_top.{0} _ ?_
  intro ε δ h1 h2 h3 h4
  obtain ⟨n, hn⟩ := hA ε δ h1 h2 h3 h4
  refine ⟨n, fun m hm hstar hH D hD => ?_⟩
  refine le_trans (le_of_eq ?_) (hn m hm hstar hH D hD)
  letI : MeasurableSpace Pt := ⊤
  unfold RandLearner.failProb failProb
  simp only [RandLearner.ofLearner]
  have key : ∀ T : Set ((Fin m → Pt) × Unit), ((Measure.pi fun _ : Fin m => D).prod (Measure.dirac ())) T
      = (Measure.pi fun _ : Fin m => D) ((fun xs => (xs, ())) ⁻¹' T) := by
    intro T
    rw [Measure.prod_dirac, Measure.map_apply (by fun_prop) (Set.to_countable _).measurableSet]
  exact key {p | ENNReal.ofReal ε < popLoss D (A m (labelSample hstar p.1)) hstar}
end AlgoPrinciplesMulticlass
end

theorem solution : type_of% @AlgoPrinciplesMulticlass.chk_pac_learner_image_ds_infinite := @AlgoPrinciplesMulticlass.chk_pac_learner_image_ds_infinite
