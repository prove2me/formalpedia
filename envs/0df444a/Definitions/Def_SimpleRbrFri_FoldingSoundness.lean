-- Prove2me | Definitions.Def_SimpleRbrFri_FoldingSoundness
-- name    : SimpleRbrFri_FoldingSoundness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T08:57:14.913229+00:00
-- url     : https://prove2.me/theorems/ea6f09bb-e29a-4b4d-b6d1-2ca520f0cc9d
-- title:
--   Folding Soundness
-- statement:
--   Definitions and structural lemmas for Folding Soundness, from zksecurity/simple-rbr-fri contributors (see pinned LICENSE and source headers)'s pinned Round-by-round soundness and completeness of FRI development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/FoldingSoundness.lean

import Definitions.Def_SimpleRbrFri_State
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
omit [Field F] in
/-
If $S \subseteq T$, then $S^m \subseteq T^m$.
-/
lemma pow_domain_subset [CommMonoid F] {S T : Finset F} {m : ℕ} (h : S ⊆ T) :
  pow_domain S m ⊆ pow_domain T m := Finset.image_subset_image h
noncomputable def cast_folding_components {F : Type*} [Field F] [DecidableEq F]
    (P : FRIParameters F) (i : Fin P.num_foldings) (f_prev : FRI_domain P i → F) :
    Fin (P.m i) → (FRI_domain P (i.succ) → F) :=
  let components := folding_components (FRI_domain P i) (P.m i)
    (extend_by_zero (FRI_domain P i) f_prev)
  let h_eq := FRI_domain_succ_eq P i i.isLt
  fun j x => components j ⟨x.1, h_eq ▸ x.2⟩
section FRI_Error_Functions
def FRI_round_error_fold (P : FRIParameters F) (bound : ℝ) (errorstar : ℕ → ℝ → ℝ)
    (i : Fin P.num_foldings) (delta : ℝ) : ℝ :=
  let delta_star := FRI_delta_star bound delta
  errorstar (P.m i) delta_star
end FRI_Error_Functions
section FRI_Probabilities
variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
  [MeasurableSpace F] [DiscreteMeasurableSpace F]
noncomputable def FRI_fold_prob (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (i : Fin P.num_foldings) (f_prev : FRI_domain P i → F) : ENNReal :=
  (PMF.uniformOfFintype F).toMeasure { alpha | FRI_BadEvent P f_0 bound i f_prev alpha }
end FRI_Probabilities
section FRI_Folding_Soundness
end FRI_Folding_Soundness


