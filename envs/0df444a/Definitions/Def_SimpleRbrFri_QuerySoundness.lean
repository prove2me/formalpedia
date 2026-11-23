-- Prove2me | Definitions.Def_SimpleRbrFri_QuerySoundness
-- name    : SimpleRbrFri_QuerySoundness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T08:59:33.367444+00:00
-- url     : https://prove2.me/theorems/d6979115-84cf-4f0f-8b4e-64a443a2a7b1
-- title:
--   Query Soundness
-- statement:
--   Definitions and structural lemmas for Query Soundness, from zksecurity/simple-rbr-fri contributors (see pinned LICENSE and source headers)'s pinned Round-by-round soundness and completeness of FRI development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/QuerySoundness.lean

import Definitions.Def_SimpleRbrFri_FoldingSoundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
lemma FRI_green_set_subset_domain (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P)
    (i : ℕ) :
    FRI_green_set P f_0 T i ⊆ FRI_domain P i := by
  classical exact Finset.filter_subset _ _
def FRI_agreement_at_round (P : FRIParameters F) (f_0 : P.D_0 → F)
    (T : FRITranscript P) (i : Fin (P.num_foldings + 1)) : Prop :=
  ∃ u ∈ FRI_code P i, ∀ x (hx : x ∈ FRI_green_set P f_0 T i),
    let hx_domain : x ∈ FRI_domain P i := FRI_green_set_subset_domain P f_0 T i hx
    u ⟨x, hx_domain⟩ = FRI_get_val P f_0 T i x


