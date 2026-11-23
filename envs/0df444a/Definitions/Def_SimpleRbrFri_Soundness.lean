-- Prove2me | Definitions.Def_SimpleRbrFri_Soundness
-- name    : SimpleRbrFri_Soundness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T09:00:31.827921+00:00
-- url     : https://prove2.me/theorems/6126dac3-93a5-47a8-a5a0-1097ef348ac1
-- title:
--   Soundness
-- statement:
--   Definitions and structural lemmas for Soundness, from zksecurity/simple-rbr-fri contributors (see pinned LICENSE and source headers)'s pinned Round-by-round soundness and completeness of FRI development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Soundness.lean

import Definitions.Def_SimpleRbrFri_QuerySoundness
set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
  [MeasurableSpace F] [DiscreteMeasurableSpace F]
open scoped Classical in
/--
Probability of state transition at folding round i:
`Pr_α[State(T, i) = 0 ∧ State(T with α_i := α, i+1) = 1]`

This is the probability over random verifier challenge α that the state changes from 0 to 1.
When State(i) = 0, this equals the probability of the bad event occurring.
-/
noncomputable def FRI_State_Transition_Prob_Fold [Fintype F]
    (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ)
    (T : FRITranscript P) (i : Fin P.num_foldings) : ℝ :=
  if FRI_State P f_0 bound T i then 0
  else FRI_BadEvent_Prob P f_0 bound i (FRI_oracle_at_round P f_0 T i i.isLt)
open scoped Classical in
/--
Probability of state transition at query round:
`Pr_s[State(T, k) = 0 ∧ State(T with s := s, k+1) = 1]`

This is the probability over random query points s that the state changes from 0 to 1.
When State(k) = 0, this equals the probability that all query points pass local checks.
-/
noncomputable def FRI_State_Transition_Prob_Query [Fintype F]
    [MeasurableSpace F] [DiscreteMeasurableSpace F]
    (P : FRIParameters F) (f_0 : P.D_0 → F) (bound : ℝ) (T : FRITranscript P) : ENNReal :=
  if FRI_State P f_0 bound T P.num_foldings then 0
  else FRI_query_prob P f_0 bound T


