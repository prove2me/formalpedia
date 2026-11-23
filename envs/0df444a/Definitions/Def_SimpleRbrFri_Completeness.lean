-- Prove2me | Definitions.Def_SimpleRbrFri_Completeness
-- name    : SimpleRbrFri_Completeness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T09:02:38.161696+00:00
-- url     : https://prove2.me/theorems/7dc18098-cfeb-4e21-ae26-ed32c113ec25
-- title:
--   Completeness
-- statement:
--   Definitions and structural lemmas for Completeness, from zksecurity/simple-rbr-fri contributors (see pinned LICENSE and source headers)'s pinned Round-by-round soundness and completeness of FRI development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Completeness.lean

import Definitions.Def_SimpleRbrFri_Soundness
import Theorems.Thm_FRI_domain_zero_eq_D0

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
noncomputable def FRI_honest_fold (P : FRIParameters F) (i : Fin P.num_foldings)
    (f_prev : FRI_domain P i → F) (alpha : F) : FRI_domain P (i + 1) → F :=
  fun z => Fold (FRI_domain P i) (P.m i) (extend_by_zero (FRI_domain P i) f_prev) alpha z.val
noncomputable def FRI_honest_messages (P : FRIParameters F) (f_0 : P.D_0 → F)
    (alpha : Fin P.num_foldings → F) :
    (i : Fin (P.num_foldings + 1)) → FRI_domain P i → F
  | 0 => fun x => f_0 ⟨x.val, (FRI_domain_zero_eq_D0 P) ▸ x.property⟩
  | ⟨i + 1, hi⟩ =>
    if h : i < P.num_foldings then
      have : i < P.num_foldings + 1 := Nat.lt_trans h (Nat.lt_succ_self _)
      FRI_honest_fold P ⟨i, h⟩ (FRI_honest_messages P f_0 alpha ⟨i, this⟩) (alpha ⟨i, h⟩)
    else
      fun _ => 0
noncomputable def FRI_honest_transcript (P : FRIParameters F) (f_0 : P.D_0 → F)
    (challenges : FRIVerifierChallenges P) : FRITranscript P :=
  { f := fun i => FRI_honest_messages P f_0 challenges.alpha i.succ,
    alpha := challenges.alpha,
    s := challenges.s }
noncomputable def poly_decompose (m : ℕ) (p : Polynomial F) (i : Fin m) : Polynomial F :=
  ∑ j ∈ Finset.range ((p.natDegree + 1) / m + 1),
    Polynomial.C (p.coeff (j * m + i)) * Polynomial.X ^ j
noncomputable def folded_poly (m : ℕ) (p : Polynomial F) (alpha : F) : Polynomial F :=
  ∑ i : Fin m, Polynomial.C (alpha ^ (i : ℕ)) * poly_decompose m p i


