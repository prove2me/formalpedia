-- Prove2me | Definitions.Def_mme_stothers_phi233_hash_state_instances
-- name    : mme_stothers_phi233_hash_state_instances
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-03T00:11:47.240584+00:00
-- url     : https://prove2.me/theorems/5bad584b-75eb-4dc0-ab1d-dd9ea05408d2
-- title:
--   Finite instance for the Phi233 hash-state space
-- statement:
--   The affine hash state used for the cyclic Phi233 extraction is finite. It consists of 6N+1 coordinates over the finite field Z/pZ together with one offset coordinate. This module supplies the canonical finite enumeration and decidable equality needed for summing incidences over all hash states and applying finite averaging.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Section 3.2, pp. 356--360; finite random hash-state space.

import Mathlib.Data.Fintype.Pi
import Definitions.Def_mme_stothers_phi233_hash_retention_data

namespace MME.StothersFourth.Phi233

set_option autoImplicit false

/-- Canonical finite enumeration of the Phi233 affine hash state space. -/
noncomputable instance hashStateFintype (p N : ℕ) [Fact p.Prime] :
    Fintype (HashState p N) := by
  unfold HashState HashIndex
  infer_instance

/-- Classical decidable equality on the finite Phi233 hash state space. -/
noncomputable instance hashStateDecidableEq (p N : ℕ) :
    DecidableEq (HashState p N) :=
  Classical.decEq _

end MME.StothersFourth.Phi233


