-- Prove2me | solution 1 for AffirmativeChoice.Reserve.theorem_1_forward
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T16:03:50.304669+00:00
-- url     : https://prove2.me/submissions/b6150929-1c1a-460d-b6bb-232f2f2e1947

import Mathlib
import Definitions.Def_AffirmativeChoice_Reserve_Model
import Theorems.Thm_AffirmativeChoice_Reserve_canonical_reserve_represents
import Theorems.Thm_AffirmativeChoice_Reserve_canonical_satisfies_B1
import Theorems.Thm_AffirmativeChoice_Reserve_canonical_satisfies_B2
import Theorems.Thm_AffirmativeChoice_Reserve_canonical_satisfies_B3_i
import Theorems.Thm_AffirmativeChoice_Reserve_canonical_satisfies_B3_ii

open AffirmativeChoice.Reserve

theorem solution {𝒮 : Type*} [Fintype 𝒮] [DecidableEq 𝒮] [Nonempty 𝒮]
    (q : ℕ) (hq : 3 ≤ q) (C : ChoiceRule 𝒮 q)
    (hAA : IsAffirmativeActionRule C) (hsub : Substitutable C)
    (hMPI : MPI C) (hMTC : MTC C) :
    HasBoundedReserveRep C := by
  obtain ⟨hR, hRep⟩ := canonical_reserve_represents q hq C hAA hsub
  exact ⟨canonicalReserve C, hR,
    ⟨canonical_satisfies_B1 q hq C hAA hsub hMPI hMTC,
     canonical_satisfies_B2 q hq C hAA hsub hMPI hMTC,
     canonical_satisfies_B3_i q hq C hAA hsub hMPI hMTC,
     canonical_satisfies_B3_ii q hq C hAA hsub hMPI hMTC⟩, hRep⟩
