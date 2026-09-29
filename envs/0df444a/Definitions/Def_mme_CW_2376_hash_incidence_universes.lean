-- Prove2me | Definitions.Def_mme_CW_2376_hash_incidence_universes
-- name    : mme_CW_2376_hash_incidence_universes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-24T22:06:20.461176+00:00
-- url     : https://prove2.me/theorems/b783872a-ed0d-4da9-b0da-aa0221466d9e
-- title:
--   Finite address and augmented hash-state universes for CW incidence counting
-- statement:
--   This module fixes the finite universes used in the outer Coppersmith--Winograd incidence double count: all marginal-supported addresses at scale $m$, all exact-profile target edges, all directed target-to-ambient collisions, and all augmented affine hash states with $N+1$ weights and one offset. It also evaluates the retained full marginal hypergraph at an augmented state, deliberately ignoring the final dummy weight.
--
--   Packaging these universes once isolates the finite-type instances and lets the target-survival and collision counts be summed without repeating subtype enumeration details.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), outer hashing and collision deletion on journal pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_CW_2376_augmented_hash_states

namespace MME

noncomputable def cw2376MarginalSupportedUniverse (m : ℕ) :
    Finset (CW2376MarginalSupportedAddress m) := by
  classical
  letI : Fintype (CW2376ProfileAddress m) :=
    inferInstanceAs (Fintype
      (Fin 3 → Fin (cw2376ProfileLength m) → Fin 5))
  letI : Fintype (CW2376MarginalSupportedAddress m) :=
    inferInstanceAs (Fintype
      {a : CW2376ProfileAddress m //
        CW2376CoordinatewiseSupported a ∧ CW2376MarginallyRegular a})
  exact Finset.univ

noncomputable def cw2376AugmentedHashStateUniverse
    (m p : ℕ) [NeZero p] :
    Finset ((Fin (cw2376ProfileLength m + 1) → ZMod p) × ZMod p) := by
  classical
  exact Finset.univ

noncomputable def cw2376RetainedEdgesAtAugmentedState
    (m p : ℕ) [NeZero p] (S : Finset ℕ)
    (q : (Fin (cw2376ProfileLength m + 1) → ZMod p) × ZMod p) :
    Finset (CW2376MarginalSupportedAddress m) :=
  cw2376MarginalHashRetainedEdges m p S q.2
    (fun j => q.1 j.castSucc)

noncomputable def cw2376AllExactTargetEdges (m : ℕ) :
    Finset (CW2376MarginalSupportedAddress m) :=
  cw2376ExactTargetEdges (cw2376MarginalSupportedUniverse m)

noncomputable def cw2376AllTargetAmbientCollisions (m : ℕ) :
    Finset (CW2376MarginalSupportedAddress m ×
      CW2376MarginalSupportedAddress m) :=
  cw2376TargetAmbientCollisions (cw2376MarginalSupportedUniverse m)

end MME


