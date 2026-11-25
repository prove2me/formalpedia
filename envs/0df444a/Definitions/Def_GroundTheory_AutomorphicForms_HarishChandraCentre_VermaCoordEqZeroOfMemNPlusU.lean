-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_VermaCoordEqZeroOfMemNPlusU
-- name    : GroundTheory_AutomorphicForms_HarishChandraCentre_VermaCoordEqZeroOfMemNPlusU
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T03:09:21.601788+00:00
-- url     : https://prove2.me/theorems/c7b47edf-ff71-4290-a8a6-328fe116f198
-- title:
--   Verma Coord Eq Zero Of Mem NPlus U
-- statement:
--   Definitions and structural lemmas for Verma Coord Eq Zero Of Mem NPlus U, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/VermaCoordEqZeroOfMemNPlusU.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}
def vermaIdeal (lam : Fin n → ℂ) : Submodule ℂ (U n) :=
  nPlusU n ⊔ Submodule.span ℂ
    {x | ∃ (u : U n) (k : Fin n), u * (e (k, k) - algebraMap ℂ (U n) (lam k)) = x}
noncomputable def lowPart (m : Fin n × Fin n →₀ ℕ) : Fin n × Fin n →₀ ℕ := m.filter IsLower
open Classical in

noncomputable def vermaCoord (lam : Fin n → ℂ) : U n →ₗ[ℂ] ((Fin n × Fin n →₀ ℕ) →₀ ℂ) :=
  pbw.constr ℂ fun m =>
    if HasUpper m then 0 else Finsupp.single (lowPart m) (eval lam (monomial (diagExp m) 1))
section SimpleRoot
variable {i j : Fin n}
end SimpleRoot
section Reflection
variable {i j : Fin n}
end Reflection
end GroundTheory.Automorphic.HarishChandra


