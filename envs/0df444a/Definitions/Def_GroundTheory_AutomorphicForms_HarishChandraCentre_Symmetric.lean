-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Symmetric
-- name    : GroundTheory_AutomorphicForms_HarishChandraCentre_Symmetric
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:39.759953+00:00
-- url     : https://prove2.me/theorems/26e6dc94-d5dc-45d1-8807-c58a662fa80e
-- title:
--   Symmetric
-- statement:
--   Definitions and structural lemmas for Symmetric, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Symmetric.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic.HarishChandra
open MvPolynomial Finset
variable {n : ℕ}
noncomputable abbrev psumFin (k : Fin n) : MvPolynomial (Fin n) ℂ := psum (Fin n) ℂ ((k : ℕ) + 1)
def TopClose (k : ℕ) (a b : MvPolynomial (Fin n) ℂ) : Prop :=
  a.totalDegree ≤ k ∧ b.totalDegree ≤ k ∧ (a = b ∨ (a - b).totalDegree < k)
def psumWt (c : Fin n →₀ ℕ) : ℕ := ∑ i ∈ c.support, c i * ((i : ℕ) + 1)
end GroundTheory.Automorphic.HarishChandra


