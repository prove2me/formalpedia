-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ComplementSubspace
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ComplementSubspace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:27:43.82249+00:00
-- url     : https://prove2.me/theorems/0d41f200-da1e-47d1-8254-730df8a8968c
-- title:
--   Complement Subspace
-- statement:
--   Definitions and structural lemmas for Complement Subspace, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ComplementSubspace.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.ComplementSubspace.IsCompl :
    {K : Type} → [Field K] → {n r : ℕ} → Matrix (Fin r) (Fin n) K → Matrix (Fin n) (Fin n) K → Prop :=
    fun {K : Type} [Field K] {n r : ℕ} (c : Matrix (Fin r) (Fin n) K) (a : Matrix (Fin n) (Fin n) K) ↦
      IsUnit a.det ∧ ∀ (i : Fin n) (hi : (↑i : ℕ) < r), a i = c (⟨(↑i : ℕ), hi⟩ : Fin r)
namespace ComplementBasis
end ComplementBasis


