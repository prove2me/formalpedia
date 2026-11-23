-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_CoordinateLengths_PairingContinuityBound
-- name    : Formalism_LocalToGlobal_GlobalTheory_CoordinateLengths_PairingContinuityBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:16:35.160605+00:00
-- url     : https://prove2.me/theorems/b75047f4-0605-4238-8a2b-a22c2e9ea17d
-- title:
--   Pairing Continuity Bound
-- statement:
--   Definitions and structural lemmas for Pairing Continuity Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/CoordinateLengths/PairingContinuityBound.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.L2.GlobalTheoryTheory.LemB
noncomputable def quotEquivSL {R R' M M' : Type*} [Ring R] [Ring R'] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R' M'] {σ : R →+* R'} {σ' : R' →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e : M ≃ₛₗ[σ] M') (P : Submodule R M) (Q : Submodule R' M') (h : P.map (e : M →ₛₗ[σ] M') = Q) :
    (M ⧸ P) ≃ₛₗ[σ] (M' ⧸ Q) :=
  LinearEquiv.ofLinearMap
    (P.mapQ Q (e : M →ₛₗ[σ] M') (by rw [← h]; exact Submodule.le_comap_map _ _))
    (Q.mapQ P (e.symm : M' →ₛₗ[σ'] M) (by
      rw [← h]; rintro _ ⟨x, hx, rfl⟩
      show e.symm (e x) ∈ P
      rw [e.symm_apply_apply]; exact hx))
    (by ext x; simp) (by ext x; simp)
end Formalism.L2.GlobalTheoryTheory.LemB


