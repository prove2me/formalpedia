-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_TraceOfDiag
-- name    : Formalism_LocalToGlobal_IndefiniteReal_TraceOfDiag
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:09:18.38703+00:00
-- url     : https://prove2.me/theorems/bb8ee68d-643a-4f9d-9a8f-0e6b49226405
-- title:
--   Trace Of Diag
-- statement:
--   Definitions and structural lemmas for Trace Of Diag, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/TraceOfDiag.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
namespace Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement
namespace CharacterLemmas
def repC {K : Type} [Field K] (σ : K →+* ℂ) {G : Type} [Group G] {T : Type} [AddCommGroup T]
    [Module K T] [FiniteDimensional K T] (τ : Representation K G T) :
    Representation ℂ G (Fin (finrank K T) → ℂ) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin (finrank K T)) (Fin (finrank K T)) ℂ ≃ₐ[ℂ] _) :
      Matrix (Fin (finrank K T)) (Fin (finrank K T)) ℂ →* _).comp
    (((σ.mapMatrix : Matrix (Fin (finrank K T)) (Fin (finrank K T)) K →+* _) :
        Matrix (Fin (finrank K T)) (Fin (finrank K T)) K →* _).comp
      (((LinearMap.toMatrixAlgEquiv (Module.finBasis K T)) : (T →ₗ[K] T) →* _).comp τ))
end CharacterLemmas
open CharacterLemmas
end Formalism.IndefR.LatticeTransfer


