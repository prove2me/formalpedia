-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_FunAct
-- name    : CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_FunAct
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T02:37:15.143804+00:00
-- url     : https://prove2.me/theorems/d97430e4-b59d-5449-9cbe-b5982a39ffec
-- title:
--   Fun Act
-- statement:
--   Definitions and structural lemmas for Fun Act, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/CapelliEigenvalues/FunAct.lean

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_Transport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants PI.DSInfCharCap
noncomputable section
namespace CompanionTheory.CapEig
section vec
variable {n : ℕ} {ε : Fin n → Bool} {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  {σ : Matrix (Fin n) (Fin n) ℂ → (Hs →L[ℂ] Hs)}
end vec
end CompanionTheory.CapEig
end


