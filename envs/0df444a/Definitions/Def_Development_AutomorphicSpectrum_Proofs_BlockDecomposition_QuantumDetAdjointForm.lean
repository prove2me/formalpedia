-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuantumDetAdjointForm
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuantumDetAdjointForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:25.314493+00:00
-- url     : https://prove2.me/theorems/be51e941-a7a5-4ef2-ab73-82a97a745963
-- title:
--   Quantum Det Adjoint Form
-- statement:
--   Definitions and structural lemmas for Quantum Det Adjoint Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuantumDetAdjointForm.lean

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuantumDetOppositeNegStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
namespace GlobalTheory.CompanionTheory.CapelliAdj
variable {V : Type} [AddCommGroup V] [Module ℂ V]
def HasAdj (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (T S : Module.End ℂ V) : Prop :=
  ∀ φ ψ : V, B (T φ) ψ = B φ (S ψ)
end GlobalTheory.CompanionTheory.CapelliAdj


