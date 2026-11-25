-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_Tensor
-- name    : Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_Tensor
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T12:07:40.311953+00:00
-- url     : https://prove2.me/theorems/ed998a27-daf0-405b-b002-44b4fda1ef47
-- title:
--   Tensor
-- statement:
--   Definitions and structural lemmas for Tensor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/Tensor.lean

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_TensorIrr
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Algebraic.LinearIndependent
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Cardinality
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SpectrumNonemptyOfCountableRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.KReal
section
variable {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
def one_op (i : ι) (f : Module.End ℂ (M i)) : Module.End ℂ (PiTensorProduct ℂ M) :=
  PiTensorProduct.map (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i f)
end
end PositivityTheory.KReal
end


