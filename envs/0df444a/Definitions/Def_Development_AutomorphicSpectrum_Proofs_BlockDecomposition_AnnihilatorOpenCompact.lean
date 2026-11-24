-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnnihilatorOpenCompact
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnnihilatorOpenCompact
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:42.118919+00:00
-- url     : https://prove2.me/theorems/13d30592-6035-4981-af0e-093a1e76da7a
-- title:
--   Annihilator Open Compact
-- statement:
--   Definitions and structural lemmas for Annihilator Open Compact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AnnihilatorOpenCompact.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.RootEx
open scoped Topology
noncomputable section
namespace GlobalTheory.CompanionTheory.CharPerp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def perp {n : ℕ} (ψ : AddChar k Circle) (A : AddSubgroup (Fin n → k)) :
    AddSubgroup (Fin n → k) where
  carrier := {ξ | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1}
  zero_mem' := fun a _ => by simp
  add_mem' := fun {x y} hx hy a ha => by
    rw [add_dotProduct, AddChar.map_add_eq_mul, hx a ha, hy a ha, one_mul]
  neg_mem' := fun {x} hx a ha => by
    rw [neg_dotProduct, AddChar.map_neg_eq_inv, hx a ha, inv_one]
end GlobalTheory.CompanionTheory.CharPerp


