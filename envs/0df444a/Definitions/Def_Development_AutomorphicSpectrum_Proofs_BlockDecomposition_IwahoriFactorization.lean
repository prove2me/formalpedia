-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:11.203117+00:00
-- url     : https://prove2.me/theorems/d81e406b-5a4f-4240-b2ab-691a1a1965dd
-- title:
--   Iwahori Factorization
-- statement:
--   Definitions and structural lemmas for Iwahori Factorization, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IwahoriFactorization.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_GroundTheory_LocalFields_Integers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel PositivityTheory.Rg.Tf.Loc Matrix
namespace GlobalTheory.CompanionTheory.TfLoc.Iw
section Entries
variable {F : Type*} [Field F] [ValuativeRel F] {m : ℕ}
theorem mul_lt_one_of_le_of_lt_alt {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ} (ha : a ≤ 1)
    (hb : b < 1) : a * b < 1 :=
  lt_of_le_of_lt (mul_le_of_le_one_left' ha) hb
def ltIdeal (F : Type*) [Field F] [ValuativeRel F] : Ideal (Valuation.integer (valuation F)) where
  carrier := {x | valuation F (x : F) < 1}
  add_mem' := fun {a b} ha hb => (valuation F).map_add_lt ha hb
  zero_mem' := by simp
  smul_mem' := fun c x hx => by
    show valuation F ((c : F) * (x : F)) < 1
    rw [map_mul]
    exact mul_lt_one_of_le_of_lt_alt c.2 hx
end Entries
section Top
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {m : ℕ}
end Top
section Ext
variable {k E : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E]
end Ext
end GlobalTheory.CompanionTheory.TfLoc.Iw


