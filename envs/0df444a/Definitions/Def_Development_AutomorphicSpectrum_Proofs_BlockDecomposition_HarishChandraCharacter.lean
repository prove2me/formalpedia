-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HarishChandraCharacter
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HarishChandraCharacter
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T18:43:57.502295+00:00
-- url     : https://prove2.me/theorems/b9d9baa1-9c9f-436f-99cb-85d1c0ad450b
-- title:
--   Harish Chandra Character
-- statement:
--   Definitions and structural lemmas for Harish Chandra Character, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HarishChandraCharacter.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TraceCompLeftFunLeft
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_FrobeniusSumFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES ReciprocityTheory.Ty.Fin
noncomputable section
namespace GlobalTheory.CompanionTheory.FinGLChar
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
  {s : ℕ} (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
def leviHom (c : Fin s) : parab K b →* GL {i // b i = c} K where
  toFun := levi K b c
  map_one' := PI.SerBridgeGLW.levi_one' K b c
  map_mul' := PI.SerBridgeGLW.levi_mul' K b c
end GlobalTheory.CompanionTheory.FinGLChar


