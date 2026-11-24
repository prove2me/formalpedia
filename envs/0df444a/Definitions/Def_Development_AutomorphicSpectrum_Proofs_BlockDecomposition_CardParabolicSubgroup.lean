-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardParabolicSubgroup
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardParabolicSubgroup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:14:32.021627+00:00
-- url     : https://prove2.me/theorems/55020a83-8f16-4f66-bd73-b91f4bf8fc3b
-- title:
--   Card Parabolic Subgroup
-- statement:
--   Definitions and structural lemmas for Card Parabolic Subgroup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardParabolicSubgroup.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
namespace GlobalTheory.CompanionTheory.FinGL
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
section Parab
variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ} (b : ι → Fin s)
def parabCoord (p : parab K b) :
    ({p : ι × ι // b p.1 < b p.2} → K) × (∀ c, GL {i // b i = c} K) :=
  (fun x => (p.1 : Matrix ι ι K) x.1.1 x.1.2, fun c => levi K b c p)
end Parab
end GlobalTheory.CompanionTheory.FinGL


