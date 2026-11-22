-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_BUnfold
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_BUnfold
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:34:53.891094+00:00
-- url     : https://prove2.me/theorems/1fb403be-c00c-405c-ac5c-4ba7a681b03d
-- title:
--   BUnfold
-- statement:
--   Definitions and structural lemmas for BUnfold, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/BUnfold.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units MeasureTheory
open scoped nonZeroDivisors ENNReal Classical Pointwise
noncomputable section
namespace PI.Residue
variable {K : Type} [Field K] [NumberField K]
def urep (g : (𝓞 K)ˣ ⧸ torsion K) : (𝓞 K)ˣ := Quotient.out g
def Fv (ρ : ℝ) (x : mixedSpace K) : ℝ≥0∞ := volume (shell K ∩ hit K ρ x)
end PI.Residue


