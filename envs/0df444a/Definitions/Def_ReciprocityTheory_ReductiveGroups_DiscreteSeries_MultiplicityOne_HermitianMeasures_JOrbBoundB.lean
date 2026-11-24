-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_HermitianMeasures_JOrbBoundB
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_HermitianMeasures_JOrbBoundB
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T14:24:17.49182+00:00
-- url     : https://prove2.me/theorems/22bff314-38c3-45d5-be54-27ec60f66cf2
-- title:
--   JOrb Bound B
-- statement:
--   Definitions and structural lemmas for JOrb Bound B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/HermitianMeasures/JOrbBoundB.lean

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
section Form
variable {k r : ℕ}
def sigI (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  ⟨if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val, by split_ifs <;> omega⟩
def sgnI (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1
end Form
section Level
variable {k r' : ℕ}
def i0 (k r' : ℕ) : Fin (2 * (1 + r') + k + 1) := ⟨0, by omega⟩
def iL (k r' : ℕ) : Fin (2 * (1 + r') + k + 1) := ⟨2 * (1 + r') + k, by omega⟩
def iM (k r' : ℕ) (j : Fin (2 * r' + k + 1)) : Fin (2 * (1 + r') + k + 1) := ⟨j.val + 1, by omega⟩
def mid (k r' : ℕ) (v : Fin (2 * (1 + r') + k + 1) → ℂ) : Fin (2 * r' + k + 1) → ℂ := fun j => v (iM k r' j)
end Level
end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.OB


