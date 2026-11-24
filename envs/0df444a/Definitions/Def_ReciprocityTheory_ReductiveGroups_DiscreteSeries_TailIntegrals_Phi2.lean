-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Phi2
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Phi2
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T15:49:18.779841+00:00
-- url     : https://prove2.me/theorems/0cf4bc22-f1d4-48a5-b1ce-6cd15c4fd0a9
-- title:
--   Phi2
-- statement:
--   Definitions and structural lemmas for Phi2, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/Phi2.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DetEqMulMinorOfColZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
def phi2 (k r' : ℕ) (a : Fin (1 + r' + 1)) : Fin (2 * (1 + r') + k + 1) → ℂ :=
  ιLev k 1 r' (Hpk k r') *ᵥ phiV k (1 + r') a
def Yx (k r' : ℕ) (x : HPar k r') (a : Fin (1 + r' + 1)) : Fin (2 * (1 + r') + k + 1) → ℂ :=
  (heis0 k r' x)⁻¹ *ᵥ phi2 k r' a
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA


