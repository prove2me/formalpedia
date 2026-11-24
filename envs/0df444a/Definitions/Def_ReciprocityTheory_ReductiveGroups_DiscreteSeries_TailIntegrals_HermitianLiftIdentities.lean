-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianLiftIdentities
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianLiftIdentities
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T15:14:45.974859+00:00
-- url     : https://prove2.me/theorems/eab45fd8-2eee-4037-8308-bb986e6f5268
-- title:
--   Hermitian Lift Identities
-- statement:
--   Definitions and structural lemmas for Hermitian Lift Identities, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianLiftIdentities.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LinIndToLp
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
open scoped ENNReal NNReal
namespace ReciprocityTheory.ChartRestriction.DS.Xi.DetB
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
def cst {k r : ℕ} (H : Mat k r) (v w : Fin (2 * r + k + 1) → ℂ) : ℝ :=
  ∑ i, ∑ m, ∑ j, ‖w i‖ * ‖H i m‖ * ‖v j‖
def K0 (k r : ℕ) : ℝ := ∑ a : Fin (r + 1), ∑ b : Fin (r + 1), cst (Hpk k r) (phiV' k r b) (phiV' k r a)
def cl (k r : ℕ) (l : Fin (r + 1)) : ℝ := (l.val + 1).factorial * K0 k r ^ (l.val + 1) + 1
end ReciprocityTheory.ChartRestriction.DS.Xi.DetB
namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 DetB
end ReciprocityTheory.ChartRestriction.DS.Xi


