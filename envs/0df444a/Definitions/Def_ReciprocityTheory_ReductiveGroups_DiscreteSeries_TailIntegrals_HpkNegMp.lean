-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkNegMp
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkNegMp
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T16:07:12.069803+00:00
-- url     : https://prove2.me/theorems/da9fe358-e421-41fa-9cd5-95a9b7dc4df4
-- title:
--   Hpk Neg Mp
-- statement:
--   Definitions and structural lemmas for Hpk Neg Mp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HpkNegMp.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Phi2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixOfPerp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight
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
namespace ThFin
def tm (k r' : ℕ) (x : HPar k r') : HPar k r' := (Hpk k r' *ᵥ (-x.1), -x.2)
def chF (p m : ℕ) (ν : Fin (p + 1) → ℝ) (y : Xp p m) : ℝ≥0∞ :=
  ∏ l, ENNReal.ofReal (de y l ^ (-(s0N p m l + ν l)))
end ThFin
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA


