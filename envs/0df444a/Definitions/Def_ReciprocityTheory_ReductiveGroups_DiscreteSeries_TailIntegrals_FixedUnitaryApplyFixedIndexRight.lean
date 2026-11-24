-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixedUnitaryApplyFixedIndexRight
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixedUnitaryApplyFixedIndexRight
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T14:49:37.769501+00:00
-- url     : https://prove2.me/theorems/14d72924-049d-429b-99da-2fe9f011c9ae
-- title:
--   Fixed Unitary Apply Fixed Index Right
-- statement:
--   Definitions and structural lemmas for Fixed Unitary Apply Fixed Index Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/FixedUnitaryApplyFixedIndexRight.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
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
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
namespace ReciprocityTheory.ChartRestriction.DS.Xi.Base0
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
def iW (k : ℕ) : Fin (2 * 0 + k + 1) := wI k 0 0
def iK (k : ℕ) : Fin (2 * 0 + k + 1) := wI k 0 (Fin.last k)
def Pk (k : ℕ) : Mat k 0 := Matrix.single (iK k) (iK k) 1
def U0 (k : ℕ) : Set (Mat k 0) := UWset k 0 (bvec (iK k))
end ReciprocityTheory.ChartRestriction.DS.Xi.Base0


