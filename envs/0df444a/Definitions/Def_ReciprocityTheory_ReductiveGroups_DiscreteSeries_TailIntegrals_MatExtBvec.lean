-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MatExtBvec
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MatExtBvec
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T14:53:46.33634+00:00
-- url     : https://prove2.me/theorems/629e76f6-75a0-480a-b059-72c06bb37d63
-- title:
--   Mat Ext Bvec
-- statement:
--   Definitions and structural lemmas for Mat Ext Bvec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/MatExtBvec.lean

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
open scoped ENNReal ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace BL
def sg (k r i : ℕ) : ℕ := if i < r ∨ r + k < i then 2 * r + k - i else i
section Lev
variable {k r' : ℕ}
def sh (q : Fin (2 * r' + k + 1)) : Fin (2 * (1 + r') + k + 1) := ⟨q.val + 1, by have := q.2; omega⟩
end Lev
end BL
end ReciprocityTheory.ChartRestriction.DS.Xi


