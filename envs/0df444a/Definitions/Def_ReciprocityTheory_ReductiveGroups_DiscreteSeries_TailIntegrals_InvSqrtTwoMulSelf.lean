-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InvSqrtTwoMulSelf
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InvSqrtTwoMulSelf
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T15:15:08.306795+00:00
-- url     : https://prove2.me/theorems/2488b1c2-a32f-45fb-941e-2b7fec856d52
-- title:
--   Inv Sqrt Two Mul Self
-- statement:
--   Definitions and structural lemmas for Inv Sqrt Two Mul Self, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/InvSqrtTwoMulSelf.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MatExtBvec
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
section herm
variable {n : ℕ}
end herm
section phi
variable (k n : ℕ)
end phi
section gram
end gram
end BL
end ReciprocityTheory.ChartRestriction.DS.Xi


