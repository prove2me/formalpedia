-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:31:06.730299+00:00
-- url     : https://prove2.me/theorems/d9534263-7e77-427e-bba5-e80a55cbe542
-- title:
--   Flag Basic
-- statement:
--   Definitions and structural lemmas for Flag Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagBasic.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
namespace RestTerms
namespace Flag
open MvPolynomial Finset
noncomputable section
end
end Flag
namespace Flag
open MvPolynomial Finset
noncomputable section
section Deriv
variable {σ ι : Type*}
def sumPderiv (s : Finset ι) (g : ι → σ) : Derivation ℚ (MvPolynomial σ ℚ) (MvPolynomial σ ℚ) :=
  ∑ l ∈ s, pderiv (g l)
end Deriv
section Indices
variable {f r a : ℕ}
end Indices
section Rest
variable (f r a : ℕ) (c : SmallBlock)
end Rest
end
end Flag
open MvPolynomial
namespace Flag
open MvPolynomial Finset
end Flag
end RestTerms
end GroundTheory.Heights₂.Heights


