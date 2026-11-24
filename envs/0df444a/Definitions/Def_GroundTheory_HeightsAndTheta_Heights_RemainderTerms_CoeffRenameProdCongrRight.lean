-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoeffRenameProdCongrRight
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoeffRenameProdCongrRight
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T18:12:09.629251+00:00
-- url     : https://prove2.me/theorems/bb4a0514-174a-45ca-973b-51d8a43e4068
-- title:
--   Coeff Rename Prod Congr Right
-- statement:
--   Definitions and structural lemmas for Coeff Rename Prod Congr Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/CoeffRenameProdCongrRight.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
namespace FlagEq
variable {f N : ℕ}
def permSign (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) : ℤ :=
  ∏ τ, ((Equiv.Perm.sign (w τ) : ℤˣ) : ℤ)
def stairExp (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) : Fin f × Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => N - 1 - ((w v.1).symm v.2 : ℕ)
def rho (f N : ℕ) : Fin f × Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => N - 1 - (v.2 : ℕ)
def stairConst (f N : ℕ) : ℝ := (∏ i : Fin N, ((N - 1 - (i : ℕ)).factorial : ℝ)) ^ f
end FlagEq
end
end GroundTheory.Heights₂.Heights.RestTerms


