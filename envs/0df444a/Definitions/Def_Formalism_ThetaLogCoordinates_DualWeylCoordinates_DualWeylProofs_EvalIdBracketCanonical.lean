-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EvalIdBracketCanonical
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EvalIdBracketCanonical
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T10:38:13.853391+00:00
-- url     : https://prove2.me/theorems/021da62e-d68b-4e14-831f-3c4ad4aa5c5b
-- title:
--   Eval Id Bracket Canonical
-- statement:
--   Definitions and structural lemmas for Eval Id Bracket Canonical, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/EvalIdBracketCanonical.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ABridge
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BideterminantMem
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
def qn_delta (n : ℕ) : MvPolynomial (Fin n × Fin n) ℤ := lpMinor ℤ n (le_refl n) (le_refl n)
def qn_nu {n : ℕ} [NeZero n] (mu : Fin n → ℤ) : Fin n → ℕ :=
  fun t => (mu t + ((-(mu (lastIdx n))).toNat : ℤ)).toNat
end Formalism.InvariantFactorPaths.ColumnFamilies


