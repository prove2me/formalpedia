-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:32.630301+00:00
-- url     : https://prove2.me/theorems/a50be7d0-9c23-4a38-b44a-2b7ab04a4313
-- title:
--   Transpose Variables
-- statement:
--   Definitions and structural lemmas for Transpose Variables, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/TransposeVariables.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementH
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
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
def transposeVariables (R : Type*) [CommRing R] (n : ℕ) :
    MvPolynomial (Fin n × Fin n) R →ₐ[R] MvPolynomial (Fin n × Fin n) R := rename Prod.swap
def qn_D (n : ℕ) (a b : Fin n) :
    Derivation ℚ (MvPolynomial (Fin n × Fin n) ℚ) (MvPolynomial (Fin n × Fin n) ℚ) :=
  ∑ l : Fin n, (X (l, a) : MvPolynomial (Fin n × Fin n) ℚ) • pderiv (l, b)
end Formalism.InvariantFactorPaths.ColumnFamilies


