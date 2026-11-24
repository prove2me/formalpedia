-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CoeffTransposeVariables
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CoeffTransposeVariables
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:40.460633+00:00
-- url     : https://prove2.me/theorems/6fb156b2-4b4d-4459-9750-a2ffbb610020
-- title:
--   Coeff Transpose Variables
-- statement:
--   Definitions and structural lemmas for Coeff Transpose Variables, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/CoeffTransposeVariables.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
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
def qn_wt {n : ℕ} (m : Fin n × Fin n →₀ ℕ) : Fin n → ℤ := fun a => ((∑ l : Fin n, m (l, a) : ℕ) : ℤ)
end Formalism.InvariantFactorPaths.ColumnFamilies


