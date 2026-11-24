-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellDecomposition
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellDecomposition
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T16:18:10.791847+00:00
-- url     : https://prove2.me/theorems/35b338dd-fd6a-4280-8a4d-4dd600f8add1
-- title:
--   Big Cell Decomposition
-- statement:
--   Definitions and structural lemmas for Big Cell Decomposition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BigCellDecomposition.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellInversePair
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter
noncomputable section
namespace Formalism.FourierDecayAlt.P.BigCellDecomposition
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.JF
def CellDecomp : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), ∀ g ∈ GV k r, (∀ l : Fin (r + 2), l.val ≤ r → Dmin k r z z' g l ≠ 0) →
    ∃ n ∈ Nset k r, ∃ n' ∈ Nset k r, ∃ c : Fin r → ℂ, (∀ a, c a ≠ 0) ∧
      ∃ μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, μᴴ * Hb k * μ = Hb k ∧ g = n⁻¹ * bigCell k r c μ * n'
variable {k r : ℕ}
end Formalism.FourierDecayAlt.P.BigCellDecomposition
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.JF
end Formalism.FourierDecayAlt.P


