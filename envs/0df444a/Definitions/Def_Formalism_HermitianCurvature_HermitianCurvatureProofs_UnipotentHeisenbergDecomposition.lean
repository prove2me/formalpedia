-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T14:41:43.04226+00:00
-- url     : https://prove2.me/theorems/adbaaf28-3d2d-413d-b377-03f261ac7e4d
-- title:
--   Unipotent Heisenberg Decomposition
-- statement:
--   Definitions and structural lemmas for Unipotent Heisenberg Decomposition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentHeisenbergDecomposition.lean

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.B2x6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
def iF (k r' : ℕ) : Fin (2 * (1 + r') + k + 1) := eI k (1 + r') (a0 r')
def iL (k r' : ℕ) : Fin (2 * (1 + r') + k + 1) := esI k (1 + r') (a0 r')
def lv (k r' : ℕ) (j : Fin (2 * r' + k + 1)) : Fin (2 * (1 + r') + k + 1) := levPos k 1 r' j
def res (u : Fin (2 * (1 + r') + k + 1) → ℂ) : Fin (2 * r' + k + 1) → ℂ := fun j => u (lv k r' j)
def blk (g : Mat k (1 + r')) : Mat k r' := fun i j => g (lv k r' i) (lv k r' j)
def rho (x : Mt k (1 + r')) : Mt k (1 + r') := ιLev k 1 r' (blk (Matrix.of x))
end Formalism.FourierDecayAlt.P.B2x6
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.B2x6
end Formalism.FourierDecayAlt.P


