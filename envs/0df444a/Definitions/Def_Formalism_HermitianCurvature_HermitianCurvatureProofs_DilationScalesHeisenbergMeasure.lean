-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationScalesHeisenbergMeasure
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T15:10:22.686812+00:00
-- url     : https://prove2.me/theorems/c6e3c045-7709-4522-b587-5d38beb5e8f1
-- title:
--   Dilation Scales Heisenberg Measure
-- statement:
--   Definitions and structural lemmas for Dilation Scales Heisenberg Measure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationScalesHeisenbergMeasure.lean

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
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
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace B2x7
variable {k r' : ℕ}
def dgR (k r : ℕ) (t : ℝ) (i : Fin (2 * r + k + 1)) : ℝ :=
  if i.val < r then t ^ (r - i.val) else if i.val ≤ r + k then 1 else (t ^ (i.val - (r + k)))⁻¹
end B2x7
open B2x7
namespace B2x7
variable {k r' : ℕ}
def heisF (k r' : ℕ) : HPar k r' → Mt k (1 + r') := fun x => heis0 k r' x
def dilL (k r' : ℕ) (t : ℝ) : HPar k r' →ₗ[ℝ] HPar k r' :=
  LinearMap.prodMap
    (LinearMap.pi fun i => ((t ^ (1 + r') * dgR k r' t i) • (LinearMap.id : ℂ →ₗ[ℝ] ℂ)).comp (LinearMap.proj i))
    ((t ^ (2 * (1 + r'))) • LinearMap.id)
end B2x7
namespace B2x7
variable {k r' : ℕ}
end B2x7
end Formalism.FourierDecayAlt.P


