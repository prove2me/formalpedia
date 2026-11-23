-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstZeroOfConstantCoeff
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstZeroOfConstantCoeff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:10:56.444807+00:00
-- url     : https://prove2.me/theorems/2a9147da-b9c7-485d-864c-d3d63e3b1f0d
-- title:
--   Subst Zero Of Constant Coeff
-- statement:
--   Definitions and structural lemmas for Subst Zero Of Constant Coeff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/SubstZeroOfConstantCoeff.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (torus lw degE degO NoLowBidegree)
open Formalism.InvariantFactorPaths.G7 (lgF at1 DivAB)
namespace TorusDerivation
section Gen
variable {K : Type} [Field K]
variable {d : ℕ} [NeZero d]
end Gen
end TorusDerivation
open TorusDerivation
namespace TorusDerivation
section Mean
variable {K : Type} [Field K] {d : ℕ} [NeZero d]
def wt (l : ℕ) (ζ : K) (n : ZMod d →₀ ℕ) : K := ∏ s : ZMod d, (ζ ^ lw l s) ^ n s
end Mean
end TorusDerivation
end Formalism.L2.Th1.D


