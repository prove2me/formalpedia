-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LemmaTwoOf
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LemmaTwoOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:55:43.050745+00:00
-- url     : https://prove2.me/theorems/9fa8b134-7639-4b16-be83-419aecfbc044
-- title:
--   Lemma Two Of
-- statement:
--   Definitions and structural lemmas for Lemma Two Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LemmaTwoOf.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
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
open Finset
namespace Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
namespace LemTwo
section Slice
variable {K : Type} [Field K]
def sl (G : MvPowerSeries (Fin 2) K) (m : ℕ) : PowerSeries K :=
  PowerSeries.mk fun i => MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 m) G
def ext3 (e : Fin 2 →₀ ℕ) (m : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.embDomain Fin.castSuccEmb e + Finsupp.single 2 m
end Slice
section Norm
variable {K : Type} [NormedField K] [IsUltrametricDist K]
end Norm
section Top
variable {K : Type} [Field K]
end Top
section Additive
variable {K : Type} [Field K]
def asm (R : ℕ → PowerSeries K) : MvPowerSeries (Fin 2) K :=
  fun n => PowerSeries.coeff (n 0) (R (n 1))
end Additive
section Norm
variable {K : Type} [NormedField K] [IsUltrametricDist K]
end Norm
end LemTwo
end Formalism.InvariantFactorPaths.G7


