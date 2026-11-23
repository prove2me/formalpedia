-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumToGaussSum
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumToGaussSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:29.061814+00:00
-- url     : https://prove2.me/theorems/72295961-c9b7-4a65-a2d8-486f4c186081
-- title:
--   Weighted Sum To Gauss Sum
-- statement:
--   Definitions and structural lemmas for Weighted Sum To Gauss Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/WeightedSumToGaussSum.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_SumSliceEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
namespace PI.TwistedEisensteinNonvanishing.W
open Loc LocE Function
variable {E K : Type} [Field E] [NumberField E] [Field K]
section QTdef
variable (P : HeightOneSpectrum (𝓞 E)) {ι : Type} [Fintype ι] [DecidableEq ι]
def QT (T : (ι → E) → (ι → E)) (c : K) : Prop :=
  ∀ a b : ℕ, ∃ a' b' : ℕ, ∀ H : (ι → E) → K, Good P a b H →
    Good P a' b' (fun t => H (T t)) ∧ RS P a' b' (fun t => H (T t)) = c * RS P a b H
variable {P}
def em (k l : ι) (d c β : E) (t : ι → E) : ι → E := update t k (d * t k + c * t l + β)
end QTdef
section Em
variable {P : HeightOneSpectrum (𝓞 E)} (hN : NTAll) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hK : ((qOf P : ℕ) : K) ≠ 0)
include hN hp hq hK
end Em
end PI.TwistedEisensteinNonvanishing.W


