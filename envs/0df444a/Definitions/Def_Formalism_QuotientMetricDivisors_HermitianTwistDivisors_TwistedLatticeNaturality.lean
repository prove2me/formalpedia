-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TwistedLatticeNaturality
-- name    : Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TwistedLatticeNaturality
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:39:50.262253+00:00
-- url     : https://prove2.me/theorems/10f266ce-89bf-4b75-b64c-5153aa342306
-- title:
--   Twisted Lattice Naturality
-- statement:
--   Definitions and structural lemmas for Twisted Lattice Naturality, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/TwistedLatticeNaturality.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors
noncomputable section
namespace Formalism.DivisionValues
section Smul
variable {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ}
def shiftEquiv (d : ℕ) (a : K) (ha : a ≠ 0) : (Fin d → K) ≃ₗ[𝓞 K] (Fin d → K) :=
  (LinearEquiv.smulOfNeZero K (Fin d → K) a ha).restrictScalars (𝓞 K)
end Smul
section Prime
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable [IsTotallyComplex K]
theorem shift_above_finite (p : ℕ) (hp : p.Prime) :
    {w : HeightOneSpectrum (𝓞 K) | Above p w}.Finite := by
  have hp0 : (p : 𝓞 K) ≠ 0 := by
    first
    | exact Nat.cast_ne_zero.mpr hp.ne_zero
    | intro h
      have h' : ((p : 𝓞 K) : K) = 0 := by rw [h]; simp
      have h'' : (p : K) = 0 := by simpa using h'
      exact hp.ne_zero (by exact_mod_cast h'')
  have hI : Ideal.span {(p : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hp0
  refine (Ideal.finite_factors hI).subset ?_
  intro w hw
  exact Ideal.dvd_span_singleton.mpr hw
end Prime
section Unit
variable {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ}
end Unit
section Ideal
variable {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ}
end Ideal
end Formalism.DivisionValues


