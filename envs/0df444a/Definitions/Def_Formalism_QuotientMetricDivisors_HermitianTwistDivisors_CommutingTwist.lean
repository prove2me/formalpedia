-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
-- name    : Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:45:46.319482+00:00
-- url     : https://prove2.me/theorems/335b4023-17ab-471e-8fcd-67131abe4436
-- title:
--   Commuting Twist
-- statement:
--   Definitions and structural lemmas for Commuting Twist, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/CommutingTwist.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.DivisionValues
namespace FinitelyNonzeroLinear
section Ext
variable {K Ω : Type} [Field K] [Field Ω] (j : K →+* Ω)
structure Fnl where
  toFun : Ω → K
  add : ∀ c c', toFun (c + c') = toFun c + toFun c'
  smul : ∀ (a : K) (c : Ω), toFun (j a * c) = a * toFun c
variable {j}
end Ext
end FinitelyNonzeroLinear
namespace FinitelyNonzeroLinear
section Herm
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end Herm
end FinitelyNonzeroLinear
namespace FinitelyNonzeroLinear
section Cx
variable {n : ℕ} {Hc : Matrix (Fin n) (Fin n) ℂ}
end Cx
section Diag
variable {K : Type} [Field K] {n : ℕ}
end Diag
end FinitelyNonzeroLinear
namespace FinitelyNonzeroLinear
section Dich
variable {n : ℕ} {Hc : Matrix (Fin n) (Fin n) ℂ}
def rankOne (Hc : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i k => y i * (star x ᵥ* Hc) k
end Dich
end FinitelyNonzeroLinear
end Formalism.DivisionValues


