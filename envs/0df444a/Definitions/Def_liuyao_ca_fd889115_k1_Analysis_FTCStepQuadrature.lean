-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FTCStepQuadrature
-- name    : liuyao_ca_fd889115_k1_Analysis_FTCStepQuadrature
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:11:44.662195+00:00
-- url     : https://prove2.me/theorems/04f4ddb5-1c34-41f3-b664-fc1b39bcf651
-- title:
--   Computable analysis · FTCStepQuadrature · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/FTCStepQuadrature.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FTCRealCalculus

set_option autoImplicit true

/-! Independent rectangle quadrature for an actual justified FTC step.
Only the derivative, its Lipschitz bound, and rational interval data execute
in the quadrature. Its mathematical integral role is a proved conclusion. -/
namespace ComputableAnalysis.FTCStepQuadrature
open ComputableCoefficient RealApproximationOrder FTCRealCalculus RawLimit Integral
set_option maxHeartbeats 1000000

/-- The fundamental theorem for any certified dyadic construction.
The endpoint sampler supplies local derivative bounds, independent of the
way the integrand's cell ranges were constructed. -/
theorem dyadic_ftc {F : FunctionOnInterval} {P : Rat → RealCompute}
    (D : BoundsQuadrature.DyadicData F) (derivative : CellDerivativeBounds F P) :
    D.integral.Equiv (P F.upper - P F.lower) :=
  D.hasIntegral.ftc derivative

private def dyadic {f d : Rat → Value} {a b : Rat} (S : Step f d a b) (hab : a≤b) :
    BoundsQuadrature.DyadicData (LipschitzIntegralBounds.onInterval d a b) :=
  LipschitzIntegralBounds.dyadicData d a b S.variation hab S.lipschitz S.variation_nonnegative

def bounds {f d : Rat → Value} {a b : Rat} (S : Step f d a b) (hab : a≤b) (n : Nat) :
    Bounds (LipschitzIntegralBounds.onInterval d a b) :=
  (dyadic S hab).tests n

def box {f d : Rat → Value} {a b : Rat} (S : Step f d a b) (hab : a≤b) (n : Nat) : QInterval :=
  ⟨(bounds S hab n).lowerSum,(bounds S hab n).upperSum⟩

def integral {f d : Rat → Value} {a b : Rat} (S : Step f d a b) (hab : a≤b) : RealCompute :=
  prefixRaw (box S hab)

theorem box_covers {f d : Rat → Value} {a b : Rat} (S : Step f d a b) (hab : a≤b) (n : Nat) :
    InInterval ((f b).real.preferred-(f a).real.preferred) (box S hab n) :=
  by
    have H := (S.hasIntegral hab).bounds (bounds S hab n)
    exact ⟨fun _ j => (H j).1,fun i _ => (H i).2⟩

theorem integral_valid {f d : Rat → Value} {a b : Rat} (S : Step f d a b) (hab : a≤b) :
    (integral S hab).Valid :=
  (dyadic S hab).valid

theorem integral_equiv_endpoint {f d : Rat → Value} {a b : Rat} (S : Step f d a b) (hab : a≤b) :
    (integral S hab).Equiv ((f b).real.preferred-(f a).real.preferred) :=
  dyadic_ftc (dyadic S hab) S.cellBounds

theorem hasIntegral {f d : Rat → Value} {a b : Rat} (S : Step f d a b) (hab : a≤b) :
    HasIntegral (LipschitzIntegralBounds.onInterval d a b) (integral S hab) :=
  (dyadic S hab).hasIntegral

end ComputableAnalysis.FTCStepQuadrature


