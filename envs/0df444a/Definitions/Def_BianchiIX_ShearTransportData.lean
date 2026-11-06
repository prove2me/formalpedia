-- Prove2me | Definitions.Def_BianchiIX_ShearTransportData
-- name    : BianchiIX_ShearTransportData
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-06T04:38:29.910798+00:00
-- url     : https://prove2.me/theorems/72ed7f49-f227-4d40-9bb1-b31b5389d0f2
-- title:
--   The shear tail and the radial derivative of its projective entrance
-- statement:
--   Write $\Phi_t x$ for the normalized vacuum Bianchi IX flow and
--   $x_h(Z)$ for the constraint-one, negative-first-shear chart with primary
--   wall $h$ and center coordinates $Z=(v,b,c)$ (second shear and the other
--   two walls). At time $t$, denote its primary wall by $n_t$ and center by
--   $Z_t$. Set $r(Z)=\sqrt{v^2+(b-c)^2}$. For $u=\sqrt{1-h^2}$ define
--   $A=3/(2+u)$, $B=3\sqrt3 h/(2+u)^2$, $H=9(1+u)/(2(2+u)^2)$,
--   $Q_h(v,w)=(Av+Bw)^2+H^2w^2$ and $F_h(Z)=\sqrt{Q_h(v,b-c)}/\sqrt3$.
--   On a shear annulus take $0<a$, $\rho\in[a,2a]$,
--   $Z=(\rho,n_2,n_3)$, $s=(q/2)\log(1/a)$, $Y=\Pi\Phi_s x_h(Z)$,
--   $k=\sqrt{(Y_0-1)^2+Y_2^2}$ and $F=F_h(Z)$. A signed annulus uses
--   $Z=(\omega\rho,n_2,n_3)$, $|\omega|=1$. Here $h>0$ is sufficiently
--   small and $a>0$ is sufficiently small thereafter. Primes are ordinary
--   radial derivatives with labels and cutoff fixed.
--   The long cutoff adds $S=(D/a)\log(1/a)$ to $s$.
--   Write $Y_L=\Pi\Phi_{s+S}x_h(Z)$, and write $(\zeta,\nu)=(n_2,n_3)$.
--   Take $0\le\epsilon\le1/128$, $0<\zeta,\nu\le2\epsilon a$,
--   $\zeta\le a^P$, $P>6D+2$.
--
--   At tail time $u$ the exact orbit is $\alpha(u)=\Phi_{s+u}x_h(Z)$.
--   Its radial variation is the initial-coordinate differential applied to
--   the shear direction. The logarithmic wall size of this variation is
--   $\max_i|\partial_\rho N_i/N_i|$. The energy
--   $E=\sum_i N_i^2+N_1(N_2+N_3)$ and its first two time moments control
--   the radius and phase at the end of the tail.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/tree/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_RadialTransportData
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.Deriv.Pi
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Mathlib.Topology.Order.ProjIcc
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

noncomputable section

namespace BianchiIX

def shearTailCurvatureDifferential (z v : NormalizedState) : ℝ :=
  2 * ((z 2 - z 3 - z 4) * v 2 + (z 3 - z 2 - z 4) * v 3 + (z 4 - z 2 - z 3) * v 4)

def shearTailCouplingDifferential (z v : NormalizedState) : ℝ :=
  (z 3 - z 4) * v 2 + (z 2 - 2 * z 3) * v 3 + (2 * z 4 - z 2) * v 4







def shearTailVariation (z v : NormalizedState) : Fin 4 → ℝ :=
  ![v 1, v 2 / z 2, v 3 / z 3, v 4 / z 4]



def shearTailVariationRate (z v : NormalizedState) : Fin 4 → ℝ :=
  let ξ := -z 0
  let dQ := shearTailCurvatureDifferential z v
  ![curvature (z 2) (z 3) (z 4) * v 1 + z 1 * dQ + Real.sqrt 3 * shearTailCouplingDifferential z v,
    (1 + ξ⁻¹) * dQ + 2 * z 1 * ξ⁻¹ * v 1,
    (1 - (2 * ξ)⁻¹) * dQ + (-z 1 * ξ⁻¹ + Real.sqrt 3) * v 1,
    (1 - (2 * ξ)⁻¹) * dQ + (-z 1 * ξ⁻¹ - Real.sqrt 3) * v 1]





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def shearTailRegion (a : ℝ) (z : NormalizedState) : Prop :=
  z 0 ≤ -(1 / 2) ∧ a / 2 ≤ z 1 ∧ z 1 ≤ 3 * a ∧
    z 2 ≤ a ^ 2 ∧ z 3 ≤ a ^ 2 ∧ z 4 ≤ a / 16

def shearTailDrift (a A X Y t : ℝ) : ℝ :=
  3 * Y ^ 2 / a * (1 - Real.exp (-a * t)) +
    X ^ 2 / (4 * a) * (Real.exp (12 * a * t) - 1) +
      a * A / 8 * (1 - Real.exp (-2 * t))







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def shearTailEnergy (z : NormalizedState) : ℝ :=
  z 2 ^ 2 + z 3 ^ 2 + z 4 ^ 2 + z 2 * (z 3 + z 4)





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def shearTailTime (a D : ℝ) : ℝ := D / a * Real.log (1 / a)





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX





def shearTailLogSize (z v : NormalizedState) : ℝ :=
  ‖fun i : Fin 3 => v (i.addNat 2) / z (i.addNat 2)‖



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def shearTailProjectiveLogState (z : NormalizedState) : Fin 5 → ℝ :=
  ![Real.log (1 + z 0), Real.log (projectiveCoord (z 0) (z 1)),
    Real.log (projectiveCoord (z 0) (z 2)), Real.log (projectiveCoord (z 0) (z 3)),
    Real.log (projectiveCoord (z 0) (z 4))]

def shearTailProjectiveLogVariation (z v : NormalizedState) : Fin 5 → ℝ :=
  ![v 0 / (1 + z 0), v 1 / z 1 - v 0 / (1 + z 0),
    v 2 / z 2 - v 0 / (1 + z 0), v 3 / z 3 - v 0 / (1 + z 0),
    v 4 / z 4 - v 0 / (1 + z 0)]







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def shearTailRadius (z : NormalizedState) : ℝ :=
  restartRadialNorm (restartCenterProjection z)

def shearTailRadiusDifferential (z v : NormalizedState) : ℝ :=
  (z 1 * v 1 + (z 3 - z 4) * (v 3 - v 4)) / shearTailRadius z

def shearTailRadiusRate (z : NormalizedState) : ℝ :=
  curvature (z 2) (z 3) (z 4) * shearTailRadius z -
    (1 + z 0) * (z 3 - z 4) ^ 2 / shearTailRadius z +
      Real.sqrt 3 * z 2 * z 1 * (z 3 - z 4) / shearTailRadius z

def shearTailRadiusEnergy (z : NormalizedState) : ℝ :=
  z 2 + z 3 ^ 2 + z 4 ^ 2

















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def shearTailRadiusNumerator (z : NormalizedState) : ℝ :=
  curvature (z 2) (z 3) (z 4) * (z 1 ^ 2 + (z 3 - z 4) ^ 2) -
    (1 + z 0) * (z 3 - z 4) ^ 2 + Real.sqrt 3 * z 2 * z 1 * (z 3 - z 4)

def shearTailRadiusNumeratorDifferential (z v : NormalizedState) : ℝ :=
  shearTailCurvatureDifferential z v * (z 1 ^ 2 + (z 3 - z 4) ^ 2) +
    2 * curvature (z 2) (z 3) (z 4) * (z 1 * v 1 + (z 3 - z 4) * (v 3 - v 4)) -
    v 0 * (z 3 - z 4) ^ 2 - 2 * (1 + z 0) * (z 3 - z 4) * (v 3 - v 4) +
    Real.sqrt 3 * (v 2 * z 1 * (z 3 - z 4) + z 2 * v 1 * (z 3 - z 4) +
      z 2 * z 1 * (v 3 - v 4))

def shearTailRadiusRateDifferential (z v : NormalizedState) : ℝ :=
  shearTailRadiusNumeratorDifferential z v / shearTailRadius z -
    shearTailRadiusNumerator z * shearTailRadiusDifferential z v / shearTailRadius z ^ 2









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def restartFastShearPhase (h T σ n₂ n₃ ρ : ℝ) : ℝ :=
  restartRadialPhase (restartSectionCenterFlow h T (restartShearCurve σ n₂ n₃ ρ))





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def restartShearTailFlow (h a q ζ ν t ρ : ℝ) : NormalizedState :=
  normalizedMaxCurve (restartSectionChart h (restartShearCurve 1 ζ ν ρ)) 0
    (t + q / 2 * Real.log (1 / a))



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def restartFastShearCoreRadius (h T σ n₂ n₃ ρ : ℝ) : ℝ :=
  let y := restartFastShearProjectiveEntry h T σ n₂ n₃ ρ
  coreRadius (y 0) (y 2)

def restartFastShearCoreAngle (h T σ n₂ n₃ ρ : ℝ) : ℝ :=
  let y := restartFastShearProjectiveEntry h T σ n₂ n₃ ρ
  coreAngle (y 0) (y 2)





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def restartFastShearProjectionPhase (h T σ n₂ n₃ ρ : ℝ) : ℝ :=
  2 / coreRadius (restartFastShearProjectiveEntry h T σ n₂ n₃ ρ 0)
    (restartFastShearProjectiveEntry h T σ n₂ n₃ ρ 2)



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def restartShearInitialVariation (h ζ ν ρ : ℝ) : NormalizedState :=
  fderiv ℝ (restartSectionChart h) (restartShearCurve 1 ζ ν ρ) (restartShearDirection 1)



def restartShearTailRadialVariation (h a q ζ ν t ρ : ℝ) : NormalizedState :=
  normalizedFlowDifferential (restartSectionChart h (restartShearCurve 1 ζ ν ρ)) 0
    (t + q / 2 * Real.log (1 / a)) (restartShearInitialVariation h ζ ν ρ)







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def restartShearTailProjectiveEntry (h a q ζ ν t ρ : ℝ) : ProjectiveState :=
  toProjectiveState (restartShearTailFlow h a q ζ ν t ρ)



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def restartShearTailPhase (h a q ζ ν t ρ : ℝ) : ℝ :=
  shearTailRadius (restartShearTailFlow h a q ζ ν t ρ) / Real.sqrt 3





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def restartShearTailProjectionPhase (h a q ζ ν t ρ : ℝ) : ℝ :=
  2 / coreRadius (toProjectiveState (restartShearTailFlow h a q ζ ν t ρ) 0)
    (toProjectiveState (restartShearTailFlow h a q ζ ν t ρ) 2)



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def restartShearTailEntranceRadius (h a q D ζ ν ρ : ℝ) : ℝ :=
  let y := entranceReturnState (restartShearTailProjectiveEntry h a q ζ ν (shearTailTime a D) ρ)
  coreRadius (y 0) (y 2)

def restartShearTailEntrancePhase (h a q D ζ ν ρ : ℝ) : ℝ :=
  2 / restartShearTailEntranceRadius h a q D ζ ν ρ



end BianchiIX

end
end


