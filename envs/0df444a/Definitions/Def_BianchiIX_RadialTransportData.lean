-- Prove2me | Definitions.Def_BianchiIX_RadialTransportData
-- name    : BianchiIX_RadialTransportData
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-06T04:37:27.283693+00:00
-- url     : https://prove2.me/theorems/1079fd00-f5ab-4d99-8b63-2ca9294f5d01
-- title:
--   Radial observables and their transport from a wall section
-- statement:
--   Write $\Phi_t x$ for the normalized vacuum Bianchi IX flow and
--   $x_h(Z)$ for the constraint-one, negative-first-shear chart with primary
--   wall $h$ and center coordinates $Z=(v,b,c)$ (second shear and the other
--   two walls). At time $t$, denote its primary wall by $n_t$ and center by
--   $Z_t$. Set $r(Z)=\sqrt{v^2+(b-c)^2}$. For $u=\sqrt{1-h^2}$ define
--   $A=3/(2+u)$, $B=3\sqrt3 h/(2+u)^2$, $H=9(1+u)/(2(2+u)^2)$,
--   $Q_h(v,w)=(Av+Bw)^2+H^2w^2$ and $F_h(Z)=\sqrt{Q_h(v,b-c)}/\sqrt3$.
--
--   The mixed coordinates are $(\log n_t,Z_t)$. The transported radius is
--   $R_t=\sqrt{Q_{n_t}((Z_t)_0,(Z_t)_1-(Z_t)_2)}$; its tail correction
--   is $R_t-r(Z_t)$. The projection height is $1+(\Phi_t x)_0$ on the
--   negative-shear chart. The definitions describe the section flow, radial
--   rates, reference variation, and the passage to projective coordinates.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/tree/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_SectionRestartData
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
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.GCongr
import Definitions.Def_BianchiIX_Algebra_Flow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.ODE.Gronwall
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Calculus.Deriv.Pi
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState

section

noncomputable section

namespace BianchiIX

def restartCurvatureDifference (x : NormalizedState) : ℝ :=
  (x 3 - x 4) ^ 2 - 2 * x 2 * (x 3 + x 4)

def restartRootDifference (x : NormalizedState) : ℝ := -x 0 - restartReferenceRoot (x 2)

def restartStrongRateDifference (x : NormalizedState) : ℝ :=
  restartCurvatureDifference x - 2 * restartRootDifference x











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def quadraticFromCoefficients (m : Fin 3 → ℝ) (s v : ℝ) : ℝ :=
  m 0 * s ^ 2 + m 1 * s * v + m 2 * v ^ 2









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

abbrev RestartState := Fin 4 → ℝ

def restartRadicand (x : RestartState) : ℝ :=
  1 - x 1 ^ 2 - curvature (x 0) (x 2) (x 3)

def restartCompactRoot (x : RestartState) : ℝ := Real.sqrt (restartRadicand x)

def restartCompactWeakRate (ε : ℝ) (x : RestartState) : ℝ :=
  curvature (x 0) (x 2) (x 3) - 1 + restartCompactRoot x + ε * Real.sqrt 3 * x 1

/-- The logarithmic strong-wall rate extends smoothly to zero strong wall. -/
def restartCompactField (x : RestartState) : RestartState :=
  ![curvature (x 0) (x 2) (x 3) - 1 - 2 * restartCompactRoot x,
    shearMinus (x 1) (x 0) (x 2) (x 3),
    x 2 * restartCompactWeakRate 1 x, x 3 * restartCompactWeakRate (-1) x]

def restartExpCoordinates (y : RestartState) : RestartState := ![Real.exp (y 0), y 1, y 2, y 3]

def restartMixedField : RestartState → RestartState := restartCompactField ∘ restartExpCoordinates

def restartMixedCoordinates (x : NormalizedState) : RestartState := ![Real.log (x 2), x 1, x 3, x 4]



















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def restartExpDifferential (n : ℝ) : RestartState →L[ℝ] RestartState :=
  let p : Fin 4 → (RestartState →L[ℝ] ℝ) := fun i => ContinuousLinearMap.proj i
  ContinuousLinearMap.pi ![n • p 0, p 1, p 2, p 3]











def restartMixedBox : Set RestartState :=
  Set.pi Set.univ (fun i => if i = 0 then Set.Iic (Real.log (1 / 16)) else Set.Icc (-(1 / 16)) (1 / 16))









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Function

def closedIntervalFamily {X : Type*} (a b : X → ℝ) : Set (X × ℝ) :=
  {p | p.2 ∈ Icc (a p.1) (b p.1)}





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def restartCompactWeakRates (x : RestartState) : Fin 2 → ℝ :=
  ![restartCompactWeakRate 1 x, restartCompactWeakRate (-1) x]

def restartMixedWeakRates : RestartState → Fin 2 → ℝ := restartCompactWeakRates ∘ restartExpCoordinates









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology



def restartReferenceVariation (h : ℝ) (d : NormalizedState) (t : ℝ) : NormalizedState :=
  normalizedFlowDifferential (restartReferenceInitial h) 0 t d









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def restartPhysicalCoordinates : NormalizedState →L[ℝ] RestartState :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 2, ContinuousLinearMap.proj 1,
    ContinuousLinearMap.proj 3, ContinuousLinearMap.proj 4]

def restartCompactCenterProjection : RestartState →L[ℝ] RestartCenterState :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 1, ContinuousLinearMap.proj 2,
    ContinuousLinearMap.proj 3]











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def restartFastBudget (C h b t : ℝ) : ℝ := C * (h / 2 * (1 - Real.exp (-2 * t)) + b * t)









def restartControlRegion (h b : ℝ) (x : NormalizedState) : Prop :=
  x 0 ≤ -(1 / 2) ∧ x 2 ≤ 2 * h ∧ ‖restartCenterProjection x‖ ≤ b



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The negative constraint branch in four mixed coordinates. -/
def restartMixedChart (y : RestartState) : NormalizedState :=
  ![-restartCompactRoot (restartExpCoordinates y), y 1, Real.exp (y 0), y 2, y 3]

def restartMixedFlow (p : RestartState × ℝ) : RestartState :=
  restartMixedCoordinates (normalizedMaxCurve (restartMixedChart p.1) 0 p.2)

def restartMixedFlowRegular (p : RestartState × ℝ) : Prop :=
  0 < restartRadicand (restartExpCoordinates p.1) ∧
    p.2 ∈ normalizedMaxDomain (restartMixedChart p.1) 0 ∧
    normalizedMaxCurve (restartMixedChart p.1) 0 p.2 0 < 0 ∧
    0 < normalizedMaxCurve (restartMixedChart p.1) 0 p.2 2



























end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def restartCenterInclusion : RestartCenterState →L[ℝ] RestartState :=
  ContinuousLinearMap.pi ![0, ContinuousLinearMap.proj 0, ContinuousLinearMap.proj 1, ContinuousLinearMap.proj 2]

def restartMixedSection (h : ℝ) (Z : RestartCenterState) : RestartState :=
  ![Real.log h, Z 0, Z 1, Z 2]

def restartSectionMixedFlow (h t : ℝ) (Z : RestartCenterState) : RestartState :=
  restartMixedFlow (restartMixedSection h Z, t)



















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def restartWeakRateIntegrand (i : Fin 2) (p : RestartState × ℝ) : ℝ :=
  restartMixedWeakRates (restartMixedFlow p) i

def restartWeakLogMultiplier (T : ℝ) (i : Fin 2) (y : RestartState) : ℝ :=
  ∫ t in 0..T, restartWeakRateIntegrand i (y, t)

def restartWeakMultiplier (T : ℝ) (i : Fin 2) (y : RestartState) : ℝ :=
  Real.exp (restartWeakLogMultiplier T i y)





















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

/-- The exact center flow minus its limiting linear transfer, at fixed height and time. -/
def restartSectionRemainder (h t : ℝ) (Z : RestartCenterState) : RestartCenterState :=
  restartSectionCenterFlow h t Z - restartCenterTransfer h Z









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def restartSectionStrongWall (h t : ℝ) (Z : RestartCenterState) : ℝ :=
  normalizedMaxCurve (restartSectionChart h Z) 0 t 2

def restartSectionStrongLog (h t : ℝ) (Z : RestartCenterState) : ℝ :=
  Real.log (restartSectionStrongWall h t Z)



















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def restartSectionWeakMultiplier (h T : ℝ) (i : Fin 2) (Z : RestartCenterState) : ℝ :=
  restartWeakMultiplier T i (restartMixedSection h Z)

def restartSectionWeakLogMultiplier (h T : ℝ) (i : Fin 2) (Z : RestartCenterState) : ℝ :=
  restartWeakLogMultiplier T i (restartMixedSection h Z)









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

abbrev RestartRadialState := ℝ × RestartCenterState

def restartGramCoefficients (n : ℝ) : Fin 3 → ℝ :=
  ![restartShearFactor n ^ 2, 2 * restartShearFactor n * restartShearCoupling n,
    restartShearCoupling n ^ 2 + restartWallFactor n ^ 2]

def restartRootCoefficients (n : ℝ) : Fin 3 → ℝ :=
  ![0, restartShearFactor n * restartShearCoupling n,
    restartShearCoupling n ^ 2 + restartWallFactor n ^ 2]

def restartRotationCoefficients (n : ℝ) : Fin 3 → ℝ :=
  ![restartShearFactor n * restartShearCoupling n,
    restartShearCoupling n ^ 2 + restartWallFactor n ^ 2 - restartShearFactor n ^ 2,
    -(restartShearFactor n * restartShearCoupling n)]

def restartRadialCurvatureDifference (p : RestartRadialState) : ℝ :=
  (p.2 1 - p.2 2) ^ 2 - 2 * p.1 * (p.2 1 + p.2 2)

def restartRadialRootDifference (p : RestartRadialState) : ℝ :=
  Real.sqrt (restartSectionRadicand p.1 p.2) - restartReferenceRoot p.1

/-- Coefficients of the exact radial drift in the monomials s^2, s v, v^2. -/
def restartRadialDriftCoefficients (p : RestartRadialState) : Fin 3 → ℝ :=
  (p.1 * (restartRadialCurvatureDifference p - 2 * restartRadialRootDifference p)) •
      deriv restartGramCoefficients p.1 +
    (2 * restartRadialCurvatureDifference p) • restartGramCoefficients p.1 +
    (2 * restartRadialRootDifference p) • restartRootCoefficients p.1 +
    (2 * Real.sqrt 3 * (p.2 1 + p.2 2)) • restartRotationCoefficients p.1















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def restartRadialDrift (p : RestartRadialState) : ℝ :=
  quadraticFromCoefficients (restartRadialDriftCoefficients p) (p.2 0) (p.2 1 - p.2 2)











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def restartRadialQuadratic (p : RestartRadialState) : ℝ :=
  restartQuadratic p.1 (p.2 0) (p.2 1 - p.2 2)











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def restartSectionQuadratic (h t : ℝ) (Z : RestartCenterState) : ℝ :=
  restartQuadratic (restartSectionStrongWall h t Z) (restartSectionCenterFlow h t Z 0)
    (restartSectionCenterFlow h t Z 1 - restartSectionCenterFlow h t Z 2)

def restartSectionQuadraticRate (h t : ℝ) (Z : RestartCenterState) : ℝ :=
  restartRadialDrift (restartSectionStrongWall h t Z, restartSectionCenterFlow h t Z)

def restartSectionRadius (h t : ℝ) (Z : RestartCenterState) : ℝ :=
  Real.sqrt (restartSectionQuadratic h t Z)

def restartRadialNorm (Z : RestartCenterState) : ℝ :=
  Real.sqrt (Z 0 ^ 2 + (Z 1 - Z 2) ^ 2)









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def restartGramDefect (n : ℝ) : Fin 3 → ℝ := restartGramCoefficients n - ![1, 0, 1]







def restartRadialQuadraticDefect (p : RestartRadialState) : ℝ :=
  restartRadialQuadratic p - (p.2 0 ^ 2 + (p.2 1 - p.2 2) ^ 2)









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def restartSectionRadialState (h t : ℝ) (Z : RestartCenterState) : RestartRadialState :=
  (restartSectionStrongWall h t Z, restartSectionCenterFlow h t Z)







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def restartSectionRadiusRate (h t : ℝ) (Z : RestartCenterState) : ℝ :=
  restartSectionQuadraticRate h t Z / (2 * restartSectionRadius h t Z)



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def restartRadialPhase (Z : RestartCenterState) : ℝ := restartRadialNorm Z / Real.sqrt 3

def restartReferenceRadialPhase (h : ℝ) (Z : RestartCenterState) : ℝ :=
  Real.sqrt (restartQuadratic h (Z 0) (Z 1 - Z 2)) / Real.sqrt 3





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def restartSectionRadiusTail (h t : ℝ) (Z : RestartCenterState) : ℝ :=
  restartSectionRadius h t Z - restartRadialNorm (restartSectionCenterFlow h t Z)





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def restartSectionRadiusRegular (h : ℝ) (p : RestartCenterState × ℝ) : Prop :=
  0 < restartSectionRadicand h p.1 ∧
    p.2 ∈ normalizedMaxDomain (restartSectionChart h p.1) 0 ∧
    normalizedMaxCurve (restartSectionChart h p.1) 0 p.2 0 < 0 ∧
    restartSectionStrongWall h p.2 p.1 ^ 2 < 1 ∧ 0 < restartSectionQuadratic h p.2 p.1













end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def restartProjectionDefect (p : RestartRadialState) : ℝ :=
  (p.2 0) ^ 2 + curvature p.1 (p.2 1) (p.2 2)

def restartProjectionHeight (p : RestartRadialState) : ℝ :=
  restartProjectionDefect p / (1 + Real.sqrt (1 - restartProjectionDefect p))

def restartProjectionPhase (p : RestartRadialState) : ℝ :=
  2 * restartProjectionHeight p /
    Real.sqrt ((Real.sqrt 3 * p.2 0 - restartProjectionHeight p) ^ 2 + 3 * (p.2 1) ^ 2)





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

abbrev RestartProjectionNormal := Fin 3 → ℝ
abbrev RestartProjectionCenter := Fin 2 → ℝ
abbrev RestartProjectionParameters := RestartProjectionNormal × RestartProjectionCenter

def restartProjectionScaledState (p : RestartProjectionParameters) : RestartRadialState :=
  (p.1 0 * p.1 1, ![p.1 0 * p.2 0, p.1 0 * p.2 1, p.1 0 * p.1 2])

def restartProjectionScaledDefect (p : RestartProjectionParameters) : ℝ :=
  (p.2 0) ^ 2 + curvature (p.1 1) (p.2 1) (p.1 2)

def restartProjectionScaledHeight (p : RestartProjectionParameters) : ℝ :=
  restartProjectionScaledDefect p /
    (1 + Real.sqrt (1 - (p.1 0) ^ 2 * restartProjectionScaledDefect p))

def restartProjectionScaledDenom (p : RestartProjectionParameters) : ℝ :=
  (Real.sqrt 3 * p.2 0 - p.1 0 * restartProjectionScaledHeight p) ^ 2 + 3 * (p.2 1) ^ 2

def restartProjectionScaledError (p : RestartProjectionParameters) : ℝ :=
  2 * restartProjectionScaledHeight p / Real.sqrt (restartProjectionScaledDenom p) -
    Real.sqrt ((p.2 0) ^ 2 + (p.2 1 - p.1 2) ^ 2) / Real.sqrt 3













end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def restartSectionRadialError (h t : ℝ) (Z : RestartCenterState) : ℝ :=
  restartRadialPhase (restartSectionCenterFlow h t Z) - restartReferenceRadialPhase h Z







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def restartProjectionDefectTangent (p v : RestartRadialState) : ℝ :=
  2 * p.2 0 * v.2 0 + 4 * (p.1 * v.1 + p.2 1 * v.2 1 + p.2 2 * v.2 2) -
    2 * (p.1 + p.2 1 + p.2 2) * (v.1 + v.2 1 + v.2 2)















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def restartProjectionError (p : RestartRadialState) : ℝ :=
  restartProjectionPhase p - restartRadialPhase p.2

def restartProjectionParametersAt (r : ℝ) (p : RestartRadialState) : RestartProjectionParameters :=
  (![r, p.1 / r, p.2 2 / r], ![p.2 0 / r, p.2 1 / r])

def restartProjectionParameterTangent (r : ℝ) (v : RestartRadialState) : RestartProjectionParameters :=
  (![0, v.1 / r, v.2 2 / r], ![v.2 0 / r, v.2 1 / r])















end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def restartFastRadialPhase (h T θ ζ ρ : ℝ) : ℝ :=
  restartRadialPhase (restartSectionCenterFlow h T (restartRadialCurve θ ζ ρ))







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def restartFastProjectionPhase (h T θ ζ ρ : ℝ) : ℝ :=
  let x := normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 T
  2 / coreRadius (toProjectiveState x 0) (toProjectiveState x 2)

def restartFastProjectionError (h T θ ζ ρ : ℝ) : ℝ :=
  restartProjectionError (restartSectionRadialState h T (restartRadialCurve θ ζ ρ))



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def restartFastProjectionHeight (h T θ ζ ρ : ℝ) : ℝ :=
  1 + normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 T 0





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def restartFastCoreRadius (h T θ ζ ρ : ℝ) : ℝ :=
  let x := normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 T
  coreRadius (toProjectiveState x 0) (toProjectiveState x 2)







end BianchiIX

end
end


