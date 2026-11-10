-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ConcreteParameters
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ConcreteParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T03:04:19.985536+00:00
-- url     : https://prove2.me/theorems/491fe7ed-31ad-4663-84d8-be30997db8c9
-- title:
--   Concrete Parameters
-- statement:
--   Definitions and structural lemmas for Concrete Parameters, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ConcreteParameters.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ProbabilityDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_DependencyCounts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_LLLCriterion
set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
def triangleDensityBound : ℕ := 4*56^3
noncomputable def capCutoff (m : ℕ) : ℝ := Real.cos (1/(12*(m : ℝ)))
def anchorRadius (m : ℕ) : ℕ := 12*m+4
def dependencyBound (M : ℕ) : ℕ := 12*56*M^3
noncomputable def densityHandoff (m : ℕ) : ℝ :=
  64*Real.pi*triangleDensityBound*(2*(6*(m : ℝ))+1)^2/
    ((6*(m : ℝ)*widthFactor-1)*((m : ℝ)-1))
structure GeometricParameters (densityLower : ℝ) where
  m : ℕ
  t : ℝ
  M : ℕ
  lambda : ℕ
  m_two : 2 ≤ m
  width_positive : 1 < 6*(m : ℝ)*widthFactor
  t_positive : 0 < t
  density_lower : densityLower < t
  triangle_density : (triangleDensityBound : ℝ) < t
  handoff : densityHandoff m < t
  pool : (2*anchorRadius m+1 : ℕ)^3*(250*t) ≤ (M : ℝ)
  lambda_one : 1 ≤ lambda
  rounding : 13 ≤ (2*(6*(m : ℝ))+1)*(lambda : ℝ)
  probability : 4*probabilityCoefficient (6*m) (capCutoff m)*
    ((dependencyBound M : ℝ)+1) ≤ (lambda : ℝ)
end QEC.Coding.BDL26RandomPerturbation


