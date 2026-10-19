-- Prove2me | Definitions.Def_MazurTransfer_Order13ReflectionDiamondParameterOriginalDataAndConstructorCertificatesMinimalPublicNamespaceV220261018
-- name    : MazurTransfer_Order13ReflectionDiamondParameterOriginalDataAndConstructorCertificatesMinimalPublicNamespaceV220261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T21:19:45.792333+00:00
-- url     : https://prove2.me/theorems/0700cc51-d486-477a-841b-8712d08336e6
-- title:
--   Original diamond action on reflection parameters
-- statement:
--   The original cubic and square certificates construct the diamond-transformed reflection parameter, with coordinates t mapped to diamondX(t) and s mapped to s/(t+1). Five complete original declaration types and the whole constructor value are checked. Named downstream consumer: MazurTransfer.Order13ActualReflectionDiamondRelation.reflectionFieldMap_diamond. The quadratic-thirteen identity and arithmetic orbit identities remain separate theorems.
-- source:
--   MazurTheorem Order13ReflectionParameterArithmetic, exact original diamondParameter constructor and its immediate polynomial and denominator certificates; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: checked algebraic coefficient identities for the reflection,
including its diamond orbit and its quadratic coefficient over the cubic field.
Named downstream consumer: the Galois orbit of the actual reflection, used
to identify the cyclotomic quotient kernel's arithmetic character.
-/
/- Constructor interface: the original diamond action on reflection parameters, including only its nonzero-coordinate and record-construction certificates. Named downstream consumer: MazurTransfer.Order13ActualReflectionDiamondRelation.reflectionFieldMap_diamond. The quadratic-thirteen identity and orbit cube formulas remain separate results. -/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ReflectionCoordinatesAndParameterOriginalDataSingleUniverseBlockV220261018
noncomputable section
universe u
namespace MazurTransfer.Order13ReflectionParameterArithmetic
open Order13ReflectionSexticSymmetry Order13ReflectionParameter
open Order13DiamondSexticSymmetry
variable {K : Type u} [Field K]

theorem parameter_t_ne_zero (a : ReflectionParameter K) : a.t ≠ 0 := by
  intro h
  have hc := a.cubic_eq_zero
  rw [h] at hc
  norm_num [reflectionCubic] at hc

theorem parameter_t_add_one_ne_zero (a : ReflectionParameter K) : a.t + 1 ≠ 0 := by
  intro h
  have he : a.t = -1 := by linear_combination h
  have hc := a.cubic_eq_zero
  rw [he] at hc
  norm_num [reflectionCubic] at hc

theorem transformed_cubic (a : ReflectionParameter K) : reflectionCubic (diamondX a.t) = 0 := by
  have ht := a.cubic_eq_zero
  have hd := parameter_t_add_one_ne_zero a
  dsimp [reflectionCubic] at ht
  dsimp [reflectionCubic, diamondX]
  field_simp [hd]
  linear_combination -ht

theorem transformed_square (a : ReflectionParameter K) :
    (a.s / (a.t + 1)) ^ 2 = reflectionScalar (diamondX a.t) := by
  have hs := a.square_eq_scalar
  have hd := parameter_t_add_one_ne_zero a
  dsimp [reflectionScalar] at hs
  dsimp [reflectionScalar, diamondX]
  field_simp [hd]
  linear_combination hs

def diamondParameter (a : ReflectionParameter K) : ReflectionParameter K where
  t := diamondX a.t
  s := a.s / (a.t + 1)
  cubic_eq_zero := transformed_cubic a
  square_eq_scalar := transformed_square a

end MazurTransfer.Order13ReflectionParameterArithmetic
#print axioms MazurTransfer.Order13ReflectionParameterArithmetic.diamondParameter


