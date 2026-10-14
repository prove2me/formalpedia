-- Prove2me | Definitions.Def_evaluationMap
-- name    : evaluationMap
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-14T09:12:22.715564+00:00
-- url     : https://prove2.me/theorems/7125c80d-12c7-4961-bb2f-5d684225c3ac
-- title:
--   Coordinate evaluation map
-- statement:
--   The linear map sending a vector to the function of its evaluations under the given family of linear functionals.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.LinearAlgebra.LinearIndependent.Basic

def evaluationMap
    {K V ι : Type} [Field K] [AddCommGroup V] [Module K V]
    (L : ι → V →ₗ[K] K) : V →ₗ[K] (ι → K) where
  toFun v x := L x v
  map_add' v w := by
    ext x
    simp
  map_smul' a v := by
    ext x
    simp


