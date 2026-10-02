-- Prove2me | Definitions.Def_DiscreteConvex_AlgorithmsC_DomR
-- name    : DiscreteConvex_AlgorithmsC_DomR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T04:19:11.366783+00:00
-- url     : https://prove2.me/theorems/6e5aeebc-e89a-43f3-824f-9111eb01ac54
-- title:
--   Effective domain of a real-domain function
-- statement:
--   The effective domain $\{x\in\mathbb{R}^V : f(x)\ne+\infty\}$ of a real-domain function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §10.3.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §10.3

import Mathlib

namespace DiscreteConvex.AlgorithmsC

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The effective domain of a real-domain function. -/
def DomR (g : (V → ℝ) → WithTop ℝ) : Set (V → ℝ) := {x | g x ≠ ⊤}

end DiscreteConvex.AlgorithmsC


