-- Prove2me | Definitions.Def_ReflectedBSDE_Obstacle_Jet
-- name    : ReflectedBSDE_Obstacle_Jet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:56.873988+00:00
-- url     : https://prove2.me/theorems/203c7eee-82e1-490a-8f76-c7ce448aaaa3
-- title:
--   Symmetric parabolic jet triple
-- statement:
--   A parabolic second-order jet is a triple $(p,q,X)$ consisting of a real time slope $p$, a spatial vector $q\in\mathbb R^d$, and a symmetric real $d\times d$ matrix $X$.
--
--   $$
--   (p,q,X)\in\mathbb R\times\mathbb R^d\times S(d).
--   $$
--
--   It supplies the local quadratic data used to test viscosity inequalities.
--
--   **Formalization Note** The printed phrase “symmetric nonnegative matrices” is treated as a misprint. Theorem 8.6 invokes a theorem of sums that produces arbitrary symmetric matrices.
-- source:
--   El Karoui, Kapoudjian, Pardoux, Peng & Quenez, Reflected solutions of backward SDE's, and related obstacle problems for PDE's, Ann. Probab. 25(2) (1997), p. 728, Definition 8.1

import Mathlib

namespace ReflectedBSDE.Obstacle

/-- A parabolic second-order jet triple. The Hessian is symmetric, with no
positivity restriction; the printed positivity in Definition 8.1 conflicts
with the theorem of sums used in the proof of Theorem 8.6. -/
structure Jet (d : ℕ) where
  p : ℝ
  q : Fin d → ℝ
  X : Matrix (Fin d) (Fin d) ℝ
  symm : X.IsSymm

end ReflectedBSDE.Obstacle


