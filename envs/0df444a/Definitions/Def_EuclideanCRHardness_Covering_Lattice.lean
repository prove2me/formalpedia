-- Prove2me | Definitions.Def_EuclideanCRHardness_Covering_Lattice
-- name    : EuclideanCRHardness_Covering_Lattice
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:26.415294+00:00
-- url     : https://prove2.me/theorems/2dbf8cb8-f2d6-4d06-ba6b-81a111d18ff5
-- title:
--   Euclidean lattice and covering radius
-- statement:
--   For a real square matrix $B$, let
--   $$\Lambda(B)=\{Bz:z\in\mathbb Z^n\},\qquad \mu(B)=\sup_{y\in\mathbb R^n}\inf_{z\in\mathbb Z^n}\|y-Bz\|_2.$$
--   The norm is the Euclidean norm of `EuclideanSpace`, and both optimization domains are unrestricted. The lattice is a set of all integer column combinations, not a finite sample.
--
--   On invertible bases the nearest-point minimum is attained and the distance range is bounded. Those semantic facts are independent theorem targets, never fields assumed by the model.
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, STOC 2027 submission #38 (October 2026), equation (1.1), printed p. 1 / PDF p. 2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/38.pdf

import Mathlib

namespace EuclideanCRHardness.Covering

open scoped BigOperators
/-- All integer combinations of the columns, in the actual Euclidean norm. -/
def latticePoint {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℤ) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => ∑ j, B i j * (z j : ℝ))
def lattice {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  Set.range (latticePoint B)
noncomputable def nearestDistance {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin n)) : ℝ := Metric.infDist y (lattice B)
noncomputable def coveringRadius {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup (Set.range (nearestDistance B))

end EuclideanCRHardness.Covering


