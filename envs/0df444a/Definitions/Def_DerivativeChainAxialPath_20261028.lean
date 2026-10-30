-- Prove2me | Definitions.Def_DerivativeChainAxialPath_20261028
-- name    : DerivativeChainAxialPath_20261028
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-28T04:22:50.953441+00:00
-- url     : https://prove2.me/theorems/eec4e29f-09b7-4460-9fb5-46643cde78bb
-- title:
--   Finite complex paths and length-weighted angular charges
-- statement:
--   Definitions for finite complex vertex lists, their consecutive differences, quadratic edge covariance, and the length-weighted angular charge from the first edge. The explicit zigzag family is indexed by a positive integer. No polynomial derivative-root realization is asserted.
-- source:
--   Private repository Amal-David/derivative-chain-prize at fb2d3b3438371d1ef39da0092241fb0db2bd6859; research-results/unrestricted-4r-20261027/formal/AxialPathObstruction.lean; SHA-256 ce69d2b671675fed81e24468ac93b488412b8e3469750059ff184ecce68eefbc

import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

set_option autoImplicit false

/-! An exact geometric countermodel, not a derivative-root tower. -/
namespace AxialPathObstruction

def zigEdges (a : ℝ) : ℕ → List ℂ
  | 0 => []
  | k+1 => ((a : ℂ)*Complex.I) :: (-((a : ℂ)*Complex.I)) :: zigEdges a k

def zigVertices (h a : ℝ) : ℕ → List ℂ
  | 0 => []
  | k+1 => ((h : ℂ)+(a : ℂ)*Complex.I) :: (h : ℂ) :: zigVertices h a k

def vertices (h a : ℝ) (k : ℕ) : List ℂ :=
  0 :: (h : ℂ) :: zigVertices h a k

def edges (h a : ℝ) (k : ℕ) : List ℂ := (h : ℂ) :: zigEdges a k

def differences : List ℂ → List ℂ
  | [] => []
  | [_] => []
  | x :: y :: zs => (y-x) :: differences (y :: zs)


def sxx (e : List ℂ) : ℝ := (e.map (fun v => v.re^2)).sum
def sxy (e : List ℂ) : ℝ := (e.map (fun v => v.re*v.im)).sum
def syy (e : List ℂ) : ℝ := (e.map (fun v => v.im^2)).sum
def covarianceDet (e : List ℂ) : ℝ := sxx e * syy e - (sxy e)^2

def wedge (v w : ℂ) : ℝ := v.re*w.im-v.im*w.re
def dot (v w : ℂ) : ℝ := v.re*w.re+v.im*w.im

/-- Equal to |v||w| sin²(angle(v,w)) for nonzero vectors. -/
noncomputable def angularCharge (v w : ℂ) : ℝ :=
  (wedge v w)^2 / (‖v‖*‖w‖)

noncomputable def mixedCharge (h a : ℝ) (k : ℕ) : ℝ :=
  ((zigEdges a k).map (angularCharge (h : ℂ))).sum

noncomputable def firstAngularCharge : List ℂ → ℝ
  | [] => 0
  | v :: vs => (vs.map (angularCharge v)).sum







































noncomputable def amplitude (M : ℕ) : ℝ := 1/(4*(M : ℝ))
def cycles (M : ℕ) : ℕ := 2*M^2




































end AxialPathObstruction


