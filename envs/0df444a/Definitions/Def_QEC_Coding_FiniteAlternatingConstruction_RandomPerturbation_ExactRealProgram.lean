-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:11:09.805683+00:00
-- url     : https://prove2.me/theorems/e68876af-086e-46ca-a3f9-7fb57819e681
-- title:
--   Exact Real Program
-- statement:
--   Definitions and structural lemmas for Exact Real Program, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/ExactRealProgram.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
set_option autoImplicit false
namespace QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace BigOperators
inductive RealExpr where
  | constant (x : ℝ)
  | vertex (i j : Fin 3)
  | center (j : Fin 3)
  | radius
  | add (a b : RealExpr)
  | sub (a b : RealExpr)
  | mul (a b : RealExpr)
  | div (a b : RealExpr)
  | min (a b : RealExpr)
  | max (a b : RealExpr)
noncomputable def RealExpr.eval (a : Fin 3 → Space) (z : Space) (ρ : ℝ) : RealExpr → ℝ
  | .constant x => x
  | .vertex i j => a i j
  | .center j => z j
  | .radius => ρ
  | .add x y => x.eval a z ρ+y.eval a z ρ
  | .sub x y => x.eval a z ρ-y.eval a z ρ
  | .mul x y => x.eval a z ρ*y.eval a z ρ
  | .div x y => x.eval a z ρ/y.eval a z ρ
  | .min x y => Min.min (x.eval a z ρ) (y.eval a z ρ)
  | .max x y => Max.max (x.eval a z ρ) (y.eval a z ρ)
def RealExpr.cost : RealExpr → ℕ
  | .constant _ | .vertex _ _ | .center _ | .radius => 1
  | .add x y | .sub x y | .mul x y | .div x y | .min x y | .max x y =>
    1+x.cost+y.cost
inductive RealTest where
  | le (a b : RealExpr)
  | ne (a b : RealExpr)
  | both (a b : RealTest)
  | either (a b : RealTest)
noncomputable def RealTest.eval (a : Fin 3 → Space) (z : Space) (ρ : ℝ) : RealTest → Bool
  | .le x y => decide (x.eval a z ρ ≤ y.eval a z ρ)
  | .ne x y => decide (x.eval a z ρ ≠ y.eval a z ρ)
  | .both x y => x.eval a z ρ && y.eval a z ρ
  | .either x y => x.eval a z ρ || y.eval a z ρ
def RealTest.cost : RealTest → ℕ
  | .le x y | .ne x y => 1+x.cost+y.cost
  | .both x y | .either x y => 1+x.cost+y.cost
abbrev VecExpr := Fin 3 → RealExpr
def dotExpr (b c : VecExpr) : RealExpr :=
  .add (.mul (b 0) (c 0)) (.add (.mul (b 1) (c 1)) (.mul (b 2) (c 2)))
def subExpr (b c : VecExpr) : VecExpr := fun j => .sub (b j) (c j)
def addExpr (b c : VecExpr) : VecExpr := fun j => .add (b j) (c j)
def smulExpr (x : RealExpr) (b : VecExpr) : VecExpr := fun j => .mul x (b j)
def vertexExpr (i : Fin 3) : VecExpr := .vertex i
def centerExpr : VecExpr := .center
def segmentExpr (i j : Fin 3) : VecExpr :=
  let b := subExpr (vertexExpr j) (vertexExpr i)
  let d := subExpr centerExpr (vertexExpr i)
  let t := RealExpr.max (.constant 0) (.min (.constant 1) (.div (dotExpr d b) (dotExpr b b)))
  addExpr (vertexExpr i) (smulExpr t b)
def determinantExpr : RealExpr :=
  let b := subExpr (vertexExpr 1) (vertexExpr 0)
  let c := subExpr (vertexExpr 2) (vertexExpr 0)
  .sub (.mul (dotExpr b b) (dotExpr c c)) (.mul (dotExpr b c) (dotExpr b c))
def planeUExpr : RealExpr :=
  let b := subExpr (vertexExpr 1) (vertexExpr 0)
  let c := subExpr (vertexExpr 2) (vertexExpr 0)
  let d := subExpr centerExpr (vertexExpr 0)
  .div (.sub (.mul (dotExpr c c) (dotExpr d b)) (.mul (dotExpr b c) (dotExpr d c))) determinantExpr
def planeVExpr : RealExpr :=
  let b := subExpr (vertexExpr 1) (vertexExpr 0)
  let c := subExpr (vertexExpr 2) (vertexExpr 0)
  let d := subExpr centerExpr (vertexExpr 0)
  .div (.sub (.mul (dotExpr b b) (dotExpr d c)) (.mul (dotExpr b c) (dotExpr d b))) determinantExpr
def planeExpr : VecExpr := addExpr
  (addExpr (vertexExpr 0) (smulExpr planeUExpr (subExpr (vertexExpr 1) (vertexExpr 0))))
  (smulExpr planeVExpr (subExpr (vertexExpr 2) (vertexExpr 0)))
def distanceTest (b : VecExpr) : RealTest :=
  let d := subExpr centerExpr b
  .le (dotExpr d d) (.mul .radius .radius)
def triangleQueryProgram : RealTest :=
  .both (.le (.constant 0) .radius)
  (.either (distanceTest (vertexExpr 0))
  (.either (distanceTest (vertexExpr 1))
  (.either (distanceTest (vertexExpr 2))
  (.either (distanceTest (segmentExpr 0 1))
  (.either (distanceTest (segmentExpr 0 2))
  (.either (distanceTest (segmentExpr 1 2))
    (.both (.ne determinantExpr (.constant 0))
      (.both (.le (.constant 0) planeUExpr)
        (.both (.le (.constant 0) planeVExpr)
          (.both (.le (.add planeUExpr planeVExpr) (.constant 1)) (distanceTest planeExpr)))))))))))
noncomputable def RealExpr.run (a : Fin 3 → Space) (z : Space) (ρ : ℝ) : RealExpr → ℝ × ℕ
  | .constant x => (x,1)
  | .vertex i j => (a i j,1)
  | .center j => (z j,1)
  | .radius => (ρ,1)
  | .add x y =>
      let X := x.run a z ρ; let Y := y.run a z ρ
      (X.1+Y.1,1+X.2+Y.2)
  | .sub x y =>
      let X := x.run a z ρ; let Y := y.run a z ρ
      (X.1-Y.1,1+X.2+Y.2)
  | .mul x y =>
      let X := x.run a z ρ; let Y := y.run a z ρ
      (X.1*Y.1,1+X.2+Y.2)
  | .div x y =>
      let X := x.run a z ρ; let Y := y.run a z ρ
      if Y.1 = 0 then (0,1+X.2+Y.2) else (X.1/Y.1,2+X.2+Y.2)
  | .min x y =>
      let X := x.run a z ρ; let Y := y.run a z ρ
      (Min.min X.1 Y.1,1+X.2+Y.2)
  | .max x y =>
      let X := x.run a z ρ; let Y := y.run a z ρ
      (Max.max X.1 Y.1,1+X.2+Y.2)
noncomputable def RealTest.run (a : Fin 3 → Space) (z : Space) (ρ : ℝ) : RealTest → Bool × ℕ
  | .le x y =>
      let X := x.run a z ρ; let Y := y.run a z ρ
      (decide (X.1 ≤ Y.1),1+X.2+Y.2)
  | .ne x y =>
      let X := x.run a z ρ; let Y := y.run a z ρ
      (decide (X.1 ≠ Y.1),1+X.2+Y.2)
  | .both x y =>
      let X := x.run a z ρ; let Y := y.run a z ρ
      (X.1 && Y.1,1+X.2+Y.2)
  | .either x y =>
      let X := x.run a z ρ; let Y := y.run a z ρ
      (X.1 || Y.1,1+X.2+Y.2)
noncomputable def triangleQuery (a : Fin 3 → Space) (z : Space) (ρ : ℝ) : Bool × ℕ :=
  triangleQueryProgram.run a z ρ
end QEC.Coding.BDL26RandomPerturbation


