-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricScanCost
-- name    : QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricScanCost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T09:32:55.283935+00:00
-- url     : https://prove2.me/theorems/ef6ab9e5-c8d0-4b16-a12f-e67e4c0bef8e
-- title:
--   Native Geometric Scan Cost
-- statement:
--   Definitions and structural lemmas for Native Geometric Scan Cost, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricScanCost.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeKeyExecutionBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26NativeGeometricScanCost
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open BDL26NativeKeyExecutionBridge
open scoped Classical
def triangleCount (S : OddScale) (n : ℕ) : ℕ :=
  (BDL26NativeMasterCandidates.actualCodes S n).length
def masterCount (S : OddScale) (n : ℕ) : ℕ :=
  Nat.choose (triangleCount S n) 4
def incomingBudget (S : OddScale) (n : ℕ) : ℕ :=
  (BDL26NativePresentationGenerator.setupQ S n).2+
    2*(SR.count S n)^2+12*SR.count S n+4
def atlasReadBudget (S : OddScale) (n : ℕ) : ℕ :=
  43*triangleCount S n+1
def colorBudget (S : OddScale) (n : ℕ) : ℕ :=
  (BDL26NativeTriangleColors.colorsQ S n).operations+43*triangleCount S n+3
def pairBudget (S : OddScale) (n : ℕ) : ℕ :=
  2*colorBudget S n+incomingBudget S n+4*SR.count S n+2007
def eligibilityBudget (S : OddScale) (n : ℕ) : ℕ :=
  4*(4*(pairBudget S n+1)+1)
def preprocessingBudget (S : OddScale) (n : ℕ) : ℕ :=
  (MC.masterCandidatesQ S n).operations+
    masterCount S n*(eligibilityBudget S n+2)+1+
    (masterCount S n+1)^2*159
def pointBudget (incomingRows stateRows : ℕ) : ℕ :=
  2*incomingRows+2*stateRows+49
def triangleBudget (S : OddScale) (n stateRows : ℕ) : ℕ :=
  (MD.atlasQ S n).operations+atlasReadBudget S n+incomingBudget S n+
    3*pointBudget (SR.count S n) stateRows+200004
def centerBudget (S : OddScale) (n K : ℕ) : ℕ :=
  36+(MD.atlasQ S n).operations+atlasReadBudget S n+incomingBudget S n+
    (2*SR.count S n+1)+(3*K+9)+45+3
def gridBudget (K : ℕ) : ℕ :=
  6*(2*K+1)^3+3*(2*K+1)^2+5*(2*K+1)+1
def queryBudget (S : OddScale) (n K stateRows : ℕ) : ℕ :=
  gridBudget K+(2*K+1)^3*
    (centerBudget S n K+4*(triangleBudget S n stateRows+1)+3)+1
def scanBudget (S : OddScale) (n K stateRows : ℕ) : ℕ :=
  preprocessingBudget S n+masterCount S n*(queryBudget S n K stateRows+1)+1
def closedScanBudget (a b K z : ℕ) : ℕ :=
  let incoming := a+2*b^2+12*b+4
  let atlas := a+178*b^2+50*b+2
  let colors := a+275*b^2+103*b+4
  let pair := 2*(colors+43*b+3)+incoming+4*b+2007
  let eligible := 4*(4*(pair+1)+1)
  let masters := a+(b+1)^4*(a+178*b^2+222*b+509)+13*(b+1)^3+2
  let preprocess := masters+b^4*(eligible+2)+1+(b^4+1)^2*159
  let triangle := atlas+(43*b+1)+incoming+3*(2*b+2*z+49)+200004
  let center := 36+atlas+(43*b+1)+incoming+(2*b+1)+(3*K+9)+45+3
  let query := gridBudget K+(2*K+1)^3*(center+4*(triangle+1)+3)+1
  preprocess+b^4*(query+1)+1
def scanPolynomialConstant (K : ℕ) : ℕ :=
  gridBudget K+(2*K+1)^3*(3*K+802225)+61537
def qubitRadius (S : OddScale) (n : ℕ) : ℕ :=
  (132*(Fintype.card (Presentation S n).Q+1))^221
end QEC.Coding.BDL26NativeGeometricScanCost


