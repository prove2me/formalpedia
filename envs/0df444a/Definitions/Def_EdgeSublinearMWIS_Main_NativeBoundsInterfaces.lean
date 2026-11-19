-- Prove2me | Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces
-- name    : EdgeSublinearMWIS_Main_NativeBoundsInterfaces
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T15:53:57.104164+00:00
-- url     : https://prove2.me/theorems/a1091e89-184d-483a-9472-2ed4ace5a97c
-- title:
--   State and bounds interfaces for native search and oracle rounds
-- statement:
--   These declarations expose the stored interval and reconstruction states, initialized ellipsoid searches, compiled flow optima, and numerical bounds used to instantiate recursive oracle rounds. They define the parameter functions, fixed input predicates and the bounds record's immediate projection interface.
--
--   For word bound $B$, a stored command contract has the form
--   $$P(\sigma)\Longrightarrow\exists\tau,\ \operatorname{Run}_B(c,\sigma,\tau,T)\land Q(\sigma,\tau).$$
--   These interfaces supply the stored data and numerical predicates. Execution, exact feasibility, reconstruction, recursive correctness and resource domination are separate theorem obligations.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/BinaryOptimization.lean (definitions and structure interfaces, starting at lines 9, 63)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/CoordinateOptimization.lean (definitions and structure interfaces, starting at lines 12, 50)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/LexicographicMinima.lean (definitions and structure interfaces, starting at lines 14)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamBisectionLoop.lean (definitions and structure interfaces, starting at lines 12, 16)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamFeasibilitySetup.lean (definitions and structure interfaces, starting at lines 24)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamPaddedFeasibility.lean (definitions and structure interfaces, starting at lines 36)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamQueryPadding.lean (definitions and structure interfaces, starting at lines 16)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamRationalScalars.lean (definitions and structure interfaces, starting at lines 12)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamReconstructionRecord.lean (definitions and structure interfaces, starting at lines 11)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamSearchStep.lean (definitions and structure interfaces, starting at lines 30)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamSeparation.lean (definitions and structure interfaces, starting at lines 183)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RationalReconstruction.lean (definitions and structure interfaces, starting at lines 49, 192)
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeRecursiveDomain.lean (definitions and structure interfaces, starting at lines 12)
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeRecursiveOracle.lean (definitions and structure interfaces, starting at lines 51)
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeRoundedResources.lean (definitions and structure interfaces, starting at lines 12)
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeSelectedRounds.lean (definitions and structure interfaces, starting at lines 16, 17, 18, 19, 20, 21, 23, 25, 29, 38, 40, 43, 44, 45, 46, 47, 48, 49, 50, 52, 54, 55, 56, 57, 58, 59, 60, 61)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamDualDistances.lean (definitions and structure interfaces, starting at lines 11)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamDualDistancesInit.lean (definitions and structure interfaces, starting at lines 25, 102, 104, 107)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamFloydWarshall.lean (definitions and structure interfaces, starting at lines 11, 15)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamMetricIndices.lean (definitions and structure interfaces, starting at lines 10)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamMetricPivot.lean (definitions and structure interfaces, starting at lines 25, 71, 73)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamMinPlus.lean (definitions and structure interfaces, starting at lines 12, 15)

import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Definitions.Def_EdgeSublinearMWIS_Main_NativeBlockInterfaces

-- Solutions.RAM_Lax109476Proofs_RationalReconstruction
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RationalReconstruction





/-- Computable continued-fraction convergents of a rational approximation. -/
def convergent : ℚ → ℕ → ℚ
  | a, 0 => Int.floor a
  | a, k + 1 => Int.floor a + (convergent (Int.fract a)⁻¹ k)⁻¹



























/-- Scan only the logarithmically many convergents, checking exact rational
inequalities and the promised denominator bound. -/
def reconstruct (l u : ℚ) (B : ℕ) : Option ℚ :=
  ((List.range (2 * u.den.size + 1)).map (convergent u)).find?
    (fun q => decide (q.den ≤ B ∧ l ≤ q ∧ q ≤ u))





end Lax109476Proofs.RationalReconstruction

end

-- Solutions.RAM_Lax109476Proofs_BinaryOptimization
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.BinaryOptimization

open RationalReconstruction

/-- A threshold query says that the attained minimum is at most `t`. -/
def bisect (query : ℚ → Bool) : ℚ → ℚ → ℕ → ℚ × ℚ
  | l, u, 0 => (l, u)
  | l, u, k + 1 =>
    let old := bisect query l u k
    let mid := (old.1 + old.2) / 2
    if query mid then (old.1, mid) else (mid, old.2)







/-- Exact recovery of a bounded rational minimum uses logarithmically many
threshold queries followed by the bounded continued-fraction scan. -/
def minimum (query : ℚ → Bool) (B : ℕ) : Option ℚ :=
  let interval := bisect query 0 B (steps B)
  reconstruct interval.1 interval.2 B



end Lax109476Proofs.BinaryOptimization

end

-- Solutions.RAM_Lax109476Proofs_CoordinateOptimization
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators

namespace Lax109476Proofs.CoordinateOptimization

open Lax109476.LinearProgram Lax109476.RationalCertificates

/-- One additional rational inequality asks whether coordinate `j` can be
at most the binary-search threshold `t`. -/
def coordinateCut {m n : ℕ} (P : Program ℚ m n) (j : Fin n) (t : ℚ) :
    Program ℚ (m + 1) n where
  A := Fin.addCases P.A (fun _ k => if k = j then 1 else 0)
  b := Fin.addCases P.b (fun _ => t)
  c := P.c



def coordinateMinimum {m n : ℕ} (P : Program ℚ m n) (j : Fin n) (B : ℕ) : Option ℚ :=
  BinaryOptimization.minimum (fun t => RationalFeasibilityDecision.feasible (coordinateCut P j t)) B



end Lax109476Proofs.CoordinateOptimization

end

-- Solutions.RAM_Lax109476Proofs_LexicographicMinima
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

open scoped BigOperators Matrix

namespace Lax109476Proofs.LexicographicMinima

open Lax109476.LinearProgram Lax109476.RationalCertificates



def fixedPrefix {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) (k : ℕ) :
    Program ℚ (m + (n + n)) n where
  A := Fin.addCases P.A (Fin.addCases
    (fun i j => if i.val < k then if j = i then 1 else 0 else 0)
    (fun i j => if i.val < k then if j = i then -1 else 0 else 0))
  b := Fin.addCases P.b (Fin.addCases
    (fun i => if i.val < k then x i else 0)
    (fun i => if i.val < k then -x i else 0))
  c := P.c













end Lax109476Proofs.LexicographicMinima

end

-- Solutions.RAM_Lax109476Proofs_RamRationalScalars
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamRationalScalars

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RamRationalArrays

def Value (name : String) (q : ℚ) (σ : Env) : Prop :=
  fractionValue (σ.vars (name ++ ".s")) (σ.vars (name ++ ".n")) (σ.vars (name ++ ".d")) = q ∧
    σ.vars (name ++ ".n") = q.num.natAbs ∧ σ.vars (name ++ ".d") = q.den ∧
    σ.vars (name ++ ".s") ≤ 1













end Lax109476Proofs.RamRationalScalars

end

-- Solutions.RAM_Lax109476Proofs_RamBisectionLoop
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamBisectionLoop

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RationalArithmeticBounds RamRationalScalars
open BinaryOptimization RamBisectionCommit

def fields : List String := ["bisect.lo.s", "bisect.lo.n", "bisect.lo.d",
  "bisect.hi.s", "bisect.hi.n", "bisect.hi.d", "bisect.mid.s", "bisect.mid.n", "bisect.mid.d",
  "bisect.i", "bisect.limit"]

def preserves (B : ℕ) (Q : Env → Prop) (c : Com) : Prop :=
  ∀ {σ τ k}, Run B c σ τ k → Q σ → Q τ













end Lax109476Proofs.RamBisectionLoop

end

-- Solutions.RAM_Lax109476Proofs_RamSeparation
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped BigOperators

namespace Lax109476Proofs.RamSeparation

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamDotProduct RamMatrixRows RamComparison RationalArithmeticBounds

































def rowCost (n H : ℕ) : ℕ := 4 + ((144 * (cap n H).size + 216 + 4) * n + 12) + 59















end Lax109476Proofs.RamSeparation

end

-- Solutions.RAM_Lax109476Proofs_RamSearchStep
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


open scoped Matrix BigOperators

namespace Lax109476Proofs.RamSearchStep

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamMatrixRows RamSeparation RamNormalSelection RamTrajectoryBounds
open RamEllipsoidStep RamEllipsoidBitBounds RamAdvanceState EllipsoidSearch RationalArithmeticBounds









def cost (m n K l : ℕ) : ℕ :=
  ((rowCost n (2 ^ stateBits n K l) + 20) * m + 8) + 126 * n + 83 +
    (stepCost n (2 ^ stateBits n K l) (2 ^ magnitudeExponent n (stateBits n K l) K) +
      71 * n + 71 * (n * n) + 60) + 12



-- The iteration-loop proof will use this fixed body and a variant
-- `search.limit - iter.k`; success lowers the limit to the current index.




end Lax109476Proofs.RamSearchStep

end

-- Solutions.RAM_Lax109476Proofs_RamFeasibilitySetup
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamFeasibilitySetup

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamMatrixStorage RamEllipsoidStep IntegerEncoding NormalizedFeasibility
open RamNormalizedBounds







def Input {m n : ℕ} (P : Program ℤ m n) (S : ℕ) (σ : Env) : Prop :=
  Represents "pad.A" (RamMatrixStorage.flatten (rationalProgram P).A) σ ∧
    Represents "pad.b" (List.ofFn (rationalProgram P).b) σ ∧
    Extents "search.rows" ((m + n) * n) σ ∧ Extents "search.rhs" (m + n) σ ∧
    Extents "ell.center" n σ ∧ Extents "ell.shape" (n * n) σ ∧ Workspace n σ ∧
    Extents "ell.normal" n σ ∧ σ.vars "query.m" = m ∧ σ.vars "query.n" = n ∧ σ.vars "query.bits" = S



end Lax109476Proofs.RamFeasibilitySetup

end

-- Solutions.RAM_Lax109476Proofs_RamQueryPadding
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamQueryPadding

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RationalArithmeticBounds RamEllipsoidStep RamMatrixStorage



def Input {m n : ℕ} (P : Program ℚ m n) (S : ℕ) (σ : Env) : Prop :=
  Represents "query.A" (RamMatrixStorage.flatten P.A) σ ∧ Represents "query.b" (List.ofFn P.b) σ ∧
    Extents "pad.A" ((m + 2) * (n + 2)) σ ∧ Extents "pad.b" (m + 2) σ ∧
    σ.vars "source.m" = m ∧ σ.vars "source.n" = n ∧ σ.vars "source.bits" = S





end Lax109476Proofs.RamQueryPadding

end

-- Solutions.RAM_Lax109476Proofs_RamPaddedFeasibility
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamPaddedFeasibility

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RamMatrixStorage IntegerEncoding RationalArithmeticBounds

 







def Input {m n : ℕ} (P : Program ℤ m n) (S : ℕ) (σ : Env) : Prop :=
  RamQueryPadding.Input (rationalProgram P) S σ ∧
    Extents "search.rows" (((m + 2) + (n + 2)) * (n + 2)) σ ∧
    Extents "search.rhs" ((m + 2) + (n + 2)) σ ∧
    Extents "ell.center" (n + 2) σ ∧ Extents "ell.shape" ((n + 2) * (n + 2)) σ ∧
    Workspace (n + 2) σ ∧ Extents "ell.normal" (n + 2) σ



end Lax109476Proofs.RamPaddedFeasibility

end

-- Solutions.RAM_Lax109476Proofs_RamReconstructionRecord
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamReconstructionRecord

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamFractionInterface RationalArithmeticBounds RamRationalScalars

def Output (r : Option ℚ) (σ : Env) : Prop := match r with
  | none => σ.vars "recon.found" = 0
  | some q => σ.vars "recon.found" = 1 ∧ Value "recon.result" q σ









end Lax109476Proofs.RamReconstructionRecord

end

-- Solutions.RAM_Lax455465Proofs_RamDualDistancesInit
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamDualDistancesInit

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational DirectedFlowLP MetricMatrix
open scoped NNRat







def coefficient : Com := .seq indices
  (.ite (.eq (.var "metric.u") (.var "metric.v")) RamFractionPrimitives.zero
    (RamUnsignedBuffer.read "flow.dual" "metric.entry"))









def build : Com := RamUnsignedVector.command "metric.entry" "metric.n2" "metric.old" "metric.position" coefficient

def setup : Com := .seq (.assign "metric.n" (.var "lp.n"))
  (.seq (.assign "metric.n2" (.var "lp.n2")) (.assign "metric.position" (.lit 0)))

def command : Com := .seq setup build



end Lax455465Proofs.RamDualDistancesInit

end

-- Solutions.RAM_Lax455465Proofs_RamMetricIndices
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamMetricIndices

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning DirectedFlowLP

def command : Com := .seq (.assign "metric.a" (.var "metric.entry"))
  (.seq (.assign "metric.u" (.div (.var "metric.entry") (.var "metric.n")))
    (.seq (.assign "metric.v" (.sub (.var "metric.entry") (.mul (.var "metric.u") (.var "metric.n"))))
      (.seq (.assign "metric.b" (.add (.mul (.var "metric.u") (.var "metric.n")) (.var "metric.p")))
        (.assign "metric.c" (.add (.mul (.var "metric.p") (.var "metric.n")) (.var "metric.v"))))))



end Lax455465Proofs.RamMetricIndices

end

-- Solutions.RAM_Lax455465Proofs_RamMinPlus
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamMinPlus

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

def restore : Com := .seq (.assign "left.s" (.lit 0))
  (.seq (.assign "left.n" (.var "metric.base.n")) (.assign "left.d" (.var "metric.base.d")))

def command : Com := .seq (RamUnsignedBuffer.read "metric.old" "metric.a")
  (.seq (RamUnsignedArithmetic.copy "metric.base")
    (.seq (RamUnsignedBuffer.read "metric.old" "metric.b")
      (.seq (RamUnsignedArithmetic.copy "left")
        (.seq (RamUnsignedBuffer.read "metric.old" "metric.c")
          (.seq (RamUnsignedArithmetic.copy "right")
            (.seq addFraction (.seq (RamUnsignedArithmetic.copy "right")
              (.seq restore RamMinimum.command))))))))









end Lax455465Proofs.RamMinPlus

end

-- Solutions.RAM_Lax455465Proofs_RamMetricPivot
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamMetricPivot

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational DirectedFlowLP MetricMatrix
open scoped NNRat





def entry : Com := .seq RamMetricIndices.command RamMinPlus.command



def build : Com := RamUnsignedVector.command "metric.entry" "metric.n2" "metric.new" "metric.position" entry

def command : Com := .seq (.assign "metric.position" (.lit 0)) build



end Lax455465Proofs.RamMetricPivot

end

-- Solutions.RAM_Lax455465Proofs_RamFloydWarshall
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamFloydWarshall

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState MetricMatrix
open scoped NNRat

def step : Com := .seq RamMetricPivot.command
  (.seq (RamArrayCopy.command "metric.new" "metric.old" "metric.words")
    (.assign "metric.p" (.add (.var "metric.p") (.lit 1))))

def command : Com := .seq (.assign "metric.words" (.mul (.lit 2) (.var "metric.n2")))
  (.seq (.assign "metric.p" (.lit 0))
    (.while (.lt (.var "metric.p") (.var "metric.n")) step))







end Lax455465Proofs.RamFloydWarshall

end

-- Solutions.RAM_Lax455465Proofs_RamDualDistances
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamDualDistances

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState MetricMatrix
open scoped NNRat

def command : Com := .seq RamDualDistancesInit.command RamFloydWarshall.command







end Lax455465Proofs.RamDualDistances

end

-- Solutions.RAM_Lax263307Proofs_NativeRecursiveOracle
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeRecursiveOracle

open Matrix
open Lax263307 GraphClasses AlgorithmParameters ComputedSeparators
open Lax109476.LinearProgram Lax109476.RationalCertificates








def child {n : ℕ} (lp flow : List ℕ → List ℕ) (a K b D fuel : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n)) (t : ℕ) : Option (Finset (Fin n)) :=
  (RecursiveAlgorithm.attempt lp flow a K b D fuel (restriction G S) t).map
    (fun I => I.image (label S))







end Lax263307Proofs.NativeRecursiveOracle

end

-- Solutions.RAM_Lax263307Proofs_NativeRecursiveDomain
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeRecursiveDomain

open Lax263307 GraphClasses ComputedSeparators NativeNodeProtocol

/-- The semantic and numerical domain of actual recursive calls. -/
def eligible (C : GraphClass) (N frameSize capacity : ℕ) : Eligible :=
  fun fuel n G k cursor => G∈C n ∧ 0< n ∧ n≤ N ∧ 0< k ∧ k≤ n ∧
    RecursionDepth.depth n≤ fuel ∧ cursor+fuel*frameSize≤ capacity







end Lax263307Proofs.NativeRecursiveDomain

end

-- Solutions.RAM_Lax263307Proofs_NativeRoundedResources
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeRoundedResources

open Lax263307 RoundedOracleSearch Matrix

def buffers : List String := ["lp.word","vm.input","vm.addresses","vm.values",
  "vm.output","round.shape","round.center"]









end Lax263307Proofs.NativeRoundedResources

end

-- Solutions.RAM_Lax263307Proofs_NativeSelectedRounds
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeSelectedRounds

open Lax263307 GraphClasses AlgorithmParameters RoundedOracleSearch Matrix
open NativeCoreMachine

abbrev level (cfg : Config) (n D : ℕ) := AlgorithmParameters.level cfg.a cfg.K cfg.b n D
abbrev F (cfg : Config) (n D : ℕ) := (floorDenominator cfg.a cfg.K cfg.b n D)^(level cfg n D)
abbrev N (cfg : Config) (n D : ℕ) := MomentLP.dimension n (level cfg n D)
abbrev limit (cfg : Config) (n D : ℕ) := iterations cfg.a cfg.K cfg.b n D
abbrev H {lp : List ℕ → List ℕ} (p : NativeSelectedLP.Program lp) (R : ℕ) := NativeSelectedLP.certificateHeight p R
abbrev flowH {lp : List ℕ → List ℕ} (cfg : Config) (p : NativeSelectedLP.Program lp) (n D k R : ℕ) :=
  NativeLargeResources.heightExponent cfg.b n (load cfg.b n D) k (2*H p R)
abbrev space {lp flow : List ℕ → List ℕ} (cfg : Config) (p : NativeSelectedLP.Program lp)
    (q : NativeSelectedNear.Program flow) (n D k R : ℕ) := NativeUniformFlow.spaceBound n (flowH cfg p n D k R) q.time
abbrev flowTime {lp flow : List ℕ → List ℕ} (cfg : Config) (p : NativeSelectedLP.Program lp)
    (q : NativeSelectedNear.Program flow) (n D k R : ℕ) :=
  NativeSeparatorOutput.timeBound n (flowH cfg p n D k R) q.code q.coeff q.time

def oracleLocal {lp flow : List ℕ → List ℕ} (cfg : Config) (p : NativeSelectedLP.Program lp)
    (q : NativeSelectedNear.Program flow) (n D k R S : ℕ) : ℕ :=
  (16*NativeMomentInput.length n (level cfg n D)+(36*(2^(100*(R+1))).size+124)*N cfg n D+135+
    NativeSelectedLP.callCost p R+2)+14+(193*N cfg n D+48)+
    NativeNearExecution.timeBound cfg n (level cfg n D) (2^H p R) S (2*H p R) 0 (flowTime cfg p q n D k R)+6



/-- Only arithmetic and storage inequalities remain in this interface.
All oracle, rounded-program and recursive callback execution is constructed. -/
structure Bounds {lp flow : List ℕ → List ℕ} (cfg : Config) (p : NativeSelectedLP.Program lp)
    (q : NativeSelectedNear.Program flow) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D k fuel S v c R w : ℕ) (extent : String → ℕ) (front : List ℕ) : Prop where
  nR : n≤ R
  kR : k≤ R
  levelR : level cfg n D≤ R
  denominatorR : D≤ R
  floorR : F cfg n D≤ R
  dimensionR : N cfg n D≤ R
  roundsR : limit cfg n D≤ R
  projection : NativeOracleExecution.ProjectionBounds D k (level cfg n D) (F cfg n D)
    (2^(100*(R+1))) w (NativeSelectedLP.oracleTime p R) G extent
  near : NativeNearExecution.Bounds n (level cfg n D) D k (sparsity cfg.a cfg.K cfg.b n D)
    (2^H p R) (2*H p R) (R+1) fuel S w cfg extent front
  lpWidth : NativeSelectedLP.wordHeight p R≤ w
  farWidth : NativeCutResources.wordExponent (N cfg n D) (2*H p R+1)+4≤ w
  queryRoom : NativeSelectedLP.queryBound R< extent "vm.input"
  flowWidth : NativeUniformFlow.wordHeight n (flowH cfg p n D k R) q.code q.width q.time q.output≤ w
  flowSpace : ∀ a∈NativeSeparatorContext.workspace,space cfg p q n D k R≤ extent a
  roundedWidth : c*(2*R+NativeOraclePrecision.roundedHeight p.width R+1)^12≤ v
  roundedHost : NativeRoundedResources.wordHeight cfg.rounded v R (NativeOraclePrecision.roundedHeight p.width R)≤ w
  roundedSpace : ∀ a∈NativeRoundedResources.buffers,
    NativeRoundedResources.space c R (NativeOraclePrecision.roundedHeight p.width R)≤ extent a







end Lax263307Proofs.NativeSelectedRounds

end


