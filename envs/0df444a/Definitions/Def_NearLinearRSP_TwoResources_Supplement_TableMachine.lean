-- Prove2me | Definitions.Def_NearLinearRSP_TwoResources_Supplement_TableMachine
-- name    : NearLinearRSP_TwoResources_Supplement_TableMachine
-- status  : Definition
-- author  : @k-variant
-- created : 2026-11-25T09:09:11.795804+00:00
-- url     : https://prove2.me/theorems/ad5bac2a-3d09-4500-933f-e5b039c9434c
-- title:
--   RAM instructions and memory layout for a multidimensional clock table
-- statement:
--   For a directed restricted shortest-path instance with $k$ resources, a clock call uses $d$ active coordinates with grid width $q$. A table stores a value, a rank, and a parent record for each represented vertex and clock vector. The input and output predicates specify the layout of these records, the graph, registers, and disjoint work areas.
--
--   The finite command constructs a table one grid row at a time. With heap capacity $B$, $N$ incident vertices, and $m$ edges, the functions specifying its instruction budget include the cost $S(k,d,q,B,N,m)$ of one row and the cost of the complete table,
--
--   $$
--   2d(4q+5)+d+32+(S(k,d,q,B,N,m)+2)q^d.
--   $$
-- source:
--   Vikrant Ashvinkumar, A Deterministic Near-Linear Time Approximation Algorithm for Restricted Shortest Paths in Directed Graphs, Theorem 2 (p. 3) and Appendix B (p. 14), extending Sections 4–6 (pp. 6–12).

import Definitions.Def_NearLinearRSP_TwoResources_Supplement_RAM
import Definitions.Def_NearLinearRSP_TwoResources_Implementation_Foundations

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
open scoped BigOperators

namespace NearLinearRSP.TwoResources.Supplement.CandidateRAM
open Mission.Structured

def current (r : ℕ) := 100 + 16 * r
def best (r : ℕ) := 101 + 16 * r

def scoreOps (d : ℕ) : List Atom :=
  [⟨.realConst 1 1, trivial⟩, ⟨.loadReal 0 50, trivial⟩,
   ⟨.realOp .sub 0 1 0, trivial⟩] ++
  (List.range d).map (fun r => ⟨.realOp .add 0 0 (current r), trivial⟩)

def saveLanes : ℕ → Cmd
  | 0 => .skip
  | d + 1 => .seq (saveLanes d)
      (.atoms [⟨.realCopy (best d) (current d), trivial⟩, ⟨.natCopy (best d) (current d), trivial⟩])

def saveHead : List Atom :=
  [⟨.realCopy 3 0, trivial⟩, ⟨.natCopy 55 50, trivial⟩, ⟨.natConst 56 1, trivial⟩]

def saveCmd (d : ℕ) : Cmd := .seq (.atoms saveHead) (saveLanes d)
def consider (d : ℕ) : Cmd :=
  .seq (.atoms (scoreOps d)) (.branch (.nat .eq 56 30) (saveCmd d)
    (.branch (.real .lt 0 3) (saveCmd d) .skip))

end NearLinearRSP.TwoResources.Supplement.CandidateRAM

end

section

set_option autoImplicit false
open scoped BigOperators

namespace NearLinearRSP.TwoResources.Supplement

def scanAddress {d : ℕ} (base n q v : ℕ) (i : Fin d → ℕ) : ℕ :=
  base + 4 + (d + 4) * (vectorIndex q i * n + v)

end NearLinearRSP.TwoResources.Supplement

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace NearLinearRSP.TwoResources.Supplement.CandidateRAM
open Mission.Structured

def guardCounts (c : Cmd) : ℕ → Cmd
  | 0 => c
  | n + 1 => .branch (.nat .lt (current n) 57) (guardCounts c n) .skip

def advanceCell : Atom := ⟨.natOp .add 50 50 59, trivial⟩
def visit (d : ℕ) : Cmd := .seq (guardCounts (consider d) d) (.atom advanceCell)

end NearLinearRSP.TwoResources.Supplement.CandidateRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators

namespace NearLinearRSP.TwoResources.Supplement.TableQuery
open Mission.Structured

def stateReg (r : ℕ) := CandidateRAM.current r + 2
def strideReg (r : ℕ) := CandidateRAM.current r + 3
def stride {d : ℕ} (n q : ℕ) (r : Fin d) := (d + 4) * n * q ^ (d - 1 - r.val)

end NearLinearRSP.TwoResources.Supplement.TableQuery

end

section

set_option autoImplicit false

namespace NearLinearRSP.TwoResources.Supplement.TableQuery
open Mission.Structured

def addCopies (dst src : ℕ) : ℕ → Cmd
  | 0 => .skip
  | n + 1 => .seq (addCopies dst src n) (.atom ⟨.natOp .add dst dst src, trivial⟩)

end NearLinearRSP.TwoResources.Supplement.TableQuery

end

section

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace NearLinearRSP.TwoResources.Supplement.CandidateRAM
open Mission.Structured
open TableQuery (stateReg)

def counterReg (r : ℕ) := current r + 4
def coeffReg (r : ℕ) := current r + 5

def laneInit (r : ℕ) : List Atom :=
  [⟨.natConst (counterReg r) 0, trivial⟩, ⟨.natCopy (current r) (stateReg r), trivial⟩,
   ⟨.realCopy (current r) (coeffReg r), trivial⟩]
def laneNext (r : ℕ) : List Atom :=
  [⟨.natOp .add (counterReg r) (counterReg r) 31, trivial⟩, ⟨.natOp .add (current r) (current r) 31, trivial⟩,
   ⟨.realOp .mul (current r) 12 (current r), trivial⟩]

end NearLinearRSP.TwoResources.Supplement.CandidateRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace NearLinearRSP.TwoResources.Supplement.CandidateRAM
open Mission.Structured

def laneLoop (r : ℕ) (c : Cmd) : Cmd :=
  .loop (.nat .lt (counterReg r) 57) (.seq c (.atoms (laneNext r)))

def sweep (d : ℕ) : List ℕ → Cmd
  | [] => visit d
  | r :: rs => .seq (.atoms (laneInit r)) (laneLoop r (sweep d rs))

end NearLinearRSP.TwoResources.Supplement.CandidateRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace NearLinearRSP.TwoResources.Supplement.TableQuery
open Mission.Structured

def productBody : List Atom :=
  [⟨.natOp .add 62 62 58, trivial⟩, ⟨.natOp .add 61 61 31, trivial⟩]
def productLoop : Cmd := .loop (.nat .lt 61 57) (.atoms productBody)
def productInit : List Atom := [⟨.natConst 62 0, trivial⟩, ⟨.natConst 61 0, trivial⟩]
def productLast : Atom := ⟨.natCopy 58 62, trivial⟩
def productCmd : Cmd := .seq (.atoms productInit) (.seq productLoop (.atom productLast))

def recordStride (r : ℕ) : Atom := ⟨.natCopy (strideReg r) 58, trivial⟩
def recordCmd (r : ℕ) : Cmd := .seq (.atom (recordStride r)) productCmd
def powers : ℕ → Cmd
  | 0 => .skip
  | n + 1 => .seq (recordCmd n) (powers n)

end NearLinearRSP.TwoResources.Supplement.TableQuery

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.TableQuery
open Mission.Structured
open Mission.Query (prependResult)

noncomputable def extent {k : ℕ} (A : ClockCall k) (base : ℕ) :=
  base + 4 + (A.d + 4) * A.I.graph.n * A.q ^ A.d

end NearLinearRSP.TwoResources.Supplement.TableQuery

end

section

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

def increment (j : ℕ) : Atom := ⟨.natOp .add 86 (stateReg j) 31, trivial⟩
def fetchOps (j : ℕ) : List Atom :=
  [⟨.natOp .add 87 49 (strideReg j), trivial⟩, ⟨.loadReal 91 87, trivial⟩,
   ⟨.realConst 92 1, trivial⟩, ⟨.realOp .sub 91 92 91, trivial⟩]
def saturated : Atom := ⟨.realConst 91 1, trivial⟩
def probe (j : ℕ) : Cmd := .seq (.atom (increment j))
  (.branch (.nat .lt 86 57) (.atoms (fetchOps j)) (.atom saturated))
def saveOps (j : ℕ) : List Atom :=
  [⟨.natConst 89 1, trivial⟩, ⟨.natConst 90 j, trivial⟩, ⟨.realCopy 90 91, trivial⟩]
def choose (j : ℕ) : Cmd := .branch (.nat .eq 89 30) (.atoms (saveOps j))
  (.branch (.real .lt 91 90) (.atoms (saveOps j)) .skip)
def step (j : ℕ) : Cmd := .seq (probe j) (choose j)

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured

def scan : List ℕ → Cmd
  | [] => .skip
  | r :: rs => .seq (step r) (scan rs)

def beginScan : Atom := ⟨.natConst 89 0, trivial⟩
def sourceOps : List Atom := [⟨.natConst 89 0, trivial⟩, ⟨.natConst 90 0, trivial⟩, ⟨.realConst 90 0, trivial⟩]
def seedCmd (d : ℕ) : Cmd := .branch (.nat .eq 76 5) (.atoms sourceOps) (.seq (.atom beginScan) (scan (List.range d)))

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

def vertexOps : List Atom :=
  [⟨.natOp .add 76 142 93, trivial⟩, ⟨.loadNat 76 76, trivial⟩, ⟨.natCopy 49 98, trivial⟩]
def vertexCmd (d : ℕ) : Cmd := .seq (.atoms vertexOps) (addCopies 49 76 (d + 4))
def commitSeed : List Atom :=
  [⟨.natOp .add 86 189 93, trivial⟩, ⟨.storeReal 86 90, trivial⟩, ⟨.storeNat 49 89, trivial⟩,
   ⟨.natOp .add 86 49 31, trivial⟩, ⟨.storeNat 86 90, trivial⟩, ⟨.natOp .add 93 93 31, trivial⟩]
def seedVertex (d : ℕ) : Cmd := .seq (vertexCmd d) (.seq (seedCmd d) (.atoms commitSeed))

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery
open Mission.Queue (slotVertex)

noncomputable def rowCell {k : ℕ} (A : ClockCall k) (base : ℕ) (i : Fin A.d → ℕ) (v : ℕ) :=
  scanAddress base A.I.graph.n A.q v i

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

namespace NearLinearRSP.TwoResources.Supplement.GraphRAM
open Mission.Structured Mission.Preprocess

structure Image {k : ℕ} (I : MultiInstance k) (base : ℕ) (s : Store) : Prop where
  vertices : ActiveRep I.graph.n base (base + I.graph.n) (incidentVertices I) s
  outgoing : AdjacencyPrefix (lengthInstance I) I.graph.edges.length
    (base + 2 * I.graph.n) (base + 3 * I.graph.n) s.nm

end NearLinearRSP.TwoResources.Supplement.GraphRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured
open Mission.Queue (Record activeLeaf vertexRecord readRecord Represents WinnerFrame)

def updateOps : List Atom :=
  [⟨.natCopy 1 180, trivial⟩, ⟨.natCopy 2 181, trivial⟩, ⟨.natConst 3 0, trivial⟩, ⟨.natConst 4 1, trivial⟩,
   ⟨.natOp .add 0 188 95, trivial⟩, ⟨.natCopy 10 96, trivial⟩, ⟨.realCopy 2 94, trivial⟩]
def updateCmd : Cmd := .seq (.atoms updateOps) Mission.Queue.updateLeaf

structure Config (B W P : ℕ) (s : Store) : Prop where
  winnerBase : s.nr 180 = W
  parentBase : s.nr 181 = P
  capacity : s.nr 188 = B

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured
open Mission.Queue (activeLeaf slotVertex WinnerFrame InitFrame)

def buildOps : List Atom :=
  [⟨.natCopy 1 180, trivial⟩, ⟨.natCopy 2 181, trivial⟩, ⟨.natConst 3 0, trivial⟩, ⟨.natConst 4 1, trivial⟩,
   ⟨.natCopy 11 188, trivial⟩, ⟨.natCopy 12 143, trivial⟩, ⟨.natCopy 13 189, trivial⟩]
def buildHeap : Cmd := .seq (.atoms buildOps) Mission.Queue.buildQueue

def rootOps : List Atom :=
  [⟨.natConst 4 1, trivial⟩, ⟨.natOp .add 7 180 4, trivial⟩, ⟨.loadNat 96 7, trivial⟩, ⟨.loadReal 94 7, trivial⟩,
   ⟨.natOp .sub 95 96 4, trivial⟩, ⟨.natOp .add 7 142 95, trivial⟩, ⟨.loadNat 97 7, trivial⟩, ⟨.natConst 96 0, trivial⟩]
def popCmd : Cmd := .seq (.atoms rootOps) updateCmd

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.SpaceRAM
open Mission.Structured TableQuery

def shapeOps (k : ℕ) : List Atom :=
  [⟨.natConst 30 0, trivial⟩, ⟨.natConst 31 1, trivial⟩, ⟨.natConst 65 2, trivial⟩,
   ⟨.loadNat 60 65, trivial⟩, ⟨.loadNat 57 30, trivial⟩, ⟨.natConst 58 0, trivial⟩,
   ⟨.natConst 49 (32 + 2 * k), trivial⟩]

def shapeCmd (k d : ℕ) : Cmd := .seq (.atoms (shapeOps k)) (.seq (addCopies 58 60 (d + 4)) (addCopies 49 60 8))

end NearLinearRSP.TwoResources.Supplement.SpaceRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery
open Mission.Queue (activeLeaf)

def seedZero : Atom := ⟨.natConst 93 0, trivial⟩
def seedAll (d : ℕ) : Cmd := .seq (.atom seedZero) (.loop (.nat .lt 93 143) (seedVertex d))
def startLayer (d : ℕ) : Cmd := .seq (seedAll d) buildHeap

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

def settledAddress : Atom := ⟨.natCopy 99 98, trivial⟩
def settleOps : List Atom :=
  [⟨.realConst 91 1, trivial⟩, ⟨.realOp .sub 91 91 94, trivial⟩, ⟨.storeReal 99 91, trivial⟩,
   ⟨.natConst 86 2, trivial⟩, ⟨.natOp .add 86 99 86, trivial⟩, ⟨.storeNat 86 191, trivial⟩,
   ⟨.natConst 86 1, trivial⟩, ⟨.natOp .add 191 191 86, trivial⟩]
def settleCmd (d : ℕ) : Cmd := .seq (.atom settledAddress) (.seq (addCopies 99 97 (d + 4)) (.atoms settleOps))

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

def pgfOps (j : ℕ) : List Atom :=
  [⟨.natConst 85 (2 * j + 1), trivial⟩, ⟨.natOp .add 85 190 85, trivial⟩, ⟨.loadReal 87 85, trivial⟩,
   ⟨.natConst 85 (4 + j), trivial⟩, ⟨.natOp .add 85 49 85, trivial⟩, ⟨.storeReal 85 87, trivial⟩]

def copyPGF : ℕ → Cmd
  | 0 => .skip
  | n + 1 => .seq (copyPGF n) (.atoms (pgfOps n))

def parentStart : Atom := ⟨.natCopy 49 98, trivial⟩
def parentOps : List Atom :=
  [⟨.natConst 86 2, trivial⟩, ⟨.storeNat 49 86, trivial⟩, ⟨.natConst 86 1, trivial⟩,
   ⟨.natOp .add 86 49 86, trivial⟩, ⟨.storeNat 86 97, trivial⟩, ⟨.realCopy 94 88, trivial⟩]
def writeParent (d : ℕ) : Cmd := .seq (.atom parentStart)
  (.seq (addCopies 49 100 (d + 4)) (.seq (.atoms parentOps) (copyPGF d)))

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

def ParentRecords {k : ℕ} (A : ClockCall k) (base : ℕ) (i : Fin A.d → ℕ) (p : ℕ → MultiParent) (s : Store) : Prop :=
  ∀ w ∈ incidentVertices A.I,
    let a := rowCell A base i w
    s.nm a = multiParentTag (p w) ∧ s.nm (a + 1) = multiParentPayload (p w) ∧
      ∀ u, p w = .edge u → ∀ r : Fin A.d, s.rm (a + 4 + r.val) = clockPGF A r u w

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured
open Mission.Queue (activeLeaf)

def probeLeaf : List Atom :=
  [⟨.natCopy 100 77, trivial⟩, ⟨.natOp .add 86 141 100, trivial⟩, ⟨.loadNat 95 86, trivial⟩,
   ⟨.natConst 4 1, trivial⟩, ⟨.natOp .sub 95 95 4, trivial⟩, ⟨.natOp .add 86 188 95, trivial⟩,
   ⟨.natOp .add 86 180 86, trivial⟩, ⟨.loadNat 96 86, trivial⟩, ⟨.loadReal 92 86, trivial⟩]

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery
open Mission.Queue (activeLeaf)

def compareEdge (d : ℕ) : Cmd := .branch (.real .lt 88 92) (.seq (writeParent d) updateCmd) .skip

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace NearLinearRSP.TwoResources.Supplement.EdgeRAM
open Mission.Structured Classical

def loadTest (r : ℕ) : List Atom :=
  [⟨.natConst 72 (r + 1), trivial⟩, ⟨.inputReal 72 72, trivial⟩,
   ⟨.natOp .add 72 70 72, trivial⟩, ⟨.inputReal 73 72, trivial⟩]
def reject : Atom := ⟨.natConst 71 0, trivial⟩
def test (r : ℕ) : Cmd := .seq (.atoms (loadTest r)) (.branch (.real .eq 72 74)
  (.branch (.real .eq 73 74) .skip (.atom reject)) .skip)
def tests : List ℕ → Cmd
  | [] => .skip
  | r :: rs => .seq (test r) (tests rs)

end NearLinearRSP.TwoResources.Supplement.EdgeRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.EdgeRAM
open Mission.Structured Classical

def baseOps (k : ℕ) : List Atom :=
  [⟨.natConst 70 k, trivial⟩, ⟨.natConst 71 1, trivial⟩, ⟨.natConst 74 0, trivial⟩, ⟨.realConst 74 0, trivial⟩,
   ⟨.natOp .add 72 75 75, trivial⟩, ⟨.natConst 73 4, trivial⟩, ⟨.natOp .add 72 73 72, trivial⟩,
   ⟨.inputNat 76 72, trivial⟩, ⟨.natConst 73 1, trivial⟩, ⟨.natOp .add 72 72 73, trivial⟩,
   ⟨.inputNat 77 72, trivial⟩]
def lengthOp : Atom := ⟨.inputReal 78 70, trivial⟩
def readCmd (k : ℕ) : Cmd := .seq (.atoms (baseOps k)) (.seq (TableQuery.addCopies 70 75 k) (.atom lengthOp))

def restrictions : Cmd := .branch (.nat .eq 76 77) (.atom reject)
  (.branch (.nat .eq 79 74) .skip (.branch (.real .eq 78 74) .skip (.atom reject)))
def loadEdge (k : ℕ) : Cmd := .seq (readCmd k) (.seq restrictions (tests (List.range (k - 1))))

end NearLinearRSP.TwoResources.Supplement.EdgeRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.EdgeRAM
open Mission.Structured

def laneRead (j : ℕ) : List Atom :=
  [⟨.natConst 84 (8 + j), trivial⟩, ⟨.loadNat 76 84, trivial⟩,
   ⟨.natOp .add 85 70 76, trivial⟩, ⟨.inputReal 85 85, trivial⟩]
def budgetCmd : Cmd := .branch (.nat .eq 76 74)
  (.atom ⟨.realCopy 84 82, trivial⟩) (.atom ⟨.inputReal 84 76, trivial⟩)
def momentOps (j : ℕ) : List Atom :=
  [⟨.realOp .mul 84 81 84, trivial⟩, ⟨.realOp .div 86 80 84, trivial⟩, ⟨.realOp .mul 86 86 85, trivial⟩,
   ⟨.realOp .mul 87 86 83, trivial⟩, ⟨.exp 87 87, trivial⟩, ⟨.natConst 84 (2 * j), trivial⟩,
   ⟨.natOp .add 84 1 84, trivial⟩, ⟨.storeReal 84 86, trivial⟩, ⟨.natConst 85 1, trivial⟩,
   ⟨.natOp .add 84 84 85, trivial⟩, ⟨.storeReal 84 87, trivial⟩]
def momentLane (j : ℕ) : Cmd := .seq (.atoms (laneRead j)) (.seq budgetCmd (.atoms (momentOps j)))

end NearLinearRSP.TwoResources.Supplement.EdgeRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace NearLinearRSP.TwoResources.Supplement.EdgeRAM
open Mission.Structured

def moments : ℕ → Cmd
  | 0 => .skip
  | n + 1 => .seq (moments n) (momentLane n)

def natOps (r : ℕ) : List Atom :=
  [⟨.natConst 84 (2 * r), trivial⟩, ⟨.natOp .add 84 1 84, trivial⟩,
   ⟨.natOp .sub 86 57 (TableQuery.stateReg r), trivial⟩, ⟨.storeNat 84 86, trivial⟩,
   ⟨.natConst 85 1, trivial⟩, ⟨.natOp .add 84 84 85, trivial⟩, ⟨.storeNat 84 (TableQuery.strideReg r), trivial⟩]
def limits : ℕ → Cmd
  | 0 => .skip
  | n + 1 => .seq (limits n) (.atoms (natOps n))

end NearLinearRSP.TwoResources.Supplement.EdgeRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.RegisterShift
open Mission.Structured

def instr (b : ℕ) : RAMInstr → RAMInstr
  | .realConst d x => .realConst (b + d) x
  | .natConst d x => .natConst (b + d) x
  | .realCopy d a => .realCopy (b + d) (b + a)
  | .natCopy d a => .natCopy (b + d) (b + a)
  | .realOp op d a c => .realOp op (b + d) (b + a) (b + c)
  | .natOp op d a c => .natOp op (b + d) (b + a) (b + c)
  | .exp d a => .exp (b + d) (b + a)
  | .realBranch test a c y n => .realBranch test (b + a) (b + c) y n
  | .natBranch test a c y n => .natBranch test (b + a) (b + c) y n
  | .loadReal d a => .loadReal (b + d) (b + a)
  | .loadNat d a => .loadNat (b + d) (b + a)
  | .storeReal a c => .storeReal (b + a) (b + c)
  | .storeNat a c => .storeNat (b + a) (b + c)
  | .inputReal d a => .inputReal (b + d) (b + a)
  | .inputNat d a => .inputNat (b + d) (b + a)
  | .jump n => .jump n
  | .halt => .halt

def atom (b : ℕ) (a : Atom) : Atom := ⟨instr b a.val, by rcases a with ⟨i, hi⟩; cases i <;> exact hi⟩
def guardAt (b : ℕ) : Guard → Guard
  | .real test a c => .real test (b + a) (b + c)
  | .nat test a c => .nat test (b + a) (b + c)
def cmd (b : ℕ) : Cmd → Cmd
  | .skip => .skip
  | .atom a => .atom (atom b a)
  | .seq c d => .seq (cmd b c) (cmd b d)
  | .branch g c d => .branch (guardAt b g) (cmd b c) (cmd b d)
  | .loop g c => .loop (guardAt b g) (cmd b c)

end NearLinearRSP.TwoResources.Supplement.RegisterShift

end

section

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
open scoped BigOperators

namespace NearLinearRSP.TwoResources.Supplement.TensorRAM
open Mission.Structured
open ActuarialValuation

def slot (n a : ℕ) : ℕ := 8 + 8 * n + a

def init (n : ℕ) : List Atom :=
  [ ⟨.natConst (slot n 4) (2 * n), trivial⟩,
    ⟨.natOp .add (slot n 4) 1 (slot n 4), trivial⟩,
    ⟨.loadNat (slot n 0) (slot n 4), trivial⟩,
    ⟨.loadReal (slot n 0) (slot n 4), trivial⟩,
    ⟨.natOp .add (slot n 4) (slot n 4) 2, trivial⟩,
    ⟨.loadNat (slot n 1) (slot n 4), trivial⟩,
    ⟨.natConst (slot n 2) 0, trivial⟩,
    ⟨.realConst (slot n 2) 0, trivial⟩,
    ⟨.realConst (slot n 3) 0, trivial⟩,
    ⟨.realOp .sub (slot n 1) 2 (slot n 0), trivial⟩,
    ⟨.exp (slot n 1) (slot n 1), trivial⟩ ]

def save (n : ℕ) : Atom := ⟨.natCopy (slot n 3) 0, trivial⟩

def finish (n : ℕ) : List Atom :=
  [ ⟨.realOp .mul (slot n 4) (slot n 1) 0, trivial⟩,
    ⟨.realOp .add (slot n 3) (slot n 3) (slot n 4), trivial⟩,
    ⟨.realOp .add (slot n 2) (slot n 2) 1, trivial⟩,
    ⟨.realOp .mul (slot n 1) (slot n 1) (slot n 0), trivial⟩,
    ⟨.realOp .div (slot n 1) (slot n 1) (slot n 2), trivial⟩,
    ⟨.natCopy 0 (slot n 3), trivial⟩,
    ⟨.natOp .add 0 0 (slot n 1), trivial⟩,
    ⟨.natOp .add (slot n 2) (slot n 2) 2, trivial⟩ ]

def tensorCmd : ℕ → Cmd
  | 0 => .atom ⟨.loadReal 0 0, trivial⟩
  | n + 1 => .seq (Cmd.atoms (init n))
      (.seq (.loop (.nat .lt (slot n 2) (slot n 0))
        (.seq (.atom (save n)) (.seq (tensorCmd n) (Cmd.atoms (finish n)))))
      (.atom ⟨.realCopy 0 (slot n 3), trivial⟩))

end NearLinearRSP.TwoResources.Supplement.TensorRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace NearLinearRSP.TwoResources.Supplement.EdgeRAM
open Mission.Structured

def bank (k : ℕ) := 512 + 32 * k
def tensorArgs (b : ℕ) : List Atom :=
  [⟨.natCopy b 0, trivial⟩, ⟨.natCopy (b + 1) 1, trivial⟩, ⟨.natConst (b + 2) 1, trivial⟩,
   ⟨.realConst (b + 1) 1, trivial⟩, ⟨.realConst (b + 2) 0, trivial⟩]
def resultOp (b : ℕ) : Atom := ⟨.realOp .sub 88 (b + 1) b, trivial⟩
def kernel (k d : ℕ) : Cmd := .seq (.atoms (tensorArgs (bank k))) (.seq
  (RegisterShift.cmd (bank k) (TensorRAM.tensorCmd d)) (.atom (resultOp (bank k))))

end NearLinearRSP.TwoResources.Supplement.EdgeRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace NearLinearRSP.TwoResources.Supplement.EdgeRAM
open Mission.Structured

def scoreCmd (k d : ℕ) : Cmd := .seq (moments d) (.seq (limits d) (kernel k d))

end NearLinearRSP.TwoResources.Supplement.EdgeRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace NearLinearRSP.TwoResources.Supplement.EdgeRAM
open Mission.Structured

structure Clocks {k : ℕ} (A : ClockCall k) (s : Store) : Prop where
  q : s.nr 57 = A.q
  zeroOnly : s.nr 79 = if A.zeroOnly then 1 else 0
  zeroNat : s.nr 74 = 0
  zeroReal : s.rr 74 = 0
  limit : s.rr 80 = (A.q : ℝ)
  denominator : s.rr 81 = 1 + A.δ / 2
  threshold : s.rr 82 = A.L
  decay : s.rr 83 = clockZ A - 1

end NearLinearRSP.TwoResources.Supplement.EdgeRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

def scoreArgs : List Atom :=
  [⟨.natCopy 0 99, trivial⟩, ⟨.natCopy 1 190, trivial⟩, ⟨.natConst 74 0, trivial⟩]
def scoreEdge (k d : ℕ) : Cmd := .seq (.atoms scoreArgs) (.seq (EdgeRAM.scoreCmd k d) (compareEdge d))
def visitEdge (k d : ℕ) : Cmd := .seq (EdgeRAM.loadEdge k) (.branch (.nat .eq 71 30) .skip
  (.seq (.atoms probeLeaf) (.branch (.nat .eq 96 30) .skip (scoreEdge k d))))

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery
open Mission.Queue (activeLeaf)

def visitCost (k d q B : ℕ) := 9 * k + 32 * d + 25 ^ (d + 1) * (q + 1) ^ d + 19 * Nat.clog 2 (2 * B) + 65

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured Mission.Preprocess TableQuery
open Mission.Queue (activeLeaf)

def advanceLink : List Atom :=
  [⟨.natConst 86 1, trivial⟩, ⟨.natOp .sub 75 194 86, trivial⟩,
   ⟨.natOp .add 86 164 75, trivial⟩, ⟨.loadNat 194 86, trivial⟩]
def scanNeighbors (k d : ℕ) := Cmd.loop (.nat .lt 30 194) (.seq (.atoms advanceLink) (visitEdge k d))

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured Mission.Preprocess TableQuery

def firstNeighbor : List Atom :=
  [⟨.natOp .add 86 163 97, trivial⟩, ⟨.loadNat 194 86, trivial⟩]
def relaxNeighbors (k d : ℕ) := Cmd.seq (.atoms firstNeighbor) (scanNeighbors k d)

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

def Numbers {k : ℕ} (A : ClockCall k) (base : ℕ) (T : MultiTable A.d) (s : Store) : Prop :=
  ∀ v ∈ incidentVertices A.I, ∀ i : Fin A.d → ℕ, (∀ r, i r < A.q) →
    let a := rowCell A base i v
    s.rm a = 1 - (T v i).value ∧ s.nm (a + 2) = (T v i).rank

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1700000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured Mission.Preprocess TableQuery
open Mission.Queue (activeLeaf)

structure Site {k : ℕ} (A : ClockCall k) (base map params B W : ℕ) : Prop where
  header : 8 + k ≤ base
  publicEnd : extent A base ≤ map
  graphEnd : map + 3 * A.I.graph.n + A.I.graph.edges.length ≤ params
  workspace : params + 2 * A.d ≤ W
  capacity : (incidentVertices A.I).length ≤ B

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1700000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured Mission.Preprocess TableQuery

def beginRow : List Atom :=
  [⟨.natConst 31 1, trivial⟩, ⟨.natConst 86 1, trivial⟩, ⟨.loadNat 5 86, trivial⟩, ⟨.natConst 191 0, trivial⟩]
def initializeRow (d : ℕ) := Cmd.seq (.atoms beginRow) (startLayer d)

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured Mission.Preprocess TableQuery
open Mission.Queue (activeLeaf)

def extractVertex (d : ℕ) : Cmd := .seq popCmd (settleCmd d)

def popLayer (k d : ℕ) : Cmd := .seq (extractVertex d) (relaxNeighbors k d)

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured Mission.Preprocess TableQuery

def layerLoop (k d : ℕ) := Cmd.loop (.nat .lt 191 143) (popLayer k d)
def vertexCost (d B : ℕ) := d + 19 * Nat.clog 2 (2 * B) + 39

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured Mission.Preprocess TableQuery

def runLayer (k d : ℕ) := Cmd.seq (initializeRow d) (layerLoop k d)
def layerWork (k d q B N m : ℕ) := 15 * B + (14 * d + 33 + 19 * Nat.clog 2 (2 * B) + vertexCost d B) * N +
  (visitCost k d q B + 6) * m + 17

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

structure TableImage {k : ℕ} (A : ClockCall k) (base : ℕ) (T : MultiTable A.d) (s : Store) : Prop where
  numbers : Numbers A base T s
  parents : ∀ j : Fin A.d → ℕ, (∀ r, j r < A.q) → ParentRecords A base j (fun v => (T v j).parent) s

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

def divideBody : List Atom := [⟨.natOp .sub 60 60 57, trivial⟩, ⟨.natOp .add 61 61 31, trivial⟩]
def divideLoop : Cmd := .loop (.nat .lt 58 60) (.atoms divideBody)
def digitZero : Atom := ⟨.natConst 61 0, trivial⟩
def digitOps (r : ℕ) : List Atom := [⟨.natCopy (stateReg r) 60, trivial⟩, ⟨.natCopy 60 61, trivial⟩]
def digitCmd (r : ℕ) : Cmd := .seq (.atom digitZero) (.seq divideLoop (.atoms (digitOps r)))
def digits : ℕ → Cmd
  | 0 => .skip
  | n+1 => .seq (digitCmd n) (digits n)

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured Mission.Preprocess TableQuery

structure TableContext {k : ℕ} (A : ClockCall k) (base map keys params B W P : ℕ) (s : Store) : Prop where
  cfg : Config B W P s
  graph : GraphRAM.Image A.I map s
  heads : s.nr 163 = map + 2 * A.I.graph.n
  links : s.nr 164 = map + 3 * A.I.graph.n
  coords : ∀ r : Fin A.d, s.nm (8 + r.val) = (A.coords.get r).val
  source : s.nm 1 = A.I.source
  keysReg : s.nr 189 = keys
  paramsReg : s.nr 190 = params
  zero : s.nr 30 = 0
  q : s.nr 57 = A.q
  mode : s.nr 79 = if A.zeroOnly then 1 else 0
  width : s.nr 195 = (A.d + 4) * A.I.graph.n
  strides : ∀ r : Fin A.d, s.nr (strideReg r.val) = stride A.I.graph.n A.q r
  limit : s.rr 80 = (A.q : ℝ)
  denom : s.rr 81 = 1 + A.δ / 2
  threshold : s.rr 82 = A.L
  decay : s.rr 83 = clockZ A - 1

def TableFrame {k : ℕ} (A : ClockCall k) (base lim : ℕ) (s t : Store) : Prop :=
  ∀ x < lim, x < base + 4 ∨ extent A base ≤ x → t.nm x = s.nm x ∧ t.rm x = s.rm x

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

def rowStepOps : List Atom :=
  [⟨.natConst 31 1, trivial⟩, ⟨.natOp .sub 196 196 31, trivial⟩, ⟨.natOp .sub 98 98 195, trivial⟩,
   ⟨.natCopy 60 196, trivial⟩, ⟨.natOp .sub 58 57 31, trivial⟩]
def stepRow (k d : ℕ) := Cmd.seq (.atoms rowStepOps) (.seq (digits d) (runLayer k d))

def stepCost (k d q B N m : ℕ) := 5 + d * (4*q^d+4) + layerWork k d q B N m

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1700000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

def tableLoop (k d : ℕ) := Cmd.loop (.nat .lt 30 196) (stepRow k d)

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

def volumeOps : List Atom := [⟨.natConst 31 1,trivial⟩,⟨.natConst 58 1,trivial⟩]
def saveVolume : Atom := ⟨.natCopy 196 58,trivial⟩
def volumeCmd (d : ℕ) := Cmd.seq (.atoms volumeOps) (.seq (powers d) (.atom saveVolume))

def saveWidth : Atom := ⟨.natCopy 195 58,trivial⟩
def gridRegs : List Atom :=
  [⟨.natConst 30 0,trivial⟩,⟨.natConst 65 4,trivial⟩,⟨.natOp .add 98 200 65,trivial⟩,
   ⟨.natOp .add 98 98 58,trivial⟩,⟨.natOp .add 163 141 60,trivial⟩,⟨.natOp .add 163 163 60,trivial⟩,
   ⟨.natOp .add 164 163 60,trivial⟩]
def gridSetup (k d : ℕ) := Cmd.seq (volumeCmd d) (.seq (SpaceRAM.shapeCmd k d) (.seq (.atom saveWidth)
  (.seq (powers d) (.atoms gridRegs))))

def GridFixed (a : ℕ) : Prop := 70 ≤ a ∧ a ≠ 98 ∧ a ≠ 163 ∧ a ≠ 164 ∧ a ≠ 195 ∧ a ≠ 196 ∧ ∀ r, a ≠ strideReg r

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end

section

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace NearLinearRSP.TwoResources.Supplement.LayerRAM
open Mission.Structured TableQuery

def saveEnd : Atom := ⟨.natCopy 203 98,trivial⟩
def buildTableCmd (k d : ℕ) := Cmd.seq (gridSetup k d) (.seq (.atom saveEnd) (tableLoop k d))

def TableOuter (k a : ℕ) : Prop :=
  101 ≤ a ∧ a < EdgeRAM.bank k ∧ a ≠ 191 ∧ a ≠ 194 ∧ a ≠ 196 ∧ ∀ r, a ≠ stateReg r

structure TableInput {k : ℕ} (A : ClockCall k) (base map keys params B W P : ℕ) (s : Store) : Prop where
  cfg : Config B W P s
  graph : GraphRAM.Image A.I map s
  clocks : EdgeRAM.Clocks A s
  coords : ∀ r : Fin A.d, s.nm (8 + r.val) = (A.coords.get r).val
  source : s.nm 1 = A.I.source
  nodes : s.nm 2 = A.I.graph.n
  q : s.nm 0 = A.q
  keys : s.nr 189 = keys
  params : s.nr 190 = params
  address : s.nr 200 = base

def tableCost (k d q B N m : ℕ) := 2*(d*(4*q+5))+d+32 + (stepCost k d q B N m + 2)*q^d

end NearLinearRSP.TwoResources.Supplement.LayerRAM

end


