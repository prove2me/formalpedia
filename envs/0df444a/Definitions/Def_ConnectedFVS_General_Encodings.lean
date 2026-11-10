-- Prove2me | Definitions.Def_ConnectedFVS_General_Encodings
-- name    : ConnectedFVS_General_Encodings
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T17:18:02.349142+00:00
-- url     : https://prove2.me/theorems/165068c9-0c38-46d5-bcf1-0d75abc8ac99
-- title:
--   Binary encodings and decision languages for CFVS and Steiner problems
-- statement:
--   A natural number is encoded by the unary length of its little-endian binary expansion, a zero separator, then that expansion. Zero has empty expansion and frame $[0]$. An integer has a sign bit followed by the frame of its absolute value. A graph is encoded by its framed vertex count followed by its full row-major Boolean adjacency matrix. CFVS appends its framed natural budget. GST appends its framed group count, the $l$ membership rows in group order, then its signed budget. Directed Steiner appends the framed root label, the terminal membership row, then its signed budget.
--
--   For each problem, the decision language consists exactly of words encoding feasible valid instances; malformed words are rejected. Thus invalid root labels, asymmetric undirected matrices, loops in an undirected matrix, overlapping GST groups, noncanonical frames and trailing data are not accepted. These encodings depend only on instance data, never on feasibility, a witness, an optimum or an execution. Their lengths include binary budgets, even when a budget exceeds the number of vertices.
-- source:
--   Misra et al., FPT-Algorithms for Connected Feedback Vertex Set, arXiv:0909.3180v1 (17 September 2009), §2–§3, PDF pp. 3–6; explicit binary input convention

import Definitions.Def_ConnectedFVS_General_CFVS
import Definitions.Def_ConnectedFVS_General_GroupSteiner
import Definitions.Def_ConnectedFVS_General_DirectedSteiner
import Mathlib.Data.Nat.Bits

namespace ConnectedFVS.General

/-- Unary bit-length, a zero separator, then little-endian binary payload.
In particular zero is [false], and every natural has a unique frame. -/
def natFrame (n : ℕ) : List Bool :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

/-- A sign bit followed by the framed binary absolute value. -/
def intFrame (z : ℤ) : List Bool :=
  decide (z < 0) :: natFrame z.natAbs

/-- Row-major matrix in increasing vertex order. -/
def matrixBits {n : ℕ} (a : Fin n → Fin n → Bool) : List Bool :=
  (List.finRange n).flatMap fun u => (List.finRange n).map (a u)

def CFVSInstance.encode (I : CFVSInstance) : List Bool :=
  natFrame I.G.n ++ matrixBits I.G.edge ++ natFrame I.k

def GSTInstance.encode (I : GSTInstance) : List Bool :=
  natFrame I.G.n ++ matrixBits I.G.edge ++ natFrame I.groups ++
    (List.finRange I.groups).flatMap (fun i =>
      (List.finRange I.G.n).map fun v => decide (v ∈ I.group i)) ++ intFrame I.budget

def DSOTInstance.encode (I : DSOTInstance) : List Bool :=
  natFrame I.D.n ++ matrixBits I.D.arc ++ natFrame I.root.val ++
    (List.finRange I.D.n).map (fun v => decide (v ∈ I.terminals)) ++ intFrame I.budget

/-- Canonical decision language, rejecting words that encode no valid instance. -/
def encodedLanguage {α : Type} (encode : α → List Bool) (yes : α → Prop)
    (w : List Bool) : Prop := ∃ I, encode I = w ∧ yes I

def cfvsLanguage : List Bool → Prop := encodedLanguage CFVSInstance.encode CFVSInstance.Yes

def gstLanguage : List Bool → Prop := encodedLanguage GSTInstance.encode GSTInstance.Yes

def dsotLanguage : List Bool → Prop := encodedLanguage DSOTInstance.encode DSOTInstance.Yes

end ConnectedFVS.General


