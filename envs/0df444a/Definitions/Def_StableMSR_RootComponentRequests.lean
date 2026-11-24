-- Prove2me | Definitions.Def_StableMSR_RootComponentRequests
-- name    : StableMSR_RootComponentRequests
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-24T16:17:48.886704+00:00
-- url     : https://prove2.me/theorems/dcad6fba-c2d7-4cf5-91b7-e0bc390f27f7
-- title:
--   The final root-component requests of the actual separator program
-- statement:
--   After geometry construction and the row traversal, the fixed source fragment allocates an empty boundary bitmap and scans the vertices. Its input consists of the active-vertex and adjacency bitmaps, with their table addresses below the allocation cursor and a consistent open output stream. The prefix contract requires geometry and rows to leave this data available. The specified suffix is the ordered list of requests for full components with empty boundary.
-- source:
--   Root-component requests after the separator dynamic program in Appendix A.6, https://arxiv.org/abs/2611.03547.

import Definitions.Def_StableMSR_InitializedSeparatorTraversal
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root
open SingleCircuit TightLanguage WindowCSP OracleQueries Compiler
set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 3500000
set_option maxRecDepth 32000

/-- Registers and sublists of the actual source for the final requests. -/
def sendOps : List Program :=
  [.op (.regular (.copy 1314 158)), .op (.regular (.set 1318 0)),
   .op (.regular (.copy 218 1313)), .op (.regular (.copy 219 1314)),
   .op (.regular (.copy 220 1318)), .op .output, .op (.regular (.copy 1312 222))]
def announceOps : List Program :=
  [.op (.regular (.set 1313 1)), .op (.regular (.copy 153 272)),
   .op (.regular (.copy 154 270)), .op (.regular (.copy 155 270)), src_name_key] ++ sendOps
def equalHead : Program := .cond 1309 271
  (.cond 271 1309 (.op (.regular (.set 1308 1))) (.op (.regular (.set 1308 0))))
  (.op (.regular (.set 1308 0)))
def announceIf := Program.cond 6 1308 (chain announceOps) .skip
def inspectOps : List Program := [.op (.regular (.copy 1305 138)), .op (.regular (.copy 272 1305)),
  .op (.regular (.copy 144 272)), src_first, .op (.regular (.copy 1309 147)), equalHead, announceIf]
def activeOps : List Program :=
  [.op (.regular (.copy 132 71)), .op (.regular (.copy 133 271)), src_component] ++ inspectOps
def stepCode := chain [.op (.fetch 1302 71 271), .cond 6 1302 (chain activeOps) .skip]
def suffixOps : List Program := [.op (.alloc 1298 64), .op (.regular (.copy 270 1298)),forCount 271 1301 64 stepCode]
def rowsCode := chain (middleList.take 3)
def inputs (d:Instance) (s:State) : Prop :=
  ∃a ed l top:ℕ, s.reg 6=1 ∧ s.reg 7=0 ∧ s.reg 64=(d.n:ℤ) ∧ s.reg 8=(top:ℤ) ∧
    s.reg 71=(a:ℤ) ∧ s.reg 75=(ed:ℤ) ∧ s.reg 76=(l:ℤ) ∧ a+d.n ≤ top ∧ ed+d.n*d.n ≤ top ∧
    (∀j<d.n,1 ≤ s.heap (a+j) ↔ d.active j=true) ∧
    (∀j<d.n,∀v<d.n,1 ≤ s.heap (ed+(j*d.n+v)) ↔ d.edge j v=true) ∧
    s.reg 82=(s.output.length:ℤ) ∧ s.closed=false
def requests (d:Instance) : List Instr :=
  (parts d (vertices d)).map (fun c=>.need (Naming.name (c,[])))
def words (d:Instance) (i:ℕ) : List Instr :=
  if d.active i then
    let c:=pieceAt d (vertices d) i
    if c.head?==some i then [.need (Naming.name (c,[]))] else []
  else []
def RowsCorrect : Prop :=
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 →
  ∀(x:World) (s:Store),1 ≤ x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∀u:State,Prepared x.n r (budget (e:ℝ)) (widthBound (e:ℝ)) u →
    let d:=integerData x.n x.mem s.imem r (budget (e:ℝ))
    ∃t k,Executes x.n s.imem rowsCode u t k ∧ k ≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
      t.output=rowTape Naming.name d (widthBound (e:ℝ)) ∧ inputs d t
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Root


