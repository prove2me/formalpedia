-- Prove2me | Definitions.Def_NogoodColoring1137_Main_Reductions
-- name    : NogoodColoring1137_Main_Reductions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T17:02:45.281093+00:00
-- url     : https://prove2.me/theorems/70123252-004e-4d43-a7d2-e6cf2d2f56a4
-- title:
--   Operational oracle reductions with graph-size promises
-- statement:
--   An oracle program is a finite multitape machine with distinct query and answer work tapes and query/resume states. Ordinary transitions are charged. A query installs the answer and resumes in one standard oracle step. Search answers may be any valid witness, and every reduction must work for every valid oracle.
--   $$f\le_T^p g\quad\Longleftrightarrow\quad\text{one finite oracle program computes }f\text{ in polynomial additional bit time using }g.$$
--   The relation requires every reached query to encode a graph of diameter at most two and at most the input's number of vertices. The polynomial transition bound also bounds the number of calls. Task inputs and outputs agree with SixTasks.
--
--   This preserves every promise in Theorem 4. **Formalization Note** Each query tape must contain exactly its encoded bit word and agree with the finite read window. Query and answer operations are standard oracle steps; all additional bit computation is charged.
-- source:
--   Philip Whittington, STOC 2027 submission #1137 (October 2026), §7, pp.21–23

import Mathlib
import Definitions.Def_NogoodColoring1137_Main_Computation

namespace NogoodColoring1137.Main

/-- Generic finite oracle machine on the shared bit-transition model. -/
structure OracleProgram where
  machine : IntMul.MultitapeTM
  symEq : DecidableEq machine.Sym
  stateEq : DecidableEq machine.K
  queryState : machine.K
  resumeState : machine.K
  queryTape : Fin machine.k
  answerTape : Fin machine.k
  queryNotHalt : queryState ≠ machine.qHalt
  queryNotInput : queryTape ≠ machine.inTape
  answerNotInput : answerTape ≠ machine.inTape
  queryNotOutput : queryTape ≠ machine.outTape
  answerNotOutput : answerTape ≠ machine.outTape
  distinctTapes : queryTape ≠ answerTape

/-- Query tape is read through its first blank; reachable queries must additionally have
exactly the prescribed bit-tape contents in Reduction below. -/
def OracleProgram.query (O : OracleProgram) (fuel : ℕ) (cfg : O.machine.Cfg) : List Bool :=
  letI := O.symEq
  ((List.range fuel).map (fun j => cfg.cells O.queryTape (j+1))).takeWhile
    (fun a => decide (a = O.machine.zero ∨ a = O.machine.one)) |>.map
      (fun a => decide (a = O.machine.one))

def OracleProgram.step (O : OracleProgram) (ans : List Bool → List Bool)
    (fuel : ℕ) (cfg : O.machine.Cfg) : O.machine.Cfg :=
  letI := O.symEq
  letI := O.stateEq
  if cfg.state = O.queryState then
    {state := O.resumeState
     cells := fun i =>
       if i = O.queryTape then O.machine.tapeOf []
       else if i = O.answerTape then
         O.machine.tapeOf ((ans (O.query fuel cfg)).map O.machine.bitSym)
       else cfg.cells i
     head := fun i => if i = O.queryTape ∨ i = O.answerTape then 0 else cfg.head i}
  else O.machine.step cfg

/-- Task order matches SixTasks: ordinary/list decision, ordinary/list search,
ordinary/list exact count. -/
def TaskInput {n : ℕ} (task : Fin 6) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (L : Lists n) : List Bool :=
  if task.val % 2 = 0 then EncodeGraph G else EncodeInstance G L

def TaskAnswer {n : ℕ} (task : Fin 6) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (L : Lists n) (out : List Bool) : Prop :=
  let lists := if task.val % 2 = 0 then FullLists n else L
  if task.val < 2 then
    ∃ b : Bool, out = [b] ∧ (b = true ↔ (Solutions G lists).Nonempty)
  else if task.val < 4 then SearchAnswer G lists out
  else out = EncodeNat (Solutions G lists).card

/-- Search oracles may choose any valid witness. No answer is assumed on nonpromised inputs. -/
def ValidOracle (task : Fin 6) (ans : List Bool → List Bool) : Prop :=
  ∀ n (G : SimpleGraph (Fin n)) (adj : DecidableRel G.Adj) (L : Lists n),
    DiameterTwo G → @TaskAnswer n task G adj L (ans (@TaskInput n task G adj L))

/-- Polynomially many calls and polynomial additional bit steps, with a universal promise
at EVERY reached query, not merely at the final answer. Oracle calls cost one step. -/
def Reduction (source target : Fin 6) : Prop :=
  ∃ (O : OracleProgram) (c e : ℕ), 0 < c ∧
    ∀ n (G : SimpleGraph (Fin n)) (adj : DecidableRel G.Adj) (L : Lists n),
      DiameterTwo G → ∀ ans, ValidOracle target ans →
      let input := @TaskInput n source G adj L
      let bound := c * (input.length + 1)^e
      ∃ t ≤ bound,
        let cfg := (O.step ans (bound+1))^[t] (O.machine.initCfg input [])
        cfg.state = O.machine.qHalt ∧
        (∃ out, cfg.cells O.machine.outTape = O.machine.tapeOf (out.map O.machine.bitSym) ∧
          @TaskAnswer n source G adj L out) ∧
        ∀ s < t,
          let cs := (O.step ans (bound+1))^[s] (O.machine.initCfg input [])
          cs.state = O.queryState →
          ∃ (m : ℕ) (H : SimpleGraph (Fin m)) (hAdj : DecidableRel H.Adj) (lists : Lists m),
            m ≤ n ∧ DiameterTwo H ∧
            cs.cells O.queryTape = O.machine.tapeOf
              ((@TaskInput m target H hAdj lists).map O.machine.bitSym) ∧
            O.query (bound+1) cs = @TaskInput m target H hAdj lists

end NogoodColoring1137.Main


