-- Prove2me | Definitions.Def_QAlgorithms_Defs_OPIUniformity
-- name    : QAlgorithms_Defs_OPIUniformity
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:30:53.637114+00:00
-- url     : https://prove2.me/theorems/34df112b-0201-4627-828a-473206fb8a2b
-- title:
--   OPIUniformity
-- statement:
--   OPIUniformity
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\OPIUniformity.lean

import Definitions.Def_QAlgorithms_ClassicalStringListEncoding
import Definitions.Def_QAlgorithms_Defs_LearningSeparation
import Definitions.Def_QAlgorithms_Defs_OPIOraclePrograms
noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.OPI

open Complexity

/-- Unary self-delimiting words for serialized public program topology;
2607.16541 p.7, 2610.02145 p.16. -/
def serializeWords (w : List ℕ) : Str := (w.map encNat).flatten

/-- Intern a node in a shared continuation table; 2607.16541 p.7, 2610.02145 p.16.
Reusing an identical continuation does not duplicate its serialized description. -/
def internProgramNode (code : Str) (nodes : List Str) : ℕ × List Str :=
  if code ∈ nodes then (nodes.idxOf code,nodes) else (nodes.length,nodes ++ [code])

/-- Canonical shared-node serialization of finite adaptive programs;
2607.16541 p.7, 2610.02145 p.16. Each node stores its known operation and child
indices. Measurements with a common continuation share that continuation. -/
def programNodeTable {r : ℕ} {a : Fin r → ℕ} {ctl : Fin r → Bool}
    {N c out : ℕ} : AdaptiveMembershipProgram htcxGateSet a ctl N c out →
      List Str → ℕ × List Str
  | .halt D _, nodes => internProgramNode
      (serializeWords [0,D.gates.length] ++
        (D.gates.flatMap fun g => serializeWords [Learning.boolOpCode g.op,g.a,g.b]) ++
        serializeWords (List.ofFn D.outputs)) nodes
  | .fail, nodes => internProgramNode (serializeWords [1]) nodes
  | .gate g next, nodes =>
      let tail := programNodeTable next nodes
      internProgramNode (serializeWords ([2,
        if g.gate = Gate.ofMatrix1 hadamard then 0
        else if g.gate = Gate.ofMatrix1 gateT then 1 else 2] ++
        List.ofFn fun i => (g.wires i).val) ++ encNat tail.1) tail.2
  | .query k adj control _ w _ next, nodes =>
      let tail := programNodeTable next nodes
      internProgramNode (serializeWords ([3,k.val,if adj then 1 else 0,
        (control.map Fin.val).getD N] ++ List.ofFn fun i => (w i).val) ++ encNat tail.1) tail.2
  | .measure q dst next, nodes =>
      let left := programNodeTable (next false) nodes
      let right := programNodeTable (next true) left.2
      internProgramNode (serializeWords [4,q.val,dst.val,left.1,right.1]) right.2
  | .prepare q next, nodes =>
      let tail := programNodeTable next nodes
      internProgramNode (serializeWords [5,q.val,tail.1]) tail.2
  | .coin dst next, nodes =>
      let left := programNodeTable (next false) nodes
      let right := programNodeTable (next true) left.2
      internProgramNode (serializeWords [6,dst.val,left.1,right.1]) right.2
  | .setBit dst bit next, nodes =>
      let tail := programNodeTable next nodes
      internProgramNode (serializeWords [7,dst.val,if bit then 1 else 0,tail.1]) tail.2
  | .boolean op dst x y next, nodes =>
      let tail := programNodeTable next nodes
      internProgramNode (serializeWords [8,Learning.boolOpCode op,dst.val,x.val,y.val,tail.1]) tail.2
  | .branch src next, nodes =>
      let left := programNodeTable (next false) nodes
      let right := programNodeTable (next true) left.2
      internProgramNode (serializeWords [9,src.val,left.1,right.1]) right.2

/-- Public topology, fixed-set gate and output-decoder serialization;
2607.16541 p.7, 2610.02145 p.16. The root index and shared node table uniquely
specify the program, without charging free real-valued gate descriptions. -/
def programSerialization {r : ℕ} {a : Fin r → ℕ} {ctl : Fin r → Bool}
    {N c out : ℕ} (P : AdaptiveMembershipProgram htcxGateSet a ctl N c out) : Str :=
  let table := programNodeTable P []
  encNat table.1 ++ encStr table.2

/-- A concrete public oracle program, with explicit dimensions and fixed-set gates;
2607.16541 p.7, 2610.02145 p.16. -/
structure PackedMembershipProgram where
  oracles : ℕ
  arity : Fin oracles → ℕ
  control : Fin oracles → Bool
  qubits : ℕ
  classicalBits : ℕ
  outputBits : ℕ
  program : AdaptiveMembershipProgram htcxGateSet arity control qubits classicalBits outputBits

/-- Dimension and topology serialization; 2607.16541 p.7. -/
def packedSerialization (P : PackedMembershipProgram) : Str :=
  serializeWords [P.oracles,P.qubits,P.classicalBits,P.outputBits] ++
    serializeWords (List.ofFn P.arity) ++ List.ofFn P.control ++ programSerialization P.program

/-- Single explicit bit constructor of public oracle programs; 2607.16541 p.7,
2607.14650 pp.16–19, 2610.02145 p.16.
The polynomial precedes public data; hidden sets never enter construction. -/
structure UniformResourceFamily (Input : Type) (encode : Input → Str) (scale : Input → ℕ) where
  constructor : BitOracleProgram
  publicOnly : IsPublicPreprocessor constructor
  construct : Input → PackedMembershipProgram
  bound : Polynomial ℕ
  generates : ∀ input, ∃ fuel, fuel ≤ bound.eval (scale input) ∧
    let result := bitProgramExecution constructor (encode input) (fun _ => false) (fun _ => false) fuel
    result.status = some true ∧ result.output = packedSerialization (construct input) ∧
      result.time ≤ bound.eval (scale input) ∧ result.visited.card ≤ bound.eval (scale input)

/-- Bounded-error solving by one uniform generated family;
2607.14650 pp.3–5,36–45. Execution bounds quantify uniformly before hidden inputs. -/
def UniformSolvingContract {Input : Type} {encode : Input → Str} {scale : Input → ℕ}
    (F : UniformResourceFamily Input encode scale)
    (Hidden : Input → Type)
    (oracle : (x : Input) → Hidden x → (k : Fin (F.construct x).oracles) →
      Matrix (Qubits ((F.construct x).arity k)) (Qubits ((F.construct x).arity k)) ℂ)
    (promise : (x : Input) → Hidden x → Prop)
    (solution : (x : Input) → Hidden x → Option (Fin (F.construct x).outputBits → Bool) → Prop) : Prop :=
  ∃ p : Polynomial ℕ, ∃ threshold : ℕ, ∀ x, threshold ≤ scale x → ∀ hidden,
    promise x hidden →
      (∀ k, oracle x hidden k ∈ Matrix.unitaryGroup _ ℂ) ∧
      membershipOutputLaw (F.construct x).program (oracle x hidden) (solution x hidden) ≥ 2/3 ∧
      membershipResources (F.construct x).program (oracle x hidden) ≤ p.eval (scale x)

/-- Uniform finite-precision sampling contract with failure and conditional TV;
2607.16541 pp.16–17. Target weights are normalized on their domain; execution
and constructor work remain attached to actual programs. -/
def UniformSamplingContract {Input : Type} {encode : Input → Str} {scale : Input → ℕ}
    (F : UniformResourceFamily Input encode scale)
    (Hidden : Input → Type)
    (oracle : (x : Input) → Hidden x → (k : Fin (F.construct x).oracles) →
      Matrix (Qubits ((F.construct x).arity k)) (Qubits ((F.construct x).arity k)) ℂ)
    (promise : (x : Input) → Hidden x → Prop)
    (target : (x : Input) → Hidden x → (Fin (F.construct x).outputBits → Bool) → ℝ)
    (eta beta : Input → ℝ) : Prop :=
  ∃ p : Polynomial ℕ, ∃ threshold : ℕ, ∀ x, threshold ≤ scale x → ∀ hidden,
    promise x hidden →
      (∀ k, oracle x hidden k ∈ Matrix.unitaryGroup _ ℂ) ∧
      Learning.IsDistribution (target x hidden) ∧
      0 < eta x ∧ eta x < 1 ∧ 0 < beta x ∧ beta x < 1 ∧
      let P := F.construct x
      let success := membershipOutputLaw P.program (oracle x hidden) (fun o => o.isSome = true)
      1-beta x ≤ success ∧
      tvDist (fun z => membershipOutputLaw P.program (oracle x hidden) (fun o => o = some z)/success)
        (target x hidden) ≤ eta x ∧
      membershipResources P.program (oracle x hidden) ≤ p.eval (scale x)

example : serializeWords [] = [] := rfl

example :
    (programNodeTable (.coin 0 (fun _ => .fail) :
      AdaptiveMembershipProgram htcxGateSet (fun _ : Fin 0 => 0) (fun _ => false) 0 1 0) []).2.length = 2 := by
  norm_num [programNodeTable,internProgramNode,serializeWords,Complexity.encNat,List.replicate_succ,List.replicate_zero]


end QAlgorithms.OPI


