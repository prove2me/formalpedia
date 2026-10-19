-- Prove2me | Definitions.Def_QAlgorithms_Defs_OPIOraclePrograms
-- name    : QAlgorithms_Defs_OPIOraclePrograms
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:23:38.308684+00:00
-- url     : https://prove2.me/theorems/db2e0e9c-1104-4272-bfaa-1ce9d1198958
-- title:
--   OPIOraclePrograms
-- statement:
--   OPIOraclePrograms
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\OPIOraclePrograms.lean

import Definitions.Def_QAlgorithms_Defs_OPIFieldData
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_CircuitResources
noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix

namespace QAlgorithms.OPI

/-- Indexed XOR membership access; 2607.16541 p.15 (41), 2607.14650 p.19.
Coherent scalar index access is allowed here; folded access uses separate labels. -/
def indexedMembershipOracle {F : Type*} [DecidableEq F] {m : ℕ}
    (S : Fin m → Finset F) : Matrix ((Fin m × F) × Bool) ((Fin m × F) × Bool) ℂ :=
  xorOracle fun ia => decide (ia.2 ∈ S ia.1)

/-- Canonical public qubit embedding of the indexed prime-field oracle basis;
2607.16541 p.7. The index comes first, then the field label, then the answer. -/
def indexedOracleEmbedding (m p : ℕ) :
    Matrix (Qubits (Nat.clog 2 m+Nat.clog 2 p+1)) ((Fin m × ZMod p) × Bool) ℂ :=
  Matrix.of fun z ia => if z =
    Fin.snoc (Fin.append (natToBits (Nat.clog 2 m) ia.1.1)
      (natToBits (Nat.clog 2 p) ia.1.2.val)) ia.2 then 1 else 0

/-- Exact total extension, identity on invalid code-space encodings;
2607.16541 p.7 (41). -/
def indexedQubitOracle {m p : ℕ} [NeZero p] (sets : Fin m → Finset (ZMod p)) :
    Matrix (Qubits (Nat.clog 2 m+Nat.clog 2 p+1))
      (Qubits (Nat.clog 2 m+Nat.clog 2 p+1)) ℂ :=
  extendEncodedUnitary (indexedOracleEmbedding m p) (indexedMembershipOracle sets)

/-- Finite adaptive gate/bit/oracle engine;
2607.16541 pp.7,14–17, 2610.02145 p.16.
Gate set and control policy are parameters; no hidden data enters known instructions. -/
inductive AdaptiveMembershipProgram (S : Set Gate) {r : ℕ}
    (a : Fin r → ℕ) (control : Fin r → Bool) (N c out : ℕ) where
  | halt (decode : BoolCircuit c out) (valid : decode.WellFormed)
  | fail
  | gate (g : GateApp S N) (next : AdaptiveMembershipProgram S a control N c out)
  | query (k : Fin r) (adjoint : Bool) (ctl : Option (Fin N))
      (allowed : ctl.isSome → control k = true) (w : Fin (a k) ↪ Fin N)
      (disjoint : ∀ q, ctl = some q → q ∉ Set.range w)
      (next : AdaptiveMembershipProgram S a control N c out)
  | measure (q : Fin N) (dst : Fin c)
      (next : Bool → AdaptiveMembershipProgram S a control N c out)
  | prepare (q : Fin N) (next : AdaptiveMembershipProgram S a control N c out)
  | coin (dst : Fin c) (next : Bool → AdaptiveMembershipProgram S a control N c out)
  | setBit (dst : Fin c) (b : Bool) (next : AdaptiveMembershipProgram S a control N c out)
  | boolean (op : BoolOp) (dst x y : Fin c)
      (next : AdaptiveMembershipProgram S a control N c out)
  | branch (src : Fin c) (next : Bool → AdaptiveMembershipProgram S a control N c out)

/-- Execution leaf: output/failure, subnormalized density, and
query/gate/preparation/measurement/classical counts; 2607.16541 p.7. -/
abbrev MembershipLeaf (N out : ℕ) :=
  (Option (Fin out → Bool) × Matrix (Qubits N) (Qubits N) ℂ) × (Fin 5 → ℕ)

/-- Born/coin execution with charged operations; 2607.16541 pp.7,14–17.
Zero ancillas are supplied at the top-level execution; prepare is a charged reset.
Postselection is explicit failure, so restarts count every attempt. -/
def adaptiveExecution {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {ctl : Fin r → Bool}
    {N c out : ℕ} (O : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) :
    AdaptiveMembershipProgram S a ctl N c out →
      Matrix (Qubits N) (Qubits N) ℂ → (Fin c → Bool) → List (MembershipLeaf N out)
  | .halt D _, rho, mem => [((some (D.eval mem),rho),fun j => if j = 4 then D.size else 0)]
  | .fail, rho, _ => [((none,rho),0)]
  | .gate g next, rho, mem =>
      (adaptiveExecution O next (conjSuperop (embedOp g.gate.mat g.wires) rho) mem).map
        fun leaf => (leaf.1,leaf.2+Pi.single 1 1)
  | .query k adj control _ w hc next, rho, mem =>
      (adaptiveExecution O next
        (conjSuperop (OracleStep.mat (S := S) O (.query k adj control w hc)) rho) mem).map
          fun leaf => (leaf.1,leaf.2+Pi.single 0 1)
  | .measure q dst next, rho, mem =>
      [false,true].flatMap fun b =>
        (adaptiveExecution O (next b) (conjSuperop (qubitOp1 (measProj b) q) rho)
          (Function.update mem dst b)).map fun leaf => (leaf.1,leaf.2+Pi.single 3 1)
  | .prepare q next, rho, mem =>
      (adaptiveExecution O next (krausApply (fun b : Bool => qubitOp1 (resetKraus b) q) rho) mem).map
        fun leaf => (leaf.1,leaf.2+Pi.single 2 1)
  | .coin dst next, rho, mem =>
      [false,true].flatMap fun b =>
        (adaptiveExecution O (next b) ((1/2 : ℂ) • rho)
          (Function.update mem dst b)).map fun leaf => (leaf.1,leaf.2+Pi.single 4 1)
  | .setBit dst b next, rho, mem =>
      (adaptiveExecution O next rho (Function.update mem dst b)).map
        fun leaf => (leaf.1,leaf.2+Pi.single 4 1)
  | .boolean op dst x y next, rho, mem =>
      let b := match op with | .and => mem x && mem y | .or => mem x || mem y | .not => !mem x
      (adaptiveExecution O next rho (Function.update mem dst b)).map
        fun leaf => (leaf.1,leaf.2+Pi.single 4 1)
  | .branch src next, rho, mem =>
      (adaptiveExecution O (next (mem src)) rho mem).map fun leaf => (leaf.1,leaf.2+Pi.single 4 1)

/-- Top-level output event law, zero quantum/classical workspace;
2607.16541 p.7, 2610.02145 p.16. -/
def membershipOutputLaw {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {ctl : Fin r → Bool}
    {N c out : ℕ} (P : AdaptiveMembershipProgram S a ctl N c out)
    (O : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ)
    (event : Option (Fin out → Bool) → Prop) : ℝ :=
  ((adaptiveExecution O P (pureDensity (zeroKet N)) (fun _ => false)).map fun leaf =>
    if event leaf.1.1 then leaf.1.2.trace.re else 0).sum

/-- Worst charged work on positive-probability branches, with explicit workspace;
2607.16541 p.7. -/
def membershipResources {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {ctl : Fin r → Bool}
    {N c out : ℕ} (P : AdaptiveMembershipProgram S a ctl N c out)
    (O : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) : ℕ :=
  N+c+(adaptiveExecution O P (pureDensity (zeroKet N)) (fun _ => false)).foldl
    (fun acc leaf => if 0 < leaf.1.2.trace.re then max acc (∑ j, leaf.2 j) else acc) 0

example {F : Type*} [DecidableEq F] {m : ℕ} :
    indexedMembershipOracle (fun _ : Fin m => (∅ : Finset F)) = 1 := by
  change xorOracle (0 : Fin m × F → Bool) = 1
  ext p q
  simp [xorOracle,Matrix.one_apply,Prod.ext_iff]

example {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {ctl : Fin r → Bool}
    {N c out : ℕ} (O : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ)
    (rho : Matrix (Qubits N) (Qubits N) ℂ) (mem : Fin c → Bool) :
    adaptiveExecution O (.fail : AdaptiveMembershipProgram S a ctl N c out) rho mem =
      [((none,rho),0)] := rfl

end QAlgorithms.OPI


