-- Prove2me | Definitions.Def_NuclearTensor_Membership_Computation
-- name    : NuclearTensor_Membership_Computation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T22:14:22.499951+00:00
-- url     : https://prove2.me/theorems/43eadf22-5e23-421f-8dfc-d5f5a7638b17
-- title:
--   Finite real arithmetic programs, charged spectral operations, and execution
-- statement:
--   A program is a finite list of instructions extending the published scalar real RAM. Its state has real registers, integer pointers, and real and integer random-access memory. Arithmetic, comparison, indexed access, jumps, square root, integer address operations, and halt cost one per executed instruction. Fixed real literals are allowed, as in the published core; programs precede all tensor instances.
--
--   An ordinary full real SVD supplies orthogonal matrices, nonnegative ordered singular values, and exact reconstruction. A fixed deterministic implementation is used throughout an execution, and algorithm guarantees range over every such implementation. An SVD of an $a\times b$ matrix is charged
--   $$1+A(a+b+1)^q+ab+\text{output length},$$
--   where $A,q$ are positive fixed model parameters. A stipulated local optimizer is accessible only at valid local indices and positive tolerance $\tau$, with charge $1+A(1+d+\lceil\tau^{-1}\rceil)^q+2d_j$. Its local feasibility/accuracy contract is stated separately. There is no global product optimizer, nuclear-norm evaluator, or membership primitive.
--
--   Finite-code calls execute supplied code in fresh memory, charging all child work and input/output copies. A runtime claim requires a finite execution derivation; output materialization is charged at the outer boundary as well. These semantics preclude assigning an invented cost to an arbitrary function.
--
--   **Formalization Note** This is the paper's arithmetic/spectral-oracle reading, not bit complexity for arbitrary reals. The goal has no local service and no supplied procedures. Nonemptiness of the ordinary SVD interface is itself included in the mathematical targets.
-- source:
--   Martino Bernasconi, Giulio Malavolta, STOC 2027 submission #945 (October 2026), pp.10–12, polynomial-time SVD; pp.17–20, local-oracle arithmetic computations

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_NuclearTensor_Membership_Geometry

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace NuclearTensor.Membership

/-- Ordinary full real SVD, with no optimization or tensor-membership primitive. -/
structure SVDResult (a b : ℕ) (M : Mat a b) where
  left : Mat a a
  right : Mat b b
  singular : Fin (min a b) → ℝ
  left_orthogonal : orthonormalColumns left
  right_orthogonal : orthonormalColumns right
  nonnegative : ∀ t, 0 ≤ singular t
  decreasing : Antitone singular
  reconstruct : ∀ i j, M i j = ∑ t : Fin (min a b),
    matEntry left i.val t.val * singular t * matEntry right j.val t.val

/-- A fixed deterministic spectral implementation. Algorithms below must work for every such
implementation, so choices of eigenbases cannot encode answers to another problem. -/
abbrev Spectral := (a b : ℕ) → (M : Mat a b) → SVDResult a b M

/-- The source's given, deterministic local linear-optimization service. Its mathematical
contract is stated separately, for all objectives and positive accuracies. It has no global
product-optimization operation. Calls outside its finite dimension list are unavailable. -/
structure LocalOracle where
  dimensions : List ℕ
  answer : (j : Fin dimensions.length) → Vec (dimensions.getD j.val 0) → ℝ →
    Vec (dimensions.getD j.val 0)

inductive Instruction where
  | core (i : SmaleNinth.RAMInstr)
  | sqrt (dst src : ℕ)
  | cast (dst src : ℕ)
  | padd (dst a b : ℕ)
  | pmul (dst a b : ℕ)
  | iload (dst address : ℕ)
  | istore (address src : ℕ)
  | jump (pc : ℕ)
  /-- Dimensions, input base and output base are held in pointer registers. -/
  | svd (rows cols input output : ℕ)
  /-- Callee index and input/output block addresses/counts are pointer-register indices. -/
  | call (callee ri rn ii inn ro io : ℕ)
  | localOptimize (site input accuracy output : ℕ)
  | halt

abbrev Program := List Instruction

/-- Finite code with real literals as in the published real RAM. Core accept/reject are
replaced by explicit halt; no arbitrary function-valued instruction exists. -/
def admissible (P : Program) : Prop := ∀ i ∈ P, match i with
  | .core .accept | .core .reject => False
  | _ => True

structure Configuration where
  core : SmaleNinth.RAMConfig
  integers : ℤ → ℤ

/-- Integer input block and real input block start at zero. The two input lengths occupy
pointer registers 0 and 1; every other register and unused cell starts at zero. -/
def initConfig (is : List ℤ) (rs : List ℝ) : Configuration where
  core := ⟨0, fun _ => 0,
    fun q => if q = 0 then is.length else if q = 1 then rs.length else 0,
    fun z => if 0 ≤ z then rs[z.toNat]?.getD 0 else 0⟩
  integers := fun z => if 0 ≤ z then is[z.toNat]?.getD 0 else 0

def readBlock {α : Type} (mem : ℤ → α) (base : ℤ) (n : ℕ) : List α :=
  List.ofFn (fun i : Fin n => mem (base + i.val))

def writeBlock {α : Type} (mem : ℤ → α) (base : ℤ) (xs : List α) : ℤ → α :=
  fun z => if h : 0 ≤ z - base ∧ (z - base).toNat < xs.length then
    xs[(z - base).toNat] else mem z

def coreCode (P : Program) : SmaleNinth.RAMProgram :=
  P.map fun i => match i with | .core c => c | _ => .const 0 0

/-- Scalar operations cost one. A full SVD on an a-by-b matrix costs
1+A(a+b+1)^q plus its explicit input/output array traffic. A and q are fixed model
parameters, not per-instance certificates. -/
def basicStep (σ : Spectral) (ω : Option LocalOracle) (A q : ℕ) (P : Program) (s : Configuration) :
    Option (Configuration × ℕ) :=
  let t : Configuration := {s with core := {s.core with pc := s.core.pc + 1}}
  match P[s.core.pc]? with
  | some (.core _) => some ({t with core := SmaleNinth.RAMStep (coreCode P) s.core}, 1)
  | some (.sqrt d a) => some ({t with core := {t.core with
      regs := Function.update s.core.regs d (Real.sqrt (s.core.regs a))}}, 1)
  | some (.cast d a) => some ({t with core := {t.core with
      regs := Function.update s.core.regs d (s.core.ptrs a : ℝ)}}, 1)
  | some (.padd d a b) => some ({t with core := {t.core with
      ptrs := Function.update s.core.ptrs d (s.core.ptrs a + s.core.ptrs b)}}, 1)
  | some (.pmul d a b) => some ({t with core := {t.core with
      ptrs := Function.update s.core.ptrs d (s.core.ptrs a * s.core.ptrs b)}}, 1)
  | some (.iload d a) => some ({t with core := {t.core with
      ptrs := Function.update s.core.ptrs d (s.integers (s.core.ptrs a))}}, 1)
  | some (.istore a v) => some ({t with integers := Function.update s.integers (s.core.ptrs a) (s.core.ptrs v)}, 1)
  | some (.jump pc) => some ({t with core := {t.core with pc := pc}}, 1)
  | some (.svd ar br inp out) =>
      let a := (s.core.ptrs ar).toNat
      let b := (s.core.ptrs br).toNat
      let M : Mat a b := fun i j => s.core.mem (s.core.ptrs inp + (i.val * b + j.val : ℕ))
      let D := σ a b M
      let xs := encodeMat D.left ++ List.ofFn D.singular ++ encodeMat D.right
      some ({t with core := {t.core with mem := writeBlock s.core.mem (s.core.ptrs out) xs}},
        1 + A * (a + b + 1) ^ q + a * b + xs.length)
  | some (.localOptimize site inp acc out) =>
      match ω with
      | none => none
      | some O =>
          if h : (s.core.ptrs site).toNat < O.dimensions.length ∧ 0 < s.core.regs acc then
            let j : Fin O.dimensions.length := ⟨(s.core.ptrs site).toNat, h.1⟩
            let n := O.dimensions.getD j.val 0
            let v : Vec n := WithLp.toLp 2 (fun i => s.core.mem (s.core.ptrs inp + i.val))
            let xs := encodeVec (O.answer j v (s.core.regs acc))
            let d := O.dimensions.foldl max 0
            some ({t with core := {t.core with mem := writeBlock s.core.mem (s.core.ptrs out) xs}},
              1 + A * (1 + d + Nat.ceil ((s.core.regs acc)⁻¹)) ^ q + 2 * n)
          else none
  | _ => none

def returnFromCall (s child : Configuration) (ro io : ℕ) : Configuration where
  core := { s.core with
    pc := s.core.pc + 1
    mem := writeBlock s.core.mem (s.core.ptrs ro)
      (readBlock child.core.mem 0 (child.core.ptrs 1).toNat) }
  integers := writeBlock s.integers (s.core.ptrs io)
    (readBlock child.integers 0 (child.core.ptrs 0).toNat)

/-- Only actual finite executions have a cost. Calls execute finite supplied code in fresh
memory, charge its complete execution and copy traffic, and return explicit finite arrays.
No instruction accepts a function or a correctness/cost certificate. -/
inductive Executes (σ : Spectral) (ω : Option LocalOracle) (A q : ℕ) (procedures : List Program) :
    Program → Configuration → Configuration → ℕ → Prop
  | halt (P : Program) (s : Configuration) (h : P[s.core.pc]? = some .halt) :
      Executes σ ω A q procedures P s s 1
  | basic (P : Program) (s t u : Configuration) (w c : ℕ)
      (h : basicStep σ ω A q P s = some (t, w))
      (tail : Executes σ ω A q procedures P t u c) :
      Executes σ ω A q procedures P s u (w + c)
  | call (P Q : Program) (s child u : Configuration) (childCost tailCost : ℕ)
      (callee ri rn ii inn ro io : ℕ)
      (hi : P[s.core.pc]? = some (.call callee ri rn ii inn ro io))
      (hc : procedures[(s.core.ptrs callee).toNat]? = some Q)
      (runChild : Executes σ ω A q procedures Q
        (initConfig
          (readBlock s.integers (s.core.ptrs ii) (s.core.ptrs inn).toNat)
          (readBlock s.core.mem (s.core.ptrs ri) (s.core.ptrs rn).toNat)) child childCost)
      (runTail : Executes σ ω A q procedures P (returnFromCall s child ro io) u tailCost) :
      Executes σ ω A q procedures P s u
        (1 + childCost + tailCost +
          2 * ((s.core.ptrs inn).toNat + (s.core.ptrs rn).toNat +
            (child.core.ptrs 0).toNat + (child.core.ptrs 1).toNat))

/-- A runtime bound is checked against the sum of executed instruction charges. -/
def runsWithin (σ : Spectral) (ω : Option LocalOracle) (A q : ℕ) (procedures : List Program)
    (P : Program) (is : List ℤ) (rs : List ℝ) (B : ℝ)
    (post : Configuration → Prop) : Prop :=
  admissible P ∧ (∀ Q ∈ procedures, admissible Q) ∧
    ∃ s c, Executes σ ω A q procedures P (initConfig is rs) s c ∧ ((c + (s.core.ptrs 0).toNat + (s.core.ptrs 1).toNat : ℕ) : ℝ) ≤ B ∧ post s

def outputReals (s : Configuration) : List ℝ :=
  readBlock s.core.mem 0 (s.core.ptrs 1).toNat

def outputIntegers (s : Configuration) : List ℤ :=
  readBlock s.integers 0 (s.core.ptrs 0).toNat

/-- Booleans are emitted as one integer, 0 or 1. -/
def outputsDecision (s : Configuration) (b : Bool) : Prop :=
  outputIntegers s = [if b then 1 else 0]

end NuclearTensor.Membership


