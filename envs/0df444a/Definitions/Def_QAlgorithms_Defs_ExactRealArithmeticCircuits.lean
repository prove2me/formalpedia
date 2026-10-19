-- Prove2me | Definitions.Def_QAlgorithms_Defs_ExactRealArithmeticCircuits
-- name    : QAlgorithms_Defs_ExactRealArithmeticCircuits
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:02:07.64675+00:00
-- url     : https://prove2.me/theorems/f23188ca-698e-4b01-b3f8-e098246aaa2f
-- title:
--   ExactRealArithmeticCircuits
-- statement:
--   ExactRealArithmeticCircuits
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\ExactRealArithmeticCircuits.lean

import Definitions.Def_QAlgorithms_Defs_RealLabelRegisters
import Definitions.Def_QAlgorithms_Defs_CircuitResources
import Definitions.Def_QAlgorithms_Defs_SpectralFilter
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

open MeasureTheory
open scoped ENNReal
namespace QAlgorithms.ExactArithmetic

/-- Implementation helper; source: arxiv-2510.08509v1 PDF p.8. -/
inductive ClassicalInstruction (input registers : ℕ) where
  | constant (dst : Fin registers) (value : ℝ)
  | read (dst : Fin registers) (src : Fin input)
  | copy (dst src : Fin registers)
  | add (dst a b : Fin registers)
  | sub (dst a b : Fin registers)
  | mul (dst a b : Fin registers)
  | div (dst a b : Fin registers)
  | coin (dst : Fin registers)

/-- Concrete fixed-position exact-real register syntax and semantics with charged retrieval, +,−,×,÷, classical random bits, ordinary elementary quantum gates and measurement. Coherent arithmetic preserves operands and reversibly writes a result, with division branches guarding bad denominators. Use an explicit ideal-arithmetic extension (e.g. atomic real-labelled Hilbert registers); finitely many qubits cannot encode all ℝ exactly. Arithmetic gates have specified basis actions, not arbitrary unitaries given unit cost. No coherent indexed memory primitive. Count actual elementary operations, inverse calls and output work. Approximation success is not a structure field. Source: arxiv-2510.08509v1 PDF p.8; arxiv-2510.08509v1 PDF p.9; arxiv-2510.08509v1 PDF p.19. -/
structure ClassicalCircuit (input registers out : ℕ) where
  instructions : List (ClassicalInstruction input registers)
  output : Fin out → Fin registers

/-- Implementation helper; source: arxiv-2510.08509v1 PDF p.8. -/
structure ClassicalState (registers : ℕ) where
  memory : Fin registers → ℝ
  failed : Bool
  work : ℕ

/-- Implementation helper; source: arxiv-2510.08509v1 PDF p.8. -/
def classicalStep {input r : ℕ} (data : Fin input → ℝ) (s : ClassicalState r) :
    ClassicalInstruction input r → PMF (ClassicalState r)
  | .constant dst v => PMF.pure ⟨Function.update s.memory dst v,s.failed,s.work+1⟩
  | .read dst src => PMF.pure ⟨Function.update s.memory dst (data src),s.failed,s.work+1⟩
  | .copy dst src => PMF.pure ⟨Function.update s.memory dst (s.memory src),s.failed,s.work+1⟩
  | .add dst a b => PMF.pure ⟨Function.update s.memory dst (s.memory a+s.memory b),s.failed,s.work+1⟩
  | .sub dst a b => PMF.pure ⟨Function.update s.memory dst (s.memory a-s.memory b),s.failed,s.work+1⟩
  | .mul dst a b => PMF.pure ⟨Function.update s.memory dst (s.memory a*s.memory b),s.failed,s.work+1⟩
  | .div dst a b => PMF.pure (if s.memory b = 0 then {s with failed := true, work := s.work+1}
      else ⟨Function.update s.memory dst (s.memory a/s.memory b),s.failed,s.work+1⟩)
  | .coin dst => (PMF.uniformOfFintype Bool).map fun bit =>
      ⟨Function.update s.memory dst (if bit then 1 else -1),s.failed,s.work+1⟩

/-- Implementation helper; source: arxiv-2510.08509v1 PDF p.8. -/
def classicalExecution {input r out : ℕ} (C : ClassicalCircuit input r out) (data : Fin input → ℝ) :
    PMF (ClassicalState r) :=
  C.instructions.foldl (fun law op => law.bind fun s => classicalStep data s op) (PMF.pure ⟨0,false,0⟩)

/-- Implementation helper; source: arxiv-2510.08509v1 PDF p.8. -/
inductive ArithmeticOperation where
  | add | sub | mul | div

/-- Implementation helper; source: arxiv-2510.08509v1 PDF p.8. -/
def ArithmeticOperation.value (op : ArithmeticOperation) (x y : ℝ) : ℝ :=
  match op with | .add => x+y | .sub => x-y | .mul => x*y | .div => x/y

/-- Implementation helper; source: arxiv-2510.08509v1 PDF p.8. -/
inductive CoherentInstruction (input r q : ℕ) where
  | read (dst : Fin r) (src : Fin input) (inverse : Bool)
  | constant (dst : Fin r) (value : ℝ) (inverse : Bool)
  | sign (dst : Fin r) (bit : Fin q) (inverse : Bool)
  | arithmetic (op : ArithmeticOperation) (dst a b : Fin r) (ha : dst ≠ a) (hb : dst ≠ b)
      (inverse : Bool)
  | gate (g : GateApp oneTwoQubitGateSet q) (inverse : Bool)

/-- Implementation helper; source: arxiv-2510.08509v1 PDF p.8. -/
abbrev Label (r q : ℕ) := (Fin r → ℝ) × Qubits q

/-- Concrete fixed-position exact-real register syntax and semantics with charged retrieval, +,−,×,÷, classical random bits, ordinary elementary quantum gates and measurement. Coherent arithmetic preserves operands and reversibly writes a result, with division branches guarding bad denominators. Use an explicit ideal-arithmetic extension (e.g. atomic real-labelled Hilbert registers); finitely many qubits cannot encode all ℝ exactly. Arithmetic gates have specified basis actions, not arbitrary unitaries given unit cost. No coherent indexed memory primitive. Count actual elementary operations, inverse calls and output work. Approximation success is not a structure field. Source: arxiv-2510.08509v1 PDF p.8; arxiv-2510.08509v1 PDF p.9; arxiv-2510.08509v1 PDF p.19. -/
structure CoherentCircuit (input r q out : ℕ) where
  instructions : List (CoherentInstruction input r q)
  output : Fin out → Fin r

/-- Implementation helper; source: arxiv-2510.08509v1 PDF p.8. -/
def basisStep {input r q : ℕ} (data : Fin input → ℝ) (op : CoherentInstruction input r q)
    (x : Label r q) : Label r q →₀ ℂ :=
  match op with
  | .read dst src inv => Finsupp.single
      (Function.update x.1 dst (x.1 dst+(if inv then -data src else data src)),x.2) 1
  | .constant dst value inv => Finsupp.single
      (Function.update x.1 dst (x.1 dst+(if inv then -value else value)),x.2) 1
  | .sign dst bit inv => Finsupp.single
      (Function.update x.1 dst (x.1 dst+(if inv then -(if x.2 bit then 1 else -1) else (if x.2 bit then 1 else -1))),x.2) 1
  | .arithmetic op dst a b _ _ inv =>
      let value := if op = .div ∧ x.1 b = 0 then 0 else op.value (x.1 a) (x.1 b)
      Finsupp.single (Function.update x.1 dst (x.1 dst+(if inv then -value else value)),x.2) 1
  | .gate g inv => ∑ bits : Qubits g.gate.arity,
      Finsupp.single (x.1,overwrite g.wires x.2 bits)
        ((if inv then star g.gate.mat else g.gate.mat) bits (x.2 ∘ g.wires))

/-- Implementation helper; source: arxiv-2510.08509v1 PDF p.8. -/
instance arithmeticOperationDecidableEq : DecidableEq ArithmeticOperation := Classical.decEq _

/-- Implementation helper; source: arxiv-2510.08509v1 PDF p.8. -/
def coherentExecution {input r q out : ℕ} (C : CoherentCircuit input r q out) (data : Fin input → ℝ) :
    Label r q →₀ ℂ := C.instructions.foldl
      (fun wave op => wave.sum fun x amp => amp • basisStep data op x) (Finsupp.single (0,0) 1)

/-- Invert an elementary reversible instruction; inverses have the same charge.
Source: arxiv-2510.08509v1 PDF pp.8–9. -/
def CoherentInstruction.inverse {input r q : ℕ} :
    CoherentInstruction input r q → CoherentInstruction input r q
  | .read dst src inv => .read dst src (!inv)
  | .constant dst v inv => .constant dst v (!inv)
  | .sign dst bit inv => .sign dst bit (!inv)
  | .arithmetic op dst a b ha hb inv => .arithmetic op dst a b ha hb (!inv)
  | .gate g inv => .gate g (!inv)

/-- Apply a concrete arithmetic word to a supplied finitely supported wave, including dirty
input registers. Source: arxiv-2510.08509v1 PDF pp.8–9,19. -/
def executeWord {input r q : ℕ} (data : Fin input → ℝ)
    (word : List (CoherentInstruction input r q)) (wave : Label r q →₀ ℂ) : Label r q →₀ ℂ :=
  word.foldl (fun state op => state.sum fun x amp => amp • basisStep data op x) wave

/-- Every division has a nonzero denominator on the actual support before it is executed.
This excludes illegal exact arithmetic without assuming any output or accuracy property.
Source: arxiv-2510.08509v1 PDF p.8. -/
def coherentLegal {input r q : ℕ} (data : Fin input → ℝ) :
    List (CoherentInstruction input r q) → (Label r q →₀ ℂ) → Prop
  | [], _ => True
  | op::rest, wave =>
    (match op with
      | .arithmetic .div _ _ b _ _ _ => ∀ x ∈ wave.support, x.1 b ≠ 0
      | _ => True) ∧
      coherentLegal data rest (wave.sum fun x amp => amp • basisStep data op x)

/-- Concrete fixed-position exact-real register syntax and semantics with charged retrieval, +,−,×,÷, classical random bits, ordinary elementary quantum gates and measurement. Coherent arithmetic preserves operands and reversibly writes a result, with division branches guarding bad denominators. Use an explicit ideal-arithmetic extension (e.g. atomic real-labelled Hilbert registers); finitely many qubits cannot encode all ℝ exactly. Arithmetic gates have specified basis actions, not arbitrary unitaries given unit cost. No coherent indexed memory primitive. Count actual elementary operations, inverse calls and output work. Approximation success is not a structure field. Source: arxiv-2510.08509v1 PDF p.8; arxiv-2510.08509v1 PDF p.9; arxiv-2510.08509v1 PDF p.19. -/
def executionLaw {input r q out : ℕ} (C : CoherentCircuit input r q out) (data : Fin input → ℝ)
    (_valid : coherentLegal data C.instructions (Finsupp.single (0,0) 1)) :
    Measure ((Fin out → ℝ) × ℕ) :=
  (coherentExecution C data).sum fun x amp =>
    ENNReal.ofReal (‖amp‖^2) • Measure.dirac ((fun i => x.1 (C.output i)),C.instructions.length+r+q+out)

example {input r q out : ℕ} (output : Fin out → Fin r) (data : Fin input → ℝ) :
    coherentExecution (⟨[],output⟩ : CoherentCircuit input r q out) data = Finsupp.single (0,0) 1 := rfl

example {input r out : ℕ} (output : Fin out → Fin r) (data : Fin input → ℝ) :
    classicalExecution (⟨[],output⟩ : ClassicalCircuit input r out) data = PMF.pure ⟨0,false,0⟩ := rfl

end QAlgorithms.ExactArithmetic


