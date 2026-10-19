-- Prove2me | Definitions.Def_QAlgorithms_Defs_ApproximateMatrixCircuitFamilies
-- name    : QAlgorithms_Defs_ApproximateMatrixCircuitFamilies
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:04:41.603622+00:00
-- url     : https://prove2.me/theorems/2567412d-760e-450e-9247-c2ebfb599cee
-- title:
--   ApproximateMatrixCircuitFamilies
-- statement:
--   ApproximateMatrixCircuitFamilies
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\ApproximateMatrixCircuitFamilies.lean

import Definitions.Def_QAlgorithms_Defs_ExactRealArithmeticCircuits
import Definitions.Def_QAlgorithms_Defs_MultipleMatrixSketches
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

open MeasureTheory
namespace QAlgorithms.MatrixApprox

/-- Full exact-real matrix data, charged classical preprocessing/construction, and separate classical/quantum online costs. A single input-taking family precedes A; generated data-specific gate parameters/subroutines are charged. Output is a classical matrix with execution-induced law. Runtime is tied to primitive execution, not to free sampling/directional oracles or an arbitrary bound number. Input/output baseline kn²/n² entries is charged in preprocessing/total cost. Source: arxiv-2510.08509v1 PDF p.5; arxiv-2510.08509v1 PDF p.8; arxiv-2510.08509v1 PDF p.21; arxiv-2510.08509v1 PDF p.22. -/
structure PreprocessedCircuitFamily (input out : ℕ) where
  preprocessingRegisters : ℕ
  preprocessingOutput : ℕ
  preprocessing : ExactArithmetic.ClassicalCircuit input preprocessingRegisters preprocessingOutput
  quantumRegisters : ℕ
  qubits : ℕ
  online : ExactArithmetic.CoherentCircuit preprocessingOutput quantumRegisters qubits out

/-- Implemented arithmetic matrix multiplication family with an achievable exponent ω and corresponding square O(n^ω) and blocked rectangular O(n² c^(ω−2)) bounds in the useful 1≤c≤n sketch range; exact multiplication fallback outside that range. Fix the implementation before all matrices, with its constants explicit; do not assert attainment of the infimum of achievable exponents. ω=3 provides the elementary case. Source: arxiv-2510.08509v1 PDF p.6; arxiv-2510.08509v1 PDF p.13; arxiv-2510.08509v1 PDF p.14; arxiv-2510.08509v1 PDF p.22. -/
structure MultiplicationImplementation where
  registers : ℕ → ℕ → ℕ → ℕ
  circuit : (rows inner cols : ℕ) →
    ExactArithmetic.ClassicalCircuit (rows*inner+inner*cols) (registers rows inner cols) (rows*cols)

/-- Implemented arithmetic matrix multiplication family with an achievable exponent ω and corresponding square O(n^ω) and blocked rectangular O(n² c^(ω−2)) bounds in the useful 1≤c≤n sketch range; exact multiplication fallback outside that range. Fix the implementation before all matrices, with its constants explicit; do not assert attainment of the infimum of achievable exponents. ω=3 provides the elementary case. Source: arxiv-2510.08509v1 PDF p.6; arxiv-2510.08509v1 PDF p.13; arxiv-2510.08509v1 PDF p.14; arxiv-2510.08509v1 PDF p.22. -/
def IsAchievableExponent (I : MultiplicationImplementation) (omega : ℝ) : Prop :=
  2 ≤ omega ∧
    (∀ rows inner cols, ∀ A : Matrix (Fin rows) (Fin inner) ℝ,
      ∀ B : Matrix (Fin inner) (Fin cols) ℝ,
      let data : Fin (rows*inner+inner*cols) → ℝ := Fin.addCases
        (fun i => A (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)
        (fun i => B (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)
      ∀ state ∈ (ExactArithmetic.classicalExecution (I.circuit rows inner cols) data).support,
        state.failed = false ∧ ∀ i : Fin (rows*cols),
          state.memory ((I.circuit rows inner cols).output i) =
            (A*B) (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ n, 1 ≤ n →
      (((I.circuit n n n).instructions.length+I.registers n n n+n*n : ℕ) : ℝ) ≤ C*(n : ℝ)^omega ∧
      ∀ c, 1 ≤ c → c ≤ n →
        ∀ dims ∈ ([(n,(n,c)),(c,(n,n)),(c,(n,c)),(n,(c,c)),(n,(c,n))] : List (ℕ × (ℕ × ℕ))),
          (((I.circuit dims.1 dims.2.1 dims.2.2).instructions.length+
            I.registers dims.1 dims.2.1 dims.2.2+dims.1*dims.2.2 : ℕ) : ℝ) ≤
            C*(n : ℝ)^2*(c : ℝ)^(omega-2)

/-- U_P prepares all (k−1)n independent sign bits by Hadamards. Reversible O_X computes X_A(s) from given matrices; O_YX preserves |Y⟩|s⟩ and writes Tr(YᵀX_A(s)) for finite Fourier-grid Y∈(−1/2,1/2)^(n²), clearing temporary values with inverses. Register actions use the specified exact-arithmetic circuit model. Charge serial O(kn²) data/arithmetic work per complete use; no free input-dependent directional oracle. Adjoints must have concrete semantics/costs. Source: arxiv-2510.08509v1 PDF p.9; arxiv-2510.08509v1 PDF p.18; arxiv-2510.08509v1 PDF p.19; arxiv-2510.08509v1 PDF p.22. -/
def signPreparation (n k : ℕ) : Matrix (Qubits (k*n)) (Qubits (k*n)) ℂ := hadamardN (k*n)


/-- Address layout for the serial reversible rank-one sketch. The source uses k+1 matrices
and k independent n-bit signs; each address is fixed, with no coherent memory primitive.
Source: arxiv-2510.08509v1 PDF pp.18–19. -/
abbrev SketchSlot (n k : ℕ) :=
  (Fin (k+1) × (Fin n × Fin n)) ⊕ ((Fin k × Fin n) ⊕
    ((Fin k × Fin n) ⊕ (Fin n ⊕ (Fin k ⊕ (Fin (k+1) ⊕
      ((Fin n × Fin n) ⊕ ((Fin n × Fin n) ⊕ Unit)))))))

/-- The serial source sketch value oracle O_X. It computes matrix-vector products and scalar
contractions using fixed-position exact additions/multiplications, copies the rank-one matrix
into the answer register, then reverses every temporary operation. The sign bits are preserved.
For k=0 it writes the single input matrix directly. Source: arxiv-2510.08509v1 PDF pp.18–19. -/
def sketchValueCircuit (n k : ℕ) :
    ExactArithmetic.CoherentCircuit ((k+1)*(n*n)) (Fintype.card (SketchSlot n k)) (k*n) (n*n) := by
  classical
  let address := Fintype.equivFin (SketchSlot n k)
  let dataAddr := fun (t : Fin (k+1)) (i j : Fin n) => address (Sum.inl (t,(i,j)))
  let signAddr := fun (t : Fin k) (i : Fin n) => address (Sum.inr (Sum.inl (t,i)))
  let vecAddr := fun (t : Fin k) (i : Fin n) => address (Sum.inr (Sum.inr (Sum.inl (t,i))))
  let rowAddr := fun (i : Fin n) => address (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))
  let factor := fun (t : Fin k) => address (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl t)))))
  let chain := fun (t : Fin (k+1)) => address (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl t))))))
  let product := fun (i j : Fin n) => address (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i,j))))))))
  let output := fun (z : Fin (n*n)) => address (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (finProdFinEquiv.symm z)))))))))
  let mul := fun (dst a b : Fin (Fintype.card (SketchSlot n k))) (ha : dst ≠ a) (hb : dst ≠ b) =>
    ExactArithmetic.CoherentInstruction.arithmetic (input := (k+1)*(n*n)) (q := k*n) .mul dst a b ha hb false
  let reads := (List.finRange (k+1)).flatMap fun t => (List.finRange n).flatMap fun i =>
    (List.finRange n).map fun j => ExactArithmetic.CoherentInstruction.read (q := k*n)
      (dataAddr t i j) (finProdFinEquiv (t,finProdFinEquiv (i,j))) false
  let signs := (List.finRange k).flatMap fun t => (List.finRange n).map fun i =>
    ExactArithmetic.CoherentInstruction.sign (input := (k+1)*(n*n)) (signAddr t i) (finProdFinEquiv (t,i)) false
  let vectors := (List.finRange k).flatMap fun t => (List.finRange n).flatMap fun i =>
    (List.finRange n).map fun j => mul (vecAddr t i) (dataAddr t.castSucc i j) (signAddr t j)
      (by simp [vecAddr,dataAddr,address]) (by simp [vecAddr,signAddr,address])
  let body := if hk : k=0 then [] else
    reads ++ signs ++ vectors ++
    ((List.finRange n).flatMap fun j => (List.finRange n).map fun i =>
      mul (rowAddr j) (signAddr ⟨k-1,by omega⟩ i) (dataAddr (Fin.last k) i j)
        (by simp [rowAddr,signAddr,address]) (by simp [rowAddr,dataAddr,address])) ++
    [ExactArithmetic.CoherentInstruction.constant (chain 0) 1 false] ++
    ((List.finRange (k-1)).flatMap fun t =>
      let prev : Fin k := ⟨t.val,by have := t.isLt; omega⟩
      let next : Fin k := ⟨t.val+1,by have := t.isLt; omega⟩
      ((List.finRange n).map fun i => mul (factor next) (signAddr prev i) (vecAddr next i)
        (by simp [factor,signAddr,address]) (by simp [factor,vecAddr,address])) ++
      [mul (chain next.castSucc) (chain prev.castSucc) (factor next)
        (by intro h; have h1 := address.injective h
            simp only [Sum.inr.injEq,Sum.inl.injEq] at h1
            have h2 := congrArg Fin.val h1; dsimp [next,prev] at h2; omega)
        (by simp [chain,factor,address])]) ++
    ((List.finRange n).flatMap fun i => (List.finRange n).map fun j =>
      mul (product i j) (vecAddr ⟨0,by omega⟩ i) (rowAddr j)
        (by simp [product,vecAddr,address]) (by simp [product,rowAddr,address]))
  let writeOutput := if hk : k=0 then (List.finRange (n*n)).map fun z =>
      ExactArithmetic.CoherentInstruction.read (output z)
        (finProdFinEquiv (⟨0,by omega⟩,z)) false
    else (List.finRange (n*n)).map fun z => mul (output z)
      (product (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2) (chain ⟨k-1,by omega⟩)
      (by simp [output,product,address]) (by simp [output,chain,address])
  exact ⟨body ++ writeOutput ++ (body.reverse.map ExactArithmetic.CoherentInstruction.inverse),output⟩

/-- Lift fixed-position elementary instructions through a register injection, leaving added
real registers unchanged. Source: arxiv-2510.08509v1 PDF pp.8–9,19. -/
def embedArithmeticWord {input r s q : ℕ} (e : Fin r ↪ Fin s) :
    ExactArithmetic.CoherentInstruction input r q → ExactArithmetic.CoherentInstruction input s q
  | .read dst src inv => .read (e dst) src inv
  | .constant dst v inv => .constant (e dst) v inv
  | .sign dst bit inv => .sign (e dst) bit inv
  | .arithmetic op dst a b ha hb inv => .arithmetic op (e dst) (e a) (e b)
      (fun h => ha (e.injective h)) (fun h => hb (e.injective h)) inv
  | .gate g inv => .gate g inv

/-- The concrete scalar sketch oracle O_YX: arbitrary real Y labels are kept in an added
register, X is computed, its dot product with Y is accumulated in an answer, and the entire
X computation is reversed. The word preserves Y and all sign bits; each use charges all
matrix reads and serial arithmetic. Source: arxiv-2510.08509v1 PDF p.19. -/
def sketchInnerProductCircuit (n k : ℕ) := by
  classical
  let C := sketchValueCircuit n k
  let r := Fintype.card (SketchSlot n k)
  let e : Fin r ↪ Fin (r+(n*n+1)) := ⟨Fin.castAdd (n*n+1),Fin.castAdd_injective _ _⟩
  let Y := fun z : Fin (n*n) => Fin.natAdd r (Fin.castAdd 1 z)
  let answer := Fin.natAdd r (Fin.last (n*n))
  let word := C.instructions.map (embedArithmeticWord e)
  let dot := (List.finRange (n*n)).map fun z =>
    ExactArithmetic.CoherentInstruction.arithmetic (input := (k+1)*(n*n)) (q := k*n)
      .mul answer (Y z) (e (C.output z))
      (by intro h; have h1 := congrArg Fin.val h; simp [answer,Y] at h1; have := z.isLt; omega)
      (by intro h; have h1 := congrArg Fin.val h; simp [answer,e] at h1; have := (C.output z).isLt; omega) false
  let scalar : ExactArithmetic.CoherentCircuit ((k+1)*(n*n)) (r+(n*n+1)) (k*n) 1 :=
    ⟨word ++ dot ++ (word.reverse.map ExactArithmetic.CoherentInstruction.inverse),fun _ => answer⟩
  exact (scalar,Y)

/-- The classical measured matrix output uses the Borel sigma-algebra of its finite
coordinate topology. Source: arxiv-2510.08509v1 PDF pp.9,19,22. -/
instance matrixOutputMeasurableSpace (n : ℕ) : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) :=
  borel _

/-- Identify the classical matrix output sigma-algebra with its Borel sigma-algebra.
Source: arxiv-2510.08509v1 PDF pp.9,19,22. -/
instance matrixOutputBorelSpace (n : ℕ) : BorelSpace (Matrix (Fin n) (Fin n) ℝ) := ⟨rfl⟩

/-- Fixed-position ideal arithmetic syntax, rational constants and fixed elementary
unitaries. Comparison reversibly XORs [a ≤ b] into a qubit, preserving real operands.
This supplies value-to-qubit control: finite phase synthesis must explicitly compute
bits, apply fixed rotations and uncompute, never call a free real-phase oracle.
Comparison is an explicit refinement of the arithmetic model (not one of the four
operations listed on p.8); its source-model compilation remains an obligation.
Source: arxiv-2510.08509v1 PDF pp.8–9; arxiv-2111.09787v2 PDF pp.8–12. -/
inductive MeanEstimatorInstruction (input r q : ℕ) where
  | read (dst : Fin r) (src : Fin input) (inverse : Bool)
  | constant (dst : Fin r) (value : ℚ) (inverse : Bool)
  | sign (dst : Fin r) (bit : Fin q) (inverse : Bool)
  | arithmetic (op : ExactArithmetic.ArithmeticOperation) (dst a b : Fin r)
      (ha : dst ≠ a) (hb : dst ≠ b) (inverse : Bool)
  | gate (g : GateApp oneTwoQubitGateSet q) (inverse : Bool)
  | compare (a b : Fin r) (bit : Fin q)

/-- Specified basis actions; no arbitrary input-dependent unitary is supplied.
Source: arxiv-2510.08509v1 PDF pp.8–9; arxiv-2111.09787v2 PDF pp.8–12. -/
def MeanEstimatorInstruction.basisStep {input r q : ℕ} (data : Fin input → ℝ) :
    MeanEstimatorInstruction input r q → ExactArithmetic.Label r q →
      (ExactArithmetic.Label r q →₀ ℂ)
  | .read dst src inv, x => ExactArithmetic.basisStep data (.read dst src inv) x
  | .constant dst v inv, x => ExactArithmetic.basisStep data (.constant dst (v : ℝ) inv) x
  | .sign dst bit inv, x => ExactArithmetic.basisStep data (.sign dst bit inv) x
  | .arithmetic op dst a b ha hb inv, x =>
      ExactArithmetic.basisStep data (.arithmetic op dst a b ha hb inv) x
  | .gate g inv, x => ExactArithmetic.basisStep data (.gate g inv) x
  | .compare a b bit, x => Finsupp.single
      (x.1, Function.update x.2 bit (xor (x.2 bit) (decide (x.1 a ≤ x.1 b)))) 1

/-- Concrete inverses with the same unit charge.
Source: arxiv-2510.08509v1 PDF pp.8–9. -/
def MeanEstimatorInstruction.inverse {input r q : ℕ} :
    MeanEstimatorInstruction input r q → MeanEstimatorInstruction input r q
  | .read dst src inv => .read dst src (!inv)
  | .constant dst v inv => .constant dst v (!inv)
  | .sign dst bit inv => .sign dst bit (!inv)
  | .arithmetic op dst a b ha hb inv => .arithmetic op dst a b ha hb (!inv)
  | .gate g inv => .gate g (!inv)
  | .compare a b bit => .compare a b bit

/-- Finite adaptive syntax fixed before real input or hidden law. Measurement has two
explicit continuation programs, not a function constructing free syntax from data.
Measured bits can be copied to real registers by sign and used by later arithmetic.
No sampling/value/scalar macro calls: full instructions and adjoints must be inlined.
This is a candidate-program type, not CHJ Algorithm 2 already constructed.
Source: arxiv-2510.08509v1 PDF p.9; arxiv-2111.09787v2 PDF pp.10–12. -/
inductive MeanEstimatorProgram (input r q : ℕ) where
  | halt
  | step (op : MeanEstimatorInstruction input r q) (next : MeanEstimatorProgram input r q)
  | observe (bit : Fin q) (zero one : MeanEstimatorProgram input r q)

/-- Serialized size including both adaptive arms, for charged construction.
Source: arxiv-2510.08509v1 PDF pp.8–9,22. -/
def MeanEstimatorProgram.nodes {input r q : ℕ} : MeanEstimatorProgram input r q → ℕ
  | .halt => 1
  | .step _ next => 1 + next.nodes
  | .observe _ zero one => 1 + zero.nodes + one.nodes

/-- Operational matrix-output circuit TYPE. Neither accuracy, a distribution nor a
query/time bound is a field. Quantify a constructor before all matrices and hidden laws;
only public dimensions/budgets may select syntax. Fixed elementary gate parameters may
depend on those public parameters, never on real matrix entries.
Source: arxiv-2510.08509v1 PDF pp.8–9,19,22. -/
structure MeanEstimatorCircuit (n input : ℕ) where
  registers : ℕ
  qubits : ℕ
  program : MeanEstimatorProgram input registers qubits
  output : Fin (n*n) → Fin registers

/-- Projective bit measurements pass unnormalized projected waves to separate arms.
Terminal Born measures are added, never amplitudes across observed arms. Each executed
instruction/measurement and final output is charged. No postselection or externally
selected law. Source: arxiv-2510.08509v1 PDF pp.8–9; arxiv-2111.09787v2 PDF pp.10–12. -/
def MeanEstimatorProgram.run {n input r q : ℕ} (data : Fin input → ℝ)
    (output : Fin (n*n) → Fin r) : MeanEstimatorProgram input r q →
      (ExactArithmetic.Label r q →₀ ℂ) → ℕ →
        Measure (Matrix (Fin n) (Fin n) ℝ × ℕ)
  | .halt, wave, work => wave.sum fun x amp =>
      ENNReal.ofReal (‖amp‖^2) • Measure.dirac
        ((Matrix.of fun i j => x.1 (output (finProdFinEquiv (i,j)))), work+n*n)
  | .step op next, wave, work =>
      next.run data output (wave.sum fun x amp => amp • op.basisStep data x) (work+1)
  | .observe bit zero one, wave, work =>
      zero.run data output (wave.filter fun x => x.2 bit = false) (work+1) +
      one.run data output (wave.filter fun x => x.2 bit = true) (work+1)

/-- Division validity on every reachable branch. Zero waves make unreachable-branch
denominator obligations vacuous. Source: arxiv-2510.08509v1 PDF p.8; arxiv-2111.09787v2 PDF p.12. -/
def MeanEstimatorProgram.legal {input r q : ℕ} (data : Fin input → ℝ) :
    MeanEstimatorProgram input r q → (ExactArithmetic.Label r q →₀ ℂ) → Prop
  | .halt, _ => True
  | .step op next, wave =>
      (match op with
        | .arithmetic .div _ _ b _ _ _ => ∀ x ∈ wave.support, x.1 b ≠ 0
        | _ => True) ∧
      next.legal data (wave.sum fun x amp => amp • op.basisStep data x)
  | .observe bit zero one, wave =>
      zero.legal data (wave.filter fun x => x.2 bit = false) ∧
      one.legal data (wave.filter fun x => x.2 bit = true)

/-- Input-taking construction baseline: read input, allocate registers/qubits and
serialize every continuation. Additional classical preprocessing must also be charged
by the theorem's implementation; this does not certify efficient construction.
Source: arxiv-2510.08509v1 PDF pp.8–9,22. -/
def MeanEstimatorCircuit.constructionWork {n input : ℕ} (C : MeanEstimatorCircuit n input) : ℕ :=
  input + C.registers + C.qubits + C.program.nodes

/-- Joint measured output and path cost including charged syntax construction.
Source: arxiv-2510.08509v1 PDF pp.8–9,19,22. -/
def MeanEstimatorCircuit.executionLaw {n input : ℕ} (C : MeanEstimatorCircuit n input)
    (data : Fin input → ℝ) : Measure (Matrix (Fin n) (Fin n) ℝ × ℕ) :=
  C.program.run data C.output (Finsupp.single (0,0) 1) C.constructionWork

/-- Operational admissibility: legal divisions and unit total Born mass. Normalization
is an explicit proof obligation, not a favorable-output assumption. General preservation
and CHJ compilation remain separate obligations.
Source: arxiv-2510.08509v1 PDF pp.8–9; arxiv-2111.09787v2 PDF pp.7,12. -/
def MeanEstimatorCircuit.Admissible {n input : ℕ} (C : MeanEstimatorCircuit n input)
    (data : Fin input → ℝ) : Prop :=
  C.program.legal data (Finsupp.single (0,0) 1) ∧ C.executionLaw data Set.univ = 1

/-- Matrix output is the pushforward of computed execution. No arbitrary distribution,
accuracy or cost certificate is accepted. Theorem 2.5 requires n>0, 0<δ<1,
N≥log(n²/δ), error sqrt(Tr Σ)*log(n²/δ)/N and success ≥1−δ; these belong to the
existential uniform-constructor theorem, not this total execution definition.
Source: arxiv-2510.08509v1 PDF pp.9,19,22; arxiv-2111.09787v2 PDF p.12. -/
def meanEstimatorLaw {n input : ℕ} (C : MeanEstimatorCircuit n input)
    (data : Fin input → ℝ) (_valid : C.Admissible data) :
    Measure (Matrix (Fin n) (Fin n) ℝ) :=
  (C.executionLaw data).map Prod.fst

/-- Admissibility yields a probability law without conditioning or renormalization.
Source: arxiv-2510.08509v1 PDF p.9; arxiv-2111.09787v2 PDF p.12. -/
theorem meanEstimatorLaw_univ {n input : ℕ} (C : MeanEstimatorCircuit n input)
    (data : Fin input → ℝ) (valid : C.Admissible data) :
    meanEstimatorLaw C data valid Set.univ = 1 := by
  rw [meanEstimatorLaw, Measure.map_apply measurable_fst MeasurableSet.univ]
  simpa using valid.2

/-- Uniform syntax constructor indexed only by public dimensions, query budget and
confidence repetition budget. A supporting existence theorem quantifies this constructor
before matrices, confidence and hidden law; relates the public budgets to N and δ;
and concludes admissibility, accuracy and bounds on charged execution/construction.
This type itself asserts neither existence of a successful estimator nor efficient
source-model compilation. Our k counts sign interfaces, hence k+1 input matrices.
Source: arxiv-2510.08509v1 PDF pp.9,19,22; arxiv-2111.09787v2 PDF p.12. -/
abbrev MeanEstimatorConstructor :=
  (n k budget repetitions : ℕ) → MeanEstimatorCircuit n ((k+1)*(n*n))

/-- Zero-output candidate demonstrates execution, not estimator accuracy.
Source: arxiv-2510.08509v1 PDF pp.8–9. -/
example {n input r q : ℕ} (output : Fin (n*n) → Fin r) (data : Fin input → ℝ) :
    (MeanEstimatorCircuit.mk r q .halt output).executionLaw data =
      Measure.dirac (0, input+r+q+1+n*n) := by
  simp [MeanEstimatorCircuit.executionLaw, MeanEstimatorCircuit.constructionWork,
    MeanEstimatorProgram.nodes, MeanEstimatorProgram.run, Finsupp.sum_single_index] <;> rfl

example : (sketchValueCircuit 0 0).instructions = [] := by
  simp [sketchValueCircuit]

example : signPreparation 0 0 = 1 := by
  change hadamardN 0 = 1
  ext i j
  have h : i = j := Subsingleton.elim _ _
  subst h
  simp [signPreparation,hadamardN,dotBits]

end QAlgorithms.MatrixApprox


