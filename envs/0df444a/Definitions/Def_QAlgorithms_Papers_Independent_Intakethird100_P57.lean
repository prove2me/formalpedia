-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P57
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P57
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T06:07:20.22172+00:00
-- url     : https://prove2.me/theorems/c3a219b1-7894-4e5d-944c-278af9d4f428
-- title:
--   Definitions for Renormalization algorithm with graph enhancement
-- statement:
--   The objects the formalized statements of *Renormalization algorithm with graph enhancement* (arXiv:0802.1211) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Tensors`: Eq.(1), PDF pp.1–2: two arbitrary complex D-by-D site matrices.
--   - `traceMPS`: Eq.(1), PDF p.1: the periodic trace MPS, with matrices multiplied in chain order.
--   - `PhaseGraph`: PDF p.2: symmetric, zero-diagonal graph weights in [0,2π).
--   - `emptyPhaseGraph`: The absent graph (PDF p.2, following Eq.(2)).
--   - `productOp`: PDF p.2: tensor product of local matrices, on arbitrary finite sets of wires.
--   - `graphAngle`: PDF p.2: each unordered edge acts once, with the positive controlled phase.
--   - `graphOp`: PDF p.2: diagonal product of all controlled-phase gates.
--   - `enhance`: Eq.(2), PDF p.2: graph enhancement followed by the local rotations.
--   - `rage`: Eq.(2), PDF p.2: the RAGE raw vector.
--   - `normalizeRageVector`: PDF pp.2–4: normalize a raw nonzero vector before physical uses. At zero this total helper is zero; all physical theorems exclude that input.
--   - `productVec`: PDF p.2, Eq.(3), second line: an arbitrary product vector.
--   - `plusFactors`: PDF p.2: normalized plus factors.
--   - `productTensors`: PDF p.2: bond-one matrices for product vectors.
--   - `diagonalTensors`: Eq.(3), second line, PDF p.2: diagonal tensors for a finite sum of products. The coefficient is placed only at site zero; N≥1 is needed for this construction.
--   - `etaAmplitude`: Eq.(3), PDF p.2: η(d)=|0⟩+exp(d)|1⟩; there is no extra i in this exponent.
--   - `RageParameters`: PDF p.2: all admissible numerical input data; constraints do not remove stored entries.
--   - `DescriptionIndex`: PDF p.2: stored real coordinates: real/imaginary tensor entries, one weight per unordered pair, and real/imaginary entries of each 2-by-2 unitary.
--   - `describe`: PDF p.2: the explicit coordinate description, with the last Boolean selecting Im.
--   - `joinBits`: PDF p.2: glue retained and traced-out bit strings, including empty supports.
--   - `rawMarginal`: PDF p.2: actual partial trace of |v⟩⟨v|, without normalization.
--   - `rageMarginal`: PDF pp.2–4: normalized reduced density matrix, used only for nonzero v.
--   - `zMean`: PDF pp.1,3–4: Z expectation on a unit vector.
--   - `connectedZ`: PDF pp.1,3–4: connected two-point Z correlation on a unit vector.
--   - `firstBlock`: PDF p.2: the first L sites (meaningful also for L=0 and L=N).
--   - `nextSite`: PDF p.2: one cyclic increment. An existing index supplies positivity of N.
--   - `CyclicInvariant`: PDF p.2: exact cyclic invariance of a vector, without a global-phase quotient.
--   - `transferE`: PDF pp.2–3: E[k,a,b]=A[k,a] ⊗ conjugate(A[k,b]); conjugation is entrywise.
--   - `bitReal`: PDF pp.2–3: real bit indicator, to keep a-b signed.
--   - `transferT`: PDF pp.2–3: corrected transfer matrices. The outside phase uses the summed physical index t, not the unbound label in the printed B formula.
--   - `crossMarginal`: PDF pp.2–3: the cross-edge reduced kernel, contracted in chain order.
--   - `retainedOp`: PDF p.2: internal graph gates followed by the rotations on retained sites.
--   - `rayleighEnergy`: PDF p.3, Eq.(4): energy of a raw nonzero vector.
--   - `SiteCoordinates`: PDF p.3: both physical tensors at one site supply 2D² complex coordinates.
--   - `replaceSite`: PDF p.3: replace one site's two tensors, freezing every other entry.
--   - `siteMap`: PDF p.3: the constructed one-site physical linear map, by its coordinate columns.
--   - `rageSiteQuadratic`: PDF p.3: x†Mx, with a complex value until its real part is taken.
--   - `siteVector`: PDF p.3: physical vector from the constructed one-site map.
--   - `controlledPhaseAction`: PDF pp.3–4: apply a phase gate to a distinct pair, using an arbitrary complex label.
--   - `edgeBackground`: PDF p.3: undo one edge from the graph-enhanced vector before the final V layer.
--   - `edgePart`: PDF p.3: the P11 or complementary component of the frozen edge background.
--   - `edgeTrial`: PDF p.3: edge-coordinate trial vector, retaining the entire two-site phase gate.
--   - `edgeCoefficients`: PDF p.3: single-edge energy coefficients, with V undone from H as printed.
--   - `minimizingPhase`: PDF p.3: a minimizing unit-modulus phase for c0+2Re(c1 z).
--   - `SingleEdgeEnergyLaw`: PDF p.3: the single-edge energy form and its constrained minimum. This is not a minimization over unconstrained complex z, and gives no joint global phase optimum.
--   - `wrapAngle`: PDF p.4: reduce any real angle to [0,2π), including negative angles.
--   - `updatedWeights`: PDF p.4: update both symmetric entries, leaving every other pair fixed.
--   - `overlapObjective`: PDF p.4, Eq.(5): normalized squared overlap with a normalized target.
--   - `localGate`: PDF p.4: put one single-qubit unitary at the selected wire.
--   - `overlapCoefficients`: PDF p.4: squared overlap coefficients for the incident-edge coordinate.
--   - `oppositeWeights`: PDF p.2, (i)–(ii): weights of a circulant opposite-site matching on 2L sites.
--   - `cyclicBlock`: PDF p.2, (ii): contiguous blocks on a cyclic chain, including wrapping blocks.
--   - `mpsTangent`: PDF p.3: derivative of the trace product, obtained by inserting one tensor derivative.
--   - `localTangent`: PDF p.3: derivative of the tensor product of local matrices.
--   - `rawTangent`: PDF p.3: explicit differentiated finite tensor/phase product. The ambient formula extends the unitary charts smoothly; no defective unrestricted real-Pauli chart is used.
--   - `ScalarInstruction`: PDF pp.2–3 and p.4 Extensions: ideal scalar instructions, with no matrix-operation primitive. A productCall is reserved for the explicitly supplied base contraction evaluator.
--   - `ScalarInstruction.eval`: PDF pp.2–3: one instruction's exact semantics. Division has a checked denominator.
--   - `ScalarProgram`: PDF pp.2–3: a straight-line scalar program. All registers initially contain zero; each instruction writes the next register. Work includes reads and output-factor formation.
--   - `ScalarProgram.execute`: PDF pp.2–3: execute the instruction list; undefined division fails explicitly.
--   - `ScalarProgram.calls`: PDF p.4: number of calls to the base product-operator evaluator.
--   - `ScalarProgram.work`: PDF pp.2–4: scalar work, charging an oracle call for formation of all 4N factors, in addition to a supplied per-call base-evaluation budget B.
--   - `ContractionInput`: PDF pp.2–3: typed scalar inputs for local contraction. O may be non-Hermitian.
--   - `contractionData`: PDF pp.2–3: numerical input values; no oracle supplies any desired marginal.
--   - `MarginalProgram`: PDF pp.2–3: program outputs include every partial transfer product, so the theorem requires the transfer construction itself, not just an unrelated scalar output.
--   - `MarginalProgram.Correct`: PDF pp.2–3: a program's full transfer-contraction specification. Partial products are in chain order. Both norm division and the final local conjugation must be executed.
--   - `supportedOp`: PDF p.4: embed an operator supported on S, with the identity on its complement.
--   - `QubitCliffordGate`: PDF p.4: a unitary Clifford circuit, with no measurements or postselection. H, S and controlled-X generate the qubit Clifford circuits.
--   - `hadamardMatrix`: PDF p.4: the elementary Hadamard matrix in Boolean basis order 0,1.
--   - `QubitCliffordGate.matrix`: PDF p.4: exact gate action of the three Clifford generators.
--   - `cliffordMatrix`: PDF p.4: circuit order is chronological, so the first gate acts first.
--   - `EnhancementInput`: PDF p.4 Extensions: enhancement inputs, excluding the base state's product evaluator.
--   - `enhancementData`: PDF p.4 Extensions: input data read by the conditional reduction.
--   - `EnhancementProgram`: PDF p.4 Extensions: output register of a product-evaluator reduction.
--   - `ExactProductEvaluator`: PDF p.4 Extensions: exact product expectations, for all complex local matrices. This interface deliberately includes non-Hermitian factors and is uniform in those factors.
--   - `localTermHamiltonian`: PDF pp.2–3: a supplied sum of local Hamiltonian terms. Supports may be long-range.
--   - `EdgeInput`: PDF p.3: scalar inputs for evaluating one-edge energy coefficients term by term.
--   - `edgeData`: PDF p.3: edge coefficient input values, with no precomputed coefficient oracle.
--   - `EdgeProgram`: PDF p.3: executable output registers for c0,c1,Z and the supplied total energy.
-- source:
--   Renormalization algorithm with graph enhancement, arXiv:0802.1211v1, https://arxiv.org/abs/0802.1211v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Ensemble

/-!
Statements from Hübener et al., arXiv:0802.1211v1, PDF pp.1–4.
Paper-local definitions use the periodic trace convention of Eq.(1), not open-boundary MPS.
All algebraic vectors are raw; every physical expectation, marginal and entropy is normalized.
Compilation is pending the batch mechanical handoff.
-/

noncomputable section

open scoped ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Intakethird100.P57

attribute [local instance] Classical.propDecidable

/-- Eq.(1), PDF pp.1–2: two arbitrary complex D-by-D site matrices. -/
abbrev Tensors (N D : ℕ) := Fin N → Bool → Matrix (Fin D) (Fin D) ℂ

/-- Eq.(1), PDF p.1: the periodic trace MPS, with matrices multiplied in chain order. -/
def traceMPS {N D : ℕ} (A : Tensors N D) : EuclideanSpace ℂ (Qubits N) :=
  WithLp.toLp 2 fun b => ((List.ofFn fun k => A k (b k)).prod).trace

/-- PDF p.2: symmetric, zero-diagonal graph weights in [0,2π). -/
structure PhaseGraph (N : ℕ) where
  weight : Fin N → Fin N → ℝ
  symmetric : ∀ i j, weight i j = weight j i
  diagonal : ∀ i, weight i i = 0
  nonnegative : ∀ i j, 0 ≤ weight i j
  bounded : ∀ i j, weight i j < 2 * Real.pi

/-- The absent graph (PDF p.2, following Eq.(2)). -/
def emptyPhaseGraph (N : ℕ) : PhaseGraph N where
  weight := fun _ _ => 0
  symmetric := by intros; rfl
  diagonal := by intros; rfl
  nonnegative := by intros; exact le_refl 0
  bounded := by intros; positivity

/-- PDF p.2: tensor product of local matrices, on arbitrary finite sets of wires. -/
def productOp {ι : Type*} [Fintype ι] (V : ι → Matrix Bool Bool ℂ) :
    Matrix (ι → Bool) (ι → Bool) ℂ :=
  Matrix.of fun a b => ∏ k, V k (a k) (b k)

/-- PDF p.2: each unordered edge acts once, with the positive controlled phase. -/
def graphAngle {ι : Type*} [Fintype ι] [LinearOrder ι]
    (w : ι → ι → ℝ) (b : ι → Bool) : ℝ :=
  ∑ i, ∑ j, if i < j ∧ b i = true ∧ b j = true then w i j else 0

/-- PDF p.2: diagonal product of all controlled-phase gates. -/
def graphOp {ι : Type*} [Fintype ι] [LinearOrder ι] (w : ι → ι → ℝ) :
    Matrix (ι → Bool) (ι → Bool) ℂ :=
  Matrix.diagonal fun b => Complex.exp (Complex.I * (graphAngle w b : ℂ))

/-- Eq.(2), PDF p.2: graph enhancement followed by the local rotations. -/
def enhance {N : ℕ} (G : PhaseGraph N) (V : Fin N → Matrix.unitaryGroup Bool ℂ)
    (v : EuclideanSpace ℂ (Qubits N)) : EuclideanSpace ℂ (Qubits N) :=
  act (productOp fun k => (V k : Matrix Bool Bool ℂ)) (act (graphOp G.weight) v)

/-- Eq.(2), PDF p.2: the RAGE raw vector. -/
def rage {N D : ℕ} (A : Tensors N D) (G : PhaseGraph N)
    (V : Fin N → Matrix.unitaryGroup Bool ℂ) : EuclideanSpace ℂ (Qubits N) :=
  enhance G V (traceMPS A)

/-- PDF pp.2–4: normalize a raw nonzero vector before physical uses.
At zero this total helper is zero; all physical theorems exclude that input. -/
def normalizeRageVector {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) : EuclideanSpace ℂ ι :=
  ((‖v‖ : ℂ)⁻¹) • v

/-- PDF p.2, Eq.(3), second line: an arbitrary product vector. -/
def productVec {N : ℕ} (r : Fin N → Bool → ℂ) : EuclideanSpace ℂ (Qubits N) :=
  WithLp.toLp 2 fun b => ∏ k, r k (b k)

/-- PDF p.2: normalized plus factors. -/
def plusFactors (N : ℕ) : Fin N → Bool → ℂ :=
  fun _ _ => (Real.sqrt 2 : ℂ)⁻¹

/-- PDF p.2: bond-one matrices for product vectors. -/
def productTensors {N : ℕ} (r : Fin N → Bool → ℂ) : Tensors N 1 :=
  fun k b => Matrix.of fun _ _ => r k b

/-- Eq.(3), second line, PDF p.2: diagonal tensors for a finite sum of products.
The coefficient is placed only at site zero; N≥1 is needed for this construction. -/
def diagonalTensors {N m : ℕ} (c : Fin m → ℂ)
    (r : Fin m → Fin N → Bool → ℂ) : Tensors N m :=
  fun k b => Matrix.diagonal fun t => (if k.val = 0 then c t else 1) * r t k b

/-- Eq.(3), PDF p.2: η(d)=|0⟩+exp(d)|1⟩; there is no extra i in this exponent. -/
def etaAmplitude (d : ℂ) (b : Bool) : ℂ := if b then Complex.exp d else 1

/-- Sanity: no spurious phase on a basis string with no occupied pair. -/
example (G : PhaseGraph 1) (b : Qubits 1) : graphAngle G.weight b = 0 := by
  simp [graphAngle]

/-- Sanity: the zero raw vector is not accidentally turned into a physical state. -/
example {ι : Type*} [Fintype ι] : normalizeRageVector (0 : EuclideanSpace ℂ ι) = 0 := by
  simp [normalizeRageVector]

/-- Sanity: the product factors in Eq.(3) have the stated amplitudes. -/
example (d : ℂ) : etaAmplitude d false = 1 ∧ etaAmplitude d true = Complex.exp d := ⟨rfl, rfl⟩

/-- PDF p.2: all admissible numerical input data; constraints do not remove stored entries. -/
structure RageParameters (N D : ℕ) where
  tensors : Tensors N D
  graph : PhaseGraph N
  rotations : Fin N → Matrix.unitaryGroup Bool ℂ

/-- PDF p.2: stored real coordinates: real/imaginary tensor entries, one weight per
unordered pair, and real/imaginary entries of each 2-by-2 unitary. -/
abbrev DescriptionIndex (N D : ℕ) :=
  (Fin N × Bool × Fin D × Fin D × Bool) ⊕
    ({p : Fin N × Fin N // p.1 < p.2} ⊕ (Fin N × Bool × Bool × Bool))

/-- PDF p.2: the explicit coordinate description, with the last Boolean selecting Im. -/
def describe {N D : ℕ} (p : RageParameters N D) : DescriptionIndex N D → ℝ
  | .inl (k,b,i,j,part) => if part then (p.tensors k b i j).im else (p.tensors k b i j).re
  | .inr (.inl e) => p.graph.weight e.val.1 e.val.2
  | .inr (.inr (k,b,c,part)) =>
      if part then ((p.rotations k : Matrix Bool Bool ℂ) b c).im
      else ((p.rotations k : Matrix Bool Bool ℂ) b c).re

/-- PDF p.2: glue retained and traced-out bit strings, including empty supports. -/
def joinBits {N : ℕ} (S : Finset (Fin N)) (a : S → Bool)
    (e : {k : Fin N // k ∉ S} → Bool) : Qubits N :=
  fun k => if h : k ∈ S then a ⟨k,h⟩ else e ⟨k,h⟩

/-- PDF p.2: actual partial trace of |v⟩⟨v|, without normalization. -/
def rawMarginal {N : ℕ} (v : EuclideanSpace ℂ (Qubits N)) (S : Finset (Fin N)) :
    Matrix (S → Bool) (S → Bool) ℂ :=
  Matrix.of fun a b => ∑ e : {k : Fin N // k ∉ S} → Bool,
    v (joinBits S a e) * conj (v (joinBits S b e))

/-- PDF pp.2–4: normalized reduced density matrix, used only for nonzero v. -/
def rageMarginal {N : ℕ} (v : EuclideanSpace ℂ (Qubits N)) (S : Finset (Fin N)) :
    Matrix (S → Bool) (S → Bool) ℂ :=
  (((‖v‖ ^ 2 : ℝ) : ℂ)⁻¹) • rawMarginal v S

/-- PDF pp.1,3–4: Z expectation on a unit vector. -/
def zMean {N : ℕ} (v : EuclideanSpace ℂ (Qubits N)) (i : Fin N) : ℝ :=
  ∑ b, (if b i then -1 else 1) * Complex.normSq (v b)

/-- PDF pp.1,3–4: connected two-point Z correlation on a unit vector. -/
def connectedZ {N : ℕ} (v : EuclideanSpace ℂ (Qubits N)) (i j : Fin N) : ℝ :=
  (∑ b, (if b i then -1 else 1) * (if b j then -1 else 1) * Complex.normSq (v b)) -
    zMean v i * zMean v j

/-- PDF p.2: the first L sites (meaningful also for L=0 and L=N). -/
def firstBlock (N L : ℕ) : Finset (Fin N) := Finset.univ.filter fun i => i.val < L

/-- PDF p.2: one cyclic increment. An existing index supplies positivity of N. -/
def nextSite {N : ℕ} (i : Fin N) : Fin N :=
  ⟨(i.val + 1) % N, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

/-- PDF p.2: exact cyclic invariance of a vector, without a global-phase quotient. -/
def CyclicInvariant {N : ℕ} (v : EuclideanSpace ℂ (Qubits N)) : Prop :=
  ∀ b, v (fun k => b (nextSite k)) = v b

/-- PDF pp.2–3: E[k,a,b]=A[k,a] ⊗ conjugate(A[k,b]); conjugation is entrywise. -/
def transferE {N D : ℕ} (A : Tensors N D) (k : Fin N) (a b : Bool) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  Matrix.kronecker (A k a) (Matrix.of fun i j => conj (A k b i j))

/-- PDF pp.2–3: real bit indicator, to keep a-b signed. -/
def bitReal (b : Bool) : ℝ := if b then 1 else 0

/-- PDF pp.2–3: corrected transfer matrices. The outside phase uses the summed physical
index t, not the unbound label in the printed B formula. -/
def transferT {N D : ℕ} (A : Tensors N D) (G : PhaseGraph N) (S : Finset (Fin N))
    (a b : S → Bool) (k : Fin N) : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  if hk : k ∈ S then transferE A k (a ⟨k,hk⟩) (b ⟨k,hk⟩)
  else ∑ t : Bool,
    Complex.exp (Complex.I * ((bitReal t *
      ∑ j : S, G.weight j.val k * (bitReal (a j) - bitReal (b j))) : ℂ)) •
      transferE A k t t

/-- PDF pp.2–3: the cross-edge reduced kernel, contracted in chain order. -/
def crossMarginal {N D : ℕ} (A : Tensors N D) (G : PhaseGraph N) (S : Finset (Fin N)) :
    Matrix (S → Bool) (S → Bool) ℂ :=
  Matrix.of fun a b => ((List.ofFn fun k => transferT A G S a b k).prod).trace

/-- PDF p.2: internal graph gates followed by the rotations on retained sites. -/
def retainedOp {N : ℕ} (G : PhaseGraph N) (V : Fin N → Matrix.unitaryGroup Bool ℂ)
    (S : Finset (Fin N)) : Matrix (S → Bool) (S → Bool) ℂ :=
  productOp (fun k : S => (V k.val : Matrix Bool Bool ℂ)) *
    graphOp (fun i j : S => G.weight i.val j.val)

/-- Sanity: no natural-number subtraction enters the phase difference. -/
example : bitReal false - bitReal true = -1 := by norm_num [bitReal]

/-- PDF p.3, Eq.(4): energy of a raw nonzero vector. -/
def rayleighEnergy {N : ℕ} (H : Matrix (Qubits N) (Qubits N) ℂ)
    (v : EuclideanSpace ℂ (Qubits N)) : ℝ :=
  (inner ℂ v (act H v)).re / ‖v‖ ^ 2

/-- PDF p.3: both physical tensors at one site supply 2D² complex coordinates. -/
abbrev SiteCoordinates (D : ℕ) := Bool × Fin D × Fin D

/-- PDF p.3: replace one site's two tensors, freezing every other entry. -/
def replaceSite {N D : ℕ} (A : Tensors N D) (k : Fin N)
    (x : SiteCoordinates D → ℂ) : Tensors N D :=
  fun j b => if j = k then Matrix.of fun i l => x (b,i,l) else A j b

/-- PDF p.3: the constructed one-site physical linear map, by its coordinate columns. -/
def siteMap {N D : ℕ} (A : Tensors N D) (G : PhaseGraph N)
    (V : Fin N → Matrix.unitaryGroup Bool ℂ) (k : Fin N) :
    Matrix (Qubits N) (SiteCoordinates D) ℂ :=
  Matrix.of fun b c => rage (replaceSite A k (fun e => if e = c then 1 else 0)) G V b

/-- PDF p.3: x†Mx, with a complex value until its real part is taken. -/
def rageSiteQuadratic {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (x : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, conj (x i) * M i j * x j

/-- PDF p.3: physical vector from the constructed one-site map. -/
def siteVector {N D : ℕ} (L : Matrix (Qubits N) (SiteCoordinates D) ℂ)
    (x : SiteCoordinates D → ℂ) : EuclideanSpace ℂ (Qubits N) :=
  WithLp.toLp 2 (L.mulVec x)

/-- PDF pp.3–4: apply a phase gate to a distinct pair, using an arbitrary complex label. -/
def controlledPhaseAction {N : ℕ} (j k : Fin N) (z : ℂ)
    (v : EuclideanSpace ℂ (Qubits N)) : EuclideanSpace ℂ (Qubits N) :=
  WithLp.toLp 2 fun b => (if b j = true ∧ b k = true then z else 1) * v b

/-- PDF p.3: undo one edge from the graph-enhanced vector before the final V layer. -/
def edgeBackground {N D : ℕ} (A : Tensors N D) (G : PhaseGraph N) (j k : Fin N) :
    EuclideanSpace ℂ (Qubits N) :=
  controlledPhaseAction j k (Complex.exp (-Complex.I * (G.weight j k : ℂ)))
    (act (graphOp G.weight) (traceMPS A))

/-- PDF p.3: the P11 or complementary component of the frozen edge background. -/
def edgePart {N : ℕ} (v : EuclideanSpace ℂ (Qubits N)) (j k : Fin N) (on : Bool) :
    EuclideanSpace ℂ (Qubits N) :=
  WithLp.toLp 2 fun b => if (b j && b k) = on then v b else 0

/-- PDF p.3: edge-coordinate trial vector, retaining the entire two-site phase gate. -/
def edgeTrial {N D : ℕ} (A : Tensors N D) (G : PhaseGraph N)
    (V : Fin N → Matrix.unitaryGroup Bool ℂ) (j k : Fin N) (z : ℂ) :
    EuclideanSpace ℂ (Qubits N) :=
  act (productOp fun q => (V q : Matrix Bool Bool ℂ))
    (controlledPhaseAction j k z (edgeBackground A G j k))

/-- PDF p.3: single-edge energy coefficients, with V undone from H as printed. -/
def edgeCoefficients {N D : ℕ} (A : Tensors N D) (G : PhaseGraph N)
    (V : Fin N → Matrix.unitaryGroup Bool ℂ) (j k : Fin N)
    (H : Matrix (Qubits N) (Qubits N) ℂ) : ℝ × ℂ :=
  let W := productOp fun q => (V q : Matrix Bool Bool ℂ)
  let HV := W.conjTranspose * H * W
  let u := edgePart (edgeBackground A G j k) j k false
  let v := edgePart (edgeBackground A G j k) j k true
  ((inner ℂ u (act HV u)).re + (inner ℂ v (act HV v)).re,
    inner ℂ u (act HV v))

/-- PDF p.3: a minimizing unit-modulus phase for c0+2Re(c1 z). -/
def minimizingPhase (c : ℂ) : ℂ := if c = 0 then 1 else -conj c / (‖c‖ : ℂ)

/-- PDF p.3: the single-edge energy form and its constrained minimum. This is not a
minimization over unconstrained complex z, and gives no joint global phase optimum. -/
def SingleEdgeEnergyLaw {N D : ℕ} (hN : 1 ≤ N) (hD : 1 ≤ D)
    (A : Tensors N D) (G : PhaseGraph N) (V : Fin N → Matrix.unitaryGroup Bool ℂ)
    (hv : traceMPS A ≠ 0) (j k : Fin N) (hjk : j ≠ k)
    (H : Matrix (Qubits N) (Qubits N) ℂ) (hH : H.IsHermitian) : Prop :=
    let c := edgeCoefficients A G V j k H
    let Z := ‖traceMPS A‖ ^ 2
    (∀ z : ℂ, ‖z‖ = 1 → ‖edgeTrial A G V j k z‖ ^ 2 = Z ∧
      rayleighEnergy H (edgeTrial A G V j k z) = (c.1 + 2 * (c.2 * z).re) / Z) ∧
    ‖minimizingPhase c.2‖ = 1 ∧
    (∀ z : ℂ, ‖z‖ = 1 → rayleighEnergy H (edgeTrial A G V j k (minimizingPhase c.2)) ≤
      rayleighEnergy H (edgeTrial A G V j k z)) ∧
    (c.2 = 0 → ∀ z : ℂ, ‖z‖ = 1 → rayleighEnergy H (edgeTrial A G V j k z) = c.1 / Z)

/-- PDF p.4: reduce any real angle to [0,2π), including negative angles. -/
def wrapAngle (theta : ℝ) : ℝ :=
  theta - (2 * Real.pi) * (Int.floor (theta / (2 * Real.pi)) : ℝ)

/-- PDF p.4: update both symmetric entries, leaving every other pair fixed. -/
def updatedWeights {N : ℕ} (G : PhaseGraph N) (j k : Fin N) (theta : ℝ) : Fin N → Fin N → ℝ :=
  fun a b => if (a = j ∧ b = k) ∨ (a = k ∧ b = j)
    then wrapAngle (G.weight j k + theta) else G.weight a b

/-- PDF p.4, Eq.(5): normalized squared overlap with a normalized target. -/
def overlapObjective {N : ℕ} (v chi : EuclideanSpace ℂ (Qubits N)) : ℝ :=
  Complex.normSq (inner ℂ v chi) / ‖v‖ ^ 2

/-- PDF p.4: put one single-qubit unitary at the selected wire. -/
def localGate {N : ℕ} (q : Fin N) (U : Matrix.unitaryGroup Bool ℂ) :
    Matrix (Qubits N) (Qubits N) ℂ :=
  productOp fun k => if k = q then (U : Matrix Bool Bool ℂ) else 1

/-- PDF p.4: squared overlap coefficients for the incident-edge coordinate. -/
def overlapCoefficients {N D : ℕ} (A : Tensors N D) (G : PhaseGraph N) (j k : Fin N)
    (chi : EuclideanSpace ℂ (Qubits N)) : ℝ × ℂ :=
  let u := edgePart (edgeBackground A G j k) j k false
  let v := edgePart (edgeBackground A G j k) j k true
  let a := inner ℂ u chi
  let b := inner ℂ v chi
  (Complex.normSq a + Complex.normSq b, a * conj b)

/-- PDF p.2, (i)–(ii): weights of a circulant opposite-site matching on 2L sites. -/
def oppositeWeights (L : ℕ) : Fin (2 * L) → Fin (2 * L) → ℝ :=
  fun i j => if i ≠ j ∧ (i.val + L) % (2 * L) = j.val then Real.pi else 0

/-- PDF p.2, (ii): contiguous blocks on a cyclic chain, including wrapping blocks. -/
def cyclicBlock (N : ℕ) (start : Fin N) (ell : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun i => ∃ t : ℕ, t < ell ∧ i.val = (start.val + t) % N

/-- PDF p.3: derivative of the trace product, obtained by inserting one tensor derivative. -/
def mpsTangent {N D : ℕ} (A Adot : Tensors N D) : EuclideanSpace ℂ (Qubits N) :=
  WithLp.toLp 2 fun b => ∑ k : Fin N,
    ((List.ofFn fun l => if l = k then Adot l (b l) else A l (b l)).prod).trace

/-- PDF p.3: derivative of the tensor product of local matrices. -/
def localTangent {N : ℕ} (V Vdot : Fin N → Matrix Bool Bool ℂ) :
    Matrix (Qubits N) (Qubits N) ℂ :=
  Matrix.of fun a b => ∑ k : Fin N,
    ∏ l : Fin N, if l = k then Vdot l (a l) (b l) else V l (a l) (b l)

/-- PDF p.3: explicit differentiated finite tensor/phase product. The ambient formula
extends the unitary charts smoothly; no defective unrestricted real-Pauli chart is used. -/
def rawTangent {N D : ℕ} (A Adot : Tensors N D)
    (w wdot : Fin N → Fin N → ℝ) (V Vdot : Fin N → Matrix Bool Bool ℂ) :
    EuclideanSpace ℂ (Qubits N) :=
  act (localTangent V Vdot) (act (graphOp w) (traceMPS A)) +
    act (productOp V) (WithLp.toLp 2 fun b =>
      Complex.exp (Complex.I * (graphAngle w b : ℂ)) *
        (mpsTangent A Adot b + Complex.I * (graphAngle wdot b : ℂ) * traceMPS A b))

/-- PDF pp.2–3 and p.4 Extensions: ideal scalar instructions, with no matrix-operation
primitive. A productCall is reserved for the explicitly supplied base contraction evaluator. -/
inductive ScalarInstruction (N : ℕ) (Input : Type*) where
  | constant (c : ℂ)
  | read (i : Input)
  | add (a b : ℕ)
  | mul (a b : ℕ)
  | divide (a b : ℕ)
  | conjugate (a : ℕ)
  | phase (a : ℕ)
  | productCall (factors : Fin N → Bool → Bool → ℕ)

/-- PDF pp.2–3: one instruction's exact semantics. Division has a checked denominator. -/
def ScalarInstruction.eval {N : ℕ} {Input : Type*}
    (data : Input → ℂ) (base : (Fin N → Matrix Bool Bool ℂ) → ℂ)
    (mem : ℕ → ℂ) : ScalarInstruction N Input → Option ℂ
  | .constant c => some c
  | .read i => some (data i)
  | .add a b => some (mem a + mem b)
  | .mul a b => some (mem a * mem b)
  | .divide a b => if mem b = 0 then none else some (mem a / mem b)
  | .conjugate a => some (conj (mem a))
  | .phase a => some (Complex.exp (Complex.I * (mem a).re))
  | .productCall factors => some (base (fun k => Matrix.of fun a b => mem (factors k a b)))

/-- PDF pp.2–3: a straight-line scalar program. All registers initially contain zero;
each instruction writes the next register. Work includes reads and output-factor formation. -/
structure ScalarProgram (N : ℕ) (Input : Type*) where
  code : List (ScalarInstruction N Input)

/-- PDF pp.2–3: execute the instruction list; undefined division fails explicitly. -/
def ScalarProgram.execute {N : ℕ} {Input : Type*} (p : ScalarProgram N Input)
    (data : Input → ℂ) (base : (Fin N → Matrix Bool Bool ℂ) → ℂ) : Option (ℕ → ℂ) :=
  ((p.code.foldl (fun (st : Option (ℕ × (ℕ → ℂ))) op =>
    st.bind fun s => (op.eval data base s.2).map fun v =>
      (s.1 + 1, Function.update s.2 s.1 v)) (some (0,fun _ => 0))).map Prod.snd)

/-- PDF p.4: number of calls to the base product-operator evaluator. -/
def ScalarProgram.calls {N : ℕ} {Input : Type*} (p : ScalarProgram N Input) : ℕ :=
  p.code.countP fun op => match op with | .productCall _ => true | _ => false

/-- PDF pp.2–4: scalar work, charging an oracle call for formation of all 4N factors,
in addition to a supplied per-call base-evaluation budget B. -/
def ScalarProgram.work {N : ℕ} {Input : Type*} (p : ScalarProgram N Input) (B : ℕ := 0) : ℕ :=
  (p.code.map fun op => match op with
    | .productCall _ => 4 * N + 1 + B
    | _ => 1).sum

/-- Sanity: a real zero denominator is never silently assigned a scalar answer. -/
example {N : ℕ} {Input : Type*} (data : Input → ℂ)
    (base : (Fin N → Matrix Bool Bool ℂ) → ℂ) :
    (ScalarInstruction.divide 0 0 : ScalarInstruction N Input).eval data base (fun _ => 0) = none := by
  simp [ScalarInstruction.eval]

/-- Sanity: the instruction list is charged, including an input read. -/
example {N : ℕ} {Input : Type*} (i : Input) :
    (ScalarProgram.mk [.read i] : ScalarProgram N Input).work 0 = 1 := rfl

/-- PDF pp.2–3: typed scalar inputs for local contraction. O may be non-Hermitian. -/
inductive ContractionInput (N D : ℕ) (S : Finset (Fin N)) where
  | tensor (k : Fin N) (b : Bool) (i j : Fin D)
  | phase (i j : Fin N)
  | rotation (k : Fin N) (a b : Bool)
  | observable (a b : S → Bool)

/-- PDF pp.2–3: numerical input values; no oracle supplies any desired marginal. -/
def contractionData {N D : ℕ} {S : Finset (Fin N)} (A : Tensors N D) (G : PhaseGraph N)
    (V : Fin N → Matrix.unitaryGroup Bool ℂ) (O : Matrix (S → Bool) (S → Bool) ℂ) :
    ContractionInput N D S → ℂ
  | .tensor k b i j => A k b i j
  | .phase i j => (G.weight i j : ℂ)
  | .rotation k a b => (V k : Matrix Bool Bool ℂ) a b
  | .observable a b => O a b

/-- PDF pp.2–3: program outputs include every partial transfer product, so the theorem
requires the transfer construction itself, not just an unrelated scalar output. -/
structure MarginalProgram (N D : ℕ) (S : Finset (Fin N)) where
  scalar : ScalarProgram N (ContractionInput N D S)
  stage : (S → Bool) → (S → Bool) → Fin (N + 1) →
    (Fin D × Fin D) → (Fin D × Fin D) → ℕ
  cross : (S → Bool) → (S → Bool) → ℕ
  norm : ℕ
  entry : (S → Bool) → (S → Bool) → ℕ
  expectation : ℕ

/-- PDF pp.2–3: a program's full transfer-contraction specification. Partial products
are in chain order. Both norm division and the final local conjugation must be executed. -/
def MarginalProgram.Correct {N D : ℕ} {S : Finset (Fin N)} (p : MarginalProgram N D S)
    (A : Tensors N D) (G : PhaseGraph N) (V : Fin N → Matrix.unitaryGroup Bool ℂ)
    (O : Matrix (S → Bool) (S → Bool) ℂ) : Prop :=
  ∃ mem : ℕ → ℂ,
    p.scalar.execute (contractionData A G V O) (fun _ => 0) = some mem ∧
    mem p.norm = (‖traceMPS A‖ ^ 2 : ℝ) ∧
    (∀ a b t i j, p.stage a b t i j < p.scalar.code.length ∧
      mem (p.stage a b t i j) =
        (((List.ofFn fun k => transferT A G S a b k).take t.val).prod) i j) ∧
    (∀ a b, p.cross a b < p.scalar.code.length ∧
      mem (p.cross a b) = crossMarginal A G S a b) ∧
    (∀ a b, p.entry a b < p.scalar.code.length ∧
      mem (p.entry a b) = rageMarginal (rage A G V) S a b) ∧
    p.norm < p.scalar.code.length ∧ p.expectation < p.scalar.code.length ∧
    mem p.expectation = (O * rageMarginal (rage A G V) S).trace

/-- PDF p.4: embed an operator supported on S, with the identity on its complement. -/
def supportedOp {N : ℕ} (S : Finset (Fin N)) (O : Matrix (S → Bool) (S → Bool) ℂ) :
    Matrix (Qubits N) (Qubits N) ℂ :=
  Matrix.of fun a b => if ∀ k : Fin N, k ∉ S → a k = b k
    then O (fun k => a k.val) (fun k => b k.val) else 0

/-- PDF p.4: a unitary Clifford circuit, with no measurements or postselection.
H, S and controlled-X generate the qubit Clifford circuits. -/
inductive QubitCliffordGate (N : ℕ) where
  | hadamard (q : Fin N)
  | phase (q : Fin N)
  | controlledX (control target : Fin N) (distinct : control ≠ target)

/-- PDF p.4: the elementary Hadamard matrix in Boolean basis order 0,1. -/
def hadamardMatrix : Matrix Bool Bool ℂ :=
  Matrix.of fun a b => if a = true ∧ b = true
    then -(Real.sqrt 2 : ℂ)⁻¹ else (Real.sqrt 2 : ℂ)⁻¹

/-- PDF p.4: exact gate action of the three Clifford generators. -/
def QubitCliffordGate.matrix {N : ℕ} : QubitCliffordGate N → Matrix (Qubits N) (Qubits N) ℂ
  | .hadamard q => productOp fun k => if k = q then hadamardMatrix else 1
  | .phase q => productOp fun k => if k = q then
      Matrix.diagonal (fun b : Bool => if b then Complex.I else 1) else 1
  | .controlledX j k _ => Matrix.of fun a b =>
      if a = (fun q => if q = k then Bool.xor (b k) (b j) else b q) then 1 else 0

/-- PDF p.4: circuit order is chronological, so the first gate acts first. -/
def cliffordMatrix {N : ℕ} (circuit : List (QubitCliffordGate N)) : Matrix (Qubits N) (Qubits N) ℂ :=
  (circuit.map QubitCliffordGate.matrix).reverse.prod

/-- Sanity: the empty Clifford circuit acts as the identity. -/
example (N : ℕ) : cliffordMatrix ([] : List (QubitCliffordGate N)) = 1 := rfl

/-- PDF p.4 Extensions: enhancement inputs, excluding the base state's product evaluator. -/
inductive EnhancementInput (N : ℕ) (S : Finset (Fin N)) where
  | phase (i j : Fin N)
  | rotation (k : Fin N) (a b : Bool)
  | observable (a b : S → Bool)

/-- PDF p.4 Extensions: input data read by the conditional reduction. -/
def enhancementData {N : ℕ} {S : Finset (Fin N)} (G : PhaseGraph N)
    (V : Fin N → Matrix.unitaryGroup Bool ℂ) (O : Matrix (S → Bool) (S → Bool) ℂ) :
    EnhancementInput N S → ℂ
  | .phase i j => (G.weight i j : ℂ)
  | .rotation k a b => (V k : Matrix Bool Bool ℂ) a b
  | .observable a b => O a b

/-- PDF p.4 Extensions: output register of a product-evaluator reduction. -/
structure EnhancementProgram (N : ℕ) (S : Finset (Fin N)) where
  scalar : ScalarProgram N (EnhancementInput N S)
  output : ℕ

/-- PDF p.4 Extensions: exact product expectations, for all complex local matrices.
This interface deliberately includes non-Hermitian factors and is uniform in those factors. -/
def ExactProductEvaluator {N : ℕ} (psi : EuclideanSpace ℂ (Qubits N))
    (base : (Fin N → Matrix Bool Bool ℂ) → ℂ) : Prop :=
  ∀ factors, base factors = inner ℂ psi (act (productOp factors) psi)

/-- PDF pp.2–3: a supplied sum of local Hamiltonian terms. Supports may be long-range. -/
def localTermHamiltonian {N m : ℕ} (supports : Fin m → Finset (Fin N))
    (terms : (r : Fin m) → Matrix (supports r → Bool) (supports r → Bool) ℂ) :
    Matrix (Qubits N) (Qubits N) ℂ :=
  ∑ r, supportedOp (supports r) (terms r)

/-- PDF p.3: scalar inputs for evaluating one-edge energy coefficients term by term. -/
inductive EdgeInput (N D m : ℕ) (supports : Fin m → Finset (Fin N)) where
  | tensor (k : Fin N) (b : Bool) (i j : Fin D)
  | phase (i j : Fin N)
  | rotation (k : Fin N) (a b : Bool)
  | term (r : Fin m) (a b : supports r → Bool)

/-- PDF p.3: edge coefficient input values, with no precomputed coefficient oracle. -/
def edgeData {N D m : ℕ} {supports : Fin m → Finset (Fin N)}
    (A : Tensors N D) (G : PhaseGraph N) (V : Fin N → Matrix.unitaryGroup Bool ℂ)
    (terms : (r : Fin m) → Matrix (supports r → Bool) (supports r → Bool) ℂ) :
    EdgeInput N D m supports → ℂ
  | .tensor k b i j => A k b i j
  | .phase i j => (G.weight i j : ℂ)
  | .rotation k a b => (V k : Matrix Bool Bool ℂ) a b
  | .term r a b => terms r a b

/-- PDF p.3: executable output registers for c0,c1,Z and the supplied total energy. -/
structure EdgeProgram (N D m : ℕ) (supports : Fin m → Finset (Fin N)) where
  scalar : ScalarProgram N (EdgeInput N D m supports)
  constantCoefficient : ℕ
  phaseCoefficient : ℕ
  norm : ℕ
  totalEnergy : ℕ

end QAlgorithms.Papers.Independent.Intakethird100.P57


