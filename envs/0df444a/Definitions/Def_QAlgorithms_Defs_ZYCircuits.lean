-- Prove2me | Definitions.Def_QAlgorithms_Defs_ZYCircuits
-- name    : QAlgorithms_Defs_ZYCircuits
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:44:19.393099+00:00
-- url     : https://prove2.me/theorems/d721f3f9-3708-4a38-8b40-891ac993e232
-- title:
--   ZYCircuits
-- statement:
--   ZYCircuits
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\ZYCircuits.lean

import Definitions.Def_QAlgorithms_Defs_ZYGraphSchedules
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.ZY

open scoped Matrix

/-- For i→j use exp(−iθ Z_i Y_j/2), with Z at the tail, Y at the head and distinct ordered wires. Source compilation is CNOT(i,j), R_Y(θ) on j, CNOT(i,j). Source: arxiv-2504.12896v4 PDF p.2; arxiv-2504.12896v4 PDF p.3. -/
def rotationGate (theta : ℝ) : Gate := Gate.ofMatrix2
  (cnot*Matrix.kronecker (1 : Matrix Bool Bool ℂ) (rotY theta)*cnot)

/-- Implementation helper; source: arxiv-2504.12896v4 PDF p.2. -/
def gateSet : Set Gate := {Gate.ofMatrix1 hadamard,Gate.ofMatrix2 cnot} ∪
  {g | ∃ theta, g = Gate.ofMatrix1 (rotY theta)}

/-- Chronological CNOT(tail,head), RY(theta) on head, CNOT(tail,head), using source elementary one or two-qubit gates and actual circuit size. Source: arxiv-2504.12896v4 PDF p.2; arxiv-2504.12896v4 PDF p.3. -/
def rotationCircuit {N : ℕ} (i j : Fin N) (h : i ≠ j) (theta : ℝ) : Circuit gateSet N :=
  [⟨Gate.ofMatrix2 cnot,Set.mem_union_left _ (Set.mem_insert_of_mem _ rfl),Stabilizer.wire2 i j h⟩,
    ⟨Gate.ofMatrix1 (rotY theta),Set.mem_union_right _ ⟨theta,rfl⟩,Stabilizer.wire1 j⟩,
    ⟨Gate.ofMatrix2 cnot,Set.mem_union_left _ (Set.mem_insert_of_mem _ rfl),Stabilizer.wire2 i j h⟩]

/-- Implementation helper; source: arxiv-2504.12896v4 PDF p.2. -/
theorem arrow_ne {N : ℕ} {G : SimpleGraph (Fin N)} (O : Orientation G) (i j : Fin N)
    (h : (i,j) ∈ directedEdges O) : i ≠ j := by
  have har := (Finset.mem_filter.mp h).2
  have had := (O.faithful i j).mpr (Or.inl har)
  exact G.ne_of_adj had

/-- Chronological product of one ZY gate of common θ per edge applied to act (hadamardN N) (zeroKet N). Construct it from orientation and gate sequence, including actual circuit size. It differs from the QAOA ZZ/mixer circuit. Source: arxiv-2504.12896v4 PDF p.3. -/
def ansatzCircuit {N : ℕ} {G : SimpleGraph (Fin N)} {O : Orientation G}
    (seq : GateSequence O) (theta : ℝ) : Circuit gateSet N :=
  seq.edges.attach.flatMap fun e => rotationCircuit e.val.1 e.val.2
    (arrow_ne O _ _ (seq.exhaustive ▸ List.mem_toFinset.mpr e.property)) theta

/-- Apply the complete chronological common-angle ansatzCircuit to H tensor N zeroKet. Norm-one follows from gates; no oracle-hidden graph. Source: arxiv-2504.12896v4 PDF p.3. -/
def ansatzState {N : ℕ} {G : SimpleGraph (Fin N)} {O : Orientation G}
    (seq : GateSequence O) (theta : ℝ) : EuclideanSpace ℂ (Qubits N) :=
  act (ansatzCircuit seq theta).unitary (act (hadamardN N) (zeroKet N))

/-- Construct the center-edge truncation with adjacent damping as in pp.17,20 and Figure 12: retain center gate; replace outside endpoints of other incident gates by independent |+⟩ boundary leaves; discard nonincident gates; preserve chronological order. Audit this one-round realization against the isolated-boundary Pauli-path prescription. Define E₀=Re⟨ψ_local|Z_i Z_j|ψ_local⟩ and L₀=Σ_edges(1−E₀)/2. Do not define it as the analytic D1 conclusion or assume D1; state that equality separately. Source: arxiv-2504.12896v4 PDF p.4; arxiv-2504.12896v4 PDF p.17; arxiv-2504.12896v4 PDF p.20; arxiv-2504.12896v4 PDF p.21. -/
def isolatedBoundaryCircuit {N : ℕ} {G : SimpleGraph (Fin N)} {O : Orientation G}
    (seq : GateSequence O) (center : Fin N × Fin N) (_mem : center ∈ seq.edges)
    (theta : ℝ) : Circuit gateSet (2+seq.edges.length) :=
  (List.finRange seq.edges.length).flatMap fun k =>
    let e := seq.edges.get k
    let leaf : Fin (2+seq.edges.length) := ⟨2+k.val,by have := k.isLt; omega⟩
    let h0 : (⟨0,by omega⟩ : Fin (2+seq.edges.length)) ≠ leaf := by
      intro h; have hh := congrArg Fin.val h; dsimp [leaf] at hh; omega
    let h1 : (⟨1,by omega⟩ : Fin (2+seq.edges.length)) ≠ leaf := by
      intro h; have hh := congrArg Fin.val h; dsimp [leaf] at hh; omega
    if e = center then rotationCircuit ⟨0,by omega⟩ ⟨1,by omega⟩
      (by intro h; have hh := congrArg Fin.val h; change (0 : ℕ) = 1 at hh; omega) theta
    else if e.1 = center.1 then rotationCircuit ⟨0,by omega⟩ leaf h0 theta
    else if e.2 = center.1 then rotationCircuit leaf ⟨0,by omega⟩ h0.symm theta
    else if e.1 = center.2 then rotationCircuit ⟨1,by omega⟩ leaf h1 theta
    else if e.2 = center.2 then rotationCircuit leaf ⟨1,by omega⟩ h1.symm theta
    else []

/-- Re inner(psi_local, Z_i Z_j psi_local) for the constructed isolated-boundary center-edge circuit. Not defined by -cos(theta)^k sin(theta). Source: arxiv-2504.12896v4 PDF p.4; arxiv-2504.12896v4 PDF p.17; arxiv-2504.12896v4 PDF p.20; arxiv-2504.12896v4 PDF p.21. -/
def localEdgeExpectation {N : ℕ} {G : SimpleGraph (Fin N)} {O : Orientation G}
    (seq : GateSequence O) (center : Fin N × Fin N) (mem : center ∈ seq.edges) (theta : ℝ) : ℝ :=
  let psi := act (isolatedBoundaryCircuit seq center mem theta).unitary
    (act (hadamardN (2+seq.edges.length)) (zeroKet _))
  (inner ℂ psi (act (embedOp (Gate.ofMatrix2 (Matrix.kronecker pauliZ pauliZ)).mat
    (Stabilizer.wire2 ⟨0,by omega⟩ ⟨1,by omega⟩
      (by intro h; have hh := congrArg Fin.val h; change (0 : ℕ) = 1 at hh; omega))) psi)).re

/-- Sum over undirected edges e of (1-localEdgeExpectation(e))/2, preserving all adjacent damping and chronological order. Source: arxiv-2504.12896v4 PDF p.4; arxiv-2504.12896v4 PDF p.17; arxiv-2504.12896v4 PDF p.20; arxiv-2504.12896v4 PDF p.21. -/
def localCut {N : ℕ} {G : SimpleGraph (Fin N)} {O : Orientation G}
    (seq : GateSequence O) (theta : ℝ) : ℝ :=
  (seq.edges.attach.map fun e => (1-localEdgeExpectation seq e.val e.property theta)/2).sum

/-- For center gate i→j, count other Y/Z endpoints at i,j before/after it using Figure 12's L/R convention. k_ij=n_R^{Y_i}+n_R^{Y_j}+n_L^{Y_j}+n_L^{Z_j}. Exclude the center gate. Derive k_ij=inDegree j−1 for lightcone order; the actual center arrow guarantees inDegree j≥1 before natural subtraction. Source: arxiv-2504.12896v4 PDF p.20; arxiv-2504.12896v4 PDF p.21. -/
def relativeGateCounts {N : ℕ} {G : SimpleGraph (Fin N)} {O : Orientation G}
    (seq : GateSequence O) (center : Fin N × Fin N) (v : Fin N) (head right : Bool) : ℕ :=
  ((if right then seq.edges.drop (seq.edges.idxOf center+1)
    else seq.edges.take (seq.edges.idxOf center)).filter fun e =>
    decide (e ≠ center) && (if head then decide (e.2 = v) else decide (e.1 = v))).length

/-- For center arrow i->j compute n_R^{Y_i}+n_R^{Y_j}+n_L^{Y_j}+n_L^{Z_j}, excluding center gate. Figure-12 chronology convention; indegree(j)-1 lightcone identity is a theorem. Source: arxiv-2504.12896v4 PDF p.20; arxiv-2504.12896v4 PDF p.21. -/
def localExponent {N : ℕ} {G : SimpleGraph (Fin N)} {O : Orientation G}
    (seq : GateSequence O) (center : Fin N × Fin N) : ℕ :=
  relativeGateCounts seq center center.1 true true + relativeGateCounts seq center center.2 true true +
    relativeGateCounts seq center center.2 true false + relativeGateCounts seq center center.2 false false

example {N : ℕ} (i j : Fin N) (h : i ≠ j) (theta : ℝ) : (rotationCircuit i j h theta).size = 3 := rfl

end QAlgorithms.ZY


