-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P01
-- name    : QAlgorithms_Papers_Independent_Renew46_P01
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T19:41:01.529475+00:00
-- url     : https://prove2.me/theorems/34fd750a-36e6-4c6e-bba6-1bef732ddcb7
-- title:
--   Definitions for Generalised Coupling and An Elementary Algorithm for the Quantum Schur Transform
-- statement:
--   The objects the formalized statements of *Generalised Coupling and An Elementary Algorithm for the Quantum Schur Transform* (arXiv:2305.04069) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `CouplingTree`: PDF pp.12--13: a finite rooted coupling tree. A leaf has physical qudit dimension `p` and `d` admissible base labels. A node has `d` admissible parent M labels and `k` children. All J and internal j labels, and the choice of coefficients at every vertex, are fixed target data.
--   - `CouplingTree.rootDim`: PDF p.12: the finite admissible M domain at the root, at fixed J,j.
--   - `CouplingTree.Config`: PDF pp.12--13: computational configurations of the leaf systems, with the tensor factors ordered by the children at every vertex.
--   - `couplingConfigFintype`: Finiteness of the physical configuration space, constructed recursively.
--   - `CouplingData`: PDF pp.12--13, (32)--(33): base-system vectors at leaves; a finite coefficient tensor and recursively specified child data at nodes. The admissible domains make GC1 automatic. No orthogonality across *different* J values is built into this data type.
--   - `CouplingValid`: PDF pp.12--13, GC2 and the base-case assumption: base columns are orthonormal; node coefficient rows are orthonormal in M at fixed J,j. `K` bounds the arity of every internal vertex; qudits have dimension ≥2.
--   - `coupledAmplitude`: PDF pp.12--13, (33): expansion of a generally coupled vector. This is a sum over child M labels and a tensor product of child vectors, not an arbitrary supplied target-state gate.
--   - `coupledState`: The vector with the recursively computed physical amplitudes.
--   - `UniqueParent`: PDF p.13, the uniqueness part of GC4, restricted to any finite admissible parent and child label domains. Failure on a restriction is already failure of GC4 for the full coefficient tensor.
--   - `su3OctetCoefficients`: PDF p.18, (50)--(51): two fixed GT-coupled states in the same copy of the SU(3) octet in 3 ⊗ conjugate(3). Parent 0 denotes (50), parent 1 (51); child indices are zero-based. The only occupied products are (0,2), (1,1), (2,0). This is the displayed restriction of the SU(3) CG tensor, not a freely selected rotation of its degenerate-weight states.
--   - `BasisPreserving`: PDF p.22, Definition VI.2: every computational basis vector is sent to a computational basis vector times a phase. Unitarity is separate.
--   - `basisPreservingGates`: PDF pp.22--24: B contains basis-preserving unitaries of every arity, including arbitrary diagonal phases, permutations, and CNOT.
--   - `MagneticAdmissible`: PDF pp.3,6: magnetic labels represented by twice their physical value. Admissibility avoids parity errors and zero-extended ghost states.
--   - `addHalfCG`: PDF pp.5--6, (9)--(11): real Condon--Shortley CG coefficient for coupling spin j/2 and a qubit. `m,M` are doubled projections and `J` is doubled output spin. These are the normalized add-spin-1/2 formulas; invalid labels are zero. False means physical projection -1/2. The lower-spin minus sign is on the child qubit with projection +1/2.
--   - `SpinPath`: PDF pp.5,27--28: a complete sequential spin path. Entry k is twice the spin on the first k qubits; the fixed entry 0 is the vacuum spin. Adjacent entries differ by one, and all entries are nonnegative.
--   - `SchurLabel`: PDF pp.27--28: all multiplicity paths and all root projections. The final index s represents M=-J+s, with physical J=rootSpin/2. At n=0 the type contains just the vacuum label.
--   - `prefixProjection`: Twice the Z projection of the first k physical qubits, in the paper's |0>=|-1/2>, |1>=|+1/2> convention (PDF p.3).
--   - `schurSynthesis`: PDF pp.5,27, (4), (B1): physical synthesis, with *all* admissible spin paths (multiplicities) as columns. The product starts with the vacuum-to-first-qubit coefficient, which is 1 on the appropriate basis entry. This makes n=0 and n=1 concrete base maps.
--   - `schurState`: The physical Schur vector with fixed complete labels (PDF p.27, B1).
--   - `upperSpinPath`: A concrete all-upper spin path, used only to pin the base definitions.
--   - `lowestUpperLabel`: The lowest-projection label on the all-upper path.
--   - `EncodedSchurSpace`: PDF pp.5,27--28: one explicit padded encoding of the n registers j1,...,j(n-2),J,M. Every register here uses the common safe width ceil(log2(n+1)); this appendix interface makes no minimum-wire claim. The root M register stores s=M+J. Ghost bit patterns remain in the ambient space. The inverse theorem is restricted to n>=2.
--   - `schurEncoding`: Concrete computational encoding, not a freely supplied isometry.
--   - `schurCodeEmbedding`: Inclusion of valid complete labels into padded computational coordinates.
--   - `encodedCoupling`: PDF p.28, (B3): coupling from code coordinates to physical states, zero on ghosts. This rectangular map is not asserted unitary on ghosts.
--   - `encodedAnalysis`: PDF p.28, (B4): encoded analysis of a physical state.
--   - `schurCodeProjector`: The valid-code projector, including all spin-path multiplicities.
--   - `cleanVector`: Clean zero padding of an arbitrary physical vector, with physical wires first and workspace last, matching the frozen circuit convention.
--   - `IsTwoLevel`: PDF p.26, Appendix A: a two-level unitary on the *active subregister*. Its matrix is the identity outside a pair of basis coordinates. It is embedded on named wires by the frozen GateApp/ Circuit definitions; spectator padding is not required to stay globally two-level.
--   - `twoLevelGates`: The active two-level gate alphabet used by Appendix A.
-- source:
--   Generalised Coupling and An Elementary Algorithm for the Quantum Schur Transform, arXiv:2305.04069v3, https://arxiv.org/abs/2305.04069v3

import Definitions.Def_QAlgorithms_Defs_Circuit

/-!
Statements from Wills--Strelchuk, arXiv:2305.04069v3.
All new definitions are local to this paper. See HARD.md and GAPS.json for
nodes whose concrete algorithm or computational model remains deferred.
Compilation is pending the separate mechanical handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P01

open scoped BigOperators ComplexConjugate

attribute [local instance] Classical.propDecidable

/-- PDF pp.12--13: a finite rooted coupling tree. A leaf has physical
qudit dimension `p` and `d` admissible base labels. A node has `d`
admissible parent M labels and `k` children. All J and internal j labels,
and the choice of coefficients at every vertex, are fixed target data. -/
inductive CouplingTree where
  | leaf (p d : ℕ)
  | node (d k : ℕ) (children : Fin k → CouplingTree)

/-- PDF p.12: the finite admissible M domain at the root, at fixed J,j. -/
def CouplingTree.rootDim : CouplingTree → ℕ
  | .leaf _ d => d
  | .node d _ _ => d

/-- PDF pp.12--13: computational configurations of the leaf systems,
with the tensor factors ordered by the children at every vertex. -/
def CouplingTree.Config : CouplingTree → Type
  | .leaf p _ => Fin p
  | .node _ k children => (i : Fin k) → (children i).Config

/-- Finiteness of the physical configuration space, constructed recursively. -/
def couplingConfigFintype : (t : CouplingTree) → Fintype t.Config
  | .leaf p _ => by
      change Fintype (Fin p)
      infer_instance
  | .node _ k children => by
      change Fintype ((i : Fin k) → (children i).Config)
      letI : (i : Fin k) → Fintype (children i).Config :=
        fun i => couplingConfigFintype (children i)
      infer_instance

/-- PDF pp.12--13: register the recursively constructed finite leaf
configuration space for finite sums and physical state coordinates. -/
instance couplingConfigFintypeInstance (t : CouplingTree) : Fintype t.Config :=
  couplingConfigFintype t

/-- PDF pp.12--13, (32)--(33): base-system vectors at leaves; a finite
coefficient tensor and recursively specified child data at nodes.
The admissible domains make GC1 automatic. No orthogonality across
*different* J values is built into this data type. -/
def CouplingData : CouplingTree → Type
  | .leaf p d => Matrix (Fin p) (Fin d) ℂ
  | .node d k children =>
      (Fin d → ((i : Fin k) → Fin (children i).rootDim) → ℂ) ×
        ((i : Fin k) → CouplingData (children i))

/-- PDF pp.12--13, GC2 and the base-case assumption: base columns are
orthonormal; node coefficient rows are orthonormal in M at fixed J,j.
`K` bounds the arity of every internal vertex; qudits have dimension ≥2. -/
def CouplingValid : (t : CouplingTree) → CouplingData t → ℕ → Prop
  | .leaf p d, A, _ =>
      2 ≤ p ∧ ∀ M N : Fin d,
        (∑ x : Fin p, star (A x M) * A x N) = if M = N then 1 else 0
  | .node d k children, A, K =>
      2 ≤ k ∧ k ≤ K ∧
        (∀ i, CouplingValid (children i) (A.2 i) K) ∧
        ∀ M N : Fin d,
          (∑ m : (i : Fin k) → Fin (children i).rootDim,
            star (A.1 M m) * A.1 N m) = if M = N then 1 else 0

/-- PDF pp.12--13, (33): expansion of a generally coupled vector.
This is a sum over child M labels and a tensor product of child vectors,
not an arbitrary supplied target-state gate. -/
def coupledAmplitude : (t : CouplingTree) → CouplingData t →
    Fin t.rootDim → t.Config → ℂ
  | .leaf _ _, A, M, x => A x M
  | .node _ k children, A, M, x =>
      ∑ m : (i : Fin k) → Fin (children i).rootDim,
        A.1 M m * ∏ i : Fin k, coupledAmplitude (children i) (A.2 i) (m i) (x i)

/-- The vector with the recursively computed physical amplitudes. -/
def coupledState (t : CouplingTree) (A : CouplingData t) (M : Fin t.rootDim) :
    EuclideanSpace ℂ t.Config :=
  WithLp.toLp 2 (coupledAmplitude t A M)

/-- Sanity: an uncoupled two-level base system retains its given columns. -/
example : coupledAmplitude (.leaf 2 2) (1 : Matrix (Fin 2) (Fin 2) ℂ) (0 : Fin 2) (0 : Fin 2) = 1 := by
  simp [coupledAmplitude]

/-- Sanity: the other computational coordinate of that column is zero. -/
example : coupledAmplitude (.leaf 2 2) (1 : Matrix (Fin 2) (Fin 2) ℂ) (0 : Fin 2) (1 : Fin 2) = 0 := by
  simp [coupledAmplitude]

/-- PDF p.13, the uniqueness part of GC4, restricted to any finite
admissible parent and child label domains. Failure on a restriction is
already failure of GC4 for the full coefficient tensor. -/
def UniqueParent {P X : Type*} (A : P → X → ℂ) : Prop :=
  ∀ x M N, A M x ≠ 0 → A N x ≠ 0 → M = N

/-- PDF p.18, (50)--(51): two fixed GT-coupled states in the same copy
of the SU(3) octet in 3 ⊗ conjugate(3). Parent 0 denotes (50), parent 1
(51); child indices are zero-based. The only occupied products are
(0,2), (1,1), (2,0). This is the displayed restriction of the SU(3) CG
tensor, not a freely selected rotation of its degenerate-weight states. -/
def su3OctetCoefficients (M : Fin 2) (x : Fin 3 × Fin 3) : ℂ :=
  if M = 0 then
    if x = (0, 2) ∨ x = (1, 1) then (1 / Real.sqrt 2 : ℝ) else 0
  else
    if x = (0, 2) then (-1 / Real.sqrt 6 : ℝ)
    else if x = (1, 1) then (1 / Real.sqrt 6 : ℝ)
    else if x = (2, 0) then (Real.sqrt (2 / 3) : ℝ) else 0

/-- Sanity: the third product is absent from (50). -/
example : su3OctetCoefficients 0 (2, 0) = 0 := by
  simp [su3OctetCoefficients]

/-- Sanity: the first coefficient of (51) has its printed minus sign. -/
example : su3OctetCoefficients 1 (0, 2) = (-1 / Real.sqrt 6 : ℝ) := by
  simp [su3OctetCoefficients]

/-- PDF p.22, Definition VI.2: every computational basis vector is sent
to a computational basis vector times a phase. Unitarity is separate. -/
def BasisPreserving (g : Gate) : Prop :=
  ∀ x : Qubits g.arity, ∃ y : Qubits g.arity, ∃ theta : ℝ,
    ∀ z : Qubits g.arity,
      g.mat z x = if z = y then Complex.exp (theta * Complex.I) else 0

/-- PDF pp.22--24: B contains basis-preserving unitaries of every arity,
including arbitrary diagonal phases, permutations, and CNOT. -/
def basisPreservingGates : Set Gate :=
  {g | g.IsUnitary ∧ BasisPreserving g}

/-- Sanity: the identity is basis preserving at every arity, including zero. -/
example (n : ℕ) : BasisPreserving (⟨n, 1⟩ : Gate) := by
  intro x
  refine ⟨x, 0, ?_⟩
  intro z
  simp [Matrix.one_apply]

/-- PDF pp.3,6: magnetic labels represented by twice their physical
value. Admissibility avoids parity errors and zero-extended ghost states. -/
def MagneticAdmissible (j : ℕ) (m : ℤ) : Prop :=
  -(j : ℤ) ≤ m ∧ m ≤ (j : ℤ) ∧ (m + (j : ℤ)) % 2 = 0

/-- PDF pp.5--6, (9)--(11): real Condon--Shortley CG coefficient for
coupling spin j/2 and a qubit. `m,M` are doubled projections and `J` is
doubled output spin. These are the normalized add-spin-1/2 formulas;
invalid labels are zero. False means physical projection -1/2.
The lower-spin minus sign is on the child qubit with projection +1/2. -/
def addHalfCG (j J : ℕ) (m M : ℤ) (b : Bool) : ℝ :=
  if MagneticAdmissible j m ∧ MagneticAdmissible J M ∧
      M = m + (if b then 1 else -1) then
    if J = j + 1 then
      if b then Real.sqrt (((j : ℝ) + (m : ℝ) + 2) / (2 * ((j : ℝ) + 1)))
      else Real.sqrt (((j : ℝ) - (m : ℝ) + 2) / (2 * ((j : ℝ) + 1)))
    else if j = J + 1 then
      if b then -Real.sqrt (((j : ℝ) - (m : ℝ)) / (2 * ((j : ℝ) + 1)))
      else Real.sqrt (((j : ℝ) + (m : ℝ)) / (2 * ((j : ℝ) + 1)))
    else 0
  else 0

/-- PDF pp.5,27--28: a complete sequential spin path. Entry k is twice
the spin on the first k qubits; the fixed entry 0 is the vacuum spin.
Adjacent entries differ by one, and all entries are nonnegative. -/
abbrev SpinPath (n : ℕ) :=
  {j : Fin (n + 1) → Fin (n + 1) //
    j 0 = 0 ∧ ∀ k : Fin n,
      (j k.succ).val = (j (Fin.castSucc k)).val + 1 ∨
        (j (Fin.castSucc k)).val = (j k.succ).val + 1}

/-- PDF pp.27--28: all multiplicity paths and all root projections.
The final index s represents M=-J+s, with physical J=rootSpin/2.
At n=0 the type contains just the vacuum label. -/
abbrev SchurLabel (n : ℕ) :=
  {p : SpinPath n × Fin (n + 1) // p.2.val ≤ (p.1.val (Fin.last n)).val}

/-- Twice the Z projection of the first k physical qubits, in the
paper's |0>=|-1/2>, |1>=|+1/2> convention (PDF p.3). -/
def prefixProjection {n : ℕ} (x : Qubits n) (k : ℕ) : ℤ :=
  ∑ i : Fin n, if i.val < k then (if x i then 1 else -1) else 0

/-- PDF pp.5,27, (4), (B1): physical synthesis, with *all* admissible
spin paths (multiplicities) as columns. The product starts with the
vacuum-to-first-qubit coefficient, which is 1 on the appropriate basis
entry. This makes n=0 and n=1 concrete base maps. -/
def schurSynthesis (n : ℕ) : Matrix (Qubits n) (SchurLabel n) ℂ :=
  fun x a =>
    if prefixProjection x n = 2 * (a.val.2.val : ℤ) -
        ((a.val.1.val (Fin.last n)).val : ℤ) then
      ∏ k : Fin n,
        (addHalfCG (a.val.1.val (Fin.castSucc k)).val (a.val.1.val k.succ).val
          (prefixProjection x k.val) (prefixProjection x (k.val + 1)) (x k) : ℂ)
    else 0

/-- The physical Schur vector with fixed complete labels (PDF p.27, B1). -/
def schurState {n : ℕ} (a : SchurLabel n) : EuclideanSpace ℂ (Qubits n) :=
  WithLp.toLp 2 (fun x => schurSynthesis n x a)

/-- A concrete all-upper spin path, used only to pin the base definitions. -/
def upperSpinPath (n : ℕ) : SpinPath n :=
  ⟨fun k => k, rfl, fun _ => Or.inl rfl⟩

/-- The lowest-projection label on the all-upper path. -/
def lowestUpperLabel (n : ℕ) : SchurLabel n :=
  ⟨(upperSpinPath n, 0), Nat.zero_le _⟩

/-- Sanity: the vacuum is mapped to the vacuum, rather than to a ghost. -/
example : schurSynthesis 0 (fun _ => false) (lowestUpperLabel 0) = 1 := by
  simp [schurSynthesis, prefixProjection, lowestUpperLabel, upperSpinPath]

/-- Sanity: the one-qubit base maps |0> to the lower magnetic state. -/
example : schurSynthesis 1 (fun _ => false) (lowestUpperLabel 1) = 1 := by
  norm_num [schurSynthesis, prefixProjection, lowestUpperLabel, upperSpinPath,
    addHalfCG, MagneticAdmissible]

/-- Sanity: adjoining the first down-spin qubit to vacuum has coefficient 1. -/
example : addHalfCG 0 1 0 (-1) false = 1 := by
  norm_num [addHalfCG, MagneticAdmissible]

/-- Sanity: the two singlet coefficients have the Condon--Shortley signs. -/
example : addHalfCG 1 0 1 0 false = Real.sqrt (1 / 2) := by
  norm_num [addHalfCG, MagneticAdmissible]

example : addHalfCG 1 0 (-1) 0 true = -Real.sqrt (1 / 2) := by
  norm_num [addHalfCG, MagneticAdmissible]

/-- Sanity: a parity-invalid magnetic label is zero-extended. -/
example : addHalfCG 1 2 0 1 true = 0 := by
  norm_num [addHalfCG, MagneticAdmissible]

/-- PDF pp.5,27--28: one explicit padded encoding of the n registers
j1,...,j(n-2),J,M. Every register here uses the common safe width
ceil(log2(n+1)); this appendix interface makes no minimum-wire claim.
The root M register stores s=M+J. Ghost bit patterns remain in the ambient
space. The inverse theorem is restricted to n>=2. -/
abbrev EncodedSchurSpace (n : ℕ) :=
  (Fin (n - 2) → Qubits (Nat.clog 2 (n + 1))) ×
    Qubits (Nat.clog 2 (n + 1)) × Qubits (Nat.clog 2 (n + 1))

/-- Concrete computational encoding, not a freely supplied isometry. -/
def schurEncoding {n : ℕ} (a : SchurLabel n) : EncodedSchurSpace n :=
  (fun i => natToBits (Nat.clog 2 (n + 1))
      (a.val.1.val ⟨i.val + 2, by have := i.isLt; omega⟩).val,
    natToBits (Nat.clog 2 (n + 1)) (a.val.1.val (Fin.last n)).val,
    natToBits (Nat.clog 2 (n + 1)) a.val.2.val)

/-- Inclusion of valid complete labels into padded computational coordinates. -/
def schurCodeEmbedding (n : ℕ) :
    Matrix (EncodedSchurSpace n) (SchurLabel n) ℂ :=
  fun z a => if z = schurEncoding a then 1 else 0

/-- PDF p.28, (B3): coupling from code coordinates to physical states,
zero on ghosts. This rectangular map is not asserted unitary on ghosts. -/
def encodedCoupling (n : ℕ) : Matrix (Qubits n) (EncodedSchurSpace n) ℂ :=
  schurSynthesis n * (schurCodeEmbedding n).conjTranspose

/-- PDF p.28, (B4): encoded analysis of a physical state. -/
def encodedAnalysis (n : ℕ) : Matrix (EncodedSchurSpace n) (Qubits n) ℂ :=
  schurCodeEmbedding n * (schurSynthesis n).conjTranspose

/-- The valid-code projector, including all spin-path multiplicities. -/
def schurCodeProjector (n : ℕ) :
    Matrix (EncodedSchurSpace n) (EncodedSchurSpace n) ℂ :=
  schurCodeEmbedding n * (schurCodeEmbedding n).conjTranspose

/-- Sanity: the inclusion has amplitude 1 at its own encoded coordinate. -/
example {n : ℕ} (a : SchurLabel n) :
    schurCodeEmbedding n (schurEncoding a) a = 1 := by
  simp [schurCodeEmbedding]

/-- Clean zero padding of an arbitrary physical vector, with physical
wires first and workspace last, matching the frozen circuit convention. -/
def cleanVector {n : ℕ} (w : ℕ) (psi : EuclideanSpace ℂ (Qubits n)) :
    EuclideanSpace ℂ (Qubits (n + w)) :=
  WithLp.toLp 2 (fun z =>
    psi (fun i => z (Fin.castAdd w i)) *
      if ∀ j : Fin w, z (Fin.natAdd n j) = false then 1 else 0)

/-- Sanity: zero added workspace leaves every physical coordinate unchanged. -/
example {n : ℕ} (psi : EuclideanSpace ℂ (Qubits n)) (x : Qubits (n + 0)) :
    cleanVector 0 psi x = psi (fun i => x (Fin.castAdd 0 i)) := by
  simp [cleanVector]

/-- PDF p.26, Appendix A: a two-level unitary on the *active subregister*.
Its matrix is the identity outside a pair of basis coordinates. It is
embedded on named wires by the frozen GateApp/ Circuit definitions;
spectator padding is not required to stay globally two-level. -/
def IsTwoLevel (g : Gate) : Prop :=
  g.IsUnitary ∧ ∃ a b : Qubits g.arity, a ≠ b ∧
    ∀ x y : Qubits g.arity,
      ((x ≠ a ∧ x ≠ b) ∨ (y ≠ a ∧ y ≠ b)) →
        g.mat x y = if x = y then 1 else 0

/-- The active two-level gate alphabet used by Appendix A. -/
def twoLevelGates : Set Gate := {g | IsTwoLevel g}

/-- Sanity: the one-qubit identity is an allowed active two-level gate. -/
example : IsTwoLevel (⟨1, 1⟩ : Gate) := by
  refine ⟨?_, (fun _ => false), (fun _ => true), ?_, ?_⟩
  · simp [Gate.IsUnitary]
  · intro h
    have h0 := congrFun h (0 : Fin 1)
    cases h0
  · intro x y _
    rfl

/-- Sanity: a gate from this alphabet must be unitary. -/
example (g : Gate) (h : g ∈ twoLevelGates) : g.IsUnitary := h.1

end QAlgorithms.Papers.Independent.Renew46.P01


