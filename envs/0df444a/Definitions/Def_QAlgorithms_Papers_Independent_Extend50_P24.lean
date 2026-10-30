-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P24
-- name    : QAlgorithms_Papers_Independent_Extend50_P24
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T17:44:18.512082+00:00
-- url     : https://prove2.me/theorems/39417874-9b05-428c-a190-28b28aebf058
-- title:
--   Definitions for An efficient high dimensional quantum Schur transform
-- statement:
--   The objects the formalized statements of *An efficient high dimensional quantum Schur transform* (arXiv:1804.00055) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `StandardTableau`: Actual standard tableaux: label-to-cell bijections, with increasing rows and columns (PDF pp.4-5). Equivalence forces exactly n occupied cells.
--   - `youngCoefficient`: Every matrix entry of (2.5)-(2.8), including the positive square root, same-row +1 and same-column -1 cases (PDF p.5).
--   - `YoungModel`: The named Young orthonormal representation, fixed independently of any input or accuracy (PDF pp.3-5). The defining generator equations are complete; no subgroup-average annihilation or multiplicity compression is assumed.
--   - `YoungFourierIndex`: Full symmetric-group Fourier labels, with irrep coordinate before multiplicity coordinate; both are genuine SYTs (PDF p.10).
--   - `SymmetricModels`: A fixed Young realization of every shape, not a transform chosen after an input vector or a requested precision (PDF pp.5,10).
--   - `symmetricFourier`: The nonabelian QFT in those Young coordinates. Left multiplication acts on the first tableau coordinate; this fixes all conjugation conventions (PDF pp.3,10,14).
--   - `IsUnitaryBetween`: Rectangular unitary/isometry equivalence in orthonormal coordinates. No accidental entrywise matrix norm is used (PDF pp.3,10).
--   - `applyMatrix`: Rectangular action on L2 vectors (PDF p.10, (3.1)).
--   - `CompiledCircuit`: Serial circuits in the frozen finite universal gate set H,S,T,X,CNOT. Each gate acts on named wires. There are no free oracle or group-operation instructions (PDF pp.2,10).
--   - `CompiledCircuit.run`: Actual gate-by-gate circuit execution (PDF p.10).
--   - `CompiledCircuit.code`: Finite binary serialization, including wire count and every gate/wire. The generating classical TM must output exactly this code (PDF pp.2,10).
--   - `CompiledCircuit.work`: Execution length and serialized allocation/output cost, all tied to actual syntax rather than an arbitrary declared runtime (PDF pp.2,10).
--   - `requestCode`: Public requests: unary n and precision bits t, binary d with a unary length prefix. Request length is O(n+t+1+log d) (PDF pp.2,10).
--   - `encodedVector`: A fixed numerical basis encoding, padded with zeroes to the circuit's wire count. Injectivity at that width is required by Approximates (PDF p.10). Leading zeroes include all input-independent clean ancillary wires.
--   - `Approximates`: Operator-norm error on the whole encoded input subspace, including ancilla leakage. No input-dependent global phase is discarded (3.1, p.10). The inequality includes every vector and is homogeneous, so zero is harmless.
--   - `permutationCode`: Canonical base-(n+1) permutation encoding, retaining the numbered tensor positions of the symmetric tower (PDF pp.5,10).
--   - `tableauCode`: Canonical label-to-cell serialization. Occupied cells determine the shape, so this code does not use an arbitrary enumeration of partitions or an uncomputed change of tableau basis (PDF pp.4-5).
--   - `symmetricCode`: Both Fourier tableau labels are serialized without a basis rotation (PDF p.10). Nat.pair is an explicit arithmetic pairing function.
--   - `FourierData`: A finite list of unitary irreps in fixed orthonormal coordinates (PDF pp.3,10-11). Completeness is imposed on the explicit Fourier matrix, not on an arbitrary block-diagonalizing map.
--   - `FourierIndex`: Irrep, irrep-space index, multiplicity index (PDF pp.3,11).
--   - `groupFourier`: Explicit group Fourier matrix with orthonormal normalization (PDF p.14, (3.7)-(3.9)). The chosen convention puts left action on the first index.
--   - `fourierAction`: Computed block action in the full padded Fourier space (PDF pp.3,11).
--   - `LeftTransversal`: A fixed left-coset transversal and the actual implemented relabelling (t,h) ↔ th, not an uncharged oracle (PDF pp.3,11).
--   - `inducedAction`: The induced representation (2.2), gt=t' h, in transversal/irrep coordinates (PDF p.3). This is computed from sigma and the transversal.
--   - `inducedEmbedding`: Steps 1 and 2 of §3.3: insert the fixed multiplicity coordinate u, apply F_H dagger, and perform the explicit relabelling |t,h>↦|th> (p.11). No choice depends on the input irrep vector v.
--   - `inducedFourier`: Step 3: F_G after the padded embedding; no unsupported clean-register compression is hidden in this definition (PDF p.11).
--   - `PermutationType`: A type represented by its uniquely sorted E0 word (PDF pp.9,11). Its counts are the source's t_i; zero counts are permitted.
--   - `ModuleWord`: The permutation module's orthonormal word/coset coordinates (PDF pp.9,11). Different permutations of E0 give the same index exactly for the same coset.
--   - `youngSubgroup`: Stabilizer Y_T of the sorted word, hence a product of symmetric groups on consecutive label-position blocks (PDF pp.9,11).
--   - `cosetEmbedding`: Normalized coset-state embedding J_T; this includes the uniform subgroup ancilla |Y_T|^(-1/2), not the unnormalized subgroup sum of Lemma 2 (p.11).
--   - `qftPermMod`: Exact action of the QFTPermMod circuit on its promised coset input: F_(S_n) J_T. Coherent right-Y_T GPE has the trivial label and leaves J_T unchanged; its clean trivial ancilla is implicit (PDF pp.13-14).
--   - `moduleAction`: Actual permutation action on the module words (PDF pp.9,11).
--   - `youngFourierAction`: Left symmetric action in the padded Fourier register (PDF pp.10,13).
--   - `moduleWordCode`: Explicit base-(n+1) word and type encoding (PDF pp.9,13).
--   - `moduleRequest`: Request for a permutation module. Unary entries of E0 add O(n^2) bits, so polynomial-time generation remains polynomial in n and t (p.13).
--   - `IsConsecutive`: Contiguous sets of numbered labels, including empty and singleton sets (PDF p.15, Lemma 2). Source labels 1,...,n correspond to Fin n.
--   - `permutationsOn`: S_A fixes every label outside A, and otherwise permits all permutations (PDF p.15). No arbitrary subgroup or subgroup invariance is assumed.
--   - `subgroupSum`: Unnormalized group-algebra symmetrizer sum_(g in S_A) lambda(g), exactly the Lemma 2 convention, not (3.2)'s average (PDF p.15).
--   - `SemistandardTableau`: Bounded-alphabet SSYTs, using the accepted row/column predicate (PDF pp.6-9). These fillings label physical U(d) factors.
--   - `alphabetMinor`: First k alphabet coordinates are the fixed U(k) minor; all other coordinates are identity (PDF pp.5-8). k≤d is required by the caller.
--   - `gtPrefixCells`: The actual subdiagram of boxes carrying letters below k, expressed as a finite set so no arbitrary GT path is substituted (PDF pp.5-8).
--   - `IsPhysicalGTBasis`: Physical GT tower adaptation, not just SSYT names or weight labels. For every k, the named vector belongs to a copy of the actual polynomial U(k) module of its prefix shape, with an injective isometric intertwiner into the fixed physical Schur factor (PDF pp.5-9,17-19). Branching is multiplicity-free, so all these prefix conditions specify the GT line.
--   - `StrongIndex`: Strong Schur output coordinates: shape, symmetric Young coordinate, and physical unitary GT coordinate (PDF pp.9,16).
--   - `StrongSchurFrame`: Exact simultaneous strong Schur transform with actual polynomial factors and both intertwining identities, not arbitrary labels on a decomposition (PDF pp.5-9,16). All basis phases are fields fixed before precision.
--   - `strongMatrix`: Matrix of the fixed exact frame, with no input-dependent phase quotient (PDF pp.9-10).
--   - `tensorWordCode`: Fixed positional input encoding in the one-qudit alphabet (PDF pp.9,16).
--   - `strongCode`: A reversible serialization of a Young/GT label, not a purported amplitude-changing SSYT compression (PDF pp.6,9,16). T determines the shape and orders its cells; entries of S are then serialized in base d.
-- source:
--   An efficient high dimensional quantum Schur transform, arXiv:1804.00055v2, https://arxiv.org/abs/1804.00055v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurWeylDecomposition
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26

/-!
Paper-local interfaces for Krovi, arXiv:1804.00055v2.
All indices are zero-based. The three source-ambiguous claims inventoried in
HARD.md are intentionally absent. No theorem below certifies DualSchur's
missing computational multiplicity-space rotation.
-/

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Extend50.P24

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Renew46.P26 (boxContent)

/-- Actual standard tableaux: label-to-cell bijections, with increasing rows
and columns (PDF pp.4-5). Equivalence forces exactly n occupied cells. -/
def StandardTableau (n : ℕ) (lambda : YoungDiagram) :=
  {p : Fin n ≃ lambda.cells // ∀ i j : Fin n,
    (((p i).val.1 = (p j).val.1 → (p i).val.2 < (p j).val.2 → i < j) ∧
     ((p i).val.2 = (p j).val.2 → (p i).val.1 < (p j).val.1 → i < j))}

/-- Enumerate the subtype of bijections between the finite label and cell sets. -/
instance standardTableauFintype (n : ℕ) (lambda : YoungDiagram) :
    Fintype (StandardTableau n lambda) := by
  classical
  unfold StandardTableau
  infer_instance

/-- Every matrix entry of (2.5)-(2.8), including the positive square root,
same-row +1 and same-column -1 cases (PDF p.5). -/
def youngCoefficient {n : ℕ} {lambda : YoungDiagram}
    (i j : Fin n) (T U : StandardTableau n lambda) : ℂ :=
  let a := (T.val i).val
  let b := (T.val j).val
  let r : ℝ := ((boxContent b - boxContent a : ℤ) : ℝ)
  if a.1 = b.1 then (if U = T then 1 else 0)
  else if a.2 = b.2 then (if U = T then -1 else 0)
  else if U = T then (r⁻¹ : ℝ)
  else if U.val = (Equiv.swap i j).trans T.val then
    (Real.sqrt (1 - r⁻¹ ^ 2) : ℝ)
  else 0

/-- The named Young orthonormal representation, fixed independently of any
input or accuracy (PDF pp.3-5). The defining generator equations are complete;
no subgroup-average annihilation or multiplicity compression is assumed. -/
structure YoungModel (n : ℕ) (lambda : YoungDiagram) where
  rho : Equiv.Perm (Fin n) →*
    Matrix (StandardTableau n lambda) (StandardTableau n lambda) ℂ
  unitary : ∀ g, rho g ∈ Matrix.unitaryGroup (StandardTableau n lambda) ℂ
  generators : ∀ (i j : Fin n), j.val = i.val + 1 → ∀ T U,
    rho (Equiv.swap i j) U T = youngCoefficient i j T U

/-- Full symmetric-group Fourier labels, with irrep coordinate before
multiplicity coordinate; both are genuine SYTs (PDF p.10). -/
abbrev YoungFourierIndex (n : ℕ) :=
  (lambda : QAlgorithms.Schur.Partition n n) ×
    (StandardTableau n lambda.val × StandardTableau n lambda.val)

/-- A fixed Young realization of every shape, not a transform chosen after
an input vector or a requested precision (PDF pp.5,10). -/
abbrev SymmetricModels (n : ℕ) :=
  (lambda : QAlgorithms.Schur.Partition n n) → YoungModel n lambda.val

/-- The nonabelian QFT in those Young coordinates. Left multiplication acts
on the first tableau coordinate; this fixes all conjugation conventions
(PDF pp.3,10,14). -/
def symmetricFourier {n : ℕ} (Y : SymmetricModels n) :
    Matrix (YoungFourierIndex n) (Equiv.Perm (Fin n)) ℂ :=
  fun z g =>
    (Real.sqrt ((Fintype.card (StandardTableau n z.1.val) : ℝ) /
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ)) : ℂ) *
      (Y z.1).rho g z.2.1 z.2.2

/-- Rectangular unitary/isometry equivalence in orthonormal coordinates.
No accidental entrywise matrix norm is used (PDF pp.3,10). -/
def IsUnitaryBetween {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    [DecidableEq alpha] [DecidableEq beta] (M : Matrix beta alpha ℂ) : Prop :=
  Mᴴ * M = 1 ∧ M * Mᴴ = 1

/-- Rectangular action on L2 vectors (PDF p.10, (3.1)). -/
def applyMatrix {alpha beta : Type*} [Fintype alpha]
    (M : Matrix beta alpha ℂ) (v : EuclideanSpace ℂ alpha) : EuclideanSpace ℂ beta :=
  WithLp.toLp 2 (M.mulVec (WithLp.ofLp v))

/-- Serial circuits in the frozen finite universal gate set H,S,T,X,CNOT.
Each gate acts on named wires. There are no free oracle or group-operation
instructions (PDF pp.2,10). -/
structure CompiledCircuit where
  wires : ℕ
  gates : List (QAlgorithms.Complexity.Instr wires)

/-- Actual gate-by-gate circuit execution (PDF p.10). -/
def CompiledCircuit.run (C : CompiledCircuit)
    (v : EuclideanSpace ℂ (QAlgorithms.Qubits C.wires)) :
    EuclideanSpace ℂ (QAlgorithms.Qubits C.wires) :=
  WithLp.toLp 2 (C.gates.foldl (fun w g => g.apply w) (WithLp.ofLp v))

/-- Finite binary serialization, including wire count and every gate/wire.
The generating classical TM must output exactly this code (PDF pp.2,10). -/
def CompiledCircuit.code (C : CompiledCircuit) : List Bool :=
  QAlgorithms.Complexity.encNat C.wires ++
    QAlgorithms.Complexity.encStr (C.gates.map QAlgorithms.Complexity.encInstr)

/-- Execution length and serialized allocation/output cost, all tied to
actual syntax rather than an arbitrary declared runtime (PDF pp.2,10). -/
def CompiledCircuit.work (C : CompiledCircuit) : ℕ :=
  C.wires + C.gates.length + C.code.length

/-- Public requests: unary n and precision bits t, binary d with a unary
length prefix. Request length is O(n+t+1+log d) (PDF pp.2,10). -/
def requestCode (n d t : ℕ) : List Bool :=
  let b := List.ofFn (QAlgorithms.natToBits (Nat.clog 2 (d + 1)) d)
  QAlgorithms.Complexity.encNat n ++ QAlgorithms.Complexity.encNat t ++
    QAlgorithms.Complexity.encNat b.length ++ b

/-- A fixed numerical basis encoding, padded with zeroes to the circuit's
wire count. Injectivity at that width is required by Approximates (PDF p.10).
Leading zeroes include all input-independent clean ancillary wires. -/
def encodedVector {alpha : Type*} [Fintype alpha]
    (code : alpha → ℕ) (q : ℕ) (v : EuclideanSpace ℂ alpha) :
    EuclideanSpace ℂ (QAlgorithms.Qubits q) :=
  ∑ x, v x • QAlgorithms.ket (QAlgorithms.natToBits q (code x))

/-- Operator-norm error on the whole encoded input subspace, including
ancilla leakage. No input-dependent global phase is discarded (3.1, p.10).
The inequality includes every vector and is homogeneous, so zero is harmless. -/
def Approximates {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (inputCode : alpha → ℕ) (outputCode : beta → ℕ)
    (M : Matrix beta alpha ℂ) (C : CompiledCircuit) (epsilon : ℝ) : Prop :=
  Function.Injective (fun x => QAlgorithms.natToBits C.wires (inputCode x)) ∧
  Function.Injective (fun y => QAlgorithms.natToBits C.wires (outputCode y)) ∧
  ∀ v : EuclideanSpace ℂ alpha,
    ‖C.run (encodedVector inputCode C.wires v) -
      encodedVector outputCode C.wires (applyMatrix M v)‖ ≤ epsilon * ‖v‖

/-- Canonical base-(n+1) permutation encoding, retaining the numbered tensor
positions of the symmetric tower (PDF pp.5,10). -/
def permutationCode {n : ℕ} (g : Equiv.Perm (Fin n)) : ℕ :=
  ∑ i : Fin n, (g i).val * (n + 1) ^ i.val

/-- Canonical label-to-cell serialization. Occupied cells determine the
shape, so this code does not use an arbitrary enumeration of partitions
or an uncomputed change of tableau basis (PDF pp.4-5). -/
def tableauCode {n : ℕ} {lambda : YoungDiagram}
    (T : StandardTableau n lambda) : ℕ :=
  ∑ i : Fin n,
    ((T.val i).val.1 * (n + 1) + (T.val i).val.2 + 1) *
      ((n + 1) ^ 2 + 1) ^ i.val

/-- Both Fourier tableau labels are serialized without a basis rotation
(PDF p.10). Nat.pair is an explicit arithmetic pairing function. -/
def symmetricCode {n : ℕ} (z : YoungFourierIndex n) : ℕ :=
  Nat.pair (tableauCode z.2.1) (tableauCode z.2.2)

/-- A finite list of unitary irreps in fixed orthonormal coordinates
(PDF pp.3,10-11). Completeness is imposed on the explicit Fourier matrix,
not on an arbitrary block-diagonalizing map. -/
structure FourierData (G : Type*) [Group G] [Fintype G] where
  labels : ℕ
  dimension : Fin labels → ℕ
  positive : ∀ l, 0 < dimension l
  rho : (l : Fin labels) → G →* Matrix (Fin (dimension l)) (Fin (dimension l)) ℂ
  unitary : ∀ l g, rho l g ∈ Matrix.unitaryGroup (Fin (dimension l)) ℂ
  irreducible : ∀ l (W : Submodule ℂ (EuclideanSpace ℂ (Fin (dimension l)))),
    (∀ g v, v ∈ W → QAlgorithms.act (rho l g) v ∈ W) → W = ⊥ ∨ W = ⊤

/-- Irrep, irrep-space index, multiplicity index (PDF pp.3,11). -/
abbrev FourierIndex {G : Type*} [Group G] [Fintype G] (D : FourierData G) :=
  (l : Fin D.labels) × (Fin (D.dimension l) × Fin (D.dimension l))

/-- Explicit group Fourier matrix with orthonormal normalization (PDF p.14,
(3.7)-(3.9)). The chosen convention puts left action on the first index. -/
def groupFourier {G : Type*} [Group G] [Fintype G] (D : FourierData G) :
    Matrix (FourierIndex D) G ℂ :=
  fun z g => (Real.sqrt ((D.dimension z.1 : ℝ) / Fintype.card G) : ℂ) *
    D.rho z.1 g z.2.1 z.2.2

/-- Computed block action in the full padded Fourier space (PDF pp.3,11). -/
def fourierAction {G : Type*} [Group G] [Fintype G]
    (D : FourierData G) (g : G) (v : EuclideanSpace ℂ (FourierIndex D)) :
    EuclideanSpace ℂ (FourierIndex D) :=
  WithLp.toLp 2 fun z => ∑ i : Fin (D.dimension z.1),
    D.rho z.1 g z.2.1 i * v ⟨z.1, (i, z.2.2)⟩

/-- A fixed left-coset transversal and the actual implemented relabelling
(t,h) ↔ th, not an uncharged oracle (PDF pp.3,11). -/
structure LeftTransversal {G : Type*} [Group G] (H : Subgroup G)
    (C : Type*) where
  representative : C → G
  coordinates : (C × H) ≃ G
  product : ∀ t h, coordinates (t,h) = representative t * (h : G)

/-- The induced representation (2.2), gt=t' h, in transversal/irrep
coordinates (PDF p.3). This is computed from sigma and the transversal. -/
def inducedAction {G C : Type*} [Group G] [Fintype G] [Fintype C]
    (H : Subgroup G) [Fintype H] (T : LeftTransversal H C)
    (D : FourierData H) (sigma : Fin D.labels) (g : G) :
    Matrix (C × Fin (D.dimension sigma)) (C × Fin (D.dimension sigma)) ℂ :=
  fun x y =>
    let p := T.coordinates.symm (g * T.representative y.1)
    if x.1 = p.1 then D.rho sigma p.2 x.2 y.2 else 0

/-- Steps 1 and 2 of §3.3: insert the fixed multiplicity coordinate u,
apply F_H dagger, and perform the explicit relabelling |t,h>↦|th> (p.11).
No choice depends on the input irrep vector v. -/
def inducedEmbedding {G C : Type*} [Group G] [Fintype G] [Fintype C]
    (H : Subgroup G) [Fintype H] (T : LeftTransversal H C)
    (D : FourierData H) (sigma : Fin D.labels) (u : Fin (D.dimension sigma)) :
    Matrix G (C × Fin (D.dimension sigma)) ℂ :=
  fun g x =>
    let p := T.coordinates.symm g
    if p.1 = x.1 then star ((groupFourier D) ⟨sigma,(x.2,u)⟩ p.2) else 0

/-- Step 3: F_G after the padded embedding; no unsupported clean-register
compression is hidden in this definition (PDF p.11). -/
def inducedFourier {G C : Type*} [Group G] [Fintype G] [Fintype C]
    (H : Subgroup G) [Fintype H] (T : LeftTransversal H C)
    (DG : FourierData G) (DH : FourierData H) (sigma : Fin DH.labels)
    (u : Fin (DH.dimension sigma)) :
    Matrix (FourierIndex DG) (C × Fin (DH.dimension sigma)) ℂ :=
  groupFourier DG * inducedEmbedding H T DH sigma u

/-- A type represented by its uniquely sorted E0 word (PDF pp.9,11).
Its counts are the source's t_i; zero counts are permitted. -/
def PermutationType (n : ℕ) := {e : Fin n → Fin n // Monotone e}

/-- The permutation module's orthonormal word/coset coordinates (PDF pp.9,11).
Different permutations of E0 give the same index exactly for the same coset. -/
def ModuleWord {n : ℕ} (T : PermutationType n) :=
  {w : Fin n → Fin n // ∃ g : Equiv.Perm (Fin n), T.val ∘ g.symm = w}

/-- Enumerate exactly the orbit-word subtype of the finite word space. -/
instance moduleWordFintype {n : ℕ} (T : PermutationType n) :
    Fintype (ModuleWord T) := by
  classical
  unfold ModuleWord
  infer_instance

/-- Stabilizer Y_T of the sorted word, hence a product of symmetric groups
on consecutive label-position blocks (PDF pp.9,11). -/
def youngSubgroup {n : ℕ} (T : PermutationType n) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter fun g => T.val ∘ g.symm = T.val

/-- Normalized coset-state embedding J_T; this includes the uniform subgroup
ancilla |Y_T|^(-1/2), not the unnormalized subgroup sum of Lemma 2 (p.11). -/
def cosetEmbedding {n : ℕ} (T : PermutationType n) :
    Matrix (Equiv.Perm (Fin n)) (ModuleWord T) ℂ :=
  fun g w => if T.val ∘ g.symm = w.val then
    ((Real.sqrt ((youngSubgroup T).card : ℝ))⁻¹ : ℂ) else 0

/-- Exact action of the QFTPermMod circuit on its promised coset input:
F_(S_n) J_T. Coherent right-Y_T GPE has the trivial label and leaves J_T
unchanged; its clean trivial ancilla is implicit (PDF pp.13-14). -/
def qftPermMod {n : ℕ} (Y : SymmetricModels n) (T : PermutationType n) :
    Matrix (YoungFourierIndex n) (ModuleWord T) ℂ :=
  symmetricFourier Y * cosetEmbedding T

/-- Actual permutation action on the module words (PDF pp.9,11). -/
def moduleAction {n : ℕ} (T : PermutationType n) (g : Equiv.Perm (Fin n)) :
    Matrix (ModuleWord T) (ModuleWord T) ℂ :=
  fun x y => if x.val = y.val ∘ g.symm then 1 else 0

/-- Left symmetric action in the padded Fourier register (PDF pp.10,13). -/
def youngFourierAction {n : ℕ} (Y : SymmetricModels n) (g : Equiv.Perm (Fin n))
    (v : EuclideanSpace ℂ (YoungFourierIndex n)) : EuclideanSpace ℂ (YoungFourierIndex n) :=
  WithLp.toLp 2 fun z => ∑ U : StandardTableau n z.1.val,
    (Y z.1).rho g z.2.1 U * v ⟨z.1,(U,z.2.2)⟩

/-- Explicit base-(n+1) word and type encoding (PDF pp.9,13). -/
def moduleWordCode {n : ℕ} (w : Fin n → Fin n) : ℕ :=
  ∑ i : Fin n, (w i).val * (n + 1) ^ i.val

/-- Request for a permutation module. Unary entries of E0 add O(n^2)
bits, so polynomial-time generation remains polynomial in n and t (p.13). -/
def moduleRequest {n : ℕ} (T : PermutationType n) (t : ℕ) : List Bool :=
  requestCode n 1 t ++ QAlgorithms.Complexity.encStr
    ((List.ofFn T.val).map fun i => QAlgorithms.Complexity.encNat i.val)

/-- Contiguous sets of numbered labels, including empty and singleton sets
(PDF p.15, Lemma 2). Source labels 1,...,n correspond to Fin n. -/
def IsConsecutive {n : ℕ} (A : Finset (Fin n)) : Prop :=
  ∀ i ∈ A, ∀ j ∈ A, ∀ k : Fin n, i ≤ k → k ≤ j → k ∈ A

/-- S_A fixes every label outside A, and otherwise permits all permutations
(PDF p.15). No arbitrary subgroup or subgroup invariance is assumed. -/
def permutationsOn {n : ℕ} (A : Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter fun g => ∀ i : Fin n, i ∉ A → g i = i

/-- Unnormalized group-algebra symmetrizer sum_(g in S_A) lambda(g),
exactly the Lemma 2 convention, not (3.2)'s average (PDF p.15). -/
def subgroupSum {n : ℕ} {lambda : YoungDiagram}
    (Y : YoungModel n lambda) (A : Finset (Fin n)) :
    Matrix (StandardTableau n lambda) (StandardTableau n lambda) ℂ :=
  ∑ g ∈ permutationsOn A, Y.rho g

/-- Bounded-alphabet SSYTs, using the accepted row/column predicate
(PDF pp.6-9). These fillings label physical U(d) factors. -/
def SemistandardTableau {d n : ℕ} (lambda : QAlgorithms.Schur.Partition d n) :=
  {S : lambda.val.cells → Fin d // QAlgorithms.Schur.IsSemistandardFilling lambda S}

/-- Enumerate bounded-alphabet fillings satisfying the semistandard predicate. -/
instance semistandardTableauFintype {d n : ℕ} (lambda : QAlgorithms.Schur.Partition d n) :
    Fintype (SemistandardTableau lambda) := by
  classical
  unfold SemistandardTableau
  infer_instance

/-- First k alphabet coordinates are the fixed U(k) minor; all other
coordinates are identity (PDF pp.5-8). k≤d is required by the caller. -/
def alphabetMinor {d k : ℕ} (U : Matrix (Fin k) (Fin k) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun i j => if hi : i.val < k then
    if hj : j.val < k then U ⟨i.val,hi⟩ ⟨j.val,hj⟩ else 0
  else if j.val < k then 0 else if i = j then 1 else 0

/-- The actual subdiagram of boxes carrying letters below k, expressed as
a finite set so no arbitrary GT path is substituted (PDF pp.5-8). -/
def gtPrefixCells {d n : ℕ} {lambda : QAlgorithms.Schur.Partition d n}
    (S : SemistandardTableau lambda) (k : ℕ) : Finset (ℕ × ℕ) :=
  lambda.val.cells.filter fun c => ∃ h : c ∈ lambda.val.cells, (S.val ⟨c,h⟩).val < k

/-- Physical GT tower adaptation, not just SSYT names or weight labels.
For every k, the named vector belongs to a copy of the actual polynomial
U(k) module of its prefix shape, with an injective isometric intertwiner
into the fixed physical Schur factor (PDF pp.5-9,17-19). Branching is
multiplicity-free, so all these prefix conditions specify the GT line. -/
def IsPhysicalGTBasis {d n : ℕ} (lambda : QAlgorithms.Schur.Partition d n)
    (B : OrthonormalBasis (SemistandardTableau lambda) ℂ (QAlgorithms.Schur.schurModule lambda)) : Prop :=
  ∀ (S : SemistandardTableau lambda) k, 0 < k → k ≤ d →
    ∃ m : ℕ, ∃ mu : QAlgorithms.Schur.Partition k m,
      mu.val.cells = gtPrefixCells S k ∧
      ∃ e : QAlgorithms.Schur.schurModule mu →ₗᵢ[ℂ] QAlgorithms.Schur.schurModule lambda,
        B S ∈ Set.range e ∧
        ∀ (U : Matrix.unitaryGroup (Fin k) ℂ) v,
          e (QAlgorithms.Schur.polynomialRepresentation mu U.val v) =
            QAlgorithms.Schur.polynomialRepresentation lambda
              (alphabetMinor (d := d) (k := k) U.val) (e v)

/-- Strong Schur output coordinates: shape, symmetric Young coordinate,
and physical unitary GT coordinate (PDF pp.9,16). -/
abbrev StrongIndex (n d : ℕ) :=
  (lambda : QAlgorithms.Schur.Partition d n) ×
    (StandardTableau n lambda.val × SemistandardTableau lambda)

/-- Exact simultaneous strong Schur transform with actual polynomial factors
and both intertwining identities, not arbitrary labels on a decomposition
(PDF pp.5-9,16). All basis phases are fields fixed before precision. -/
structure StrongSchurFrame (n d : ℕ) where
  young : (lambda : QAlgorithms.Schur.Partition d n) → YoungModel n lambda.val
  unitaryBasis : (lambda : QAlgorithms.Schur.Partition d n) →
    OrthonormalBasis (SemistandardTableau lambda) ℂ (QAlgorithms.Schur.schurModule lambda)
  gt : ∀ lambda, IsPhysicalGTBasis lambda (unitaryBasis lambda)
  transform : EuclideanSpace ℂ (Fin n → Fin d) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (StrongIndex n d)
  symmetricIntertwining : ∀ (g : Equiv.Perm (Fin n)) v (z : StrongIndex n d),
    transform (QAlgorithms.act (QAlgorithms.Schur.tensorPermutation d n g) v) z =
      ∑ T : StandardTableau n z.1.val,
        (young z.1).rho g z.2.1 T * transform v ⟨z.1,(T,z.2.2)⟩
  unitaryIntertwining : ∀ (U : Matrix.unitaryGroup (Fin d) ℂ) v (z : StrongIndex n d),
    transform (QAlgorithms.act (QAlgorithms.piKron n (U : Matrix _ _ ℂ)) v) z =
      ∑ S : SemistandardTableau z.1,
        inner ℂ (unitaryBasis z.1 z.2.2)
          (QAlgorithms.Schur.polynomialRepresentation z.1 (U : Matrix _ _ ℂ)
            (unitaryBasis z.1 S)) * transform v ⟨z.1,(z.2.1,S)⟩

/-- Matrix of the fixed exact frame, with no input-dependent phase quotient
(PDF pp.9-10). -/
def strongMatrix {n d : ℕ} (F : StrongSchurFrame n d) :
    Matrix (StrongIndex n d) (Fin n → Fin d) ℂ :=
  fun z w => F.transform (QAlgorithms.ket w) z

/-- Fixed positional input encoding in the one-qudit alphabet (PDF pp.9,16). -/
def tensorWordCode {n d : ℕ} (w : Fin n → Fin d) : ℕ :=
  ∑ i : Fin n, (w i).val * d ^ i.val

/-- A reversible serialization of a Young/GT label, not a purported
amplitude-changing SSYT compression (PDF pp.6,9,16). T determines the shape
and orders its cells; entries of S are then serialized in base d. -/
def strongCode {n d : ℕ} (z : StrongIndex n d) : ℕ :=
  Nat.pair (tableauCode z.2.1)
    (∑ i : Fin n, (z.2.2.val (z.2.1.val i)).val * d ^ i.val)

/-- Definition sanity examples; result proofs are intentionally absent. -/

example : boxContent (1,0) = -1 := by norm_num [boxContent]

example : boxContent (0,1) = 1 := by norm_num [boxContent]

example {n : ℕ} {lambda : YoungDiagram} (i j : Fin n)
    (T U : StandardTableau n lambda) (h : (T.val i).val.1 = (T.val j).val.1) :
    youngCoefficient i j T U = (if U = T then 1 else 0) := by
  simp [youngCoefficient,h]

example (q : ℕ) (v : EuclideanSpace ℂ (QAlgorithms.Qubits q)) :
    (CompiledCircuit.mk q []).run v = v := rfl

example {n : ℕ} (A : Finset (Fin n)) : (1 : Equiv.Perm (Fin n)) ∈ permutationsOn A := by
  simp [permutationsOn]

example {n : ℕ} (T : PermutationType n) : (1 : Equiv.Perm (Fin n)) ∈ youngSubgroup T := by
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, by funext i; rfl⟩

example {G C : Type*} [Group G] [Fintype G] [Fintype C]
    (H : Subgroup G) [Fintype H] (T : LeftTransversal H C)
    (DG : FourierData G) (DH : FourierData H) (sigma : Fin DH.labels)
    (u : Fin (DH.dimension sigma)) :
    inducedFourier H T DG DH sigma u =
      groupFourier DG * inducedEmbedding H T DH sigma u := rfl

example {n : ℕ} (Y : SymmetricModels n) (T : PermutationType n) :
    qftPermMod Y T = symmetricFourier Y * cosetEmbedding T := rfl

example {d n : ℕ} {lambda : QAlgorithms.Schur.Partition d n}
    (S : SemistandardTableau lambda) : gtPrefixCells S 0 = ∅ := by
  ext c
  simp [gtPrefixCells]

example (d : ℕ) :
    alphabetMinor (d := d) (k := 0) (1 : Matrix (Fin 0) (Fin 0) ℂ) = 1 := by
  ext i j
  simp [alphabetMinor, Matrix.one_apply]

example {n d : ℕ} (F : StrongSchurFrame n d)
    (v : EuclideanSpace ℂ (Fin n → Fin d)) : ‖F.transform v‖ = ‖v‖ :=
  F.transform.norm_map v

end QAlgorithms.Papers.Independent.Extend50.P24


