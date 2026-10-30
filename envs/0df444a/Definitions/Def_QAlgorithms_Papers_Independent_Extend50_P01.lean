-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P01
-- name    : QAlgorithms_Papers_Independent_Extend50_P01
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T22:28:25.339506+00:00
-- url     : https://prove2.me/theorems/d61ef01f-44c8-48a9-a761-e2f4672ad5e5
-- title:
--   Definitions for Exploiting symmetry in variational quantum machine learning
-- statement:
--   The objects the formalized statements of *Exploiting symmetry in variational quantum machine learning* (arXiv:2205.06217) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `finiteTwirl`: PDF p.8, Eq.(52): normalized finite average.
--   - `operatorHaarAverage`: PDF p.8, Eq.(53): Haar integral; the projection theorem supplies integrability.
--   - `tensorLocal`: PDF p.5, Eq.(19): tensor product in the frozen wire convention.
--   - `axis`: PDF p.5: axis order X,Y,Z.
--   - `localEncoding`: PDF p.5, Eq.(19): tensor product of half-angle Pauli rotations.
--   - `permMatrix`: PDF pp.4–6: computational-basis permutation matrix.
--   - `featurePullback`: PDF p.5, Eq.(18): inverse pullback supplies a consistent left action.
--   - `wirePerm`: PDF p.5, Eq.(20): inverse pullback on bit strings.
--   - `wireMatrix`: PDF p.5, Eq.(20): wire-permutation unitary matrix.
--   - `SignedPerm`: PDF p.5, footnote 2: permutation and sign mask.
--   - `signedMul`: PDF p.5: explicit semidirect multiplication.
--   - `signedInv`: PDF p.5: inverse for the semidirect multiplication.
--   - `signedData`: PDF p.5: signed coordinate action.
--   - `signedMatrix`: PDF p.5: wire permutations followed by local X gates.
--   - `kleinMul`: PDF p.4, Eq.(7): multiplication of exchange/sign bits.
--   - `kleinData`: PDF p.4: action on the two real features.
--   - `kleinMatrix`: PDF p.4, Eqs.(16),(17): all four specified matrices.
--   - `kleinEncoding`: PDF p.4, Eq.(10): two-qubit embedding.
--   - `zWord`: PDF p.5: squarefree Z word, including identity at empty support.
--   - `extraGenerator`: PDF p.5: local-Z generators and the additional full Z word.
--   - `extraEncoding`: PDF p.5: d+1-feature encoding.
--   - `extraSwap`: PDF p.5, corrected controls: every other wire controls target i.
--   - `balancedEncoding`: PDF p.5: balanced three-feature encoding.
--   - `axisHadamard`: PDF p.5, Eqs.(21)–(23): retains the printed -i Hadamard phase.
--   - `supportOrbit`: PDF p.5: distinct squarefree supports in a subgroup orbit.
--   - `monomialEncoding`: PDF p.5: matched monomials and commuting Z words over the complete orbit.
--   - `basisEncoding`: PDF pp.5–6, Eq.(24): independent basis phase features.
--   - `featureMatrix`: PDF p.6, Eq.(25): unused basis labels are fixed.
--   - `inversionEncoding`: PDF p.7, Eq.(35): inversion embedding with the specified tensor placement.
--   - `reupload`: PDF pp.10–11, Eq.(68): W_L E ... W_1 E W_0, including L=0.
--   - `involutionTwirl`: PDF pp.8–9: normalized twirl by an order-two unitary.
--   - `twoGateSet`: PDF pp.8–9, Eq.(55): the seven original generators.
--   - `boardRotation`: PDF p.12, Fig.3: clockwise perimeter shift by two; center 8 is fixed.
--   - `boardReflection`: PDF p.12: the specified vertical reflection SWAP02 SWAP73 SWAP64.
--   - `boardGroup`: PDF pp.11–12: the actual D4 subgroup on the nine labeled wires.
--   - `vehicleGroup`: PDF pp.14–15: rotations alone generate the vehicle C4 group.
--   - `vertexClass`: PDF p.12: center, corners, and edges, indexed 0,1,2 for subsequent formulas.
--   - `vertexOrbit`: PDF pp.12,19: explicit vertex orbits.
--   - `clockwiseEdges`: PDF pp.12,15: clockwise corner-to-edge pairs.
--   - `counterEdges`: PDF pp.12,15: counterclockwise corner-to-edge pairs.
--   - `inwardEdges`: PDF p.12: edges control the center.
--   - `diagonalEdges`: PDF p.12: the center controls the corners.
--   - `controlledGenerator`: PDF p.12: generator of a controlled rotation; all spectators are identities.
--   - `controlledOrbit`: PDF pp.12,15: an entire commuting controlled-rotation orbit, one shared half-angle. Each source orbit has disjoint sets of control and target sites, so its gates commute.
--   - `boardSingle`: PDF p.12, Fig.3: RY(theta_2) RX(theta_1), with two real angles shared within each of the three vertex classes. The rightmost X rotation acts first.
--   - `boardLayer`: PDF p.12: one complete cemoid block, with chronological order c,e,m,o,i,d.
--   - `vehicleLayer`: PDF p.15: CRZ vehicle block; clockwise and counterclockwise coordinates are independent.
--   - `learningCircuit`: PDF pp.12–15: repeated data embeddings, each followed by the specified block list.
--   - `boardObservable`: PDF p.13, Eqs.(88)–(90): the circle, draw, cross observable vector, with 1/4 averages.
--   - `boardPrediction`: PDF pp.12–13: the complete real prediction vector, before an unspecified tie rule.
--   - `vehiclePrediction`: PDF p.15, Eq.(92): normalized central-Z vehicle regression.
--   - `nextSite`: PDF p.16, Eq.(94): cyclic successor; only used with a positive chain length.
--   - `axisSum`: PDF pp.16–18: sum of one-site axis generators.
--   - `tfim`: PDF p.16, Eq.(94): periodic ferromagnetic TFIM, including literal Z_i^2 at n=1.
--   - `plusState`: PDF p.17: normalized all-plus input.
--   - `qaoa`: PDF p.17, Eq.(97): QAOA matrix product, no half-angle factor.
--   - `twirledQaoa`: PDF p.17, Eq.(98): every generator of QAOA-prime is parity-twirled.
--   - `SU2`: PDF p.17, Eq.(100): the native determinant-one qubit unitary group.
--   - `heisenberg`: PDF p.17, Eq.(99): periodic antiferromagnetic isotropic chain.
--   - `singletProduct`: PDF p.18, Eq.(101): neighboring normalized singlets on sites (0,1),(2,3),... .
--   - `totalSpinSquared`: PDF pp.17–18: the usual total-spin squared, sum of the squares of collective half-Paulis.
--   - `collectiveTwirl`: PDF p.18, Eq.(104): normalized collective SU(2) Haar average.
--   - `bondHamiltonian`: PDF p.18, Eq.(103): zero-based bond starts 0,2,... for even, and 1,3,... for odd.
--   - `twirledHeisenbergLayer`: PDF p.18, corrected Eq.(102): one Y-mixer and one even and one odd block per layer.
--   - `isotropicLayer`: PDF p.18, corrected Eq.(110): one isotropic even and one isotropic odd block.
--   - `reduceHeisenberg`: PDF p.18: the two surviving coordinates are the means of the three anisotropies.
--   - `HeisenbergParameters`: PDF p.18: source parameter coordinates, not a claim about minimal functional dimension.
--   - `latticeEdges`: PDF p.19, Fig.12: contour, inside, diagonal undirected edges, represented once each.
--   - `latticeInteraction`: PDF p.19, Eqs.(112),(113): the sum of ZZ interactions in a fixed orbit.
--   - `latticeHamiltonian`: PDF p.19, Eqs.(111),(112): weights 1,1/2,3/2 on the fixed Fig.12 graph.
--   - `orbitLocal`: PDF pp.19–20: averaged local generator on one vertex orbit.
--   - `orbitInteraction`: PDF pp.19–20: average ZZ generator in one edge orbit.
--   - `boardTwirl`: PDF pp.19–20: finite D4 average over the actual board subgroup.
--   - `latticeLayer`: PDF pp.19–20: one shared angle for each ZZ edge orbit and each X/Z vertex orbit.
--   - `LatticeOriginalParameters`: PDF p.20: named parameter slots of the unrestricted ansatz.
--   - `LatticeSymmetricParameters`: PDF p.20: named parameter slots of the shared orbit ansatz.
-- source:
--   Exploiting symmetry in variational quantum machine learning, arXiv:2205.06217v1, https://arxiv.org/abs/2205.06217v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P49
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P33

/-! Statements from Meyer et al., arXiv:2205.06217v1. All page numbers are PDF pages.
Paper-local constructions below supplement the frozen register, state and Pauli conventions.
Source corrections and deferred claims are recorded in the accompanying audit artifacts. -/

noncomputable section

open scoped Matrix Kronecker ComplexConjugate Matrix.Norms.L2Operator Manifold ContDiff
open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P01

attribute [local instance] Classical.propDecidable Classical.decEq

-- PDF pp.3,8: reuse the accepted operator type, exp(-itH), and A X A†.
-- Notation specializes the imported interfaces without introducing duplicate declarations.
local notation "Op" => (fun n : ℕ => QAlgorithms.Papers.Independent.Information100.P21.Op (Qubits n))

local notation "evolve" => QAlgorithms.Papers.Independent.Information100.P32.evolution

local notation "conjugate" => QAlgorithms.conjSuperop

-- PDF pp.3,10–11: the imported quadratic form is Re(psi† A psi).
local notation "expectation" => QAlgorithms.Papers.Independent.Information100.P21.quad

-- PDF pp.5,16–19: accepted active-wire operator, with identities on all spectators.
local notation "onWire" => QAlgorithms.Papers.Independent.Advance50.P49.onWire

-- PDF p.5: the imported phase-free Pauli tensor uses 0=I,1=X,2=Y,3=Z.
local notation "pauliWord" => QAlgorithms.Papers.Independent.Gap48.P33.pauliWord

/-- PDF p.8, Eq.(52): normalized finite average. -/
def finiteTwirl {S ι : Type*} [Fintype S] [Fintype ι]
    (U : S → Matrix ι ι ℂ) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (Fintype.card S : ℂ)⁻¹ • ∑ s, conjugate (U s) A

/-- PDF p.8, Eq.(53): Haar integral; the projection theorem supplies integrability. -/
def operatorHaarAverage {S ι : Type*} [MeasurableSpace S] [Fintype ι]
    (mu : Measure S) (U : S → Matrix ι ι ℂ) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ∫ s, conjugate (U s) A ∂mu

/-- PDF p.5, Eq.(19): tensor product in the frozen wire convention. -/
def tensorLocal {n : ℕ} (A : Fin n → Matrix Bool Bool ℂ) : Op n :=
  fun a b => ∏ i, A i (a i) (b i)

/-- PDF p.5: axis order X,Y,Z. -/
def axis (a : Fin 3) : Matrix Bool Bool ℂ := ![pauliX, pauliY, pauliZ] a

/-- PDF p.5, Eq.(19): tensor product of half-angle Pauli rotations. -/
def localEncoding {n : ℕ} (A : Matrix Bool Bool ℂ) (x : Fin n → ℝ) : Op n :=
  tensorLocal (fun i => evolve A (x i / 2))

/-- PDF pp.4–6: computational-basis permutation matrix. -/
def permMatrix {ι : Type*} [DecidableEq ι] (p : Equiv.Perm ι) : Matrix ι ι ℂ :=
  fun a b => if a = p b then 1 else 0

/-- PDF p.5, Eq.(18): inverse pullback supplies a consistent left action. -/
def featurePullback {n : ℕ} (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => x (p.symm i)

/-- PDF p.5, Eq.(20): inverse pullback on bit strings. -/
def wirePerm {n : ℕ} (p : Equiv.Perm (Fin n)) : Equiv.Perm (Qubits n) where
  toFun b := fun i => b (p.symm i)
  invFun b := fun i => b (p i)
  left_inv b := by funext i; simp
  right_inv b := by funext i; simp

/-- PDF p.5, Eq.(20): wire-permutation unitary matrix. -/
def wireMatrix {n : ℕ} (p : Equiv.Perm (Fin n)) : Op n := permMatrix (wirePerm p)

/-- PDF p.5, footnote 2: permutation and sign mask. -/
abbrev SignedPerm (n : ℕ) := Equiv.Perm (Fin n) × (Fin n → Bool)

/-- PDF p.5: explicit semidirect multiplication. -/
def signedMul {n : ℕ} (g h : SignedPerm n) : SignedPerm n :=
  (g.1 * h.1, fun i => xor (g.2 i) (h.2 (g.1.symm i)))

/-- PDF p.5: inverse for the semidirect multiplication. -/
def signedInv {n : ℕ} (g : SignedPerm n) : SignedPerm n :=
  (g.1.symm, fun i => g.2 (g.1 i))

/-- PDF p.5: signed coordinate action. -/
def signedData {n : ℕ} (g : SignedPerm n) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (if g.2 i then -1 else 1) * x (g.1.symm i)

/-- PDF p.5: wire permutations followed by local X gates. -/
def signedMatrix {n : ℕ} (g : SignedPerm n) : Op n :=
  fun a b => if a = (fun i => xor (b (g.1.symm i)) (g.2 i)) then 1 else 0

/-- PDF p.4, Eq.(7): multiplication of exchange/sign bits. -/
def kleinMul (a b : Bool × Bool) : Bool × Bool := (xor a.1 b.1, xor a.2 b.2)

/-- PDF p.4: action on the two real features. -/
def kleinData (a : Bool × Bool) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => (if a.2 then -1 else 1) * x (if a.1 then (Equiv.swap 0 1) i else i)

/-- PDF p.4, Eqs.(16),(17): all four specified matrices. -/
def kleinMatrix (a : Bool × Bool) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  (if a.1 then swapGate else 1) * (if a.2 then pauliX ⊗ₖ pauliX else 1)

/-- PDF p.4, Eq.(10): two-qubit embedding. -/
def kleinEncoding (x : Fin 2 → ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  evolve pauliZ (x 0 / 2) ⊗ₖ evolve pauliZ (x 1 / 2)

/-- PDF p.5: squarefree Z word, including identity at empty support. -/
def zWord {n : ℕ} (A : Finset (Fin n)) : Op n :=
  Matrix.diagonal (fun b => ∏ i ∈ A, if b i then (-1 : ℂ) else 1)

/-- PDF p.5: local-Z generators and the additional full Z word. -/
def extraGenerator {d : ℕ} (k : Fin (d + 1)) : Op d :=
  if h : k.val < d then onWire ⟨k.val, h⟩ pauliZ else zWord Finset.univ

/-- PDF p.5: d+1-feature encoding. -/
def extraEncoding {d : ℕ} (x : Fin (d + 1) → ℝ) : Op d :=
  evolve (∑ k, (x k : ℂ) • extraGenerator k) (1 / 2)

/-- PDF p.5, corrected controls: every other wire controls target i. -/
def extraSwap {d : ℕ} (i : Fin d) : Op d :=
  fun a b => if a = (fun j => if j = i then
    xor (b i) (∑ k ∈ Finset.univ.erase i, b k) else b j) then 1 else 0

/-- PDF p.5: balanced three-feature encoding. -/
def balancedEncoding (x : Fin 3 → ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  evolve (∑ a, (x a : ℂ) • (axis a ⊗ₖ axis a)) (1 / 2)

/-- PDF p.5, Eqs.(21)–(23): retains the printed -i Hadamard phase. -/
def axisHadamard (a b : Fin 3) : Matrix Bool Bool ℂ :=
  evolve (axis a + axis b) (Real.pi / (2 * Real.sqrt 2))

/-- PDF p.5: distinct squarefree supports in a subgroup orbit. -/
def supportOrbit {d : ℕ} (K : Subgroup (Equiv.Perm (Fin d)))
    (A : Finset (Fin d)) : Finset (Finset (Fin d)) :=
  ((Finset.univ : Finset (Equiv.Perm (Fin d))).filter (fun s => s ∈ K)).image
    (fun s => A.image s)

/-- PDF p.5: matched monomials and commuting Z words over the complete orbit. -/
def monomialEncoding {d : ℕ} (K : Subgroup (Equiv.Perm (Fin d)))
    (A : Finset (Fin d)) (x : Fin d → ℝ) : Op d :=
  evolve (∑ B ∈ supportOrbit K A, ((∏ i ∈ B, x i : ℝ) : ℂ) • zWord B) (1 / 2)

/-- PDF pp.5–6, Eq.(24): independent basis phase features. -/
def basisEncoding {n m : ℕ} (e : Fin m ↪ Qubits n) (x : Fin m → ℝ) : Op n :=
  evolve (∑ k, (x k : ℂ) • Matrix.single (e k) (e k) 1) 1

/-- PDF p.6, Eq.(25): unused basis labels are fixed. -/
def featureMatrix {n m : ℕ} (e : Fin m ↪ Qubits n)
    (s : Equiv.Perm (Fin m)) : Op n := permMatrix (s.viaEmbedding e)

/-- PDF p.7, Eq.(35): inversion embedding with the specified tensor placement. -/
def inversionEncoding (x : Fin 3 → ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  evolve ((∑ a, (x a : ℂ) • axis a) ⊗ₖ pauliX) (1 / 2)

/-- PDF pp.10–11, Eq.(68): W_L E ... W_1 E W_0, including L=0. -/
def reupload {n : ℕ} (E : Op n) (W : List (Op n)) : Op n :=
  match W with
  | [] => 1
  | W0 :: rest => (rest.map (fun A => A * E)).reverse.prod * W0

example {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) : evolve A 0 = 1 := by
  simp [QAlgorithms.Papers.Independent.Information100.P32.evolution]

example (x : Fin 0 → ℝ) : localEncoding pauliZ x = (1 : Op 0) := by
  ext a b
  have h : a = b := Subsingleton.elim _ _
  subst b
  simp [localEncoding, tensorLocal]

example (E W0 : Op 2) : reupload E [W0] = W0 := by simp [reupload]

example : kleinMatrix (false, false) = 1 := by simp [kleinMatrix]

example {n : ℕ} : zWord (∅ : Finset (Fin n)) = 1 := by simp [zWord]

example (A : Op 1) : finiteTwirl (fun _ : Unit => (1 : Op 1)) A = A := by
  simp [finiteTwirl, QAlgorithms.conjSuperop]

example {S : Type*} [MeasurableSpace S] (mu : Measure S) (U : S → Op 1) :
    operatorHaarAverage mu U 0 = 0 := by simp [operatorHaarAverage, QAlgorithms.conjSuperop]

example {n : ℕ} (x : Fin n → ℝ) : signedData (1, fun _ => false) x = x := by
  funext i
  change (1 : ℝ) * x i = x i
  exact one_mul _

example {n m : ℕ} (e : Fin m ↪ Qubits n) : basisEncoding e (fun _ => 0) = 1 := by
  simp [basisEncoding, QAlgorithms.Papers.Independent.Information100.P32.evolution]

example {d : ℕ} : extraGenerator (Fin.last d) = zWord (Finset.univ : Finset (Fin d)) := by
  simp [extraGenerator]

example : inversionEncoding (fun _ => 0) = 1 := by simp [inversionEncoding, QAlgorithms.Papers.Independent.Information100.P32.evolution]

/-- PDF pp.8–9: normalized twirl by an order-two unitary. -/
def involutionTwirl {ι : Type*} [Fintype ι] (V A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (1 / 2 : ℂ) • (A + conjugate V A)

/-- PDF pp.8–9, Eq.(55): the seven original generators. -/
def twoGateSet : Set (Matrix (Bool × Bool) (Bool × Bool) ℂ) :=
  Set.range (fun a : Fin 3 => axis a ⊗ₖ (1 : Matrix Bool Bool ℂ)) ∪
  Set.range (fun a : Fin 3 => (1 : Matrix Bool Bool ℂ) ⊗ₖ axis a) ∪ {pauliZ ⊗ₖ pauliZ}

/-- PDF p.12, Fig.3: clockwise perimeter shift by two; center 8 is fixed. -/
def boardRotation : Equiv.Perm (Fin 9) :=
  (Equiv.swap 0 2 * Equiv.swap 2 4 * Equiv.swap 4 6) *
  (Equiv.swap 1 3 * Equiv.swap 3 5 * Equiv.swap 5 7)

/-- PDF p.12: the specified vertical reflection SWAP02 SWAP73 SWAP64. -/
def boardReflection : Equiv.Perm (Fin 9) := Equiv.swap 0 2 * Equiv.swap 7 3 * Equiv.swap 6 4

/-- PDF pp.11–12: the actual D4 subgroup on the nine labeled wires. -/
def boardGroup : Subgroup (Equiv.Perm (Fin 9)) := Subgroup.closure {boardRotation, boardReflection}

/-- PDF pp.14–15: rotations alone generate the vehicle C4 group. -/
def vehicleGroup : Subgroup (Equiv.Perm (Fin 9)) := Subgroup.zpowers boardRotation

/-- PDF p.12: center, corners, and edges, indexed 0,1,2 for subsequent formulas. -/
def vertexClass (i : Fin 9) : Fin 3 := if i = 8 then 0 else if i.val % 2 = 0 then 1 else 2

/-- PDF pp.12,19: explicit vertex orbits. -/
def vertexOrbit (a : Fin 3) : Finset (Fin 9) := Finset.univ.filter (fun i => vertexClass i = a)

/-- PDF pp.12,15: clockwise corner-to-edge pairs. -/
def clockwiseEdges : Finset (Fin 9 × Fin 9) := {(0,1),(2,3),(4,5),(6,7)}

/-- PDF pp.12,15: counterclockwise corner-to-edge pairs. -/
def counterEdges : Finset (Fin 9 × Fin 9) := {(0,7),(2,1),(4,3),(6,5)}

/-- PDF p.12: edges control the center. -/
def inwardEdges : Finset (Fin 9 × Fin 9) := {(1,8),(3,8),(5,8),(7,8)}

/-- PDF p.12: the center controls the corners. -/
def diagonalEdges : Finset (Fin 9 × Fin 9) := {(8,0),(8,2),(8,4),(8,6)}

/-- PDF p.12: generator of a controlled rotation; all spectators are identities. -/
def controlledGenerator (a : Matrix Bool Bool ℂ) (e : Fin 9 × Fin 9) : Op 9 :=
  onWire e.1 (Matrix.diagonal (fun b => if b then (1 : ℂ) else 0)) * onWire e.2 a

/-- PDF pp.12,15: an entire commuting controlled-rotation orbit, one shared half-angle.
Each source orbit has disjoint sets of control and target sites, so its gates commute. -/
def controlledOrbit (a : Matrix Bool Bool ℂ) (edges : Finset (Fin 9 × Fin 9)) (theta : ℝ) : Op 9 :=
  evolve (∑ e ∈ edges, controlledGenerator a e) (theta / 2)

example (a : Matrix Bool Bool ℂ) (theta : ℝ) : controlledOrbit a ∅ theta = 1 := by
  simp [controlledOrbit, QAlgorithms.Papers.Independent.Information100.P32.evolution]

/-- PDF p.12, Fig.3: RY(theta_2) RX(theta_1), with two real angles shared
within each of the three vertex classes. The rightmost X rotation acts first. -/
def boardSingle (angles : Fin 3 → Fin 2 → ℝ) : Op 9 :=
  tensorLocal (fun i => evolve pauliY (angles (vertexClass i) 1 / 2) *
    evolve pauliX (angles (vertexClass i) 0 / 2))

example : boardSingle (fun _ _ => 0) (fun _ => false) (fun _ => false) = 1 := by
  simp [boardSingle, tensorLocal, QAlgorithms.Papers.Independent.Information100.P32.evolution]

/-- PDF p.12: one complete cemoid block, with chronological order c,e,m,o,i,d. -/
def boardLayer (p : (Fin 3 → Fin 2 → ℝ) × (Fin 3 → ℝ)) : Op 9 :=
  controlledOrbit pauliY diagonalEdges (p.2 2) * controlledOrbit pauliY inwardEdges (p.2 1) *
    controlledOrbit pauliY (clockwiseEdges ∪ counterEdges) (p.2 0) * boardSingle p.1

/-- PDF p.15: CRZ vehicle block; clockwise and counterclockwise coordinates are independent. -/
def vehicleLayer (p : (Fin 3 → Fin 2 → ℝ) × (Fin 4 → ℝ)) : Op 9 :=
  controlledOrbit pauliZ diagonalEdges (p.2 3) * controlledOrbit pauliZ inwardEdges (p.2 2) *
    controlledOrbit pauliZ counterEdges (p.2 1) * controlledOrbit pauliZ clockwiseEdges (p.2 0) *
    boardSingle p.1

/-- PDF pp.12–15: repeated data embeddings, each followed by the specified block list. -/
def learningCircuit {P : Type*} (layer : P → Op 9) (W : List (List P)) (x : Fin 9 → ℝ) : Op 9 :=
  (W.map (fun block => (block.map layer).reverse.prod *
    localEncoding pauliX (fun i => (2 * Real.pi / 3) * x i))).reverse.prod

/-- PDF p.13, Eqs.(88)–(90): the circle, draw, cross observable vector, with 1/4 averages. -/
def boardObservable (a : Fin 3) : Op 9 :=
  ![(1 / 4 : ℂ) • ∑ i ∈ vertexOrbit 1, onWire i pauliZ,
    onWire (8 : Fin 9) pauliZ,
    (1 / 4 : ℂ) • ∑ i ∈ vertexOrbit 2, onWire i pauliZ] a

/-- PDF pp.12–13: the complete real prediction vector, before an unspecified tie rule. -/
def boardPrediction (W : List (List ((Fin 3 → Fin 2 → ℝ) × (Fin 3 → ℝ))))
    (x : Fin 9 → ℝ) : Fin 3 → ℝ :=
  fun a => expectation (boardObservable a) (act (learningCircuit boardLayer W x) (zeroKet 9))

/-- PDF p.15, Eq.(92): normalized central-Z vehicle regression. -/
def vehiclePrediction (W : List (List ((Fin 3 → Fin 2 → ℝ) × (Fin 4 → ℝ))))
    (x : Fin 9 → ℝ) : ℝ :=
  (expectation (onWire (8 : Fin 9) pauliZ) (act (learningCircuit vehicleLayer W x) (zeroKet 9)) + 1) / 2

example : boardReflection (0 : Fin 9) = 2 := by decide

example : vertexClass (8 : Fin 9) = 0 := by rfl

example {P : Type*} (layer : P → Op 9) (x : Fin 9 → ℝ) : learningCircuit layer [] x = 1 := by
  simp [learningCircuit]

/-- PDF p.16, Eq.(94): cyclic successor; only used with a positive chain length. -/
def nextSite {n : ℕ} (i : Fin n) : Fin n := ⟨(i.val + 1) % n, Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩

/-- PDF pp.16–18: sum of one-site axis generators. -/
def axisSum (n : ℕ) (a : Fin 3) : Op n := ∑ i, onWire i (axis a)

-- PDF p.16, Eq.(95): accepted tensor power, specialized to the global X parity.
local notation "parity" => (fun n : ℕ => QAlgorithms.Papers.Independent.Information100.P69.matrixPower pauliX n)

/-- PDF p.16, Eq.(94): periodic ferromagnetic TFIM, including literal Z_i^2 at n=1. -/
def tfim (n : ℕ) (g : ℝ) : Op n :=
  -(∑ i, onWire i pauliZ * onWire (nextSite i) pauliZ) - (g : ℂ) • axisSum n 0

/-- PDF p.17: normalized all-plus input. -/
def plusState (n : ℕ) : EuclideanSpace ℂ (Qubits n) :=
  WithLp.toLp 2 (fun _ => (((Real.sqrt 2)⁻¹ : ℂ) ^ n))

/-- PDF p.17, Eq.(97): QAOA matrix product, no half-angle factor. -/
def qaoa {n p : ℕ} (beta gamma : Fin p → ℝ) : Op n :=
  (List.ofFn (fun m => evolve (axisSum n 0) (beta m) *
    evolve (∑ i, onWire i pauliZ * onWire (nextSite i) pauliZ) (gamma m))).prod

/-- PDF p.17, Eq.(98): every generator of QAOA-prime is parity-twirled. -/
def twirledQaoa {n p : ℕ} (alpha beta gamma : Fin p → ℝ) : Op n :=
  (List.ofFn (fun m => evolve (involutionTwirl (parity n) (axisSum n 1)) (alpha m) *
    evolve (involutionTwirl (parity n) (axisSum n 0)) (beta m) *
    evolve (involutionTwirl (parity n) (∑ i, onWire i pauliZ * onWire (nextSite i) pauliZ)) (gamma m))).prod

example : nextSite (0 : Fin 1) = 0 := by decide

example (g : ℝ) : tfim 0 g = 0 := by simp [tfim, axisSum]

example (beta gamma : Fin 0 → ℝ) : qaoa (n := 1) beta gamma = 1 := by simp [qaoa]

/-- PDF p.17, Eq.(100): the native determinant-one qubit unitary group. -/
abbrev SU2 := Matrix.specialUnitaryGroup Bool ℂ

/-- PDF p.18, Eq.(104): the Borel sigma-algebra of the native SU(2) topology. -/
local instance su2MeasurableSpace : MeasurableSpace SU2 := borel SU2

/-- PDF p.18, Eq.(104): the chosen sigma-algebra is exactly Borel. -/
local instance su2BorelSpace : BorelSpace SU2 := ⟨rfl⟩

example : (inferInstance : MeasurableSpace SU2) = borel SU2 := by rfl

-- PDF p.17, Eq.(100): the accepted tensor power restricted to determinant-one unitaries.
local notation "collective" => (fun (n : ℕ) (V : SU2) => QAlgorithms.Papers.Independent.Information100.P69.matrixPower (Subtype.val V) n)

/-- PDF p.17, Eq.(99): periodic antiferromagnetic isotropic chain. -/
def heisenberg (n : ℕ) : Op n :=
  ∑ i, ∑ a : Fin 3, onWire i (axis a) * onWire (nextSite i) (axis a)

/-- PDF p.18, Eq.(101): neighboring normalized singlets on sites (0,1),(2,3),... . -/
def singletProduct (k : ℕ) : EuclideanSpace ℂ (Qubits (2 * k)) :=
  WithLp.toLp 2 (fun b => ∏ j : Fin k,
    if b ⟨2 * j.val, by omega⟩ = b ⟨2 * j.val + 1, by omega⟩ then 0
    else if b ⟨2 * j.val, by omega⟩ then -((Real.sqrt 2)⁻¹ : ℂ) else ((Real.sqrt 2)⁻¹ : ℂ))

/-- PDF pp.17–18: the usual total-spin squared, sum of the squares of collective half-Paulis. -/
def totalSpinSquared (n : ℕ) : Op n := ∑ a : Fin 3, ((1 / 2 : ℂ) • axisSum n a) ^ 2

/-- PDF p.18, Eq.(104): normalized collective SU(2) Haar average. -/
def collectiveTwirl (n : ℕ) (mu : Measure SU2) (A : Op n) : Op n := operatorHaarAverage mu (collective n) A

example : singletProduct 0 (fun i : Fin 0 => Fin.elim0 i) = 1 := by
  simp [singletProduct]

/-- PDF p.18, Eq.(103): zero-based bond starts 0,2,... for even, and 1,3,... for odd. -/
def bondHamiltonian (N : ℕ) (par : Fin 2) (b : Fin 3 → ℝ) : Op N :=
  ∑ i ∈ (Finset.univ : Finset (Fin N)).filter (fun i => i.val % 2 = par.val),
    ∑ a : Fin 3, (b a : ℂ) • (onWire i (axis a) * onWire (nextSite i) (axis a))

/-- PDF p.18, corrected Eq.(102): one Y-mixer and one even and one odd block per layer. -/
def twirledHeisenbergLayer (N : ℕ) (mu : Measure SU2) (theta : Fin 7 → ℝ) : Op N :=
  evolve (collectiveTwirl N mu (axisSum N 1)) (theta 0) *
  evolve (collectiveTwirl N mu (bondHamiltonian N 0 (fun a => theta ⟨a.val + 1, by omega⟩))) 1 *
  evolve (collectiveTwirl N mu (bondHamiltonian N 1 (fun a => theta ⟨a.val + 4, by omega⟩))) 1

/-- PDF p.18, corrected Eq.(110): one isotropic even and one isotropic odd block. -/
def isotropicLayer (N : ℕ) (b c : ℝ) : Op N :=
  evolve (bondHamiltonian N 0 (fun _ => 1)) b * evolve (bondHamiltonian N 1 (fun _ => 1)) c

/-- PDF p.18: the two surviving coordinates are the means of the three anisotropies. -/
def reduceHeisenberg (theta : Fin 7 → ℝ) : Fin 2 → ℝ :=
  ![(theta 1 + theta 2 + theta 3) / 3, (theta 4 + theta 5 + theta 6) / 3]

/-- PDF p.18: source parameter coordinates, not a claim about minimal functional dimension. -/
abbrev HeisenbergParameters (p : ℕ) (symmetric : Bool) := Fin p × Fin (if symmetric then 2 else 7)

example (N : ℕ) (mu : Measure SU2) :
    (List.ofFn (fun j : Fin 0 => twirledHeisenbergLayer N mu (fun _ => (j.elim0)))).prod = 1 := by simp

/-- PDF p.19, Fig.12: contour, inside, diagonal undirected edges, represented once each. -/
def latticeEdges (a : Fin 3) : Finset (Fin 9 × Fin 9) :=
  ![clockwiseEdges ∪ counterEdges, inwardEdges, diagonalEdges] a

/-- PDF p.19, Eqs.(112),(113): the sum of ZZ interactions in a fixed orbit. -/
def latticeInteraction (a : Fin 3) : Op 9 :=
  ∑ e ∈ latticeEdges a, onWire e.1 pauliZ * onWire e.2 pauliZ

/-- PDF p.19, Eqs.(111),(112): weights 1,1/2,3/2 on the fixed Fig.12 graph. -/
def latticeHamiltonian : Op 9 := latticeInteraction 0 + (1 / 2 : ℂ) • latticeInteraction 1 +
  (3 / 2 : ℂ) • latticeInteraction 2 + axisSum 9 0 + axisSum 9 2

/-- PDF pp.19–20: averaged local generator on one vertex orbit. -/
def orbitLocal (a : Matrix Bool Bool ℂ) (c : Fin 3) : Op 9 :=
  ((vertexOrbit c).card : ℂ)⁻¹ • ∑ i ∈ vertexOrbit c, onWire i a

/-- PDF pp.19–20: average ZZ generator in one edge orbit. -/
def orbitInteraction (c : Fin 3) : Op 9 :=
  ((latticeEdges c).card : ℂ)⁻¹ • latticeInteraction c

/-- PDF pp.19–20: finite D4 average over the actual board subgroup. -/
def boardTwirl (A : Op 9) : Op 9 :=
  let groupElements := (Finset.univ : Finset (Equiv.Perm (Fin 9))).filter (fun s => s ∈ boardGroup)
  (groupElements.card : ℂ)⁻¹ • ∑ s ∈ groupElements, conjugate (wireMatrix s) A

/-- PDF pp.19–20: one shared angle for each ZZ edge orbit and each X/Z vertex orbit. -/
def latticeLayer (theta : Fin 9 → ℝ) : Op 9 :=
  evolve (∑ c : Fin 3, (theta ⟨c.val + 6, by omega⟩ : ℂ) •
    ∑ i ∈ vertexOrbit c, onWire i pauliZ) (1 / 2) *
  evolve (∑ c : Fin 3, (theta ⟨c.val + 3, by omega⟩ : ℂ) •
    ∑ i ∈ vertexOrbit c, onWire i pauliX) (1 / 2) *
  evolve (∑ c : Fin 3, (theta ⟨c.val, by omega⟩ : ℂ) • latticeInteraction c) (1 / 2)

/-- PDF p.20: named parameter slots of the unrestricted ansatz. -/
abbrev LatticeOriginalParameters (p : ℕ) :=
  Fin p × (({e : Fin 9 × Fin 9 // e ∈ latticeEdges 0 ∪ latticeEdges 1 ∪ latticeEdges 2}) ⊕ (Fin 2 × Fin 9))

/-- PDF p.20: named parameter slots of the shared orbit ansatz. -/
abbrev LatticeSymmetricParameters (p : ℕ) := Fin p × Fin 9

example : (latticeEdges 1).card = 4 := by decide

end QAlgorithms.Papers.Independent.Extend50.P01


