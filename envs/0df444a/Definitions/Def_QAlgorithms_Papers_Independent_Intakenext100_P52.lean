-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P52
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T23:30:02.001874+00:00
-- url     : https://prove2.me/theorems/2a1d45dc-16cd-4d3b-9ab8-976867463df6
-- title:
--   Definitions for An introduction to measurement based quantum computation
-- statement:
--   The objects the formalized statements of *An introduction to measurement based quantum computation* (arXiv:quant-ph/0508124) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `QubitPair`
--   - `rotatedEntangledKet`: PDF p.3: (U† ⊗ I)|phi>, with the first factor the input-side register.
--   - `teleportContraction`: PDF p.3: sum over registers 1 and 2, leaving register 3 in that order.
--   - `sourceBellBasis`: PDF p.2: source Bell labels c,d, with B11=(01-10)/sqrt(2).
--   - `rotatedBell`: PDF p.2: rotate only the first qubit of the measured Bell ket.
--   - `pauliByproduct`: PDF pp.2,5: tensor Pauli representatives with the source output order X^x Z^z.
--   - `hBond`: PDF p.2: the H-bond is a state, distinct from the Hadamard operator.
--   - `phaseGate`: PDF p.5, equation (2): positive-exponent phase gate.
--   - `wGate`: PDF p.5, equation (2): W(theta)=H P(theta).
--   - `rx`: PDF p.5: exp(-i theta X), explicitly cos(theta) I - i sin(theta) X. There is no half-angle in this paper's rotation convention.
--   - `rz`: PDF p.5: exp(-i theta Z), explicitly diagonal.
--   - `equatorial`: PDF pp.8–10: normalized equatorial basis, plus=0 and minus=1.
--   - `angleSign`: PDF pp.5,9,13: (-1)^s as a real angle sign.
--   - `bellPauliRepresentative`: PDF p.4: real Pauli representatives in the order I,X,Z,XZ.
--   - `czTeleportGate`: PDF p.4: the sixteen dimension-four teleportation gates.
--   - `BellFrame`: PDF p.4: the actual rank-one Bell frame identity, with positive weights separate.
--   - `weightedTeleport`: PDF p.4: the rank-one POVM branch bra includes sqrt(k_i).
--   - `czPhase`: PDF p.8: one CZ phase for two computational bits.
--   - `edgePhase`: PDF pp.8,11–12: ordered edges are used once each, with no implicit wire permutations.
--   - `graphClusterState`: PDF p.8: normalized graph cluster, obtained by CZ edges on |+> at every site.
--   - `RectangularSites`
--   - `gridEdges`: PDF p.8 Fig.4: rectangular nearest-neighbour edges, oriented down and right.
--   - `lineBranch`: PDF pp.9–10: all k+1 line sites are entangled first; the first k are then contracted against their normalized measurement bras. Angles may be evaluated from the preceding outcome bits, as explicitly done in Figures 5 and 10. At k=0 there are no ancillas, edges or measurements: the surviving vector is psi.
--   - `figure5Angles`: PDF p.9 Fig.5, corrected for Rx/Rz=exp(-i theta Pauli): double the three printed nonzero measurement angles; keep their causal dependence unchanged.
--   - `insertSite`: PDF pp.11–12: explicit insertion/renaming of the measured site.
--   - `deletedEdges`: PDF pp.11–12: induced edge set on the surviving site subtype.
--   - `neighbourPhase`: PDF p.12: tensor product of Z^s on neighbours of the deleted site.
--   - `PrepGate`: PDF p.8: physical preparation gates, each with its support explicit.
--   - `PrepGate.support`: PDF p.8: the sites occupied by a preparation gate.
--   - `PrepGate.matrix`: PDF p.8: coordinate matrices of one-site H and two-site CZ.
--   - `LegalPrepLayer`: PDF p.8: a physical layer has pairwise disjoint gate supports.
--   - `prepMatrix`: PDF p.8: flattening layers gives the actual gate word (first gate applied first).
--   - `GridPrepGate`: PDF p.8: H at any site, and CZ only on the rectangular nearest-neighbour edges.
--   - `ghzSeed`: PDF p.4 Fig.3: representative strings for the four complementary GHZ pairs.
--   - `threeQubitBellKet`: PDF p.4 Fig.3: normalized plus/minus three-qubit Bell kets.
--   - `figure3Resource`: PDF p.4 Fig.3, actual eight-wire resource: input12 and H-bonds34,57,68.
--   - `figure3Branch`: PDF p.4 Fig.3: destructive measurements on 135 and 246, outputs 78.
--   - `figure8Output`: PDF p.11 Fig.8: unmeasured output sites, top then bottom.
--   - `Figure8Measured`
--   - `figure8Resource`: PDF p.11 Fig.8: arbitrary two-qubit input at upper/lower left, ten |+> ancillas, then all rectangular grid CZs, in the displayed wire order.
--   - `figure8Basis`: PDF p.11 Fig.8: all first-column sites and top/bottom middle sites use X; the other four measured sites use Z. The two rightmost corner sites survive.
--   - `figure8Branch`: PDF p.11 Fig.8: full physical bra contraction, with no assumption of independent or uniformly distributed X/Z outcomes.
--   - `pairBra`: PDF pp.15–16: destructive contraction on a pair, retaining an arbitrary reference.
--   - `localBellAnalysis`: PDF pp.15–16: Bell analysis by CX followed by local X on wire1, Z on wire2.
--   - `cxWires`: PDF p.16 Fig.12: CX with explicitly named control and target.
--   - `figure12Input`: PDF p.16 Fig.12: input psi1, |0>2, |+>3, before either entangling gate.
--   - `figure12Branch`: PDF p.16 Fig.12: prepare pair23 by CX3->2, analyze by CX1->2, then destructively measure X1 and Z2, leaving qubit3.
--   - `hBell`: PDF p.16 equation (3): labels (c,d) order I,X,Z,XZ.
--   - `fuse`: PDF pp.17–18: the local projection with renaming, |00>->|0>, |11>->|1>. This is a rectangular coisometry, not merely the ambient even-space projector.
--   - `fusionResource`: PDF p.18 Fig.14: left site=(left bond half,psi1), right=(right bond half,psi2).
--   - `EdgeLabel`
--   - `bondGrid`: PDF p.17 Fig.13: one independent normalized H-bond per edge. Virtual wire (e,false) is at e's first endpoint, (e,true) at its second.
--   - `valenceProjection`: PDF p.17: tensor product of the explicitly displayed local maps Pi, with all incident virtual wires set to the physical site's bit.
--   - `cutDownKet`: PDF pp.17–18: all four rotated H-bond measurement kets, constructed from W.
--   - `cutDownFormula`: PDF p.18: explicit even/odd representatives for all four outcomes.
--   - `ladderWires`: PDF pp.14–15 Fig.11: adjacent wire placement for a ladder gate.
--   - `ladderState`: PDF p.14: actual (m+1)-qubit ladder state, each Ui,i+1 applied once in order.
--   - `ladderEvent`: PDF p.14: full joint event effect, identity at unmeasured sites and the chosen normalized rank-one projector at every measured site.
--   - `reduceFirst`: PDF p.15: retain the second site, tracing the first or applying its chosen bra.
--   - `ladderSigma`: PDF p.15: two-site intermediate sigma=U(rho tensor |0><0|)U†.
--   - `ladderScan`: PDF p.15: the increasing-site contraction stores only one-site and two-site matrices.
--   - `ladderScanProbability`: PDF p.15: trace the last subnormalized site, or contract its selected bra.
--   - `ScalarInstruction`: PDF pp.14–15: exact scalar arithmetic syntax, with shared previous registers. Complex conjugation is constant work on real/imaginary coordinates.
--   - `ScalarInstruction.readsBefore`: PDF pp.14–15: no uninitialized-register defaults are allowed in a valid word.
--   - `ScalarInstruction.eval`: PDF pp.14–15: one arithmetic instruction, with input reads charged as instructions.
--   - `ScalarProgram`: PDF pp.14–15: a straight-line program has one new scalar register per operation.
--   - `ScalarProgram.Valid`: PDF pp.14–15: all referenced registers exist before the operation using them.
--   - `ScalarProgram.eval`: PDF pp.14–15: evaluation counts actual word operations rather than an unattached cost.
--   - `LadderScalarInput`
--   - `ladderScalarData`: PDF pp.14–15: input entries of the ladder gates and selected measurement bras.
--   - `outcomeHistoryPrefix`: PDF p.19: a history available before stage t contains only t earlier bits.
--   - `AdaptiveProcess`: PDF p.19: finite adaptive unitary/projective process on n data qubits. The basis columns are the measured vectors. All controls are functions of the recorded past, fixed before the unknown input. No cost is attached to them here.
--   - `siteProjector`: PDF p.19: rank-one site projector in the basis supplied as columns of B.
--   - `processBranchOperator`: PDF p.19: branch operator built by actual chronological gate/projector products.
--   - `pointerWave`: PDF p.19: the coherent pointer wave, with data first and k fresh pointer bits second.
-- source:
--   An introduction to measurement based quantum computation, arXiv:quant-ph/0508124v2, https://arxiv.org/abs/quant-ph/0508124v2

import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P01

/-!
Statements from Jozsa, arXiv:quant-ph/0508124v2. Local definitions have executable
finite-coordinate bodies. A bra destroys its measured registers. Branch vectors
are never silently normalized. Density equalities identify global phases.
The normalization/angle/label corrections are recorded in MODERATION_NOTES.md.
Compilation is deliberately left to the batch handoff.
-/

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intakenext100.P52

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

abbrev QubitPair := Bool × Bool

/-- PDF p.3: (U† ⊗ I)|phi>, with the first factor the input-side register. -/
def rotatedEntangledKet {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I]
    (U : Matrix I I ℂ) : Vec (I × I) :=
  act (Matrix.kronecker Uᴴ 1) (finiteMaxEntangled I)

/-- PDF p.3: sum over registers 1 and 2, leaving register 3 in that order. -/
def teleportContraction {I : Type*} [Fintype I]
    (alpha : Vec I) (resource measured : Vec (I × I)) : Vec I :=
  WithLp.toLp 2 fun k => ∑ i, ∑ j, conj (measured (i,j)) * alpha i * resource (j,k)

/-- PDF p.2: source Bell labels c,d, with B11=(01-10)/sqrt(2). -/
def sourceBellBasis (c d : Bool) : Vec QubitPair :=
  act (Matrix.kronecker (pauliZ ^ c.toNat * pauliX ^ d.toNat) 1)
    (finiteMaxEntangled Bool)

/-- PDF p.2: rotate only the first qubit of the measured Bell ket. -/
def rotatedBell (U : Matrix Bool Bool ℂ) (c d : Bool) : Vec QubitPair :=
  act (Matrix.kronecker Uᴴ 1) (sourceBellBasis c d)

/-- PDF pp.2,5: tensor Pauli representatives with the source output order X^x Z^z. -/
def pauliByproduct (x z : Bool) : Matrix Bool Bool ℂ :=
  pauliX ^ x.toNat * pauliZ ^ z.toNat

/-- PDF p.2: the H-bond is a state, distinct from the Hadamard operator. -/
def hBond : Vec QubitPair :=
  act (controlled pauliZ) (tensorVec (act hadamard (ket false)) (act hadamard (ket false)))

/-- PDF p.5, equation (2): positive-exponent phase gate. -/
def phaseGate (theta : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun b => if b then Complex.exp (Complex.I * theta) else 1

/-- PDF p.5, equation (2): W(theta)=H P(theta). -/
def wGate (theta : ℝ) : Matrix Bool Bool ℂ := hadamard * phaseGate theta

/-- PDF p.5: exp(-i theta X), explicitly cos(theta) I - i sin(theta) X.
There is no half-angle in this paper's rotation convention. -/
def rx (theta : ℝ) : Matrix Bool Bool ℂ :=
  (Real.cos theta : ℂ) • (1 : Matrix Bool Bool ℂ) -
    (Complex.I * Real.sin theta) • pauliX

/-- PDF p.5: exp(-i theta Z), explicitly diagonal. -/
def rz (theta : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun b => Complex.exp ((if b then Complex.I else -Complex.I) * theta)

/-- PDF pp.8–10: normalized equatorial basis, plus=0 and minus=1. -/
def equatorial (theta : ℝ) (s : Bool) : Vec Bool :=
  WithLp.toLp 2 fun b => ((Real.sqrt 2)⁻¹ : ℂ) *
    if b then (if s then -1 else 1) * Complex.exp (Complex.I * theta) else 1

/-- PDF pp.5,9,13: (-1)^s as a real angle sign. -/
def angleSign (s : Bool) : ℝ := if s then -1 else 1

/-- PDF p.4: real Pauli representatives in the order I,X,Z,XZ. -/
def bellPauliRepresentative (a : Fin 4) : Matrix Bool Bool ℂ := ![1,pauliX,pauliZ,pauliX * pauliZ] a

/-- PDF p.4: the sixteen dimension-four teleportation gates. -/
def czTeleportGate (a b : QubitPair) : Matrix QubitPair QubitPair ℂ :=
  Matrix.kronecker (pauliByproduct a.1 a.2) (pauliByproduct b.1 b.2) * controlled pauliZ

/-- PDF p.4: the actual rank-one Bell frame identity, with positive weights separate. -/
def BellFrame {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I]
    {n : ℕ} (U : Fin n → Matrix I I ℂ) (k : Fin n → ℝ) : Prop :=
  ∑ i, (k i : ℂ) • pureDensity (rotatedEntangledKet (U i)) = 1

/-- PDF p.4: the rank-one POVM branch bra includes sqrt(k_i). -/
def weightedTeleport {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I]
    (U : Matrix I I ℂ) (k : ℝ) (alpha : Vec I) : Vec I :=
  (Real.sqrt k : ℂ) • teleportContraction alpha (finiteMaxEntangled I) (rotatedEntangledKet U)

example (A : Matrix Bool Bool ℂ) (v : Vec Bool) : applyRect A v = act A v := rfl

example : pauliByproduct false false = 1 := by simp [pauliByproduct]

example : phaseGate 0 = 1 := by ext a b; simp [phaseGate]

example : wGate 0 = hadamard := by
  have h : phaseGate 0 = 1 := by ext a b; simp [phaseGate]
  simp [wGate, h]

example : rx 0 = 1 := by simp [rx]

example : rz 0 = 1 := by ext a b; simp [rz]

example : bellPauliRepresentative 0 = 1 ∧ bellPauliRepresentative 1 = pauliX ∧ bellPauliRepresentative 2 = pauliZ ∧ bellPauliRepresentative 3 = pauliX * pauliZ := by
  simp [bellPauliRepresentative]

example : equatorial 0 false false = ((Real.sqrt 2)⁻¹ : ℂ) := by simp [equatorial]

example : teleportContraction (ket () : Vec Unit) (finiteMaxEntangled Unit)
    (finiteMaxEntangled Unit) = ket () := by
  ext x; cases x; simp [teleportContraction, finiteMaxEntangled, ket]

/-- PDF p.8: one CZ phase for two computational bits. -/
def czPhase (a b : Bool) : ℂ := if a && b then -1 else 1

/-- PDF pp.8,11–12: ordered edges are used once each, with no implicit wire permutations. -/
def edgePhase {V : Type*} [DecidableEq V] (E : Finset (V × V)) (z : V → Bool) : ℂ :=
  ∏ e ∈ E, czPhase (z e.1) (z e.2)

/-- PDF p.8: normalized graph cluster, obtained by CZ edges on |+> at every site. -/
def graphClusterState {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (V × V)) : Vec (V → Bool) :=
  WithLp.toLp 2 fun z => ((Real.sqrt 2)⁻¹ : ℂ) ^ Fintype.card V * edgePhase E z

abbrev RectangularSites (r c : ℕ) := Fin r × Fin c

/-- PDF p.8 Fig.4: rectangular nearest-neighbour edges, oriented down and right. -/
def gridEdges (r c : ℕ) : Finset (RectangularSites r c × RectangularSites r c) :=
  Finset.univ.filter fun e =>
    (e.1.1.val + 1 = e.2.1.val ∧ e.1.2 = e.2.2) ∨
    (e.1.1 = e.2.1 ∧ e.1.2.val + 1 = e.2.2.val)

/-- PDF pp.9–10: all k+1 line sites are entangled first; the first k are then
contracted against their normalized measurement bras. Angles may be evaluated
from the preceding outcome bits, as explicitly done in Figures 5 and 10.
At k=0 there are no ancillas, edges or measurements: the surviving vector is psi. -/
def lineBranch (k : ℕ) (angles : Fin k → ℝ) (s : Fin k → Bool) (psi : Vec Bool) : Vec Bool :=
  WithLp.toLp 2 fun b => ∑ z : Qubits (k+1),
    if z ⟨k,Nat.lt_succ_self k⟩ = b then
      psi (z 0) * ((Real.sqrt 2)⁻¹ : ℂ)^k *
        (∏ i : Fin k, czPhase (z i.castSucc) (z i.succ)) *
        (∏ i : Fin k, conj (equatorial (angles i) (s i) (z i.castSucc)))
    else 0

/-- PDF p.9 Fig.5, corrected for Rx/Rz=exp(-i theta Pauli): double the three
printed nonzero measurement angles; keep their causal dependence unchanged. -/
def figure5Angles (xi eta zeta : ℝ) (s : Fin 4 → Bool) : Fin 4 → ℝ :=
  ![0, -2 * xi * angleSign (s 0), -2 * eta * angleSign (s 1),
    -2 * zeta * angleSign (xor (s 0) (s 2))]

/-- PDF pp.11–12: explicit insertion/renaming of the measured site. -/
def insertSite {V : Type*} [DecidableEq V] (A : V) (s : Bool)
    (z : {v : V // v ≠ A} → Bool) : V → Bool :=
  fun v => if h : v = A then s else z ⟨v,h⟩

/-- PDF pp.11–12: induced edge set on the surviving site subtype. -/
def deletedEdges {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (V × V)) (A : V) :
    Finset ({v : V // v ≠ A} × {v : V // v ≠ A}) :=
  Finset.univ.filter fun e => (e.1.val,e.2.val) ∈ E

/-- PDF p.12: tensor product of Z^s on neighbours of the deleted site. -/
def neighbourPhase {V : Type*} [DecidableEq V] (E : Finset (V × V)) (A : V)
    (s : Bool) (z : {v : V // v ≠ A} → Bool) : ℂ :=
  ∏ e ∈ E, if e.1 = A ∨ e.2 = A then
    czPhase (insertSite A s z e.1) (insertSite A s z e.2) else 1

/-- PDF p.8: physical preparation gates, each with its support explicit. -/
inductive PrepGate (V : Type*) where
  | h (v : V)
  | cz (v w : V)

/-- PDF p.8: the sites occupied by a preparation gate. -/
def PrepGate.support {V : Type*} [DecidableEq V] : PrepGate V → Finset V
  | .h v => {v}
  | .cz v w => {v,w}

/-- PDF p.8: coordinate matrices of one-site H and two-site CZ. -/
def PrepGate.matrix {V : Type*} [Fintype V] [DecidableEq V] :
    PrepGate V → Matrix (V → Bool) (V → Bool) ℂ
  | .h v => fun y z => if ∀ w, w ≠ v → y w = z w then hadamard (y v) (z v) else 0
  | .cz v w => Matrix.diagonal fun z => czPhase (z v) (z w)

/-- PDF p.8: a physical layer has pairwise disjoint gate supports. -/
def LegalPrepLayer {V : Type*} [DecidableEq V] (L : List (PrepGate V)) : Prop :=
  L.Pairwise fun a b => Disjoint a.support b.support

/-- PDF p.8: flattening layers gives the actual gate word (first gate applied first). -/
def prepMatrix {V : Type*} [Fintype V] [DecidableEq V]
    (layers : List (List (PrepGate V))) : Matrix (V → Bool) (V → Bool) ℂ :=
  (layers.flatten.map PrepGate.matrix).reverse.prod

/-- PDF p.8: H at any site, and CZ only on the rectangular nearest-neighbour edges. -/
def GridPrepGate {r c : ℕ} : PrepGate (RectangularSites r c) → Prop
  | .h _ => True
  | .cz v w => (v,w) ∈ gridEdges r c ∨ (w,v) ∈ gridEdges r c

example : edgePhase (∅ : Finset (Bool × Bool)) (fun b => b) = 1 := by simp [edgePhase]

example : gridEdges 1 1 = ∅ := by
  ext e
  simp only [gridEdges, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  have h1 := e.1.1.isLt; have h2 := e.2.1.isLt
  have h3 := e.1.2.isLt; have h4 := e.2.2.isLt
  omega

example (xi eta zeta : ℝ) (s : Fin 4 → Bool) : figure5Angles xi eta zeta s 0 = 0 := rfl

example {V : Type*} [DecidableEq V] (A : V) (s : Bool)
    (z : {v : V // v ≠ A} → Bool) : insertSite A s z A = s := by simp [insertSite]

example {V : Type*} [Fintype V] [DecidableEq V] :
    prepMatrix ([] : List (List (PrepGate V))) = 1 := rfl

/-- PDF p.4 Fig.3: representative strings for the four complementary GHZ pairs. -/
def ghzSeed (a : Fin 4) : Qubits 3 :=
  ![![false,false,false], ![false,false,true], ![false,true,false], ![true,false,false]] a

/-- PDF p.4 Fig.3: normalized plus/minus three-qubit Bell kets. -/
def threeQubitBellKet (a : Fin 4) (s : Bool) : Vec (Qubits 3) :=
  WithLp.toLp 2 fun z =>
    if z = ghzSeed a then ((Real.sqrt 2)⁻¹ : ℂ)
    else if z = fun i => !(ghzSeed a i) then
      (if s then -1 else 1) * ((Real.sqrt 2)⁻¹ : ℂ) else 0

/-- PDF p.4 Fig.3, actual eight-wire resource: input12 and H-bonds34,57,68. -/
def figure3Resource (psi : Vec QubitPair) : Vec (Qubits 8) :=
  WithLp.toLp 2 fun z => psi (z 0,z 1) * hBond (z 2,z 3) * hBond (z 4,z 6) * hBond (z 5,z 7)

/-- PDF p.4 Fig.3: destructive measurements on 135 and 246, outputs 78. -/
def figure3Branch (a b : Fin 4 × Bool) (psi : Vec QubitPair) : Vec QubitPair :=
  WithLp.toLp 2 fun y => ∑ z : Qubits 8,
    if (z 6,z 7) = y then
      conj (threeQubitBellKet a.1 a.2 ![z 0,z 2,z 4]) *
      conj (threeQubitBellKet b.1 b.2 ![z 1,z 3,z 5]) * figure3Resource psi z else 0

/-- PDF p.11 Fig.8: unmeasured output sites, top then bottom. -/
def figure8Output (i : Bool) : RectangularSites 4 3 := if i then (3,2) else (0,2)

abbrev Figure8Measured := {v : RectangularSites 4 3 // v ≠ figure8Output false ∧ v ≠ figure8Output true}

/-- PDF p.11 Fig.8: arbitrary two-qubit input at upper/lower left, ten |+>
ancillas, then all rectangular grid CZs, in the displayed wire order. -/
def figure8Resource (psi : Vec QubitPair) : Vec (RectangularSites 4 3 → Bool) :=
  WithLp.toLp 2 fun z => psi (z (0,0),z (3,0)) * ((Real.sqrt 2)⁻¹ : ℂ)^10 *
    edgePhase (gridEdges 4 3) z

/-- PDF p.11 Fig.8: all first-column sites and top/bottom middle sites use X;
the other four measured sites use Z. The two rightmost corner sites survive. -/
def figure8Basis (v : Figure8Measured) (s : Bool) : Vec Bool :=
  if v.val.2 = 0 ∨ v.val.1 = 0 ∨ v.val.1 = 3 then equatorial 0 s else ket s

/-- PDF p.11 Fig.8: full physical bra contraction, with no assumption of
independent or uniformly distributed X/Z outcomes. -/
def figure8Branch (s : Figure8Measured → Bool) (psi : Vec QubitPair) : Vec QubitPair :=
  WithLp.toLp 2 fun y => ∑ z : RectangularSites 4 3 → Bool,
    if (z (figure8Output false),z (figure8Output true)) = y then
      (∏ v : Figure8Measured, conj (figure8Basis v (s v) (z v.val))) * figure8Resource psi z else 0

example : ghzSeed 0 = (![false,false,false] : Qubits 3) := rfl

example : figure8Output false = (0,2) ∧ figure8Output true = (3,2) := by
  simp [figure8Output]

example (psi : Vec QubitPair) : figure3Resource psi (fun _ => false) =
    psi (false,false) * hBond (false,false) * hBond (false,false) * hBond (false,false) := rfl

/-- PDF pp.15–16: destructive contraction on a pair, retaining an arbitrary reference. -/
def pairBra {R : Type*} (b : Vec QubitPair) (psi : Vec (QubitPair × R)) : Vec R :=
  WithLp.toLp 2 fun r => ∑ p : QubitPair, conj (b p) * psi (p,r)

/-- PDF pp.15–16: Bell analysis by CX followed by local X on wire1, Z on wire2. -/
def localBellAnalysis {R : Type*} [Fintype R] [DecidableEq R]
    (c d : Bool) (psi : Vec (QubitPair × R)) : Vec R :=
  pairBra (tensorVec (equatorial 0 c) (ket d))
    (act (Matrix.kronecker cnot 1) psi)

/-- PDF p.16 Fig.12: CX with explicitly named control and target. -/
def cxWires {V : Type*} [Fintype V] [DecidableEq V] (control target : V) :
    Matrix (V → Bool) (V → Bool) ℂ :=
  fun y z => if y = Function.update z target (xor (z target) (z control)) then 1 else 0

/-- PDF p.16 Fig.12: input psi1, |0>2, |+>3, before either entangling gate. -/
def figure12Input (psi : Vec Bool) : Vec (Qubits 3) :=
  WithLp.toLp 2 fun z => psi (z 0) * (if z 1 then 0 else 1) * ((Real.sqrt 2)⁻¹ : ℂ)

/-- PDF p.16 Fig.12: prepare pair23 by CX3->2, analyze by CX1->2,
then destructively measure X1 and Z2, leaving qubit3. -/
def figure12Branch (c d : Bool) (psi : Vec Bool) : Vec Bool :=
  let v := act (cxWires (0 : Fin 3) 1 * cxWires (2 : Fin 3) 1) (figure12Input psi)
  WithLp.toLp 2 fun b => ∑ a : Bool, conj (equatorial 0 c a) * v ![a,d,b]

/-- PDF p.16 equation (3): labels (c,d) order I,X,Z,XZ. -/
def hBell (c d : Bool) : Vec QubitPair :=
  act (Matrix.kronecker (pauliByproduct d c) 1) hBond

/-- PDF pp.17–18: the local projection with renaming, |00>->|0>, |11>->|1>.
This is a rectangular coisometry, not merely the ambient even-space projector. -/
def fuse : Matrix Bool QubitPair ℂ := fun b p => if p = (b,b) then 1 else 0

/-- PDF p.18 Fig.14: left site=(left bond half,psi1), right=(right bond half,psi2). -/
def fusionResource (psi1 psi2 : Vec Bool) : Vec (QubitPair × QubitPair) :=
  WithLp.toLp 2 fun p => hBond (p.1.1,p.2.1) * psi1 p.1.2 * psi2 p.2.2

abbrev EdgeLabel {V : Type*} (E : Finset (V × V)) := {e : V × V // e ∈ E}

/-- PDF p.17 Fig.13: one independent normalized H-bond per edge.
Virtual wire (e,false) is at e's first endpoint, (e,true) at its second. -/
def bondGrid {V : Type*} [DecidableEq V] (E : Finset (V × V)) :
    Vec ((EdgeLabel E × Bool) → Bool) :=
  WithLp.toLp 2 fun w => ∏ e : EdgeLabel E, hBond (w (e,false),w (e,true))

/-- PDF p.17: tensor product of the explicitly displayed local maps Pi,
with all incident virtual wires set to the physical site's bit. -/
def valenceProjection {V : Type*} [DecidableEq V] (E : Finset (V × V)) :
    Matrix (V → Bool) ((EdgeLabel E × Bool) → Bool) ℂ :=
  fun x w => if ∀ e : EdgeLabel E,
    w (e,false) = x e.val.1 ∧ w (e,true) = x e.val.2 then 1 else 0

/-- PDF pp.17–18: all four rotated H-bond measurement kets, constructed from W. -/
def cutDownKet (theta : ℝ) (a : Fin 4) : Vec QubitPair :=
  act (Matrix.kronecker ((wGate (-theta))ᴴ * bellPauliRepresentative a) 1) hBond

/-- PDF p.18: explicit even/odd representatives for all four outcomes. -/
def cutDownFormula (theta : ℝ) (a : Fin 4) : Vec QubitPair :=
  WithLp.toLp 2 fun p => ((Real.sqrt 2)⁻¹ : ℂ) *
    if a.val < 2 then
      if p.1 = p.2 then
        if p.1 then (if a.val = 1 then -1 else 1) * Complex.exp (Complex.I * theta) else 1
      else 0
    else if p.1 ≠ p.2 then
      if p.1 then (if a.val = 3 then -1 else 1) * Complex.exp (Complex.I * theta) else 1
    else 0

example : fuse false (false,false) = 1 ∧ fuse true (true,true) = 1 ∧
    fuse false (false,true) = 0 := by simp [fuse]

example : hBell false false = hBond := by simp [hBell, pauliByproduct, act]

example {V : Type*} [DecidableEq V] (x : V → Bool)
    (w : (EdgeLabel (∅ : Finset (V × V)) × Bool) → Bool) :
    valenceProjection ∅ x w = 1 := by simp [valenceProjection]

example (theta : ℝ) : cutDownFormula theta 0 (false,false) = ((Real.sqrt 2)⁻¹ : ℂ) := by
  simp [cutDownFormula]

/-- PDF pp.14–15 Fig.11: adjacent wire placement for a ladder gate. -/
def ladderWires {m : ℕ} (t : Fin m) : Fin 2 ↪ Fin (m+1) where
  toFun j := ⟨t.val+j.val, by have ht := t.isLt; have hj := j.isLt; omega⟩
  inj' := by intro a b h; apply Fin.ext; have hv := congrArg Fin.val h; change t.val + a.val = t.val + b.val at hv; exact Nat.add_left_cancel hv

/-- PDF p.14: actual (m+1)-qubit ladder state, each Ui,i+1 applied once in order. -/
def ladderState (m : ℕ) (U : Fin m → Matrix QubitPair QubitPair ℂ) : Vec (Qubits (m+1)) :=
  act ((List.ofFn fun t => embedOp (Gate.ofMatrix2 (U t)).mat (ladderWires t)).reverse.prod)
    (zeroKet (m+1))

/-- PDF p.14: full joint event effect, identity at unmeasured sites and the
chosen normalized rank-one projector at every measured site. -/
def ladderEvent {m : ℕ} (measured : Fin (m+1) → Bool)
    (v : Fin (m+1) → Vec Bool) : Matrix (Qubits (m+1)) (Qubits (m+1)) ℂ :=
  fun y z => ∏ i : Fin (m+1), if measured i then v i (y i) * conj (v i (z i))
    else if y i = z i then 1 else 0

/-- PDF p.15: retain the second site, tracing the first or applying its chosen bra. -/
def reduceFirst (selected : Option (Vec Bool)) (rho : Matrix QubitPair QubitPair ℂ) : Matrix Bool Bool ℂ :=
  match selected with
  | none => traceLeft rho
  | some v => fun b c => ∑ a : Bool, ∑ d : Bool, conj (v a) * rho (a,b) (d,c) * v d

/-- PDF p.15: two-site intermediate sigma=U(rho tensor |0><0|)U†. -/
def ladderSigma (U : Matrix QubitPair QubitPair ℂ) (rho : Matrix Bool Bool ℂ) : Matrix QubitPair QubitPair ℂ :=
  U * Matrix.kronecker rho (pureDensity (ket false)) * Uᴴ

/-- PDF p.15: the increasing-site contraction stores only one-site and two-site matrices. -/
def ladderScan {m : ℕ} (U : Fin m → Matrix QubitPair QubitPair ℂ)
    (measured : Fin (m+1) → Bool) (v : Fin (m+1) → Vec Bool) : Matrix Bool Bool ℂ :=
  (List.finRange m).foldl (fun rho t =>
    reduceFirst (if measured t.castSucc then some (v t.castSucc) else none)
      (ladderSigma (U t) rho)) (pureDensity (ket false))

/-- PDF p.15: trace the last subnormalized site, or contract its selected bra. -/
def ladderScanProbability {m : ℕ} (U : Fin m → Matrix QubitPair QubitPair ℂ)
    (measured : Fin (m+1) → Bool) (v : Fin (m+1) → Vec Bool) : ℝ :=
  let rho := ladderScan U measured v
  let last : Fin (m+1) := ⟨m,Nat.lt_succ_self m⟩
  if measured last then (∑ a : Bool, ∑ b : Bool, conj (v last a) * rho a b * v last b).re
  else rho.trace.re

/-- PDF pp.14–15: exact scalar arithmetic syntax, with shared previous registers.
Complex conjugation is constant work on real/imaginary coordinates. -/
inductive ScalarInstruction (I : Type*) where
  | input (i : I)
  | constant (c : ℂ)
  | add (a b : ℕ)
  | mul (a b : ℕ)
  | conjugate (a : ℕ)

/-- PDF pp.14–15: no uninitialized-register defaults are allowed in a valid word. -/
def ScalarInstruction.readsBefore {I : Type*} (t : ℕ) : ScalarInstruction I → Prop
  | .input _ => True
  | .constant _ => True
  | .add a b => a < t ∧ b < t
  | .mul a b => a < t ∧ b < t
  | .conjugate a => a < t

/-- PDF pp.14–15: one arithmetic instruction, with input reads charged as instructions. -/
def ScalarInstruction.eval {I : Type*} (data : I → ℂ) (memory : List ℂ) : ScalarInstruction I → ℂ
  | .input i => data i
  | .constant c => c
  | .add a b => (memory[a]?).getD 0 + (memory[b]?).getD 0
  | .mul a b => (memory[a]?).getD 0 * (memory[b]?).getD 0
  | .conjugate a => conj ((memory[a]?).getD 0)

/-- PDF pp.14–15: a straight-line program has one new scalar register per operation. -/
structure ScalarProgram (I : Type*) where
  word : List (ScalarInstruction I)
  output : ℕ

/-- PDF pp.14–15: all referenced registers exist before the operation using them. -/
def ScalarProgram.Valid {I : Type*} (P : ScalarProgram I) : Prop :=
  P.output < P.word.length ∧ ∀ t (h : t < P.word.length), ScalarInstruction.readsBefore t (P.word[t])

/-- PDF pp.14–15: evaluation counts actual word operations rather than an unattached cost. -/
def ScalarProgram.eval {I : Type*} (P : ScalarProgram I) (data : I → ℂ) : ℂ :=
  ((P.word.foldl (fun mem op => mem ++ [ScalarInstruction.eval data mem op]) [])[P.output]?).getD 0

abbrev LadderScalarInput (m : ℕ) := (Fin m × QubitPair × QubitPair) ⊕ (Fin (m+1) × Bool)

/-- PDF pp.14–15: input entries of the ladder gates and selected measurement bras. -/
def ladderScalarData {m : ℕ} (U : Fin m → Matrix QubitPair QubitPair ℂ)
    (v : Fin (m+1) → Vec Bool) : LadderScalarInput m → ℂ
  | .inl (t,a,b) => U t a b
  | .inr (t,a) => v t a

example (U : Fin 0 → Matrix QubitPair QubitPair ℂ) (s : Fin 1 → Bool) (v : Fin 1 → Vec Bool) :
    ladderScan U s v = pureDensity (ket false) := rfl

example (data : Unit → ℂ) :
    ScalarProgram.eval (⟨[.constant 1],0⟩ : ScalarProgram Unit) data = 1 := rfl

example {I : Type*} : ScalarInstruction.readsBefore 0 (.constant (1 : ℂ) : ScalarInstruction I) :=
  True.intro

/-- PDF p.19: a history available before stage t contains only t earlier bits. -/
def outcomeHistoryPrefix {k : ℕ} (s : Qubits k) (t : Fin k) : Qubits t.val :=
  fun i => s ⟨i.val, Nat.lt_trans i.isLt t.isLt⟩

/-- PDF p.19: finite adaptive unitary/projective process on n data qubits.
The basis columns are the measured vectors. All controls are functions of the
recorded past, fixed before the unknown input. No cost is attached to them here. -/
structure AdaptiveProcess (n k : ℕ) where
  gate : (t : Fin k) → Qubits t.val → Matrix (Qubits n) (Qubits n) ℂ
  gate_unitary : ∀ t h, gate t h ∈ Matrix.unitaryGroup (Qubits n) ℂ
  wire : (t : Fin k) → Qubits t.val → Fin n
  basis : (t : Fin k) → Qubits t.val → Matrix Bool Bool ℂ
  basis_unitary : ∀ t h, basis t h ∈ Matrix.unitaryGroup Bool ℂ
  finalGate : Qubits k → Matrix (Qubits n) (Qubits n) ℂ
  final_unitary : ∀ h, finalGate h ∈ Matrix.unitaryGroup (Qubits n) ℂ

/-- PDF p.19: rank-one site projector in the basis supplied as columns of B. -/
def siteProjector {n : ℕ} (wire : Fin n) (B : Matrix Bool Bool ℂ) (s : Bool) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  fun y z => if ∀ i, i ≠ wire → y i = z i then B (y wire) s * conj (B (z wire) s) else 0

/-- PDF p.19: branch operator built by actual chronological gate/projector products. -/
def processBranchOperator {n k : ℕ} (P : AdaptiveProcess n k) (s : Qubits k) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  P.finalGate s * (List.ofFn fun t : Fin k =>
    let h := outcomeHistoryPrefix s t
    siteProjector (P.wire t h) (P.basis t h) (s t) * P.gate t h).reverse.prod

/-- PDF p.19: the coherent pointer wave, with data first and k fresh pointer bits second. -/
def pointerWave {n k : ℕ} (P : AdaptiveProcess n k) (psi : Vec (Qubits n)) :
    Vec (Qubits n × Qubits k) :=
  WithLp.toLp 2 fun p => act (processBranchOperator P p.2) psi p.1

example {n : ℕ} (P : AdaptiveProcess n 0) (s : Qubits 0) :
    processBranchOperator P s = P.finalGate s := by simp [processBranchOperator]

example {n : ℕ} (i : Fin n) (y z : Qubits n) :
    siteProjector i (1 : Matrix Bool Bool ℂ) false y z =
      if ∀ j, j ≠ i → y j = z j then
        (if y i = false then 1 else 0) * conj (if z i = false then 1 else 0) else 0 := by
  simp only [siteProjector, Matrix.one_apply]

/-- Degenerate-resource sanity: a zero input gives the zero physical branch. -/
example {I : Type*} [Fintype I] (resource measured : Vec (I × I)) :
    teleportContraction (0 : Vec I) resource measured = 0 := by
  ext k; simp [teleportContraction]

/-- The identity rotation keeps the resource orientation explicit. -/
example (i j : Bool) : sourceBellBasis false false (i,j) =
    act (Matrix.kronecker (1 : Matrix Bool Bool ℂ) 1) (finiteMaxEntangled Bool) (i,j) := by
  simp only [sourceBellBasis, Bool.toNat_false, pow_zero, mul_one]

/-- The positive weight branch has an actual sqrt-weight, including k=0 off-domain. -/
example {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I]
    (U : Matrix I I ℂ) (alpha : Vec I) : weightedTeleport U 0 alpha = 0 := by
  simp [weightedTeleport]

/-- CZ's zero-control phase is +1, pinning its computational-basis sign. -/
example (b : Bool) : czPhase false b = 1 := by simp [czPhase]

/-- The H-bond's tensor order is left endpoint then right endpoint. -/
example : hBond (false,false) = (1 / 2 : ℂ) := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  norm_num [hBond, act, tensorVec, hadamard, ket, controlled, pauliZ,
    Matrix.mulVec, dotProduct, Matrix.one_apply, Fintype.sum_prod_type, Fintype.sum_bool,
    Complex.ofReal_inv, ← pow_two, inv_pow, h2]

/-- No measurement is performed by the empty preparation word. -/
example {V : Type*} [DecidableEq V] : LegalPrepLayer ([] : List (PrepGate V)) := by
  simp [LegalPrepLayer]

/-- An isolated site's neighbour correction is the empty product. -/
example {V : Type*} [DecidableEq V] (A : V) (s : Bool)
    (z : {v : V // v ≠ A} → Bool) : neighbourPhase ∅ A s z = 1 := by
  simp [neighbourPhase]

/-- With no selected measurement the ladder step is exactly an unnormalized trace. -/
example (rho : Matrix QubitPair QubitPair ℂ) : reduceFirst none rho = traceLeft rho := rfl

/-- A branch's outcome-dependent final unitary is applied after its projectors. -/
example {n k : ℕ} (P : AdaptiveProcess n k) (psi : Vec (Qubits n))
    (x : Qubits n) (s : Qubits k) :
    pointerWave P psi (x,s) = act (processBranchOperator P s) psi x := rfl

end QAlgorithms.Papers.Independent.Intakenext100.P52


