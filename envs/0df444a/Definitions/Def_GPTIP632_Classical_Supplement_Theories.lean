-- Prove2me | Definitions.Def_GPTIP632_Classical_Supplement_Theories
-- name    : GPTIP632_Classical_Supplement_Theories
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:12:04.536334+00:00
-- url     : https://prove2.me/theorems/c00cd59b-48e2-4f02-a918-097fa121d6b4
-- title:
--   Concrete data for QC, classical theory and the two triangular theories
-- statement:
--   A pretheory contains the published Core and a finite set of outcome maps on elementary registers. Its validity predicate says exactly that Core.IsTheory holds and every specified gate is an allowed instrument; a proof packages these same data as a published Theory. Validity is proved as an existential conclusion in the companion statements, never assumed there. QC has all positive-dimensional quantum and classical systems, ordinary quantum composites, all completely positive trace-preserving maps, and CP instruments with trace-preserving sum. Classical theory has orthant cones and stochastic channels and instruments. The theory $G_v$ has classical and triangular leaves, minimal composites (equivalently transported diagonal PSD cones), all positive unit-preserving channels, and positive instruments with unit-preserving sum. The theory $G_v^Q$ transports QC cones, channels and instruments through the tensor powers of $L_v$. The finite gates are Hadamard, T, CNOT, quantum preparation, measurement and discard, and the classical preparation, discard, readout, fair coin, NOT, Toffoli and copy gates as applicable. The triangular gates prepare $e_0$, discard by $z$, and measure $y$ versus $z-y$; outcome index zero denotes $y$. A list entry $n$ adjoins $\Delta_{n+1}$ with first-label preparation, label readout and discard, covering every finite list of positive dimensions. The distinguished standard leaf is a labelled copy of $\Delta_3$, also available among the standard classical systems. Isomorphisms do not require equality of designated gate sets.
-- source:
--   Kishor Bharti, Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical Theories, STOC 2027 submission #632 (October 2026), source.pdf SHA-256 ebbc45027e7a3b48cbfb1a2deb89e9a7d8374373b23763680b948fda16cf4da7, pp.14, 17–19, 22–23, 28, 32–35 (PDF pp.16, 19–21, 24–25, 30, 34–37), Examples B.3, B.5, B.17–B.23, Definitions D.3–D.4, F.1, §G

import Mathlib
import Definitions.Def_GPTIP632_Classical_Supplement_Trees
import Definitions.Def_GPTIP632_Classical_Theory

set_option autoImplicit false

/-!
# The constructed theories: QC (with adjoined classical systems), classical theory, `G_v`, `G^Q_v`

Kishor Bharti, *Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical
Theories*, STOC 2027 submission #632 (October 2026), Examples B.17, B.18 (p.18, PDF p.20),
Examples B.22, B.23 (p.19, PDF p.21), Lemma F.9 (p.31, PDF p.33), (T4) (p.17, PDF p.19).

Each theory is given by its data (`PreTheory`: systems, composites, channels, instruments, gate
set). Whether the data satisfy the axioms of a theory (`Core.IsTheory`) and whether the gates are
allowed instruments is the proposition `PreTheory.Ok`; given a proof, `PreTheory.toTheory` is a
`GPTIP632.Classical.Theory`. The paper asserts these axioms for each construction; the theorems of
this mission state them as conclusions, never as hypotheses.

**Gates.** A gate on qubits and classical bits is specified by Kraus operators on the matrix index
`Fin m → Fin 2` of a register of `m` two-level wires (wire `i` ↦ coordinate `i`): the gate's outcome
`o` acts as `X ↦ ∑_K K X K†`. Its real matrix in a theory is read off in the coordinates of the
registers (`rawGateMat`): the qubit has the coordinates of `hermB 2`, the bit those of `Δ_2`.
-/

noncomputable section

namespace GPTIP632.Classical.Supplement

open GPTIP632.Classical Matrix Complex _root_.GPTIP632.Classical.Supplement.Tree
open scoped Kronecker ComplexOrder

attribute [local instance] _root_.Classical.propDecidable

/-! ### The data of a theory, and its axioms -/

/-- The data of a theory with its gate set (the fields of `Theory` without the two proofs). -/
structure PreTheory where
  C : Core
  Gate : Type
  [gateFintype : Fintype Gate]
  ins : Gate → List C.Elem
  outs : Gate → List C.Elem
  nout : Gate → ℕ
  gate : (g : Gate) → Fin (nout g) → Matrix (C.sys (C.reg (outs g))).ι (C.sys (C.reg (ins g))).ι ℝ

attribute [instance] PreTheory.gateFintype

/-- The data form a theory (Definition B.6 with (T1)–(T2) and Definition B.16) whose gates are
allowed instruments. -/
def PreTheory.Ok (P : PreTheory) : Prop :=
  P.C.IsTheory ∧ ∀ g, P.gate g ∈ P.C.inst (P.C.reg (P.ins g)) (P.C.reg (P.outs g)) (P.nout g)

/-- The theory of data satisfying the axioms. -/
def PreTheory.toTheory (P : PreTheory) (h : P.Ok) : Theory where
  C := P.C
  isTheory := h.1
  Gate := P.Gate
  ins := P.ins
  outs := P.outs
  nout := P.nout
  gate := P.gate
  gate_allowed := h.2

/-! ### Systems of tree theories -/

/-- The systems: in the quantum–classical reading (`none`), or with `W_v` (`some v`). -/
def tsys : Option (Set.Ioo (0 : ℝ) 1) → Tree → System
  | none, t => hsys t
  | some v, t => wsys v t

/-- The coordinates of `tsys w t` are those of the tree. -/
def tcoord : (w : Option (Set.Ioo (0 : ℝ) 1)) → (t : Tree) → (tsys w t).ι ≃ t.ι
  | none, _ => Equiv.refl _
  | some _, _ => Equiv.refl _

/-- The theory core of a tree theory: the trees with `ok t`, composites the nodes, product
coordinates, `Δ_{n+1}` the classical leaves. -/
def treeCore (w : Option (Set.Ioo (0 : ℝ) 1)) (ok : Tree → Bool)
    (hnode : ∀ A B, ok A = true → ok B = true → ok (.node A B) = true)
    (hcl : ∀ n, ok (.classical n) = true)
    (Elem : Type) [Fintype Elem] [DecidableEq Elem] (elem : Elem → {t : Tree // ok t = true})
    (chan : (A B : {t : Tree // ok t = true}) → Set (Matrix (tsys w B.1).ι (tsys w A.1).ι ℝ))
    (inst : (A B : {t : Tree // ok t = true}) → (k : ℕ) →
      Set (Fin k → Matrix (tsys w B.1).ι (tsys w A.1).ι ℝ)) : Core where
  Sys := {t : Tree // ok t = true}
  sys A := tsys w A.1
  comp A B := ⟨.node A.1 B.1, hnode _ _ A.2 B.2⟩
  compEquiv A B := (tcoord w _).trans ((tcoord w A.1).prodCongr (tcoord w B.1)).symm
  Elem := Elem
  elem := elem
  cl n := ⟨.classical n, hcl n⟩
  clEquiv n := tcoord w _
  chan := chan
  inst := inst

/-! ### Channels -/

/-- **Complete positivity** (Example B.15): `Φ ⊗ id` maps the cone of `A Q_{d+1}` into that of
`B Q_{d+1}` for every quantum system `Q_{d+1}` (positivity on every quantum extension). -/
def IsCP (A B : Tree) (Φ : Matrix B.ι A.ι ℝ) : Prop :=
  ∀ d : ℕ, ∀ x ∈ (hsys (.node A (.quantum d))).cone,
    (Φ ⊗ₖ (1 : Matrix (Tree.quantum d).ι (Tree.quantum d).ι ℝ)) *ᵥ x ∈ (hsys (.node B (.quantum d))).cone

/-- Trace preservation: `u_B ∘ Φ = u_A`. -/
def IsTP (A B : Tree) (Φ : Matrix B.ι A.ι ℝ) : Prop := (hsys B).unit ᵥ* Φ = (hsys A).unit

/-- The CPTP maps (Example B.18). -/
def cptp (A B : Tree) : Set (Matrix B.ι A.ι ℝ) := {Φ | IsCP A B Φ ∧ IsTP A B Φ}

/-- The instruments of QC: families of CP maps with a CPTP sum. -/
def cpInst (A B : Tree) (k : ℕ) : Set (Fin k → Matrix B.ι A.ι ℝ) :=
  {Φ | (∀ o, IsCP A B (Φ o)) ∧ IsTP A B (∑ o, Φ o)}

/-- Positive unit-preserving maps of `G_v` (Example B.22). -/
def posChan (v : Set.Ioo (0 : ℝ) 1) (A B : Tree) : Set (Matrix B.ι A.ι ℝ) :=
  {Φ | (∀ x ∈ (wsys v A).cone, Φ *ᵥ x ∈ (wsys v B).cone) ∧ (wsys v B).unit ᵥ* Φ = (wsys v A).unit}

/-- Instruments of `G_v`: families of positive maps with unit-preserving sum. -/
def posInst (v : Set.Ioo (0 : ℝ) 1) (A B : Tree) (k : ℕ) : Set (Fin k → Matrix B.ι A.ι ℝ) :=
  {Φ | (∀ o, ∀ x ∈ (wsys v A).cone, Φ o *ᵥ x ∈ (wsys v B).cone) ∧
    (wsys v B).unit ᵥ* (∑ o, Φ o) = (wsys v A).unit}

/-! ### Wire matrices and gate matrices -/

/-- The `2 × 2` matrix of a coordinate of a two-level leaf: the basis matrix `hermB 2` of the
qubit `Q_2`, the diagonal unit of the bit `Δ_2`; `0` for every other leaf. -/
def twoLevel : (t : Tree) → t.ι → Matrix (Fin 2) (Fin 2) ℂ
  | .quantum 1 => hermB 2
  | .classical 1 => fun i => Matrix.single i i 1
  | _ => fun _ => 0

/-- The matrix of a list of wire coordinates of a register of `n` two-level wires: the Kronecker
product of the wire matrices, on the index `Fin n → Fin 2`. -/
def rawMatOf {W : Type} (wm : W → Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) (k : List W) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  fun s t => ∏ i : Fin n, match k[i.1]? with
    | some w => wm w (s i) (t i)
    | none => 0

/-- The raw wire coordinates of a register coordinate. -/
def regRaw (C : Core) : (l : List C.Elem) → (C.sys (C.reg l)).ι → List C.Wire
  | [], _ => []
  | [a], i => [⟨a, i⟩]
  | a :: b :: l, i => ⟨a, (C.compEquiv _ _ i).1⟩ :: regRaw C (b :: l) (C.compEquiv _ _ i).2

/-- The Kraus map `X ↦ ∑_K K X K†`. -/
def krausL {m n : Type} [Fintype n] (L : List (Matrix m n ℂ)) (X : Matrix n n ℂ) : Matrix m m ℂ :=
  (L.map fun K => K * X * Kᴴ).sum

/-- The coordinate of a matrix along an orthogonal basis element: `Re Tr(β M) / Re Tr(β β)`. -/
def coefOf {n : Type} [Fintype n] (β M : Matrix n n ℂ) : ℝ := (β * M).trace.re / (β * β).trace.re

/-- The real matrix of the gate with Kraus operators `L` from the register `ins` (of `n` wires)
to `outs` (of `m` wires), in the coordinates given by the wire matrices `wm`. -/
def rawGateMat (C : Core) (wm : C.Wire → Matrix (Fin 2) (Fin 2) ℂ) (ins outs : List C.Elem)
    (n m : ℕ) (L : List (Matrix (Fin m → Fin 2) (Fin n → Fin 2) ℂ)) :
    Matrix (C.sys (C.reg outs)).ι (C.sys (C.reg ins)).ι ℝ :=
  fun i j => coefOf (rawMatOf wm m (regRaw C outs i)) (krausL L (rawMatOf wm n (regRaw C ins j)))

/-! ### The quantum and classical gates (Examples B.17, B.18; (T4)) -/

/-- The two-level wire kinds: qubit, classical bit. -/
inductive QB where
  | qubit
  | bit
  deriving DecidableEq

instance : Fintype QB := ⟨{.qubit, .bit}, by intro x; cases x <;> simp⟩

/-- The quantum gates of Example B.18 together with the qubit discard of (T4): Hadamard, π/8,
controlled-NOT, preparation of `|0⟩`, measurement in the computational basis, discard. -/
inductive QGate where
  | had
  | tg
  | cnot
  | prepQ
  | measQ
  | discQ
  deriving DecidableEq

instance : Fintype QGate := ⟨{.had, .tg, .cnot, .prepQ, .measQ, .discQ}, by intro x; cases x <;> simp⟩

/-- The classical gates required by (T4): preparation of `δ_0`, discard, readout of a classical
bit, preparation of a fair coin, NOT and Toffoli. -/
inductive CGate where
  | prepB
  | discB
  | readB
  | coin
  | notB
  | tof
  | copyB
  deriving DecidableEq

instance : Fintype CGate := ⟨{.prepB, .discB, .readB, .coin, .notB, .tof, .copyB}, by intro x; cases x <;> simp⟩

/-- `|b⟩` on one wire, as a map from the trivial register. -/
def ketK (b : Fin 2) : Matrix (Fin 1 → Fin 2) (Fin 0 → Fin 2) ℂ := fun s _ => if s 0 = b then 1 else 0

/-- `⟨b|` on one wire, as a map to the trivial register. -/
def braK (b : Fin 2) : Matrix (Fin 0 → Fin 2) (Fin 1 → Fin 2) ℂ := fun _ t => if t 0 = b then 1 else 0

/-- A one-wire operator. -/
def oneWire (U : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 1 → Fin 2) (Fin 1 → Fin 2) ℂ :=
  fun s t => U (s 0) (t 0)

/-- The Hadamard matrix. -/
def hadU : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.sqrt 2 : ℂ)⁻¹, (Real.sqrt 2 : ℂ)⁻¹; (Real.sqrt 2 : ℂ)⁻¹, -(Real.sqrt 2 : ℂ)⁻¹]

/-- The π/8 gate `diag(1, e^{iπ/4})`. -/
def tU : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, Complex.exp (I * (Real.pi / 4))]

/-- NOT. -/
def xU : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Controlled-NOT `|a, c⟩ ↦ |a, c ⊕ a⟩` (control wire 0). -/
def cnotK : Matrix (Fin 2 → Fin 2) (Fin 2 → Fin 2) ℂ :=
  fun s t => if s 0 = t 0 ∧ s 1 = t 1 + t 0 then 1 else 0

/-- Toffoli `|x, y, z⟩ ↦ |x, y, z ⊕ (x ∧ y)⟩`. -/
def tofK : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ :=
  fun s t => if s 0 = t 0 ∧ s 1 = t 1 ∧ s 2 = t 2 + t 0 * t 1 then 1 else 0

/-- Copy `|b⟩ ↦ |b, b⟩`, Kraus operator for the value `c`. -/
def copyK (c : Fin 2) : Matrix (Fin 2 → Fin 2) (Fin 1 → Fin 2) ℂ :=
  fun s t => if s 0 = c ∧ s 1 = c ∧ t 0 = c then 1 else 0

def QGate.ins : QGate → List QB
  | .had | .tg | .measQ | .discQ => [.qubit]
  | .cnot => [.qubit, .qubit]
  | .prepQ => []

def QGate.outs : QGate → List QB
  | .had | .tg | .prepQ => [.qubit]
  | .cnot => [.qubit, .qubit]
  | .measQ | .discQ => []

def QGate.nout : QGate → ℕ
  | .measQ => 2
  | _ => 1

/-- The Kraus operators of each outcome of the quantum gates. -/
def QGate.kraus : (g : QGate) → Fin g.nout →
    List (Matrix (Fin g.outs.length → Fin 2) (Fin g.ins.length → Fin 2) ℂ)
  | .had, _ => [oneWire hadU]
  | .tg, _ => [oneWire tU]
  | .cnot, _ => [cnotK]
  | .prepQ, _ => [ketK 0]
  | .measQ, o => [braK o]
  | .discQ, _ => [braK 0, braK 1]

def CGate.ins : CGate → List QB
  | .discB | .readB | .notB | .copyB => [.bit]
  | .tof => [.bit, .bit, .bit]
  | .prepB | .coin => []

def CGate.outs : CGate → List QB
  | .prepB | .coin | .notB => [.bit]
  | .tof => [.bit, .bit, .bit]
  | .copyB => [.bit, .bit]
  | .discB | .readB => []

def CGate.nout : CGate → ℕ
  | .readB => 2
  | _ => 1

/-- The Kraus operators of each outcome of the classical gates (on diagonal matrices). -/
def CGate.kraus : (g : CGate) → Fin g.nout →
    List (Matrix (Fin g.outs.length → Fin 2) (Fin g.ins.length → Fin 2) ℂ)
  | .prepB, _ => [ketK 0]
  | .discB, _ => [braK 0, braK 1]
  | .readB, o => [braK o]
  | .coin, _ => [(Real.sqrt 2 : ℂ)⁻¹ • ketK 0, (Real.sqrt 2 : ℂ)⁻¹ • ketK 1]
  | .notB, _ => [oneWire xU]
  | .tof, _ => [tofK]
  | .copyB, _ => [copyK 0, copyK 1]

/-- The gates acting on the triangular system `W_v` (Example B.22): preparation of `e0`, the
discard `u`, and the measurement `(f_y, u − f_y)` (outcome `0` is `f_y`). -/
inductive WGate where
  | prepE0
  | discW
  | measY
  deriving DecidableEq

instance : Fintype WGate := ⟨{.prepE0, .discW, .measY}, by intro x; cases x <;> simp⟩

/-- Adjoined classical systems `Δ_{n+1}` (`n` an entry of `ds`) with their gates (Lemma F.9):
preparation of `δ_1` (the first label), readout of the label, discard. -/
inductive AdjGate (ds : List ℕ) where
  | prep (i : Fin ds.length)
  | read (i : Fin ds.length)
  | disc (i : Fin ds.length)
  deriving DecidableEq

instance (ds : List ℕ) : Fintype (AdjGate ds) := ⟨(Finset.univ.image AdjGate.prep ∪ Finset.univ.image AdjGate.read) ∪ Finset.univ.image AdjGate.disc, by intro x; cases x <;> simp⟩

/-! ### QC with adjoined classical systems (Example B.18, Lemma F.9) -/

/-- The elementary systems of `QC_ds`: the qubit, the classical bit, and `Δ_{n+1}` for each entry
`n` of `ds`. -/
inductive QCElem (ds : List ℕ) where
  | qubit
  | bit
  | adj (i : Fin ds.length)
  deriving DecidableEq

instance (ds : List ℕ) : Fintype (QCElem ds) := ⟨({.qubit, .bit} : Finset (QCElem ds)) ∪ Finset.univ.image QCElem.adj, by intro x; cases x <;> simp⟩

/-- The systems of QC: all trees, with the distinguished leaf read as a labelled Delta_3. -/
def okQC (_t : Tree) : Bool := true

lemma okQC_node (A B : Tree) (hA : okQC A = true) (hB : okQC B = true) : okQC (.node A B) = true := by
  rfl

def qcElem (ds : List ℕ) : QCElem ds → {t : Tree // okQC t = true}
  | .qubit => ⟨.quantum 1, rfl⟩
  | .bit => ⟨.classical 1, rfl⟩
  | .adj i => ⟨.classical (ds.get i), rfl⟩

/-- The core of `QC_ds`: classical–quantum registers and all quantum and classical systems;
channels the CPTP maps, instruments the CP families with CPTP sum (Example B.18). -/
def qcCore (ds : List ℕ) : Core :=
  treeCore none okQC okQC_node (fun _ => rfl) (QCElem ds) (qcElem ds)
    (fun A B => cptp A.1 B.1) (fun A B k => cpInst A.1 B.1 k)

/-- The wire matrices of a tree theory (qubit and bit coordinates; `0` on other wires). -/
def treeWire {w : Option (Set.Ioo (0 : ℝ) 1)} {ok : Tree → Bool} {Elem : Type}
    (elem : Elem → {t : Tree // ok t = true}) (x : Σ a : Elem, (tsys w (elem a).1).ι) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  twoLevel (elem x.1).1 (tcoord w _ x.2)

def QB.toQC (ds : List ℕ) : QB → QCElem ds
  | .qubit => .qubit
  | .bit => .bit

/-- The gate set of `QC_ds`: the quantum gates, the classical gates, and the gates of the adjoined
`Δ_{n+1}`. -/
abbrev QCGate (ds : List ℕ) := QGate ⊕ CGate ⊕ AdjGate ds

def qcIns (ds : List ℕ) : QCGate ds → List (QCElem ds)
  | .inl g => g.ins.map (QB.toQC ds)
  | .inr (.inl g) => g.ins.map (QB.toQC ds)
  | .inr (.inr (.prep _)) => []
  | .inr (.inr (.read i)) => [.adj i]
  | .inr (.inr (.disc i)) => [.adj i]

def qcOuts (ds : List ℕ) : QCGate ds → List (QCElem ds)
  | .inl g => g.outs.map (QB.toQC ds)
  | .inr (.inl g) => g.outs.map (QB.toQC ds)
  | .inr (.inr (.prep i)) => [.adj i]
  | .inr (.inr (.read _)) => []
  | .inr (.inr (.disc _)) => []

def qcNout (ds : List ℕ) : QCGate ds → ℕ
  | .inl g => g.nout
  | .inr (.inl g) => g.nout
  | .inr (.inr (.prep _)) => 1
  | .inr (.inr (.read i)) => ds.get i + 1
  | .inr (.inr (.disc _)) => 1

/-- The gate matrices of `QC_ds`. -/
def qcGateMat (ds : List ℕ) : (g : QCGate ds) → Fin (qcNout ds g) →
    Matrix ((qcCore ds).sys ((qcCore ds).reg (qcOuts ds g))).ι
      ((qcCore ds).sys ((qcCore ds).reg (qcIns ds g))).ι ℝ
  | .inl g, o => rawGateMat (qcCore ds) (treeWire (qcElem ds)) _ _ g.ins.length g.outs.length
      (g.kraus o)
  | .inr (.inl g), o => rawGateMat (qcCore ds) (treeWire (qcElem ds)) _ _ g.ins.length
      g.outs.length (g.kraus o)
  | .inr (.inr (.prep i)), _ =>
      (fun a _ => if a = 0 then 1 else 0 : Matrix (Fin (ds.get i + 1)) (Fin 1) ℝ)
  | .inr (.inr (.read i)), o =>
      (fun _ a => if a = o then 1 else 0 : Matrix (Fin 1) (Fin (ds.get i + 1)) ℝ)
  | .inr (.inr (.disc i)), _ => (fun _ _ => 1 : Matrix (Fin 1) (Fin (ds.get i + 1)) ℝ)

/-- The data of `QC_ds` (Example B.18 with the classical systems of `ds` adjoined, Lemma F.9). -/
def qcPre (ds : List ℕ) : PreTheory where
  C := qcCore ds
  Gate := QCGate ds
  ins := qcIns ds
  outs := qcOuts ds
  nout := qcNout ds
  gate := qcGateMat ds

/-! ### Classical theory (Example B.17), with adjoined classical systems -/

/-- The systems of classical theory: trees of classical leaves. -/
def okCl (t : Tree) : Bool := !t.hasQ

lemma okCl_node (A B : Tree) (hA : okCl A = true) (hB : okCl B = true) : okCl (.node A B) = true := by
  simp_all [okCl, Tree.hasQ]

/-- The elementary systems of classical theory: the bit and the adjoined `Δ_{n+1}`. -/
inductive ClElem (ds : List ℕ) where
  | bit
  | adj (i : Fin ds.length)
  deriving DecidableEq

instance (ds : List ℕ) : Fintype (ClElem ds) := ⟨({.bit} : Finset (ClElem ds)) ∪ Finset.univ.image ClElem.adj, by intro x; cases x <;> simp⟩

def clElem (ds : List ℕ) : ClElem ds → {t : Tree // okCl t = true}
  | .bit => ⟨.classical 1, rfl⟩
  | .adj i => ⟨.classical (ds.get i), rfl⟩

/-- The core of classical theory: systems `Δ_n` and their composites; channels the
column-stochastic matrices; instruments the families of nonnegative matrices with stochastic sum. -/
def clCore (ds : List ℕ) : Core :=
  treeCore none okCl okCl_node (fun _ => rfl) (ClElem ds) (clElem ds)
    (fun _ _ => {Φ | IsStochastic Φ})
    (fun _ _ _ => {Φ | (∀ o i j, 0 ≤ Φ o i j) ∧ IsStochastic (∑ o, Φ o)})

def QB.toCl (ds : List ℕ) : ClElem ds := .bit

/-- The gate set of classical theory: the classical gates, copy, and the gates of the adjoined
classical systems (Example B.17: Toffoli, fair coin, copy, bit readout, discard; with NOT and the
`δ_0` preparation of (T4)). -/
abbrev ClGate (ds : List ℕ) := CGate ⊕ Unit ⊕ AdjGate ds

def clIns (ds : List ℕ) : ClGate ds → List (ClElem ds)
  | .inl g => g.ins.map fun _ => .bit
  | .inr (.inl ()) => [.bit]
  | .inr (.inr (.prep _)) => []
  | .inr (.inr (.read i)) => [.adj i]
  | .inr (.inr (.disc i)) => [.adj i]

def clOuts (ds : List ℕ) : ClGate ds → List (ClElem ds)
  | .inl g => g.outs.map fun _ => .bit
  | .inr (.inl ()) => [.bit, .bit]
  | .inr (.inr (.prep i)) => [.adj i]
  | .inr (.inr (.read _)) => []
  | .inr (.inr (.disc _)) => []

def clNout (ds : List ℕ) : ClGate ds → ℕ
  | .inl g => g.nout
  | .inr (.inl ()) => 1
  | .inr (.inr (.prep _)) => 1
  | .inr (.inr (.read i)) => ds.get i + 1
  | .inr (.inr (.disc _)) => 1

def clGateMat (ds : List ℕ) : (g : ClGate ds) → Fin (clNout ds g) →
    Matrix ((clCore ds).sys ((clCore ds).reg (clOuts ds g))).ι
      ((clCore ds).sys ((clCore ds).reg (clIns ds g))).ι ℝ
  | .inl g, o => rawGateMat (clCore ds) (treeWire (clElem ds)) _ _ g.ins.length g.outs.length
      (g.kraus o)
  | .inr (.inl ()), _ => rawGateMat (clCore ds) (treeWire (clElem ds)) _ _ 1 2 [copyK 0, copyK 1]
  | .inr (.inr (.prep i)), _ =>
      (fun a _ => if a = 0 then 1 else 0 : Matrix (Fin (ds.get i + 1)) (Fin 1) ℝ)
  | .inr (.inr (.read i)), o =>
      (fun _ a => if a = o then 1 else 0 : Matrix (Fin 1) (Fin (ds.get i + 1)) ℝ)
  | .inr (.inr (.disc i)), _ => (fun _ _ => 1 : Matrix (Fin 1) (Fin (ds.get i + 1)) ℝ)

/-- The data of classical theory with the classical systems of `ds` adjoined (`ds = []`: classical
theory, Example B.17). -/
def clPre (ds : List ℕ) : PreTheory where
  C := clCore ds
  Gate := ClGate ds
  ins := clIns ds
  outs := clOuts ds
  nout := clNout ds
  gate := clGateMat ds

/-! ### The gates on `W_v` -/

def WGate.nout : WGate → ℕ
  | .measY => 2
  | _ => 1

/-- `e0 = (0, 0, 1)` as a preparation; `u = (0, 0, 1)` as the discard; `f_y = (0, 1, 0)` and
`u − f_y = (0, −1, 1)` as the two outcomes of the measurement (Examples B.5, B.22). -/
def wPrep : Matrix (Fin 3) (Fin 1) ℝ := fun i _ => if i = 2 then 1 else 0
def wDisc : Matrix (Fin 1) (Fin 3) ℝ := fun _ i => if i = 2 then 1 else 0
def wMeas (o : Fin 2) : Matrix (Fin 1) (Fin 3) ℝ :=
  fun _ i => if o = 0 then (if i = 1 then 1 else 0) else (if i = 1 then -1 else if i = 2 then 1 else 0)

/-! ### `G_v` (Example B.22) -/

/-- The systems of `G_v`: trees of classical and triangular leaves. -/
def okGv (t : Tree) : Bool := !t.hasQ

lemma okGv_node (A B : Tree) (hA : okGv A = true) (hB : okGv B = true) : okGv (.node A B) = true := by
  simp_all [okGv, Tree.hasQ]

/-- The elementary systems of `G_v`: `W_v` and the classical bit. -/
inductive GvElem where
  | wtri
  | bit
  deriving DecidableEq

instance : Fintype GvElem := ⟨{.wtri, .bit}, by intro x; cases x <;> simp⟩

def gvElem : GvElem → {t : Tree // okGv t = true}
  | .wtri => ⟨.tri, rfl⟩
  | .bit => ⟨.classical 1, rfl⟩

/-- The core of `G_v`: systems `Δ_n` and their composites with copies of `W_v`, every composite
the minimal tensor product (through the transport, see `Tree.wsys`); channels all positive
unit-preserving maps, instruments all families of positive maps with unit-preserving sum. -/
def gvCore (v : Set.Ioo (0 : ℝ) 1) : Core :=
  treeCore (some v) okGv okGv_node (fun _ => rfl) GvElem gvElem
    (fun A B => posChan v A.1 B.1) (fun A B k => posInst v A.1 B.1 k)

/-- The gate set of `G_v`: the classical gates of (T4) and the three gates on `W_v`. -/
abbrev GvGate := CGate ⊕ WGate

def gvIns : GvGate → List GvElem
  | .inl g => g.ins.map fun _ => .bit
  | .inr .prepE0 => []
  | .inr _ => [.wtri]

def gvOuts : GvGate → List GvElem
  | .inl g => g.outs.map fun _ => .bit
  | .inr .prepE0 => [.wtri]
  | .inr _ => []

def gvNout : GvGate → ℕ
  | .inl g => g.nout
  | .inr g => g.nout

def gvGateMat (v : Set.Ioo (0 : ℝ) 1) : (g : GvGate) → Fin (gvNout g) →
    Matrix ((gvCore v).sys ((gvCore v).reg (gvOuts g))).ι
      ((gvCore v).sys ((gvCore v).reg (gvIns g))).ι ℝ
  | .inl g, o => rawGateMat (gvCore v) (treeWire gvElem) _ _ g.ins.length g.outs.length
      (g.kraus o)
  | .inr .prepE0, _ => wPrep
  | .inr .discW, _ => wDisc
  | .inr .measY, o => wMeas o

/-- The data of `G_v`. -/
def gvPre (v : Set.Ioo (0 : ℝ) 1) : PreTheory where
  C := gvCore v
  Gate := GvGate
  ins := gvIns
  outs := gvOuts
  nout := gvNout
  gate := gvGateMat v

/-! ### `G^Q_v` (Example B.23) -/

/-- The elementary systems of `G^Q_v`: the qubit, the classical bit and `W_v`. -/
inductive GQvElem where
  | qubit
  | bit
  | wtri
  deriving DecidableEq

instance : Fintype GQvElem := ⟨{.qubit, .bit, .wtri}, by intro x; cases x <;> simp⟩

def gqvElem : GQvElem → {t : Tree // (fun _ => true : Tree → Bool) t = true}
  | .qubit => ⟨.quantum 1, rfl⟩
  | .bit => ⟨.classical 1, rfl⟩
  | .wtri => ⟨.tri, rfl⟩

/-- The core of `G^Q_v`: systems `A ⊗ W_v^{⊗c}` (all trees), cones and units transported from the
QC systems `A ⊗ Δ_3^{⊗c}` through `id ⊗ L_v^{⊗c}`; channels and instruments the transports of the
CPTP maps and CP instruments of QC: `Φ` is allowed iff `T_B Φ T_A⁻¹` is. -/
def gqvCore (v : Set.Ioo (0 : ℝ) 1) : Core :=
  treeCore (some v) (fun _ => true) (fun _ _ _ _ => rfl) (fun _ => rfl) GQvElem gqvElem
    (fun A B => {Φ | Tmat v B.1 * Matrix.reindex (tcoord _ B.1) (tcoord _ A.1) Φ * Tinv v A.1 ∈ cptp A.1 B.1})
    (fun A B k => {Φ | (fun o => Tmat v B.1 * Matrix.reindex (tcoord _ B.1) (tcoord _ A.1) (Φ o) * Tinv v A.1) ∈
      cpInst A.1 B.1 k})

def QB.toGQv : QB → GQvElem
  | .qubit => .qubit
  | .bit => .bit

/-- The gate set of `G^Q_v`: the quantum and classical gates and the three gates on `W_v`. -/
abbrev GQvGate := QGate ⊕ CGate ⊕ WGate

def gqvIns : GQvGate → List GQvElem
  | .inl g => g.ins.map QB.toGQv
  | .inr (.inl g) => g.ins.map QB.toGQv
  | .inr (.inr .prepE0) => []
  | .inr (.inr _) => [.wtri]

def gqvOuts : GQvGate → List GQvElem
  | .inl g => g.outs.map QB.toGQv
  | .inr (.inl g) => g.outs.map QB.toGQv
  | .inr (.inr .prepE0) => [.wtri]
  | .inr (.inr _) => []

def gqvNout : GQvGate → ℕ
  | .inl g => g.nout
  | .inr (.inl g) => g.nout
  | .inr (.inr g) => g.nout

def gqvGateMat (v : Set.Ioo (0 : ℝ) 1) : (g : GQvGate) → Fin (gqvNout g) →
    Matrix ((gqvCore v).sys ((gqvCore v).reg (gqvOuts g))).ι
      ((gqvCore v).sys ((gqvCore v).reg (gqvIns g))).ι ℝ
  | .inl g, o => rawGateMat (gqvCore v) (treeWire gqvElem) _ _ g.ins.length g.outs.length
      (g.kraus o)
  | .inr (.inl g), o => rawGateMat (gqvCore v) (treeWire gqvElem) _ _ g.ins.length g.outs.length
      (g.kraus o)
  | .inr (.inr .prepE0), _ => wPrep
  | .inr (.inr .discW), _ => wDisc
  | .inr (.inr .measY), o => wMeas o

/-- The data of `G^Q_v`. -/
def gqvPre (v : Set.Ioo (0 : ℝ) 1) : PreTheory where
  C := gqvCore v
  Gate := GQvGate
  ins := gqvIns
  outs := gqvOuts
  nout := gqvNout
  gate := gqvGateMat v

end GPTIP632.Classical.Supplement

end


