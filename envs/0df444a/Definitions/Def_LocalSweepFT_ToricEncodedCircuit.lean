-- Prove2me | Definitions.Def_LocalSweepFT_ToricEncodedCircuit
-- name    : LocalSweepFT_ToricEncodedCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:44:04.648529+00:00
-- url     : https://prove2.me/theorems/a7d297e9-253a-41ff-9c3d-2c332a77a214
-- title:
--   Toric encoded circuits (hybrid layers), their noisy runs under Pauli fault layers, depth and width
-- statement:
--   A **Toric encoded circuit** $\tilde C$ has $R$ quantum registers, each a side-$n$ $(d,d')$-Toric code in the nice encoding, and $nb$ classical bits. At $t=0$ every register holds $|\bar0\rangle$, the encoded $|S\rangle=S|+\rangle$, the encoded $|T\rangle=T|+\rangle$, or one half of the encoded two-register resource $|H\rangle=(I\otimes H)(|00\rangle+|11\rangle)/\sqrt2$, and every bit is $0$. Its layers alternate:
--   1. odd times: logical layers of logical Paulis $X_{S'}$, $Z_{S'}$, the same controlled by a classical bit, transversal CX (possibly controlled by a classical bit), measurement of every qubit of a register in the computational or phase basis into classical bits, and any two-bit classical gates;
--   2. even times: the sweep cycle on every register, together with two-bit classical gates;
--
--   the operations of a layer having disjoint supports. The depth is the number of layers and the width is $R\binom{d}{d'}n^d+nb$.
--
--   A **fault pattern** puts a single-qubit Pauli $X^aZ^b$ on every (layer, register qubit) location. The **run** $\tilde C[E]$ applies, for each layer $t$, the fault layer $t$ and then layer $t$ to the initial state; the zero pattern is the noiseless run.
--
--   This is the circuit model of the threshold theorem, pinned down from Def. 5.13 and §§4.5–4.6.
--
--   **Formalization Note** Layer index $t$ is time $t+1$; the first fault layer precedes the first layer ($m=1$). Classical bits are never faulty (p.4: "reliable classical bits and logic"). Measured registers stay in the circuit as quantum wires.
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5…), Definition 5.13, pp.44–45; Definitions 3.4 and 3.7, pp.13–14; §§4.5–4.6, pp.32–39

import Mathlib
import Definitions.Def_LocalSweepFT_Chain
import Definitions.Def_LocalSweepFT_xLog
import Definitions.Def_LocalSweepFT_IsSweepRule
import Definitions.Def_LocalSweepFT_liftOn
import Definitions.Def_LocalSweepFT_encMat
import Definitions.Def_LocalSweepFT_sweepCycleKraus

open Matrix

namespace LocalSweepFT

/-! Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*, arXiv:2610.38847 (version of
November 3, 2026, sha256 85723eb5…): Toric encoded circuits (Def 5.13, pp.44–45) as hybrid
quantum–classical circuits, their noisy runs under Pauli fault layers (Defs 3.4, 3.7, pp.13–14), and
their depth and width. -/

/-- The wires of a hybrid circuit with `R` quantum registers of the side-`n` `(d, d′)`-Toric code
(one qubit per `d′`-cell) and `nb` classical bits. -/
abbrev Wire (R nb d d' n : ℕ) := (Fin R × QCell d d' n) ⊕ Fin nb

/-- A classical two-bit gate `g` on the distinct bits `c₁, c₂` (Def 5.13: "we allow any two-bit
gates" on the classical registers). -/
structure ClGate (nb : ℕ) where
  c₁ : Fin nb
  c₂ : Fin nb
  ne : c₁ ≠ c₂
  g : ZMod 2 × ZMod 2 → ZMod 2 × ZMod 2

/-- The operations of an odd ("logical") layer (Def 5.13 item 2; §4.5–4.6):
* `logX r`, `logZ r`: the logical Paulis `X_{S′}`, `Z_{S′}` on register `r` (Claim 4.30);
* `ctrlLogX c r`, `ctrlLogZ c r`: the same, controlled by the classical bit `c` (the corrections of
  the gate-teleportation gadgets, Figs. 8–9);
* `cx r r'`: transversal CX, qubit `θ` of register `r` controlling qubit `θ` of register `r'`;
* `ctrlCX c r r'`: the same, controlled by the classical bit `c` (the conditional use of the `|S⟩`
  resource in the T-teleportation gadget, Fig. 11, p.38; conditional gates, Remark 3.9, p.15);
* `measZ r f`, `measX r f`: measure every qubit `θ` of register `r` in the computational (resp.
  phase) basis, writing the outcome into the classical bit `f θ`;
* `cgate G`: a classical two-bit gate. -/
inductive LogOp (R nb d d' n : ℕ)
  | logX (r : Fin R)
  | logZ (r : Fin R)
  | ctrlLogX (c : Fin nb) (r : Fin R)
  | ctrlLogZ (c : Fin nb) (r : Fin R)
  | cx (r r' : Fin R) (ne : r ≠ r')
  | ctrlCX (c : Fin nb) (r r' : Fin R) (ne : r ≠ r')
  | measZ (r : Fin R) (f : QCell d d' n ↪ Fin nb)
  | measX (r : Fin R) (f : QCell d d' n ↪ Fin nb)
  | cgate (G : ClGate nb)

/-- A layer: an odd layer of logical operations, or an even layer consisting of the sweep cycle on
every quantum register together with classical two-bit gates (Def 5.13 item 2). -/
inductive Layer (R nb d d' n : ℕ)
  | logical (ops : List (LogOp R nb d d' n))
  | sweep (cls : List (ClGate nb))

variable {R nb d d' n : ℕ}

/-- The wires of register `r`. -/
def regWires (r : Fin R) : Set (Wire R nb d d' n) := {w | ∃ q, w = Sum.inl (r, q)}

/-- The support of a classical gate. -/
def ClGate.supp (G : ClGate nb) : Set (Wire R nb d d' n) := {Sum.inr G.c₁, Sum.inr G.c₂}

/-- The support of a logical-layer operation. -/
def LogOp.supp : LogOp R nb d d' n → Set (Wire R nb d d' n)
  | .logX r => regWires r
  | .logZ r => regWires r
  | .ctrlLogX c r => insert (Sum.inr c) (regWires r)
  | .ctrlLogZ c r => insert (Sum.inr c) (regWires r)
  | .cx r r' _ => regWires r ∪ regWires r'
  | .ctrlCX c r r' _ => insert (Sum.inr c) (regWires r ∪ regWires r')
  | .measZ r f => regWires r ∪ Set.range (fun q => Sum.inr (f q))
  | .measX r f => regWires r ∪ Set.range (fun q => Sum.inr (f q))
  | .cgate G => G.supp

/-- The operations of a layer have pairwise disjoint supports (Def 3.1, p.12). -/
def Layer.WellFormed : Layer R nb d d' n → Prop
  | .logical ops => ops.Pairwise (fun a b => Disjoint a.supp b.supp)
  | .sweep cls => cls.Pairwise (fun a b => Disjoint (ClGate.supp (R := R) (d := d) (d' := d')
      (n := n) a) (ClGate.supp b))

/-- The layer is an odd (logical) layer. -/
def Layer.IsLogical : Layer R nb d d' n → Prop
  | .logical _ => True
  | .sweep _ => False

/-- The initial content of a quantum register at `t = 0` (Def 5.13 item 1): `|0̄⟩`, the encoded
resource state `|S⟩ = S|+⟩` or `|T⟩ = T|+⟩`, or one half of the encoded two-register resource
`|H⟩ = (I ⊗ H)(|00⟩ + |11⟩)/√2` (p.35). -/
inductive ResourceKind
  | zero | magicS | magicT | hadamardFirst | hadamardSecond

/-- The initialization of the `R` registers: a resource kind for each register, and for the two
halves of each `|H⟩` resource their partner register. -/
structure InitSpec (R : ℕ) where
  kind : Fin R → ResourceKind
  partner : Fin R → Fin R
  first_ok : ∀ r, kind r = .hadamardFirst →
    kind (partner r) = .hadamardSecond ∧ partner (partner r) = r
  second_ok : ∀ r, kind r = .hadamardSecond →
    kind (partner r) = .hadamardFirst ∧ partner (partner r) = r

/-- A Toric encoded circuit (Def 5.13, pp.44–45) whose quantum registers are encoded in the nice
encoding of the side-`n` `(d, d′)`-Toric code: `R` registers, `nb` classical bits (initialized to
`0`), an initialization of the registers, and `depth` layers, indexed `0, …, depth − 1`, that
alternate between logical layers (even index) and sweep layers (odd index), each with pairwise
disjoint supports.

**Formalization Note.** Layer index `t` is time `t + 1` of Def 5.13 (time `0` is the
initialization), so logical layers are at odd times and sweep cycles at even times, as in the
paper. -/
structure ToricEncodedCircuit (d d' n : ℕ) where
  R : ℕ
  nb : ℕ
  init : InitSpec R
  depth : ℕ
  layer : Fin depth → Layer R nb d d' n
  alternating : ∀ t : Fin depth, (layer t).IsLogical ↔ Even (t : ℕ)
  wellFormed : ∀ t, (layer t).WellFormed

/-- The depth of `C̃`: its number of layers (classical computation included). -/
def ToricEncodedCircuit.depthOf (C : ToricEncodedCircuit d d' n) : ℕ := C.depth

/-- The width of `C̃`: its number of wires, `R · C(d, d′) n^d` qubits plus `nb` classical bits. -/
def ToricEncodedCircuit.width (C : ToricEncodedCircuit d d' n) : ℕ :=
  C.R * (Nat.choose d d' * n ^ d) + C.nb

variable [NeZero n]

/-- The computational-basis strings of the wires form a finite type (an explicit instance, since
the default instance search needs a larger size bound for this nested type). -/
noncomputable instance instFintypeWireBasis : Fintype (Wire R nb d d' n → ZMod 2) := Pi.instFintype

/-- Decidable equality of computational-basis strings of the wires. -/
instance instDecEqWireBasis : DecidableEq (Wire R nb d d' n → ZMod 2) :=
  Fintype.decidablePiFintype

/-- Register `r` as a map of its qubits into the wires. -/
def regEmb (r : Fin R) : QCell d d' n → Wire R nb d d' n := fun q => Sum.inl (r, q)

open Classical in
/-- The operator `K`, controlled by one classical bit (the `Unit` wire). -/
noncomputable def ctrlOp {A : Type} [Fintype A] [DecidableEq A] (K : Op A) : Op (A ⊕ Unit) :=
  fun a b =>
  if a (Sum.inr ()) = b (Sum.inr ()) then
    (if b (Sum.inr ()) = 1 then K (a ∘ Sum.inl) (b ∘ Sum.inl)
      else (if a ∘ Sum.inl = b ∘ Sum.inl then 1 else 0))
  else 0

open Classical in
/-- Transversal CX between two registers: qubit `θ` of the first controls qubit `θ` of the
second. -/
noncomputable def cxOp : Op (QCell d d' n ⊕ QCell d d' n) := fun a b =>
  if a ∘ Sum.inl = b ∘ Sum.inl ∧ a ∘ Sum.inr = b ∘ Sum.inr + b ∘ Sum.inl then 1 else 0

open Classical in
/-- The Kraus operator of outcome `β` of the computational-basis measurement of a register (left
summand) into bits (right summand): project the register on `|β⟩` and add `β` into the bits. -/
noncomputable def measKraus (β : QCell d d' n → ZMod 2) : Op (QCell d d' n ⊕ QCell d d' n) :=
  fun a b => if b ∘ Sum.inl = β ∧ a ∘ Sum.inl = β ∧ a ∘ Sum.inr = b ∘ Sum.inr + β then 1 else 0

open Classical in
/-- The transversal Hadamard on the register (left summand), identity on the bits. -/
noncomputable def hadReg : Op (QCell d d' n ⊕ QCell d d' n) := fun a b =>
  if a ∘ Sum.inr = b ∘ Sum.inr then hadOn (a ∘ Sum.inl) (b ∘ Sum.inl) else 0

open Classical in
/-- The Kraus family of a classical two-bit gate, `{|g(β)⟩⟨β| : β}`. -/
noncomputable def ClGate.kraus (G : ClGate nb) : List (Op (Wire R nb d d' n)) :=
  (Finset.univ : Finset (ZMod 2 × ZMod 2)).toList.map fun β =>
    liftOn (![Sum.inr G.c₁, Sum.inr G.c₂] : Fin 2 → Wire R nb d d' n)
      (fun a b => if b 0 = β.1 ∧ b 1 = β.2 ∧ a 0 = (G.g β).1 ∧ a 1 = (G.g β).2 then 1 else 0)

/-- The Kraus family of a logical-layer operation, for the nice encoding with direction set `S′`. -/
noncomputable def LogOp.kraus (S : DirSet d d') : LogOp R nb d d' n → List (Op (Wire R nb d d' n))
  | .logX r => [liftOn (regEmb r) (xOn ⇑(xLog (n := n) S))]
  | .logZ r => [liftOn (regEmb r) (zOn ⇑(zLog (n := n) S))]
  | .ctrlLogX c r =>
      [liftOn (Sum.elim (regEmb r) (fun _ => Sum.inr c)) (ctrlOp (xOn ⇑(xLog (n := n) S)))]
  | .ctrlLogZ c r =>
      [liftOn (Sum.elim (regEmb r) (fun _ => Sum.inr c)) (ctrlOp (zOn ⇑(zLog (n := n) S)))]
  | .cx r r' _ => [liftOn (Sum.elim (regEmb r) (regEmb r')) cxOp]
  | .ctrlCX c r r' _ =>
      [liftOn (Sum.elim (Sum.elim (regEmb r) (regEmb r')) (fun _ => Sum.inr c)) (ctrlOp cxOp)]
  | .measZ r f => (Finset.univ : Finset (QCell d d' n → ZMod 2)).toList.map fun β =>
      liftOn (Sum.elim (regEmb r) (fun q => Sum.inr (f q))) (measKraus β)
  | .measX r f => (Finset.univ : Finset (QCell d d' n → ZMod 2)).toList.map fun β =>
      liftOn (Sum.elim (regEmb r) (fun q => Sum.inr (f q))) (hadReg * measKraus β * hadReg)
  | .cgate G => G.kraus

/-- Sequential composition of a list of Kraus families. -/
noncomputable def seqK {W : Type} [Fintype W] [DecidableEq W] (L : List (List (Op W))) :
    List (Op W) :=
  L.foldl compK [1]

/-- The Kraus family of a layer: the logical operations one after the other, or the sweep cycle
(with sweep rules `rule₁`, `rule₂`) on every register followed by the classical gates. -/
noncomputable def Layer.kraus (h : d' + (d - d') = d) (S : DirSet d d')
    (rule₁ : LocalRule d d') (rule₂ : LocalRule d (d - d')) :
    Layer R nb d d' n → List (Op (Wire R nb d d' n))
  | .logical ops => seqK (ops.map (LogOp.kraus S))
  | .sweep cls => seqK ((List.finRange R).map
      (fun r => (sweepCycleKraus (n := n) h rule₁ rule₂).map (liftOn (regEmb r))) ++
      cls.map ClGate.kraus)

/-- The logical amplitude `⟨a|ψ_init⟩` of the initial resource states of the registers. -/
noncomputable def logicalAmp (I : InitSpec R) (a : Fin R → ZMod 2) : ℂ :=
  ∏ r, match I.kind r with
    | .zero => if a r = 0 then 1 else 0
    | .magicS => (Real.sqrt 2 : ℂ)⁻¹ * (if a r = 0 then 1 else Complex.I)
    | .magicT => (Real.sqrt 2 : ℂ)⁻¹ *
        (if a r = 0 then 1 else Complex.exp (Complex.I * ((Real.pi / 4 : ℝ) : ℂ)))
    | .hadamardFirst => (1 / 2 : ℂ) * sgn (a r * a (I.partner r))
    | .hadamardSecond => 1

open Classical in
/-- The initial pure state of `C̃` at `t = 0` (Def 5.13 item 1): every register is encoded in the
nice encoding with direction set `S′`, carrying its resource state, and every classical bit is
`0`. -/
noncomputable def initVec (S : DirSet d d') (C : ToricEncodedCircuit d d' n) :
    (Wire C.R C.nb d d' n → ZMod 2) → ℂ := fun x =>
  (if ∀ c, x (Sum.inr c) = 0 then 1 else 0) *
    ∑ a : Fin C.R → ZMod 2, logicalAmp C.init a * ∏ r, encAmp S (a r) (fun q => x (Sum.inl (r, q)))

/-- The initial density matrix `|ψ₀⟩⟨ψ₀|`. -/
noncomputable def initState (S : DirSet d d') (C : ToricEncodedCircuit d d' n) :
    Op (Wire C.R C.nb d d' n) :=
  fun x y => initVec S C x * star (initVec S C y)

/-- A fault pattern of `C̃` (Defs 3.4, 3.7): a single-qubit Pauli `X^a Z^b` at every location
`(t, q)`, `t` a layer index and `q` a qubit of a quantum register; the fault layer `t` is applied
just before layer `t` (so the first one precedes the first layer, `m = 1`). Classical bits are never
faulty. The zero pattern is the noiseless run. -/
abbrev FaultPattern (C : ToricEncodedCircuit d d' n) :=
  Fin C.depth → (Fin C.R × QCell d d' n) → ZMod 2 × ZMod 2

/-- The Pauli fault layer `Π_q X_q^{e(q).1} Z_q^{e(q).2}` on the quantum wires. -/
noncomputable def faultOp (e : (Fin R × QCell d d' n) → ZMod 2 × ZMod 2) :
    Op (Wire R nb d d' n) :=
  xOn (Sum.elim (fun q => (e q).1) (0 : Fin nb → ZMod 2) : Wire R nb d d' n → ZMod 2) *
    zOn (Sum.elim (fun q => (e q).2) (0 : Fin nb → ZMod 2) : Wire R nb d d' n → ZMod 2)

/-- The run `C̃[E] ∘ ρ₀` (Defs 3.3–3.4) with the fault pattern `E`, the sweep rules `rule₁`, `rule₂`
and the nice encoding with direction set `S′ = {1_1, …, 1_{d′}}`: for `t = 0, …, depth − 1`, apply
fault layer `t`, then layer `t`. -/
noncomputable def run (hd : d' ≤ d) (rule₁ : LocalRule d d') (rule₂ : LocalRule d (d - d'))
    (C : ToricEncodedCircuit d d' n) (E : FaultPattern C) : Op (Wire C.R C.nb d d' n) :=
  (List.finRange C.depth).foldl
    (fun ρ t => applyK ((C.layer t).kraus (Nat.add_sub_cancel' hd) (Sfix hd) rule₁ rule₂)
      (applyK [faultOp (E t)] ρ))
    (initState (Sfix hd) C)

end LocalSweepFT


