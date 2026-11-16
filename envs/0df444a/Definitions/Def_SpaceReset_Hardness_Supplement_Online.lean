-- Prove2me | Definitions.Def_SpaceReset_Hardness_Supplement_Online
-- name    : SpaceReset_Hardness_Supplement_Online
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T13:40:27.840931+00:00
-- url     : https://prove2.me/theorems/7f88fdd6-a7bc-4540-83bb-24d812c6af3c
-- title:
--   Online instruments with input and output registers, budgeted implementations, adaptive testers, the Choi state and the parity schedule $\mathcal P_m$
-- statement:
--   An **online instrument** with $N$ slots receives at slot $j$ an input register $I_j$ and returns an output register $O_j$ before the next slot; the output is never touched again. Here it is given as an online process: a private memory $M$, an initial memory state $\sigma$, and for each slot a map from $I_j\otimes M$ to $O_j\otimes M$. Slots are numbered $0,1,\dots$ (slot $j$ is the paper's slot $j+1$).
--
--   An **implementation with budgets $(q,g)$** (§4, p. 29, the analogue of Definition 4) has memory of dimension at most $2^q$, which counts every retained classical or quantum record, a freely chosen initial state $\sigma$, and slot isometries $V_j : I_j\otimes M\to O_j\otimes M\otimes E_j$. Fresh registers are pure. The discarded environments $E_j$ have product dimension at most $2^g$ and are never accessed again.
--
--   An **adaptive tester** holds a reference $R$. It prepares the first input jointly with $R$, and after slot $j$ it applies a channel from $O_j\otimes R$ to $I_{j+1}\otimes R$. The operational error of an implementation is the trace distance $d(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1$ between the tester's states under the implementation and under the target. It is maximized over all testers; the bound is required after every slot.
--
--   In a **non-adaptive experiment** the joint state of all inputs and an external reference is prepared in advance and the outputs are collected. The **normalized Choi state** (p. 8) feeds one half of a maximally entangled pair into every input and keeps all references and outputs. The definition also provides **basis runs** (computational-basis input strings), and the past and future output marginals at a cut $t$.
--
--   The **parity schedule** $\mathcal P_m$ (p. 8, Figure 1, p. 29) comprises $2m$ disjoint checks
--   $$\mathcal M(\rho)=\sum_{s=0}^{1}P_s\rho P_s\otimes|s\rangle\langle s|,\qquad P_s=\tfrac12\big(I+(-1)^sZ\otimes Z\big).$$
--   The first $m$ pairs arrive consecutively (0-based slots $2c,2c+1$). Then the first members of the last $m$ pairs arrive (slots $2m+i$), followed by their second members in the same order (slots $3m+i$). Each data qubit is returned in its arrival slot, and the syndrome bit accompanies the second member. The target is realized by accumulator bits that are never returned; tracing them out dephases the syndrome and keeps all coherence within parity sectors.
--
--   A **parity circuit** (§4.2, p. 31) acts on $q+2$ device qubits: the data carrier, the syndrome carrier and $q$ private cells. Each cell starts in $|0\rangle$ or in $I/2$, and each slot applies named gates ($H$, $S$, controlled-$X/Y/Z$, single-qubit RESET, $D_Z$). The definition also provides its online process and the counts of RESETs and of mixed cells.
--
--   **Formalization Note.** Register families are indexed by $\mathbb N$; an experiment with $N$ slots uses slots $0,\dots,N-1$. On a slot without a syndrome, the syndrome factor of the output is the trivial one-dimensional system. Non-adaptive experiments use one cell per slot, which holds the input before the slot and the output afterwards.
-- source:
--   Rinka Miura, STOC 2027 submission #1715 (October 2026), The Complexity of Space–Reset Tradeoffs in Online Quantum Computation (held submission, no arXiv version; SHA-256 c2a340e2195da0d130bf10d936d56d4f1d4da805e644efb7fe1c36d9c904f3e5), §1.5.4 p. 8; Figure 1 p. 9; §4 pp. 29–31 (Theorem 20, Lemma 21, §4.2)

import Mathlib
import Definitions.Def_SpaceReset_Hardness_Native

set_option autoImplicit false

noncomputable section

namespace SpaceReset.Hardness.Supplement

/-!
Rinka Miura, STOC 2027 submission #1715 (October 2026): online instruments with an input and an
output register per slot, their budgeted implementations, adaptive testers, non-adaptive
experiments, the normalized Choi state (§1.5.4, p. 8; §4, pp. 29–31), the parity schedule `P_m`
(p. 8, Figure 1 on p. 9, p. 29) and explicit Clifford circuits for it (§4.2, p. 31).

Conventions. Slots are numbered `0, 1, 2, …` (slot `j` is the paper's slot `j + 1`); slot `j`
receives an input register `I j` and returns an output register `O j` (finite types; a qubit is
`Bool`, `false = |0⟩`). The register families are indexed by all of `ℕ`; an experiment with `N`
slots uses slots `0, …, N − 1` only. An online process has a private memory `M`, an initial
memory state `σ` and a map per slot from `I j ⊗ M` to `O j ⊗ M`; the output register is returned
and never touched again. An adaptive tester holds a reference `R`, prepares the first input
jointly with `R`, and after slot `j` applies a channel from `O j ⊗ R` to `I (j+1) ⊗ R`: it may
entangle inputs with its reference, measure, and choose later inputs adaptively. The operational
error is the trace distance between the tester's states under the implementation and under the
target; the supremum over testers is stated as a bound for every tester, and the bound is
required after every slot `j < N` (the state after an earlier slot can be carried to the end in
the reference, so this is the same as the bound after the last slot).
-/

open Matrix
open SpaceReset.Hardness

section Model

variable (I O : ℕ → Type) [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]

/-- An online process (instrument) with register families `I`, `O`: memory `M`, initial memory
state `σ`, and the slot maps `Φ j : L(I j ⊗ M) → L(O j ⊗ M)`. -/
structure OProcess where
  M : Type
  [fM : Fintype M]
  [dM : DecidableEq M]
  σ : Matrix M M ℂ
  Φ : (j : ℕ) → Matrix (I j × M) (I j × M) ℂ → Matrix (O j × M) (O j × M) ℂ

attribute [instance] OProcess.fM OProcess.dM

/-- A valid online process: the initial memory state is a state and every slot map is a channel. -/
def OProcess.Valid {I O : ℕ → Type} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] (D : OProcess I O) : Prop :=
  IsDensity D.σ ∧ ∀ j, IsChannel (D.Φ j)

/-- An adaptive tester with a quantum reference `R`: initial state `τ` on `I 0 ⊗ R` and, after
slot `j`, a map `T j : L(O j ⊗ R) → L(I (j+1) ⊗ R)`. -/
structure OTester where
  R : Type
  [fR : Fintype R]
  [dR : DecidableEq R]
  τ : Matrix (I 0 × R) (I 0 × R) ℂ
  T : (j : ℕ) → Matrix (O j × R) (O j × R) ℂ → Matrix (I (j + 1) × R) (I (j + 1) × R) ℂ

attribute [instance] OTester.fR OTester.dR

/-- A tester is valid when its initial state is a state and all its maps are channels. -/
def OTester.Valid {I O : ℕ → Type} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] (T : OTester I O) : Prop :=
  IsDensity T.τ ∧ ∀ j, IsChannel (T.T j)

/-- Definition 4 for online instruments (§4, p. 29): an implementation with `N` slots, at most
`q` persistent private qubits (memory of dimension at most `2^q`, every retained classical or
quantum record included), a freely chosen initial memory state `σ`, and slot isometries
`V_j : I j ⊗ M → O j ⊗ M ⊗ E_j` (fresh registers are pure) whose discarded Stinespring
environments `E_j` have product dimension at most `2^g` and are never accessed again. -/
structure ODevice (N q g : ℕ) where
  M : Type
  [fM : Fintype M]
  [dM : DecidableEq M]
  card_le : Fintype.card M ≤ 2 ^ q
  σ : Matrix M M ℂ
  σ_density : IsDensity σ
  E : Fin N → Type
  [fE : ∀ j, Fintype (E j)]
  [dE : ∀ j, DecidableEq (E j)]
  V : (j : Fin N) → Matrix ((O j × M) × E j) (I j × M) ℂ
  isometry : ∀ j, (V j)ᴴ * V j = 1
  discard_le : ∏ j, Fintype.card (E j) ≤ 2 ^ g

attribute [instance] ODevice.fM ODevice.dM ODevice.fE ODevice.dE

end Model

section Run

variable {I O : ℕ → Type} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]

/-- The online process of an implementation: slot `j < N` acts by `ρ ↦ Tr_{E_j}(V_j ρ V_j†)`;
slots `j ≥ N` are never used. -/
def ODevice.toProcess {N q g : ℕ} (D : ODevice I O N q g) : OProcess I O where
  M := D.M
  σ := D.σ
  Φ := fun j ρ => if h : j < N then ptraceRight (D.V ⟨j, h⟩ * ρ * (D.V ⟨j, h⟩)ᴴ) else 0

section Apply

variable {A B M R : Type} [Fintype A] [Fintype B] [Fintype M] [Fintype R]

/-- `(Φ ⊗ id_R)` on `A ⊗ M ⊗ R` for a (linear) map `Φ : L(A ⊗ M) → L(B ⊗ M)`. -/
def applyDev (Φ : Matrix (A × M) (A × M) ℂ → Matrix (B × M) (B × M) ℂ)
    (ρ : Matrix (A × M × R) (A × M × R) ℂ) : Matrix (B × M × R) (B × M × R) ℂ :=
  fun x x' => Φ (fun a a' => ρ (a.1, a.2, x.2.2) (a'.1, a'.2, x'.2.2)) (x.1, x.2.1) (x'.1, x'.2.1)

/-- `(id_M ⊗ T)` on `B ⊗ M ⊗ R` for a (linear) map `T : L(B ⊗ R) → L(A ⊗ R)`. -/
def applyTes (T : Matrix (B × R) (B × R) ℂ → Matrix (A × R) (A × R) ℂ)
    (ρ : Matrix (B × M × R) (B × M × R) ℂ) : Matrix (A × M × R) (A × M × R) ℂ :=
  fun x x' => T (fun a a' => ρ (a.1, x.2.1, a.2) (a'.1, x'.2.1, a'.2)) (x.1, x.2.2) (x'.1, x'.2.2)

end Apply

/-- The joint state of `I j ⊗ M ⊗ R` when input `j` has just been prepared (after slots
`0, …, j − 1`, each followed by the tester's map). -/
def stateBefore (D : OProcess I O) (T : OTester I O) :
    (j : ℕ) → Matrix (I j × D.M × T.R) (I j × D.M × T.R) ℂ
  | 0 => fun x x' => T.τ (x.1, x.2.2) (x'.1, x'.2.2) * D.σ x.2.1 x'.2.1
  | j + 1 => applyTes (T.T j) (applyDev (D.Φ j) (stateBefore D T j))

/-- The tester's state on `O j ⊗ R` right after slot `j` (device memory traced out). -/
def outState (D : OProcess I O) (T : OTester I O) (j : ℕ) : Matrix (O j × T.R) (O j × T.R) ℂ :=
  fun a a' => ∑ m : D.M, applyDev (D.Φ j) (stateBefore D T j) (a.1, m, a.2) (a'.1, m, a'.2)

/-- Operational error at most `ε` over `N` slots (§4, p. 29): for every valid adaptive tester with
quantum reference and every slot `j < N`, the trace distance between the tester's states under
`D` and under the target is at most `ε`. -/
def OErrorLE (N : ℕ) (D Tgt : OProcess I O) (ε : ℝ) : Prop :=
  ∀ T : OTester I O, T.Valid → ∀ j, j < N → tdist (outState D T j) (outState Tgt T j) ≤ ε

/-! ### Non-adaptive experiments and the Choi state -/

/-- One cell per slot: it holds the slot's input before the slot and its output afterwards. -/
abbrev Cells (N : ℕ) := (k : Fin N) → I k ⊕ O k

/-- All cells holding inputs. -/
def allIn {N : ℕ} (x : (k : Fin N) → I k) : Cells (I := I) (O := O) N := fun k => Sum.inl (x k)

/-- All cells holding outputs. -/
def allOut {N : ℕ} (o : (k : Fin N) → O k) : Cells (I := I) (O := O) N := fun k => Sum.inr (o k)

variable {A : Type} [Fintype A] [DecidableEq A]

/-- Slot `j` of a non-adaptive experiment: the device acts on cell `j` (input → output) and its
memory; the other cells and the external reference `A` are spectators. -/
def collectStep {N : ℕ} (D : OProcess I O) (j : Fin N)
    (X : Matrix (Cells (I := I) (O := O) N × D.M × A) (Cells (I := I) (O := O) N × D.M × A) ℂ) :
    Matrix (Cells (I := I) (O := O) N × D.M × A) (Cells (I := I) (O := O) N × D.M × A) ℂ :=
  fun x x' => match x.1 j, x'.1 j with
    | Sum.inr o, Sum.inr o' =>
        D.Φ j (fun im im' => X (Function.update x.1 j (Sum.inl im.1), im.2, x.2.2)
          (Function.update x'.1 j (Sum.inl im'.1), im'.2, x'.2.2)) (o, x.2.1) (o', x'.2.1)
    | _, _ => 0

/-- The joint state after the first `t` slots of the non-adaptive experiment that prepares the
joint state `ω` of all `N` inputs and a reference `A` in advance. -/
def collectAux {N : ℕ} (D : OProcess I O)
    (ω : Matrix (((k : Fin N) → I k) × A) (((k : Fin N) → I k) × A) ℂ) :
    ℕ → Matrix (Cells (I := I) (O := O) N × D.M × A) (Cells (I := I) (O := O) N × D.M × A) ℂ
  | 0 => fun x x' => ∑ z : (k : Fin N) → I k, ∑ z' : (k : Fin N) → I k,
      if x.1 = allIn z ∧ x'.1 = allIn z' then ω (z, x.2.2) (z', x'.2.2) * D.σ x.2.1 x'.2.1 else 0
  | t + 1 => if h : t < N then collectStep D ⟨t, h⟩ (collectAux D ω t) else collectAux D ω t

/-- The non-adaptive experiment: the joint state of all `N` outputs and the reference `A` when the
inputs, jointly prepared with `A` in the state `ω`, are fed in slot order (memory traced out). -/
def collect (N : ℕ) (D : OProcess I O)
    (ω : Matrix (((k : Fin N) → I k) × A) (((k : Fin N) → I k) × A) ℂ) :
    Matrix (((k : Fin N) → O k) × A) (((k : Fin N) → O k) × A) ℂ :=
  fun p p' => ∑ m : D.M, collectAux D ω N (allOut p.1, m, p.2) (allOut p'.1, m, p'.2)

/-- The normalized Choi state (p. 8): one half of a maximally entangled pair is fed into every
input, and all references (copies of the inputs) and all outputs are kept. -/
def choiState (N : ℕ) (D : OProcess I O) :
    Matrix (((k : Fin N) → O k) × ((k : Fin N) → I k))
      (((k : Fin N) → O k) × ((k : Fin N) → I k)) ℂ :=
  collect N D (fun p p' => if p.1 = p.2 ∧ p'.1 = p'.2 then
    ((Fintype.card ((k : Fin N) → I k) : ℂ))⁻¹ else 0)

/-- The joint state of all `N` outputs when the computational-basis input string `x` is fed. -/
def basisRun (N : ℕ) (D : OProcess I O) (x : (k : Fin N) → I k) :
    Matrix ((k : Fin N) → O k) ((k : Fin N) → O k) ℂ :=
  fun o o' => collect N D (A := Unit) (ketbra (x, ())) (o, ()) (o', ())

/-- Splitting a string over the slots `0, …, N − 1` at the cut `t` into its past (slots `< t`)
and future (slots `≥ t`) parts. -/
def cutEquiv (N t : ℕ) (β : Fin N → Type) :
    ((k : Fin N) → β k) ≃
      ((k : {k : Fin N // k.val < t}) → β k) × ((k : {k : Fin N // ¬ k.val < t}) → β k) :=
  Equiv.piEquivPiSubtypeProd (fun k : Fin N => k.val < t) β

/-- The input string with past part `x` and future part `y`. -/
def joinInputs {N t : ℕ} (x : (k : {k : Fin N // k.val < t}) → I k)
    (y : (k : {k : Fin N // ¬ k.val < t}) → I k) : (k : Fin N) → I k :=
  (cutEquiv N t (fun k => I k)).symm (x, y)

/-- The marginal of an output state on the past outputs (slots `< t`). -/
def pastMarginal {N : ℕ} (t : ℕ) (ρ : Matrix ((k : Fin N) → O k) ((k : Fin N) → O k) ℂ) :
    Matrix ((k : {k : Fin N // k.val < t}) → O k) ((k : {k : Fin N // k.val < t}) → O k) ℂ :=
  ptraceRight (ρ.reindex (cutEquiv N t (fun k => O k)) (cutEquiv N t (fun k => O k)))

/-- The marginal of an output state on the future outputs (slots `≥ t`). -/
def futureMarginal {N : ℕ} (t : ℕ) (ρ : Matrix ((k : Fin N) → O k) ((k : Fin N) → O k) ℂ) :
    Matrix ((k : {k : Fin N // ¬ k.val < t}) → O k) ((k : {k : Fin N // ¬ k.val < t}) → O k) ℂ :=
  ptraceLeft (ρ.reindex (cutEquiv N t (fun k => O k)) (cutEquiv N t (fun k => O k)))

end Run

/-! ### The parity schedule `P_m` (p. 8, Figure 1, p. 29) -/

/-- The 0-based slot of the first member of check `c` (`c < m`: the early pairs, arriving
consecutively; `c = m + i`: the late pairs, whose first members all arrive before their second
members). -/
def firstSlot (m : ℕ) (c : Fin (2 * m)) : ℕ :=
  if c.val < m then 2 * c.val else 2 * m + (c.val - m)

/-- The 0-based slot of the second member of check `c`. -/
def secondSlot (m : ℕ) (c : Fin (2 * m)) : ℕ :=
  if c.val < m then 2 * c.val + 1 else 3 * m + (c.val - m)

/-- The checks whose second member arrives at slot `j` (exactly one on a syndrome slot, none
elsewhere). -/
abbrev SynIdx (m j : ℕ) := {c : Fin (2 * m) // secondSlot m c = j}

/-- The input register of `P_m`: one data qubit per slot. -/
abbrev PmIn : ℕ → Type := fun _ => Bool

/-- The output register of `P_m` at slot `j`: the data qubit, together with one syndrome qubit
per check closing at slot `j` (one syndrome qubit on the second member's slot; on other slots
this factor is the trivial one-dimensional system). -/
abbrev PmOut (m : ℕ) : ℕ → Type := fun j => Bool × (SynIdx m j → Bool)

/-- The matrix `Σ_a |f a⟩⟨a|` of a map of basis labels. -/
def basisMat {α β : Type} [DecidableEq β] (f : α → β) : Matrix β α ℂ :=
  fun b a => if f a = b then 1 else 0

/-- The classical-reversible step of the ideal parity instrument at slot `j`: the arriving data
bit `x` is returned unchanged and added into the accumulator bit of its check; on the second
member's slot the accumulated parity is also written to the syndrome output. -/
def parityStep (m j : ℕ) (p : Bool × (Fin (2 * m) → Bool)) :
    PmOut m j × (Fin (2 * m) → Bool) :=
  let acc' : Fin (2 * m) → Bool := fun c =>
    if firstSlot m c = j ∨ secondSlot m c = j then xor (p.2 c) p.1 else p.2 c
  ((p.1, fun c => acc' c.1), acc')

/-- The target instrument `P_m` (p. 29): `2m` disjoint parity checks
`M(ρ) = Σ_s P_s ρ P_s ⊗ |s⟩⟨s|`, `P_s = (I + (−1)^s Z ⊗ Z)/2`, with the arrival order of
Figure 1; each data qubit is returned in its arrival slot and the syndrome accompanies the second
member. It is realized here by accumulator bits (initially `|0⟩`) that are never returned:
since the accumulator keeps a copy of the syndrome, tracing it out dephases the syndrome while
keeping all coherence within parity sectors and with any reference. -/
def parityTarget (m : ℕ) : OProcess PmIn (PmOut m) where
  M := Fin (2 * m) → Bool
  σ := ketbra (fun _ => false)
  Φ := fun j ρ => basisMat (parityStep m j) * ρ * (basisMat (parityStep m j))ᴴ

/-! ### Explicit Clifford circuits for `P_m` (§4.2, p. 31) -/

/-- A Clifford circuit for `P_m` on `q + 2` device qubits: wire `0` is the current data carrier,
wire `1` the syndrome carrier (fresh `|0⟩` at every slot), and wires `2, …, q + 1` are the `q`
private cells, each starting in `|0⟩` (`cells i = false`) or maximally mixed `I/2`
(`cells i = true`). Slot `j` applies the named gates `gates j` (first gate first). -/
structure ParityCircuit (m q : ℕ) where
  cells : Fin q → Bool
  gates : ℕ → List (CGate (q + 2))

/-- The wire string with data bit `d`, syndrome bit `s` and private cells `x`. -/
def toWires {q : ℕ} (d s : Bool) (x : Fin q → Bool) : Fin (q + 2) → Bool :=
  Fin.cons d (Fin.cons s x)

/-- The private cells of a wire string. -/
def memOf {q : ℕ} (w : Fin (q + 2) → Bool) : Fin q → Bool := fun i => w i.succ.succ

open Classical in
/-- The online process of a parity circuit. At slot `j` the data input and the private memory are
placed on wires `0` and `2, …`, the syndrome wire starts in `|0⟩`, the gates act, and the data
wire is returned together with the syndrome wire on a syndrome slot; on any other slot the
syndrome wire is traced out (it is untouched there, see `ParityCircuit.SynClean`). -/
def ParityCircuit.toProcess {m q : ℕ} (C : ParityCircuit m q) : OProcess PmIn (PmOut m) where
  M := Fin q → Bool
  σ := cellState C.cells
  Φ := fun j ρ =>
    let X : Matrix (Fin (q + 2) → Bool) (Fin (q + 2) → Bool) ℂ := fun w w' =>
      if w 1 = false ∧ w' 1 = false then ρ (w 0, memOf w) (w' 0, memOf w') else 0
    let Y := applyGates ((C.gates j).map Gate.named) X
    fun a a' => ∑ b : Bool, ∑ b' : Bool,
      if (∀ c, a.1.2 c = b) ∧ (∀ c, a'.1.2 c = b') ∧ (Nonempty (SynIdx m j) ∨ b = b') then
        Y (toWires a.1.1 b a.2) (toWires a'.1.1 b' a'.2) else 0

/-- The wires a named gate acts on. -/
def gateWires {P : ℕ} : CGate P → List (Fin P)
  | .h w => [w]
  | .s w => [w]
  | .cx a b => [a, b]
  | .cy a b => [a, b]
  | .cz a b => [a, b]
  | .reset w => [w]
  | .dz w => [w]

/-- Only Clifford gates (`H`, `S`, controlled-`X/Y/Z`) and single-qubit `RESET`s: no `D_Z`. -/
def ParityCircuit.CliffordResetOnly {m q : ℕ} (C : ParityCircuit m q) : Prop :=
  ∀ j, ∀ gt ∈ C.gates j, ∀ w, gt ≠ CGate.dz w

/-- The syndrome carrier is used only on syndrome slots: on every other slot no gate touches
wire `1`, so it stays in its fresh `|0⟩` and nothing is discarded through it. -/
def ParityCircuit.SynClean {m q : ℕ} (C : ParityCircuit m q) : Prop :=
  ∀ j, IsEmpty (SynIdx m j) → ∀ gt ∈ C.gates j, (1 : Fin (q + 2)) ∉ gateWires gt

/-- The number of `RESET` gates in the slots `0, …, 4m − 1`. -/
def ParityCircuit.resetCount {m q : ℕ} (C : ParityCircuit m q) : ℕ :=
  ∑ j ∈ Finset.range (4 * m), ((C.gates j).filter (fun gt => match gt with
    | .reset _ => true | _ => false)).length

/-- The number of initially maximally mixed private cells. -/
def ParityCircuit.mixedCount {m q : ℕ} (C : ParityCircuit m q) : ℕ :=
  (Finset.univ.filter (fun i => C.cells i = true)).card

end SpaceReset.Hardness.Supplement


