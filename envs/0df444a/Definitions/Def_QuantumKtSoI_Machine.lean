-- Prove2me | Definitions.Def_QuantumKtSoI_Machine
-- name    : QuantumKtSoI_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:32:52.988204+00:00
-- url     : https://prove2.me/theorems/a9295d0d-db29-4905-9410-f8d932a4976a
-- title:
--   Machines of Definition 3.1: controlled machines with classical and qubit tapes
-- statement:
--   A **machine** (Definition 3.1, §2.2) has finitely many states $Q$ and tapes $T$. Each tape is classical or qubit and has a finite alphabet; tape $\mathrm{in}$ is the input tape and $\mathrm{out}$ the output tape. A nonfinal state is either **classical**, with a set $T_p$ of active tapes and a transition sending the tuple $\sigma$ of scanned active symbols to a next state, symbols written on the active tapes, and a move $L,N,R$ for every head; or a **gate state**, with a gate $g_p\in\{H,X,\mathrm{CNOT},\mathrm{SWAP},\mathrm{Toff}\}$, an ordered tuple of active tapes, a next state and a move tuple. Gate entries are those of
--   $$H|b\rangle=\tfrac{1}{\sqrt2}\big(|0\rangle+(-1)^b|1\rangle\big),\quad X|b\rangle=|1-b\rangle,\quad \mathrm{CNOT}|a,b\rangle=|a,a\oplus b\rangle,\quad \mathrm{SWAP}|a,b\rangle=|b,a\rangle,\quad \mathrm{Toff}|a,b,c\rangle=|a,b,c\oplus ab\rangle .$$
--
--   A machine is **valid** when it satisfies conditions (i)–(iv) of Definition 3.1:
--   1. every alphabet contains the endmarker $\vdash$; a qubit alphabet is $\{\vdash,0,1\}$ (blank $0$); a classical alphabet contains a blank $\#$;
--   2. every qubit tape has a classical companion whose head makes the same move in every transition row; a classical step writes $\vdash$ on an active tape exactly when it scans $\vdash$ there; a classical head moves left only if its tape is active and does not scan $\vdash$, and a qubit head only if some companion is active and does not scan $\vdash$; gate states move heads only by $N$ or $R$;
--   3. the active tapes of a gate state are distinct qubit tapes, as many as the gate acts on;
--   4. the input and output tapes are distinct classical tapes with alphabet $\{\vdash,0,1,\#\}$, and every classical step writes back the symbol scanned on the input tape.
--
--   Machines are the witnesses charged by quantum Kt complexity; their semantics is `Machine.outputProb`.
--
--   **Formalization Note** All alphabets are finite subsets of one countable symbol type, which renames symbols only. A classical transition is applied to the scanned tuple with inactive coordinates masked, so it depends on the active symbols only. Every qubit tape carries a designated companion (used by the constructions of §3.2); validity requires it to be a companion. Fields that do not apply to a state's kind are ignored.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), §2.2, pp.15–16; Definition 3.1, p.20

import Mathlib

namespace QuantumKtSoI

/-- Tape symbols. `mark` is the endmarker `⊢`, `b0`/`b1` the bits `0`/`1`, `blank` the
classical blank `#`, and `other n` the further symbols a classical alphabet may contain
(Definition 3.1(i), p.20).

**Formalization Note** Every tape alphabet is a finite subset of this one countable symbol type;
a finite alphabet of any machine is a renaming of such a subset. -/
inductive Sym
  | mark
  | b0
  | b1
  | blank
  | other (n : ℕ)
  deriving DecidableEq

/-- The symbol of a bit. -/
def Sym.ofBit (b : Bool) : Sym := if b then Sym.b1 else Sym.b0

/-- Head moves `L`, `N`, `R` (§2.2, p.15). -/
inductive Move
  | L
  | N
  | R
  deriving DecidableEq

/-- The displacement of a head move: `L ↦ −1`, `N ↦ 0`, `R ↦ +1` (§2.2, p.16). -/
def Move.toInt : Move → ℤ
  | .L => -1
  | .N => 0
  | .R => 1

/-- The two kinds of tapes of Definition 3.1 (p.20). -/
inductive TapeKind
  | classical
  | qubit
  deriving DecidableEq

/-- The gate set `G = {H, X, CNOT, SWAP, Toff}` (§3.1, p.20). -/
inductive Gate
  | H
  | X
  | CNOT
  | SWAP
  | Toff
  deriving DecidableEq

/-- The number of qubits a gate acts on. -/
def Gate.arity : Gate → ℕ
  | .H => 1
  | .X => 1
  | .CNOT => 2
  | .SWAP => 2
  | .Toff => 3

/-- The matrix entry `g[ζ', ζ]` (row `ζ'` = output bits, column `ζ` = input bits) of a gate in
the computational basis (§2.2, p.15; §3.1, p.20):
`H|b⟩ = (|0⟩ + (−1)^b|1⟩)/√2`, `X|b⟩ = |1−b⟩`, `CNOT|a,b⟩ = |a,a⊕b⟩`, `SWAP|a,b⟩ = |b,a⟩`,
`Toff|a,b,c⟩ = |a,b,c⊕ab⟩`. -/
noncomputable def Gate.amp : (g : Gate) → (Fin g.arity → Bool) → (Fin g.arity → Bool) → ℂ
  | .H, o, i =>
      if (i ⟨0, by decide⟩ && o ⟨0, by decide⟩) then -(1 / (Real.sqrt 2 : ℂ)) else 1 / (Real.sqrt 2 : ℂ)
  | .X, o, i => if o ⟨0, by decide⟩ = !(i ⟨0, by decide⟩) then 1 else 0
  | .CNOT, o, i =>
      if o ⟨0, by decide⟩ = i ⟨0, by decide⟩ ∧
          o ⟨1, by decide⟩ = xor (i ⟨0, by decide⟩) (i ⟨1, by decide⟩) then 1 else 0
  | .SWAP, o, i =>
      if o ⟨0, by decide⟩ = i ⟨1, by decide⟩ ∧ o ⟨1, by decide⟩ = i ⟨0, by decide⟩ then 1 else 0
  | .Toff, o, i =>
      if o ⟨0, by decide⟩ = i ⟨0, by decide⟩ ∧ o ⟨1, by decide⟩ = i ⟨1, by decide⟩ ∧
          o ⟨2, by decide⟩ = xor (i ⟨2, by decide⟩) (i ⟨0, by decide⟩ && i ⟨1, by decide⟩)
        then 1 else 0

/-- A **machine**: a controlled machine (§2.2, pp.15–16) with classical and qubit tapes
(Definition 3.1, p.20), given as raw data. Its legality conditions are `Machine.Valid`.

* `Q` states and `T` tapes, both finite;
* `kind t` and the finite alphabet `alph t` of each tape; `inT`, `outT` the input and output tape;
* `companion t`, the designated companion of a qubit tape (p.23, p.26);
* `init` the initial state, `isFinal`, and `isGate` (a nonfinal state is a gate state or a
  classical state);
* a classical state `p` has the active tapes `act p` and the transition `δ p`, which maps the
  tuple of scanned symbols (inactive coordinates masked, see `Machine.mask`) to the next state,
  the symbols written on the active tapes and a move for every tape;
* a gate state `p` has a gate `gate p`, the ordered tuple `gtapes p` of its active tapes, a next
  state `gnext p` and a move tuple `gmove p`.

**Formalization Note** Fields of a state that do not apply to its kind (the gate fields of a
classical state, and every field of a final state) are ignored by the semantics. -/
structure Machine where
  Q : Type
  T : Type
  [instFQ : Fintype Q]
  [instDQ : DecidableEq Q]
  [instFT : Fintype T]
  [instDT : DecidableEq T]
  kind : T → TapeKind
  alph : T → Finset Sym
  inT : T
  outT : T
  companion : T → T
  init : Q
  isFinal : Q → Bool
  isGate : Q → Bool
  act : Q → Finset T
  δ : Q → (T → Sym) → Q × (T → Sym) × (T → Move)
  gate : Q → Gate
  gtapes : (q : Q) → Fin (gate q).arity → T
  gnext : Q → Q
  gmove : Q → T → Move

attribute [instance] Machine.instFQ Machine.instDQ Machine.instFT Machine.instDT

namespace Machine

variable (M : Machine)

/-- The scanned tuple restricted to the active tapes of `p`: inactive coordinates are replaced by
`#`, so a classical transition sees only `σ_{T_p}` (§2.2, p.16). -/
def mask (p : M.Q) (σ : M.T → Sym) : M.T → Sym :=
  fun t => if t ∈ M.act p then σ t else Sym.blank

/-- A classical state `p` is *nonfinal classical*. -/
def IsClassical (p : M.Q) : Prop := M.isFinal p = false ∧ M.isGate p = false

/-- A state `p` is a *nonfinal gate state*. -/
def IsGateState (p : M.Q) : Prop := M.isFinal p = false ∧ M.isGate p = true

/-- A scanned tuple is *legal* for `p` when every active coordinate lies in that tape's
alphabet. -/
def Legal (p : M.Q) (σ : M.T → Sym) : Prop := ∀ t ∈ M.act p, σ t ∈ M.alph t

/-- The classical tape `c` is a *companion* of the tape `t`: its head makes the same move as the
head of `t` in every transition row (Definition 3.1(ii), p.20; p.23). -/
def IsCompanion (c t : M.T) : Prop :=
  M.kind c = TapeKind.classical ∧
    (∀ p, M.IsClassical p → ∀ σ, M.Legal p σ →
      (M.δ p (M.mask p σ)).2.2 c = (M.δ p (M.mask p σ)).2.2 t) ∧
    (∀ p, M.IsGateState p → M.gmove p c = M.gmove p t)

/-- **Definition 3.1** (Machines, p.20), conditions (i)–(iv), stated on every transition row. -/
structure Valid : Prop where
  /-- (i) every alphabet contains `⊢`. -/
  mark_mem : ∀ t, Sym.mark ∈ M.alph t
  /-- (i) a qubit alphabet is `{⊢, 0, 1}` (blank `0`). -/
  qubit_alph : ∀ t, M.kind t = TapeKind.qubit → M.alph t = {Sym.mark, Sym.b0, Sym.b1}
  /-- (i) a classical alphabet contains the blank `#`. -/
  classical_blank : ∀ t, M.kind t = TapeKind.classical → Sym.blank ∈ M.alph t
  /-- (iv) the input and output tapes are distinct classical tapes over `{⊢, 0, 1, #}`. -/
  io_ne : M.inT ≠ M.outT
  in_kind : M.kind M.inT = TapeKind.classical
  out_kind : M.kind M.outT = TapeKind.classical
  in_alph : M.alph M.inT = {Sym.mark, Sym.b0, Sym.b1, Sym.blank}
  out_alph : M.alph M.outT = {Sym.mark, Sym.b0, Sym.b1, Sym.blank}
  /-- (ii) every qubit tape has a companion (the designated one). -/
  companion_ok : ∀ t, M.kind t = TapeKind.qubit → M.IsCompanion (M.companion t) t
  /-- classical steps write symbols of the alphabet. -/
  write_alph : ∀ p, M.IsClassical p → ∀ σ, M.Legal p σ → ∀ t ∈ M.act p,
    (M.δ p (M.mask p σ)).2.1 t ∈ M.alph t
  /-- (ii) a classical step writes `⊢` on an active tape exactly when it scans `⊢` there. -/
  write_mark : ∀ p, M.IsClassical p → ∀ σ, M.Legal p σ → ∀ t ∈ M.act p,
    ((M.δ p (M.mask p σ)).2.1 t = Sym.mark ↔ σ t = Sym.mark)
  /-- (iv) every classical step writes back on the input tape the symbol it scans there. -/
  input_writeback : ∀ p, M.IsClassical p → ∀ σ, M.Legal p σ → M.inT ∈ M.act p →
    (M.δ p (M.mask p σ)).2.1 M.inT = σ M.inT
  /-- (ii) a classical head moves left only if its tape is active and does not scan `⊢`. -/
  left_classical : ∀ p, M.IsClassical p → ∀ σ, M.Legal p σ → ∀ t,
    M.kind t = TapeKind.classical → (M.δ p (M.mask p σ)).2.2 t = Move.L →
      t ∈ M.act p ∧ σ t ≠ Sym.mark
  /-- (ii) a qubit head moves left only if some companion is active and does not scan `⊢`. -/
  left_qubit : ∀ p, M.IsClassical p → ∀ σ, M.Legal p σ → ∀ t,
    M.kind t = TapeKind.qubit → (M.δ p (M.mask p σ)).2.2 t = Move.L →
      ∃ c, M.IsCompanion c t ∧ c ∈ M.act p ∧ σ c ≠ Sym.mark
  /-- (iii) the active tapes of a gate state are distinct qubit tapes, one per qubit of the gate
  (which keeps the input and output tapes inactive, by (iv)). -/
  gate_inj : ∀ p, M.IsGateState p → Function.Injective (M.gtapes p)
  gate_qubit : ∀ p, M.IsGateState p → ∀ i, M.kind (M.gtapes p i) = TapeKind.qubit
  /-- (ii) every gate state has a move tuple in `{N, R}^k`. -/
  gate_moves : ∀ p, M.IsGateState p → ∀ t, M.gmove p t ≠ Move.L

end Machine

end QuantumKtSoI


