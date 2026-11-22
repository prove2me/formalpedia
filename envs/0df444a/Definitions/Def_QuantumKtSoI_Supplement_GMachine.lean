-- Prove2me | Definitions.Def_QuantumKtSoI_Supplement_GMachine
-- name    : QuantumKtSoI_Supplement_GMachine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:35:00.260452+00:00
-- url     : https://prove2.me/theorems/505248ab-d99f-4d0f-9ae8-18918538a315
-- title:
--   Finite gate sets $\mathcal G'$ and $\mathcal G'$-machines (Definition 9.3)
-- statement:
--   A **finite gate set** $\mathcal G'$ is a finite set of gates, each a unitary matrix $g$ on $(\mathbb C^2)^{\otimes\mathrm{arity}(g)}$ for an integer $\mathrm{arity}(g)\ge1$. A **$\mathcal G'$-machine** is defined as a machine of Definition 3.1 with condition (iii) replaced by: each gate state $p$ carries a gate $g_p\in\mathcal G'$ and an ordered tuple of $\mathrm{arity}(g_p)$ distinct qubit tapes, its active tapes, and its unitary acts as $g_p$ on tuples of active symbols in $\{0,1\}$ and as the identity on tuples containing $\vdash$.
--
--   The module also fixes the native gate set $\mathcal G=\{H,X,\mathrm{CNOT},\mathrm{SWAP},\mathrm{Toff}\}$ as a gate set, the set $\mathcal G'\cup\{g\}$ for one further gate, and the sets $\mathcal G\cup\{T_m\}$ with $T_m=\mathrm{diag}(1,e^{2\pi i/2^m})$ and $\mathcal G\cup\{T\}$ with $T=\mathrm{diag}(1,e^{i\pi/4})$.
--
--   These are the machines over which the gate-set comparisons of §9 and Appendix D.9 are stated.
--
--   **Formalization Note** A gate set is a finite indexed family of matrices with a name (a natural number) for each gate, the fixed enumeration that encodings use; `Wf` requires arities at least $1$, unitarity and distinct names. A $\mathcal G'$-machine has the fields of the published `Machine`, with the gate and its tape tuple of a state given together as an optional datum, so that the empty gate set is allowed. For the native gate set the semantics is that of the published machine.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Definition 9.3, p.118; T_m and G_CT, p.120; Definition 3.1, p.20

import Mathlib
import Definitions.Def_QuantumKtSoI_Machine
import Definitions.Def_QuantumKtSoI_CodedMachine

open Classical

namespace QuantumKtSoI.Supplement

/-- A **finite gate set** `G′` (Definition 9.3, p.118 of Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…): finitely many gates,
indexed by the finite type `ι`; the gate `g` is the matrix `amp g` on `(ℂ²)^{⊗ arity g}` in the
computational basis (`amp g ζ' ζ` is the entry in row `ζ'` = output bits and column `ζ` = input
bits), and `idx g` is the name of `g` in a fixed enumeration of the library, used by encodings.

**Formalization Note** A finite set of gates is given as a finite indexed family; `Wf` adds the
paper's requirements (arity at least one, unitary matrices, distinct names). -/
structure GateLib where
  ι : Type
  [instF : Fintype ι]
  [instD : DecidableEq ι]
  arity : ι → ℕ
  amp : (g : ι) → (Fin (arity g) → Bool) → (Fin (arity g) → Bool) → ℂ
  idx : ι → ℕ

attribute [instance] GateLib.instF GateLib.instD

/-- The requirements of Definition 9.3 on a gate set: every gate has arity `≥ 1` and is unitary
(`g† g = 1`, which for a square matrix is unitarity), and the names `idx` are distinct. -/
def GateLib.Wf (L : GateLib) : Prop :=
  Function.Injective L.idx ∧ ∀ g : L.ι, 1 ≤ L.arity g ∧
    ∀ i j : Fin (L.arity g) → Bool,
      (∑ o : Fin (L.arity g) → Bool, (starRingEnd ℂ) (L.amp g o i) * L.amp g o j) = if i = j then 1 else 0

/-- The native gate set `G = {H, X, CNOT, SWAP, Toff}` of Definition 3.1 (§3.1, p.20) as a gate
library: the published `Gate`, `Gate.arity`, `Gate.amp`, with the names of the published encoding. -/
noncomputable def nativeLib : GateLib where
  ι := Gate
  instF := ⟨{Gate.H, Gate.X, Gate.CNOT, Gate.SWAP, Gate.Toff}, by intro g; cases g <;> simp⟩
  arity := Gate.arity
  amp := Gate.amp
  idx := CodedMachine.gateCode

/-- The gate set `L ∪ {g}` for one further gate `g` of arity `a` with matrix `m`, named by the
least number above the names of `L`. -/
noncomputable def GateLib.adjoin (L : GateLib) (a : ℕ) (m : (Fin a → Bool) → (Fin a → Bool) → ℂ) : GateLib where
  ι := Option L.ι
  arity := fun g => match g with | none => a | some g => L.arity g
  amp := fun g => match g with | none => m | some g => L.amp g
  idx := fun g => match g with | none => (Finset.univ.sup L.idx) + 1 | some g => L.idx g

/-- The one-qubit phase gate `diag(1, e^{iθ})`. -/
noncomputable def phaseAmp (θ : ℝ) : (Fin 1 → Bool) → (Fin 1 → Bool) → ℂ :=
  fun o i => if o 0 = i 0 then (if i 0 then Complex.exp (θ * Complex.I) else 1) else 0

/-- `G ∪ {T_m}` with `T_m = diag(1, e^{2πi/2^m})` (p.120). -/
noncomputable def nativeTm (m : ℕ) : GateLib := nativeLib.adjoin 1 (phaseAmp (2 * Real.pi / 2 ^ m))

/-- `G ∪ {T}` with `T = diag(1, e^{iπ/4})` (p.120), the host of the "GT-blocks". -/
noncomputable def nativeT : GateLib := nativeLib.adjoin 1 (phaseAmp (Real.pi / 4))

/-- A **`G′`-machine** (Definition 9.3, p.118): a machine of Definition 3.1 (p.20) whose gate states
carry gates of the library `L`, given as raw data; its legality conditions are `GMachine.Valid`.
All fields are those of the published `QuantumKtSoI.Machine`, except that the gate of a state and
its ordered tuple of active tapes are given together by `gdata`: `gdata p = some ⟨g, tp⟩` makes `p`
a gate state with gate `g ∈ G′` applied to the tapes `tp 0, …, tp (arity g − 1)`, and
`gdata p = none` makes a nonfinal `p` a classical state. A gate state has the next state `gnext p`
and the move tuple `gmove p`.

**Formalization Note** The published `Machine` stores `isGate`, `gate`, `gtapes` separately and so
needs a default gate; the optional `gdata` carries the same information and also allows the empty
library. Fields that do not apply to the kind of a state are ignored by the semantics. -/
structure GMachine (L : GateLib) where
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
  act : Q → Finset T
  δ : Q → (T → Sym) → Q × (T → Sym) × (T → Move)
  gdata : Q → Option ((g : L.ι) × (Fin (L.arity g) → T))
  gnext : Q → Q
  gmove : Q → T → Move

attribute [instance] GMachine.instFQ GMachine.instDQ GMachine.instFT GMachine.instDT

namespace GMachine

variable {L : GateLib} (M : GMachine L)

/-- `p` carries a gate. -/
def isGate (p : M.Q) : Bool := (M.gdata p).isSome

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

/-- **Definition 9.3** (`G′`-machines, p.118): conditions (i)–(iv) of Definition 3.1 (p.20), stated on
every transition row, with (iii) reading: the active tapes of a gate state are distinct qubit
tapes, one per qubit of its gate of `G′`. -/
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
  gate_inj : ∀ p, M.IsGateState p → ∀ d ∈ M.gdata p, Function.Injective d.2
  gate_qubit : ∀ p, M.IsGateState p → ∀ d ∈ M.gdata p, ∀ i, M.kind (d.2 i) = TapeKind.qubit
  /-- (ii) every gate state has a move tuple in `{N, R}^k`. -/
  gate_moves : ∀ p, M.IsGateState p → ∀ t, M.gmove p t ≠ Move.L

end GMachine

end QuantumKtSoI.Supplement


