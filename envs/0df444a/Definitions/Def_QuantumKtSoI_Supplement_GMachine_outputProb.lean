-- Prove2me | Definitions.Def_QuantumKtSoI_Supplement_GMachine_outputProb
-- name    : QuantumKtSoI_Supplement_GMachine_outputProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:35:31.107606+00:00
-- url     : https://prove2.me/theorems/e09f25ab-eecd-428b-8b1d-877cd0dce235
-- title:
--   Configurations, branch vectors and the output law $P_A$ of a $\mathcal G'$-machine
-- statement:
--   Records, branch vectors and the output law $P_A(x;t,w)$ of a $\mathcal G'$-machine $A$ are given by Definitions 3.2 and 3.4, with the conventions after Definition 3.4. A gate step in state $p$ with gate $g_p\in\mathcal G'$ maps a basis configuration whose scanned active tuple $\zeta$ consists of bits to
--   $$\sum_{\zeta'} g_p[\zeta',\zeta]\,|q_p,\ h+d_p,\ \zeta',\ \gamma\rangle ,$$
--   and acts as the identity on the symbols (with the state change and the moves) when the tuple contains $\vdash$. As for native machines,
--   $$P_A(x;t,w)=\sum_{\rho\in R^t}\ \sum_{C \text{ final},\ \mathrm{out}(C)=w}|\psi_\rho(C)|^2\quad(t\ge1),$$
--   with the deadline-$0$ convention, real deadlines read as floors, and halting within $t$ steps meaning that every branch of length $t$ ends in a final state.
--
--   This output law defines $P'_{e'}$ and the measure $\mathrm{qKt}_{\mathcal G'}$.
--
--   **Formalization Note** The definitions are those of the published `Machine.outputProb` module with the gate amplitude taken from the gate set; tapes are indexed by $\mathbb Z$ and vectors are finitely supported.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Definition 9.3, p.118; Definitions 3.2 and 3.4, pp.21–22

import Mathlib
import Definitions.Def_QuantumKtSoI_Supplement_GMachine

open Classical

noncomputable section

namespace QuantumKtSoI.Supplement

namespace GMachine

variable {L : GateLib} (M : GMachine L)

/-- A **configuration** of a `G′`-machine (§2.2, p.16; Definition 9.3, p.118 of Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…): the control state, the contents of every tape (cells
indexed by `ℤ`), and the head position on every tape. -/
structure Config where
  state : M.Q
  cont : M.T → ℤ → Sym
  head : M.T → ℤ

variable {M}

/-- The blank symbol of a tape: `0` on a qubit tape, `#` on a classical tape
(Definition 3.1(i), p.20). -/
def blankOf (t : M.T) : Sym :=
  if M.kind t = TapeKind.qubit then Sym.b0 else Sym.blank

variable (M)

/-- The initial configuration `C_x` (Definition 3.1, p.20): the initial state, every head on
cell `0`, the input tape holding `⊢ x₁ ⋯ x_{|x|}` followed by blanks, every other tape holding
`⊢` followed by blanks, and every cell of negative index blank. -/
def initConfig (x : List Bool) : M.Config where
  state := M.init
  cont := fun t i =>
    if i = 0 then Sym.mark
    else if t = M.inT ∧ 1 ≤ i ∧ i ≤ x.length then Sym.ofBit (x.getD (i - 1).toNat false)
    else blankOf t
  head := fun _ => 0

variable {M}

/-- The symbol scanned on tape `t`. -/
def Config.scanned (C : M.Config) (t : M.T) : Sym := C.cont t (C.head t)

/-- The length of the output prefix: the largest `k` such that cells `1, …, k` of the output tape
hold bits.

**Formalization Note** `sSup` of an unbounded set of naturals is `0`; this happens only for
configurations with infinitely many written cells, which are never reached from `C_x`
(at most `s` cells are written after `s` steps, p.21). -/
def Config.outLen (C : M.Config) : ℕ :=
  sSup {k : ℕ | ∀ i < k, C.cont M.outT ((i : ℤ) + 1) = Sym.b0 ∨ C.cont M.outT ((i : ℤ) + 1) = Sym.b1}

/-- The **output** of a configuration: the longest `w ∈ {0,1}*` such that cells `1, …, |w|` of the
output tape hold `w` (Definition 3.1, p.20). -/
def Config.output (C : M.Config) : List Bool :=
  List.ofFn fun i : Fin C.outLen => decide (C.cont M.outT ((i : ℤ) + 1) = Sym.b1)

/-- The configuration after a classical step from `C` (§2.2, p.16): the state becomes
`q(p,σ)`, the active scanned cells receive `τ(p,σ)`, inactive tapes are unchanged, and every head
moves by `d(p,σ)`. -/
def Config.classicalNext (C : M.Config) : M.Config :=
  let p := C.state
  let r := M.δ p (M.mask p C.scanned)
  { state := r.1
    cont := fun t => if t ∈ M.act p then Function.update (C.cont t) (C.head t) (r.2.1 t) else C.cont t
    head := fun t => C.head t + (r.2.2 t).toInt }

/-- The contents after writing the bit tuple `ζ'` on the scanned cells of the tapes `tp`. -/
def Config.writeBits (C : M.Config) {a : ℕ} (tp : Fin a → M.T) (ζ' : Fin a → Bool) :
    M.T → ℤ → Sym :=
  (List.finRange a).foldl
    (fun acc i => Function.update acc (tp i) (Function.update (acc (tp i)) (C.head (tp i))
      (Sym.ofBit (ζ' i)))) C.cont

/-- The image of a basis configuration in a gate state `p` (§2.2, p.16; Definition 3.1(iii);
Definition 9.3, p.118): `S|p,h,ζ,γ⟩ = Σ_{ζ'} g_p[ζ',ζ] |q_p, h + d_p, ζ', γ⟩` for the gate `g_p ∈ G′` when the scanned
tuple `ζ` on the active tapes consists of bits, and the identity on the symbols (with the state
change and the moves) when the tuple contains any other symbol, such as `⊢`. -/
def Config.gateImage (C : M.Config) : M.Config →₀ ℂ :=
  match M.gdata C.state with
  | none => Finsupp.single C 1
  | some ⟨g, tp⟩ =>
      let moved : (M.T → ℤ → Sym) → M.Config := fun c =>
        { state := M.gnext C.state, cont := c,
          head := fun t => C.head t + (M.gmove C.state t).toInt }
      if ∀ i, C.scanned (tp i) = Sym.b0 ∨ C.scanned (tp i) = Sym.b1 then
        ∑ ζ' : Fin (L.arity g) → Bool,
          Finsupp.single (moved (C.writeBits tp ζ'))
            (L.amp g ζ' (fun i => decide (C.scanned (tp i) = Sym.b1)))
      else Finsupp.single (moved C.cont) 1

/-- The step from a basis configuration: the identity at a final state, the gate image at a gate
state, and the single classical successor at a classical state (p.21). -/
def Config.stepBasis (C : M.Config) : M.Config →₀ ℂ :=
  if M.isFinal C.state then Finsupp.single C 1
  else if M.isGate C.state then C.gateImage
  else Finsupp.single C.classicalNext 1

variable (M)

/-- The **step operator** `S` (p.21), the linear map on finite linear combinations of basis
configurations extending `Config.stepBasis`. -/
def step : (M.Config →₀ ℂ) →ₗ[ℂ] (M.Config →₀ ℂ) :=
  Finsupp.linearCombination ℂ Config.stepBasis

/-- **Records** (Definition 3.2, p.21): `(p, σ)` for a classical state with scanned active tuple
`σ` (inactive coordinates masked), `(p, •)` for a gate state, and `(p)` for a final state. -/
inductive Record
  | cl (p : M.Q) (σ : M.T → Sym)
  | gt (p : M.Q)
  | fn (p : M.Q)

variable {M}

/-- The record of a basis configuration (Definition 3.2). -/
def Config.record (C : M.Config) : M.Record :=
  if M.isFinal C.state then Record.fn C.state
  else if M.isGate C.state then Record.gt C.state
  else Record.cl C.state (M.mask C.state C.scanned)

variable (M)

/-- The orthogonal projector `Π_r` onto the span of the basis configurations with record `r`. -/
def proj (r : M.Record) (v : M.Config →₀ ℂ) : M.Config →₀ ℂ :=
  v.filter fun C => C.record = r

/-- The **branch vector** `ψ_ρ = S Π_{r_s} ⋯ S Π_{r_1} |C_x⟩` of a record sequence
`ρ = r₁ ⋯ r_s` (Definition 3.2, p.21; `r₁` acts first). -/
def branch (x : List Bool) (ρ : List M.Record) : M.Config →₀ ℂ :=
  ρ.foldl (fun v r => M.step (M.proj r v)) (Finsupp.single (M.initConfig x) 1)

/-- The squared `ℓ²` norm `‖v‖² = Σ_C |v_C|²` of a finite-support configuration vector. -/
def sqNorm (v : M.Config →₀ ℂ) : ℝ := v.sum fun _ a => ‖a‖ ^ 2

/-- The records that occur in the support of `ψ_ρ`; every other record annihilates `ψ_ρ`. -/
def nextRecords (x : List Bool) (ρ : List M.Record) : Finset M.Record :=
  (M.branch x ρ).support.image Config.record

/-- The finite set of extensions `ν` of length `u` of `ρ` that can have `ψ_{ρν} ≠ 0`: every
record sequence of length `u` outside it has `ψ_{ρν} = 0`. -/
def extSeqs (x : List Bool) (ρ : List M.Record) : ℕ → Finset (List M.Record)
  | 0 => {[]}
  | u + 1 => (extSeqs x ρ u).biUnion fun ν =>
      (M.nextRecords x (ρ ++ ν)).image fun r => ν ++ [r]

/-- The record sequences of length `s` that can have a nonzero branch vector; every
`ρ ∈ Rˢ` outside this finite set has `ψ_ρ = 0`. -/
def recSeqs (x : List Bool) (s : ℕ) : Finset (List M.Record) := M.extSeqs x [] s

/-- **Definition 3.4** (Output distribution, p.22) for a `G′`-machine (Definition 9.3, p.118): the probability `P_M(x; t, w)` that `M` halts
within `t` steps on `x` with output `w`,
`P_M(x;t,w) = Σ_{ρ ∈ Rᵗ} Σ_{C final, out(C) = w} |ψ_ρ(C)|²` for `t ≥ 1`, and, at deadline `0`,
`1` when the initial state is final and `w = ε`, and `0` otherwise.

**Formalization Note** The paper sums `‖ψ_ρ‖²` over the `ρ ∈ Rᵗ` with `ψ_ρ ≠ 0`, `st(ρ)` final
and `out(ρ) = w`; by Lemma 3.3(iii) all configurations in the support of a nonzero `ψ_ρ` share
the state and the output, so summing `|ψ_ρ(C)|²` over the final configurations with output `w`
gives the same value and needs no choice of a representative. Record sequences outside
`recSeqs` have `ψ_ρ = 0` and contribute nothing. -/
def outputProb (x : List Bool) (t : ℕ) (w : List Bool) : ℝ :=
  if t = 0 then (if M.isFinal M.init = true ∧ w = [] then 1 else 0)
  else ∑ ρ ∈ M.recSeqs x t, ∑ C ∈ (M.branch x ρ).support with
      (M.isFinal C.state = true ∧ C.output = w), ‖M.branch x ρ C‖ ^ 2

/-- `P_M(x; T, w)` at a real deadline `T ≥ 0`, namely `P_M(x; ⌊T⌋, w)` (p.22). -/
def outputProbR (x : List Bool) (T : ℝ) (w : List Bool) : ℝ := M.outputProb x ⌊T⌋₊ w

/-- `M` **halts within `t` steps** on `x` (Definition 3.4, p.22): every record sequence of
length `t` with nonzero branch vector ends in a final state. At `t = 0` this says that the
initial state is final. -/
def HaltsWithin (x : List Bool) (t : ℕ) : Prop :=
  ∀ ρ ∈ M.recSeqs x t, ∀ C ∈ (M.branch x ρ).support, M.isFinal C.state = true

end GMachine

end QuantumKtSoI.Supplement


