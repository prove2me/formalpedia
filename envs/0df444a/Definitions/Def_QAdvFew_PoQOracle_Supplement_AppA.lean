-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_Supplement_AppA
-- name    : QAdvFew_PoQOracle_Supplement_AppA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:20:00.750673+00:00
-- url     : https://prove2.me/theorems/505e8259-9e24-41e2-b6eb-af6b2627676e
-- title:
--   The setting of Appendix A: $S=\{S^{U_t}_{\sigma_t}\}$, access to $\vec\sigma$, and oracles for $\mathsf{QCMA}^{\vec\sigma}$
-- statement:
--   Let $\vec\sigma=\{\sigma_t\}_{t\in\mathbb N}$ be states, $\sigma_t$ on $t$ qubits, each with a fixed purification $|\phi_t\rangle$ on $2t$ qubits, and let $U_t\leftarrow\mathrm{Haar}(\{0,1\}^t)$ be independent. The oracle is $S=\{S^{U_t}_{\sigma_t}\}_{t\in\mathbb N}$.
--
--   **Access to $\vec\sigma$** is a channel that on input $t$ returns a fresh copy of $\sigma_t$; a circuit with this access may write $|\phi_t\rangle$ onto fresh wires and afterwards never touch the purifying half. A copy of $\sigma_t$, like a query to level $t$, costs $t$.
--
--   An **oracle for $\mathsf{QCMA}^{\vec\sigma}$** is an oracle for the complete verification promise problem: given a verifier with access to $\vec\sigma$ and a runtime bound $T$ in unary, it answers $1$ if some classical witness is accepted with probability at least $\frac23$ and $0$ if every classical witness is accepted with probability at most $\frac13$; its behavior outside the promise is arbitrary. The class $\mathsf{BQP}^{S,\mathsf{QCMA}^{\vec\sigma}}$ consists of the promise problems decided by one uniform QPT algorithm with access to $S$ and to **every** such oracle.
--
--   **Formalization Note** A verifier instance is encoded as the tuple (number of wires, witness length, output wire, circuit description, $1^T$); a string is read as the instance it encodes, if any.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Appendix A, p. 51 (PDF p. 53)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Supplement_haarU
import Definitions.Def_QAdvFew_PoQOracle_Supplement_stPrep
import Definitions.Def_QAdvFew_PoQOracle_Supplement_UQFamily
import Definitions.Def_QAdvFew_PoQOracle_tup

open QAlgorithms.Complexity MeasureTheory

namespace QAdvFew.PoQOracle.Supplement

open QAdvFew.PoQOracle

/-- The arity of the oracle `S = {S^{U_t}_{σ_t}}_t` of Appendix A: component `0` at level `t` acts on
`1 + (t + t)` qubits (flag, the `t`-qubit register of `σ_t`, its `t`-qubit purifying register);
other components have arity `0`. -/
def arA : ℕ → ℕ → ℕ
  | 0, t => 1 + (t + t)
  | _, _ => 0

/-- The oracle `S = {S^{U_t}_{σ_t}}_{t ∈ ℕ}` (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, Appendix A, p. 51 (PDF p. 53): "Let
`σ⃗ = {σ_t}_{t∈ℕ}` be any fixed family of states, where `σ_t` is a state on `t` qubits. Fix a
purification of each `σ_t` on `2t` qubits, and independently sample `U_t ← Haar({0,1}^t)`. Write
`S = {S^{U_t}_{σ_t}}_{t∈ℕ}`"), for the purifications `φ t` (first `t` qubits: `σ_t`; last `t`:
purifying register, on which `U_t` acts; `stPrepU`, Definition 3.21). -/
noncomputable def oracleS (φ : (t : ℕ) → QState (t + t))
    (U : (t : ℕ) → Matrix.unitaryGroup (Bits t) ℂ) : UOracle arA
  | 0, t => stPrepU (φ t) (U t : Matrix (Bits t) (Bits t) ℂ)
  | _ + 1, _ => 1

/-- The law of `{U_t}_{t∈ℕ}`: independent Haar unitaries on `t` qubits. -/
noncomputable def haarFamily : Measure ((t : ℕ) → Matrix.unitaryGroup (Bits t) ℂ) :=
  Measure.infinitePi fun t => haarU (Bits t)

/-- An instruction of a circuit with **access to `σ⃗`** (Appendix A, p. 51: "Access to `σ⃗` means
access to a channel which, on input `t`, returns a fresh copy of `σ_t`"): a Clifford+T gate, or
`samp t ws es`, which writes the fixed purification `|φ_t⟩` of `σ_t` onto the fresh wires `ws`
(the copy of `σ_t`) and `es` (its purifying register). -/
inductive SInstr (m : ℕ) where
  | gate (g : Instr m)
  | samp (t : ℕ) (ws es : Fin t → Fin m) (h : Function.Injective (Fin.append ws es))

namespace SInstr

variable {m : ℕ}

/-- The wires an instruction touches. -/
def support : SInstr m → Finset (Fin m)
  | .gate g => g.support
  | .samp _ ws es _ => Finset.univ.image ws ∪ Finset.univ.image es

/-- The action of an instruction: `samp` maps `ψ` to `(⟨0|_{ws,es} ψ) ⊗ |φ_t⟩_{ws,es}`, which is
`ψ ⊗ |φ_t⟩` on fresh (`|0⟩`) wires. -/
noncomputable def apply (φ : (t : ℕ) → QState (t + t)) : SInstr m → QState m → QState m
  | .gate g => g.apply
  | .samp t ws es _ => fun ψ y =>
      φ t (Fin.append (y ∘ ws) (y ∘ es)) * ψ (Function.extend (Fin.append ws es) (fun _ => false) y)

/-- The binary description: Clifford+T gates as in `UInstr.instrDesc`, `samp` as the tag `7`, `t`,
and the wires. -/
def desc : SInstr m → Str
  | .gate g => UInstr.instrDesc g
  | .samp t ws es _ => bnat 7 ++ bnat t ++ (List.ofFn (fun j => bnat (ws j : ℕ))).flatten ++
      (List.ofFn (fun j => bnat (es j : ℕ))).flatten

/-- A copy of `σ_t` is charged `t` (p. 51: "Queries to level `t` take at least `t` time"). -/
def levelCost : SInstr m → ℕ
  | .samp t _ _ _ => t
  | .gate _ => 0

end SInstr

/-- A circuit with access to `σ⃗`. -/
abbrev SCirc (m : ℕ) := List (SInstr m)

namespace SCirc

variable {m : ℕ}

/-- Running it. -/
noncomputable def run (φ : (t : ℕ) → QState (t + t)) (c : SCirc m) (ψ : QState m) : QState m :=
  c.foldl (fun st g => g.apply φ st) ψ

/-- Its description. -/
def desc (c : SCirc m) : Str := (c.map SInstr.desc).flatten

/-- Its size: description length plus `t` per copy of `σ_t`. -/
def size (c : SCirc m) : ℕ := c.desc.length + (c.map SInstr.levelCost).sum

/-- Well-formedness for a circuit whose first `k` wires hold the witness and whose output wire is
`out`: every `samp` writes onto wires that are not witness wires and that no earlier instruction
touched (so they hold `|0⟩`), and its purifying wires `es` are touched by no later instruction and
are not the output wire, so the circuit holds only the copy of `σ_t`. -/
def WellFormed (c : SCirc m) (k : ℕ) (out : Fin m) : Prop :=
  ∀ i : Fin c.length, ∀ t ws es h, c.get i = SInstr.samp t ws es h →
    (∀ a, k ≤ (ws a : ℕ) ∧ k ≤ (es a : ℕ)) ∧
    (∀ j : Fin c.length, j < i → ∀ a, ws a ∉ (c.get j).support ∧ es a ∉ (c.get j).support) ∧
    (∀ j : Fin c.length, i < j → ∀ a, es a ∉ (c.get j).support) ∧
    (∀ a, es a ≠ out)

end SCirc

/-- An instance of the complete verification problem of `QCMA^{σ⃗}` (Appendix A, p. 51: "given a
verifier and a runtime bound in unary"): a well-formed circuit with access to `σ⃗` on `m` wires,
the first `k` of which hold the classical witness, an output wire, and a bound `T` on its size and
width. -/
structure SInst where
  m : ℕ
  k : ℕ
  hk : k ≤ m
  out : Fin m
  c : SCirc m
  T : ℕ
  wf : c.WellFormed k out
  hT : c.size ≤ T ∧ m ≤ T

namespace SInst

/-- The acceptance probability with witness `w`. -/
noncomputable def accept (φ : (t : ℕ) → QState (t + t)) (I : SInst) (w : Bits I.k) : ℝ :=
  probOne (I.c.run φ (basisState fun i => if h : (i : ℕ) < I.k then w ⟨i, h⟩ else false)) I.out

/-- Yes-instance: some classical witness is accepted with probability at least `2/3`. -/
def Yes (φ : (t : ℕ) → QState (t + t)) (I : SInst) : Prop := ∃ w, (2 : ℝ) / 3 ≤ I.accept φ w

/-- No-instance: every classical witness is accepted with probability at most `1/3`. -/
def No (φ : (t : ℕ) → QState (t + t)) (I : SInst) : Prop := ∀ w, I.accept φ w ≤ (1 : ℝ) / 3

/-- The string encoding of an instance: `(m, k, out, circuit, 1^T)`. -/
def code (I : SInst) : Str := tup [bnat I.m, bnat I.k, bnat (I.out : ℕ), I.c.desc, unary I.T]

open Classical in
/-- The instance a string encodes, if any. -/
noncomputable def decode (s : Str) : Option SInst :=
  if h : ∃ I : SInst, I.code = s then some h.choose else none

end SInst

/-- `Q` is **an oracle for `QCMA^{σ⃗}`** (Appendix A, p. 51: "An oracle for `QCMA^{σ⃗}` means an oracle
for its complete verification promise problem: given a verifier and a runtime bound in unary,
distinguish whether some classical witness is accepted with probability at least `2/3`, or every
classical witness is accepted with probability at most `1/3`. Its behavior outside the promise is
arbitrary"): on the code of a yes-instance it answers `1`, on the code of a no-instance `0`, and
anything elsewhere. -/
def IsQCMASigmaOracle (φ : (t : ℕ) → QState (t + t)) (Q : Oracle) : Prop :=
  ∀ (s : Str) (I : SInst), SInst.decode s = some I →
    (I.Yes φ → Q s = true) ∧ (I.No φ → Q s = false)

/-- The promise class `BQP^{S, QCMA^{σ⃗}}` (Appendix A, p. 51: "Throughout this section, complexity
classes refer to promise problems"): a single uniform polynomial-time algorithm with access to the
unitary oracle `S` and to a classical oracle decides the promise problem for **every** oracle `Q`
satisfying `valid` (here: every oracle for `QCMA^{σ⃗}`, whatever it answers outside the promise). -/
def PromiseBQPUForAll {ar : ℕ → ℕ → ℕ} (S : UOracle ar) (valid : Oracle → Prop) :
    Set PromiseProblem :=
  {Pp | ∃ Q : UQFamily ar, Q.Uniform ∧ Q.PolyBounded ∧ ∀ C : Oracle, valid C → ∀ x : Str,
    (x ∈ Pp.yes → (2 : ℝ) / 3 ≤ Q.accept S C x) ∧ (x ∈ Pp.no → Q.accept S C x ≤ (1 : ℝ) / 3)}

end QAdvFew.PoQOracle.Supplement


