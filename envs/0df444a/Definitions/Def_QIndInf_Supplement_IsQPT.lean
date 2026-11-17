-- Prove2me | Definitions.Def_QIndInf_Supplement_IsQPT
-- name    : QIndInf_Supplement_IsQPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:19:47.541194+00:00
-- url     : https://prove2.me/theorems/6622e58f-83e5-4e5a-895d-ce68f34e1553
-- title:
--   Turing machines, quantum polynomial-time algorithms and finite universal gate sets
-- statement:
--   **Turing machines.** A classical Turing machine is identified with its binary description $T\in\{0,1\}^*$, and $|T|$ is the length of that string. The $t$-step run $T^t(x)$ decodes $T$ into a multi-tape machine (every bit string decodes to a machine, and every machine has a description) and runs it on the input $x$ for $t$ steps; it returns the bit string on the output tape if the machine has halted within $t$ steps, and nothing otherwise.
--
--   **Quantum algorithms.** Fix a finite gate set $G$. A quantum algorithm is the description $A$ of a classical machine that, on a classical input $x$, writes the description of a quantum circuit over $G$ with $x$ hard-wired into it. With classical output, the circuit is run on the all-zero state and its output register is measured in the computational basis, giving $\Pr[A(x)=z]$; with a quantum input on $n$ qubits and a quantum output on $k$ qubits, the algorithm applies the channel of the circuit (input wires carry the quantum input, ancillas start in $|0\rangle$, non-output wires are discarded). An algorithm that writes no circuit outputs the empty string (classical case) or the zero map (quantum case).
--
--   1. $A$ is **QPT** (quantum polynomial time) if, for one polynomial $P$, its machine halts on every input $x$ within $P(|x|)$ steps.
--   2. $A$ **runs in time** $\tau$ if its machine halts on $1^\lambda$ within $\tau(\lambda)$ steps for every $\lambda$.
--
--   **Universal gate sets.** $G$ is a **finite universal gate set** if (density) every unitary on $n$ qubits is approximated, up to a global phase and within any $\varepsilon>0$, by an ancilla-free circuit over $G$, and (computable gates) the matrix entries of every gate have dyadic approximations $(a_m+\mathrm i\,b_m)/2^m$ within $2^{-m}$ computable from $1^m$ in polynomial time.
--
--   These notions give Definitions 3.7, 4.3 and 5.4 their precise computational meaning.
--
--   **Formalization Note** Machines are the published Complexitylib multi-tape machines, decoded by `decodeDesc` and run by the universal function `universal`. Circuits, their channels and descriptions are the published `QiOPoQ.Circ`, `QiOPoQ.chan`, `QiOPoQ.encCirc` over a `QiOPoQ.GateSet` (which contains $I$, $X$, CNOT and is closed under adjoints). The density clause measures distance by the entrywise $\ell_1$ norm; all norms on matrices of a fixed size are equivalent.
-- source:
--   Hiroka, Hsieh, Shirakawa, Universal Inductive Inference of Quantum States, arXiv:2609.36912 (PDF of 2026-11-02, sha256 ac6387756651cc50c671f36acf1ef987db0df0c463581cd948250204441f6925), §3.1, p.15 (fixed finite universal gate set, binary circuit encoding, T^t); Definition 3.7, p.17 (QPT); Lemma 3.6, p.17 (|T| = length of the binary description)

import Mathlib
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Machine
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Decode
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_QiOPoQ_chan
import Definitions.Def_QiOPoQ_encCirc

set_option autoImplicit false

namespace QIndInf.Supplement

open QAlgorithms QAlgorithms.Complexity QiOPoQ

/-- A symbol of the machine's output tape read as a bit (`0 ↦ 0`, `1 ↦ 1`); any other symbol is
not a bit. -/
def symBit : ℕ → Option Bool
  | 0 => some false
  | 1 => some true
  | _ => none

/-- **The `t`-step run `T^t(x)` of the classical Turing machine with binary description `T`.**
The description is decoded by the published Complexitylib decoder
(`Turing.MultiTapeTM.Universal.decodeDesc`, which turns every bit string into a multi-tape machine),
and the machine is run on the input `x` (bits as tape symbols `0`, `1`) for `t` steps by the
published universal function (`Turing.MultiTapeTM.Universal.universal`). The result is `some y`
when the machine has halted within `t` steps with the bit string `y` on its output tape, and
`none` otherwise (not halted, or an output symbol that is not a bit).

Hiroka, Hsieh, Shirakawa, *Universal Inductive Inference of Quantum States*, arXiv:2609.36912
(PDF of 2026-11-02), §3.1, p.15: "For a Turing machine T and a time bound t ∈ N, T^t denotes the
t-time execution of T", and Lemma 3.6, p.17: "|T| denotes the length of the binary description
of T".

**Formalization Note.** A Turing machine is identified with its binary description `T : List Bool`;
its length `|T|` is `T.length`. Every machine has a description (the decoder inverts the published
encoding `eDesc`), so these descriptions range over all multi-tape machines. -/
def tmRun (T x : Str) (t : ℕ) : Option Str :=
  let r := Turing.MultiTapeTM.Universal.universal
    (Turing.MultiTapeTM.Universal.decodeDesc T, x.map Bool.toNat, t)
  if r.2 then r.1.mapM symBit else none

open Classical in
/-- The output of the machine `T` on `x` once it has halted (at the first step count at which
`tmRun` succeeds), or `none` if it never halts with a bit-string output. -/
noncomputable def tmResult (T x : Str) : Option Str :=
  if h : ∃ t, (tmRun T x t).isSome then tmRun T x (Nat.find h) else none

/-- **Quantum polynomial time (QPT).** A quantum algorithm is given by the description `A` of a
classical machine that, on the classical input `x`, writes the description of a quantum circuit
over the gate set `G` (with the input hard-wired into it). `A` is QPT when the machine halts on
every input `x` within `P(|x|)` steps for one polynomial `P`; the circuit it writes then has
polynomial size.

arXiv:2609.36912 (PDF of 2026-11-02), §3.4, Definition 3.7, p.17 ("A QPT algorithm"), and §3.1,
p.15 ("we fix an arbitrary finite universal quantum gate set G and a binary encoding of quantum
circuits over G").

**Formalization Note.** This is the standard model "a uniform classical polynomial-time generator
of polynomial-size quantum circuits" (no advice). Circuit descriptions are the published
`QiOPoQ.encCirc`. -/
def IsQPT (A : Str) : Prop :=
  ∃ P : Polynomial ℕ, ∀ x : Str, (tmRun A x (P.eval x.length)).isSome

/-- `A` runs in time `τ` on the input `1^λ`: the generating machine halts within `τ(λ)` steps.
Used for the instance generators of Definitions 4.3 and 5.4 ("all `t′(λ)`-time algorithms G").

**Formalization Note.** The time of a quantum algorithm is that of its classical generator; the
circuit it writes is no longer than the generator's run. -/
def RunsInTime (A : Str) (τ : ℕ → ℕ) : Prop :=
  ∀ lam : ℕ, (tmRun A (unary lam) (τ lam)).isSome

/-- The circuit written by the algorithm `A` on the classical input `x`, if any. -/
noncomputable def algCirc (G : GateSet) (A x : Str) : Option (Circ G) :=
  (tmResult A x).bind (decCirc G)

/-- **Output distribution of a quantum algorithm with classical input and output**:
`Pr[A(x) = z]`. The circuit written by `A` on `x` is run on the all-zero state and its output
register is measured in the computational basis. If `A` writes no circuit, the output is the empty
string. -/
noncomputable def algProb (G : GateSet) (A x z : Str) : ℝ :=
  match algCirc G A x with
  | some C => runProb C [] z
  | none => if z = [] then 1 else 0

/-- **The channel of a quantum algorithm with classical input `x`, quantum input on `n` qubits and
quantum output on `k` qubits**: the channel of the circuit written by `A` on `x` (input wires = the
quantum input, ancillas `|0⟩`, the designated output register kept, the rest discarded), and the
zero map if `A` writes no circuit with `n` input and `k` output wires. -/
noncomputable def algChan (G : GateSet) (A x : Str) (n k : ℕ) :
    Superop (Fin n → Bool) (Fin k → Bool) :=
  match algCirc G A x with
  | some C => chanAs C n k
  | none => fun _ => 0

/-- An integer as a bit string: its sign bit and the binary digits of its absolute value. -/
def encZ (z : ℤ) : Str := QAdvFew.PoQOracle.tup [[decide (z < 0)], Nat.bits z.natAbs]

/-- **A finite universal gate set** (§3.1, p.15: "we fix an arbitrary finite universal quantum
gate set G").
1. (density) for every `n`, every unitary `U` on `n` qubits and every `ε > 0`, some ancilla-free
   circuit over `G` on `n` qubits implements `U` up to a global phase within `ε` (entrywise
   `ℓ₁` distance of the matrices);
2. (computable gates) every matrix entry of every gate has dyadic approximations
   `(a_m + i b_m)/2^m` within `2^{−m}` that are computed from `1^m` in polynomial time.

**Formalization Note.** Clause 2 is the standing premise under which circuits over `G` are
synthesized efficiently (Solovay–Kitaev); every concrete finite gate set (e.g. Clifford+T) has it.
All norms on matrices of a fixed size are equivalent, so the choice of norm in clause 1 does not
matter. -/
def IsUniversalGateSet (G : GateSet) : Prop :=
  (∀ (n : ℕ) (U : Matrix (Fin (n + 0) → Bool) (Fin (n + 0) → Bool) ℂ),
      U ∈ Matrix.unitaryGroup (Fin (n + 0) → Bool) ℂ → ∀ ε : ℝ, 0 < ε →
      ∃ (gs : List (Σ i : Fin G.k, Fin (G.arity i) ↪ Fin (n + 0))) (θ : ℝ),
        ∑ y, ∑ y', ‖circUnitary (⟨n, 0, gs, List.finRange (n + 0), List.nodup_finRange _⟩ : Circ G) y y'
          - Complex.exp (θ * Complex.I) * U y y'‖ ≤ ε) ∧
    ∀ (i : Fin G.k) (y y' : Fin (G.arity i) → Bool), ∃ a b : ℕ → ℤ,
      (∀ m : ℕ, ‖G.mat i y y' - ((a m : ℂ) + (b m : ℂ) * Complex.I) / 2 ^ m‖ ≤ 1 / 2 ^ m) ∧
      ∃ f : Str → Str, PolyTimeComputable f ∧
        ∀ m, f (unary m) = QAdvFew.PoQOracle.tup [encZ (a m), encZ (b m)]

end QIndInf.Supplement


