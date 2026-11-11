-- Prove2me | Definitions.Def_QNatProofs_reducedOutput
-- name    : QNatProofs_reducedOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:59:35.461771+00:00
-- url     : https://prove2.me/theorems/7fcc1d0a-f201-4383-8698-1c0ffe7aeb51
-- title:
--   Circuit classes, reduced output states, approximate preparation and nonclean coherent evaluation
-- statement:
--   This file fixes how a quantum circuit prepares a state and how it evaluates a classical function.
--
--   A **circuit class** $\mathcal C$ over a gate set $S$ is, for every number $m$ of wires, a set of circuits on $m$ wires (the paper's "quantum circuit model").
--
--   For a circuit $C$ on $n+w$ wires let $|\Phi_C\rangle = C|0^{n+w}\rangle$. Its **reduced output state** is the $n$-qubit density matrix obtained by tracing out the last $w$ wires,
--   $$
--   \sigma_C(y,y') \;=\; \sum_{z\in\{0,1\}^w} \Phi_C(yz)\,\overline{\Phi_C(y'z)} .
--   $$
--   $C$ **$\varepsilon$-approximately prepares** an $n$-qubit pure state $|\psi\rangle$ if $\tfrac12\big\||\psi\rangle\langle\psi|-\sigma_C\big\|_1\le\varepsilon$ (Definition 2.2, (3), and Definition 2.4). The ancillas need not return to $|0\rangle$.
--
--   A unitary $U$ on $n+(r+w)$ wires is an **exact nonclean coherent implementation** of $f:\{0,1\}^n\to\{0,1\}^r$ if for every basis input $x$,
--   $$
--   U\,|x\rangle|0^r\rangle|0^w\rangle = |x\rangle|f(x)\rangle|\mathrm{junk}_x\rangle
--   $$
--   for some vector $|\mathrm{junk}_x\rangle$ on the workspace, which may depend on $x$ (Lemma 4.4, (43); Definition 4.1).
--
--   A circuit on $n+w$ wires **prepares $|\psi\rangle$ with probability $p$** if, for some computational-basis success event on the last $w$ wires, the part of $C|0^{n+w}\rangle$ on that event is $|\psi\rangle\otimes|\varphi\rangle$ with $\|\varphi\|^2=p$ (Lemma 4.5).
--
--   **Formalization Note** The output register is the first $n$ wires and the wires of an evaluator are ordered input, output, workspace. Any other designation is a renaming of wires, which changes neither the size nor the magic-hierarchy level of a circuit.
-- source:
--   Li, Parham, Natural proofs for quantum state preparation lower bounds, arXiv:2610.06826 (held copy sha256 b604fa11…), Definition 2.2 item 3, p.9; Definition 2.4, p.10; Lemma 4.4 (43), p.22; Definition 4.1, p.25; Lemma 4.5, p.26

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_QuantumOutputMetrics

set_option autoImplicit false

namespace QNatProofs

open QAlgorithms
open scoped ComplexConjugate

/-- A circuit class: for every number `m` of wires a set of circuits on `m` wires over the gate set
`S` (Li, Parham, arXiv:2610.06826 (held copy sha256 b604fa11…): the paper's "quantum circuit model", Definition 2.2, p.9). -/
abbrev CircuitClass (S : Set Gate) : Type := (m : ℕ) → Set (Circuit S m)

/-- The first `a` bits of a basis label of `a + b` qubits. -/
def fstBits {a b : ℕ} (y : Qubits (a + b)) : Qubits a := fun i => y (Fin.castAdd b i)

/-- The last `b` bits of a basis label of `a + b` qubits. -/
def sndBits {a b : ℕ} (y : Qubits (a + b)) : Qubits b := fun i => y (Fin.natAdd a i)

/-- The final state `C |0^{m}⟩` of a circuit on `m` wires started on the all-zero state. -/
noncomputable def outState {S : Set Gate} {m : ℕ} (c : Circuit S m) : EuclideanSpace ℂ (Qubits m) :=
  act c.unitary (zeroKet m)

/-- The **reduced output state** of a circuit on `n + w` wires: the state `C |0^{n+w}⟩` with the
last `w` wires traced out, an `n`-qubit density matrix on the output register (the first `n`
wires): `σ_{y y'} = Σ_z ψ(y z) conj(ψ(y' z))` with `ψ = C|0^{n+w}⟩`.

Li, Parham, arXiv:2610.06826 (held copy sha256 b604fa11…), Definition 2.2 item 3, p.9: "each
circuit acts on an all zero input, has a designated output register, and the remaining qubits can
be traced out. In particular, the ancillary qubits need not be returned to `|0⟩`."

**Formalization Note** The designated output register is the first `n` wires. Any other
designation is obtained by renaming the wires of every gate, which changes neither the size nor
the level of a circuit. -/
noncomputable def reducedOutput {S : Set Gate} {n w : ℕ} (c : Circuit S (n + w)) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun y y' => ∑ z : Qubits w,
    outState c (Fin.append y z) * conj (outState c (Fin.append y' z))

/-- The circuit `c` on `n + w` wires **`ε`-approximately prepares** the `n`-qubit pure state `ψ`:
its reduced output state `σ` satisfies `½‖|ψ⟩⟨ψ| − σ‖₁ ≤ ε` (Definition 2.2, (3), p.9;
Definition 2.4, p.10). -/
def ApproxPrepares {S : Set Gate} {n w : ℕ} (c : Circuit S (n + w))
    (ψ : EuclideanSpace ℂ (Qubits n)) (ε : ℝ) : Prop :=
  traceDistance (pureDensity ψ) (reducedOutput c) ≤ ε

/-- The basis-state superposition `|x⟩ |f x⟩ |junk⟩` on `n + (r + w)` wires: the input `x` on the
first `n` wires, the bit string `out` on the next `r`, and the vector `junk` on the last `w`. -/
noncomputable def placed {n r w : ℕ} (x : Qubits n) (out : Qubits r)
    (junk : EuclideanSpace ℂ (Qubits w)) : EuclideanSpace ℂ (Qubits (n + (r + w))) :=
  WithLp.toLp 2 fun y =>
    if fstBits y = x ∧ fstBits (sndBits y) = out then junk (sndBits (sndBits y)) else 0

/-- `U` is an **exact nonclean coherent implementation** of `f : {0,1}ⁿ → {0,1}^r`: for every
basis input `x`,
`U |x⟩ |0^r⟩ |0^w⟩ = |x⟩ |f(x)⟩ |junk_x⟩`
for some vector `junk_x` on the `w` workspace wires, which may depend on `x` (Li, Parham,
arXiv:2610.06826 (held copy sha256 b604fa11…), Lemma 4.4, (43), p.22; Definition 4.1, p.25;
Corollary 4.6.1, (55), p.32).

**Formalization Note** The wires are ordered input, output, workspace. The paper writes the
workspace before the output in (43) and (55); the orders differ by a renaming of wires, which
changes neither the size nor the level of a circuit. -/
def IsNoncleanEval {n r w : ℕ} (U : Matrix (Qubits (n + (r + w))) (Qubits (n + (r + w))) ℂ)
    (f : Qubits n → Qubits r) : Prop :=
  ∀ x : Qubits n, ∃ junk : EuclideanSpace ℂ (Qubits w),
    act U (ket (Fin.append x (fun _ => false))) = placed x (f x) junk

/-- The circuit `c` on `n + w` wires **prepares `ψ` with probability `p`** (Lemma 4.5, p.26):
there is a computational-basis event `succ` on the last `w` wires (the success flags) such that
the part of `C|0^{n+w}⟩` on that event is `|ψ⟩ ⊗ |φ⟩` with `‖φ‖² = p` (so measuring the last `w`
wires gives a success outcome with probability `p · ‖ψ‖²`, and the first `n` wires are then in
the state `ψ`). -/
def PreparesWithProb {S : Set Gate} {n w : ℕ} (c : Circuit S (n + w))
    (ψ : EuclideanSpace ℂ (Qubits n)) (p : ℝ) : Prop :=
  ∃ (succ : Qubits w → Bool) (φ : Qubits w → ℂ),
    (∀ (y : Qubits n) (z : Qubits w), succ z = true →
      outState c (Fin.append y z) = ψ y * φ z) ∧
    ∑ z : Qubits w, (if succ z = true then ‖φ z‖ ^ 2 else 0) = p

end QNatProofs


