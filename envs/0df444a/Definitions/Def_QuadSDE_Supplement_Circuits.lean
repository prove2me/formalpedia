-- Prove2me | Definitions.Def_QuadSDE_Supplement_Circuits
-- name    : QuadSDE_Supplement_Circuits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:12:22.597073+00:00
-- url     : https://prove2.me/theorems/94495d2b-78f6-4e04-a4b9-4f1d21ebd7de
-- title:
--   Toffoli / paired-Hadamard circuits, their unitary and acceptance probability $p_U$
-- statement:
--   The circuits of Theorem 5 act on $n\ge1$ qubits and are lists of $\ell$ gates of three kinds:
--   1. a **Toffoli gate** on three distinct qubits $a,b,c$, which flips the target $c$ when $a$ and $b$ are both $1$;
--   2. a **paired Hadamard gate** $H\otimes H$ on two distinct qubits $a,b$, with entries $\langle x|H\otimes H|y\rangle=(-1)^{x_ay_a+x_by_b}/2$ when $x,y$ agree elsewhere and $0$ otherwise;
--   3. the **identity gate**.
--
--   Every gate has entries in $\{0,\pm\frac12,\pm1\}$. The circuit's unitary is $U=G_\ell\cdots G_1$, the first gate acting first, and its **acceptance probability** is
--   $$p_U=\langle0^n|U^\dagger\big(|0\rangle\langle0|_{\mathrm{out}}\otimes I_{\mathrm{else}}\big)U|0^n\rangle,$$
--   the output qubit being the first one. A circuit is written as a bit string by giving $n$ and $\ell$ in self-delimiting binary, then a two-bit tag and the qubit indices of each gate.
--
--   These are the inputs of the reduction of Theorem 5 from approximating $p_U$ (a BQP-hard problem) to APX-SDE.
--
--   **Formalization Note** Qubits are `Fin n`; wire $0$ is the output qubit. The basis-state index set is `QAlgorithms.Qubits n` (bit strings). $p_U$ is written literally as the inner product of $U|0^n\rangle$ with its image under the diagonal projector onto "wire 0 reads 0", real part taken.
-- source:
--   Bravyi, Byrne, Zayats, Zhuk, Zlokapa, Quantum algorithms for stochastic nonlinear differential equations, arXiv:2606.08349 (sha256 29bd9b01…94cdf), §5, p. 33

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding

open QAlgorithms QAlgorithms.Complexity QAlgorithms.LocalHamiltonian

noncomputable section

namespace QuadSDE.Supplement

/-- Bravyi, Byrne, Zayats, Zhuk, Zlokapa, *Quantum algorithms for stochastic nonlinear differential
equations*, arXiv:2606.08349 (sha256 29bd9b01…), §5, p. 33: the gates of the circuits of Theorem 5,
"quantum circuits built from Toffoli gates and pairs of Hadamard gates acting on two distinct
qubits", together with identity gates ("We allow identity gates"), on `n` qubits.
* `toffoli a b c` flips qubit `c` (the target) when qubits `a` and `b` are both `1`; the three
  qubits are distinct;
* `hh a b` is `H ⊗ H` on the two distinct qubits `a, b`;
* `id` is the identity gate.

**Formalization Note.** Qubits are `Fin n` (wire `i` is the source's qubit `i + 1`). -/
inductive Gate (n : ℕ) where
  | toffoli (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
  | hh (a b : Fin n) (hab : a ≠ b)
  | id

/-- The basis-state map of the Toffoli gate with controls `a, b` and target `c`:
`|y⟩ ↦ |y ⊕ (y_a ∧ y_b) e_c⟩`. -/
def toffoliMap {n : ℕ} (a b c : Fin n) (y : Qubits n) : Qubits n :=
  Function.update y c (xor (y c) (y a && y b))

/-- The matrix of a gate in the computational basis of `(ℂ²)^{⊗n}`:
* Toffoli: `⟨x|G|y⟩ = 1` if `x = toffoliMap a b c y`, else `0`;
* `H ⊗ H` on `a, b`: `⟨x|G|y⟩ = (−1)^{x_a y_a + x_b y_b} / 2` if `x` and `y` agree on every other
  qubit, else `0` (the Hadamard entries are `H_{uv} = (−1)^{uv}/√2`);
* identity: the identity matrix.

Every entry lies in `{0, ±1/2, ±1}` (p. 33). -/
def Gate.mat {n : ℕ} : Gate n → Matrix (Qubits n) (Qubits n) ℂ
  | .toffoli a b c _ _ _ => fun x y => if x = toffoliMap a b c y then 1 else 0
  | .hh a b _ => fun x y =>
      if ∀ i : Fin n, i ≠ a → i ≠ b → x i = y i then
        (1 / 2 : ℂ) * (-1) ^ ((if x a && y a then 1 else 0) + (if x b && y b then 1 else 0) : ℕ)
      else 0
  | .id => 1

/-- p. 33: a circuit `U` "as above": `n ≥ 1` qubits (the first one is the designated output qubit)
and a list of `ℓ` gates `g_1, …, g_ℓ`, applied in list order. -/
structure THCircuit where
  n : ℕ
  n_pos : 0 < n
  gates : List (Gate n)

/-- The unitary `U = G_ℓ ⋯ G_2 G_1` of the circuit (the first gate of the list acts first). -/
def THCircuit.unitary (U : THCircuit) : Matrix (Qubits U.n) (Qubits U.n) ℂ :=
  (U.gates.map Gate.mat).foldl (fun acc G => G * acc) 1

/-- p. 33: the acceptance probability
`p_U = ⟨0ⁿ| U† (|0⟩⟨0|_out ⊗ I_else) U |0ⁿ⟩`, where the projector acts on the designated output
qubit, the first one (wire `0`).

**Formalization Note.** Written literally as `⟨U 0ⁿ, Π U 0ⁿ⟩` with `Π` the diagonal projector onto
the basis states whose wire `0` reads `0` (`false`); the value is real and its real part is taken. -/
def THCircuit.acceptProb (U : THCircuit) : ℝ :=
  let v : Qubits U.n → ℂ := U.unitary.mulVec (Pi.single (fun _ => false) 1)
  let proj : Matrix (Qubits U.n) (Qubits U.n) ℂ :=
    Matrix.diagonal fun x => if x ⟨0, U.n_pos⟩ = false then 1 else 0
  (dotProduct (star v) (proj.mulVec v)).re

/-- The binary code of a gate: a two-bit tag, then its qubit indices in self-delimiting binary. -/
def Gate.encode {n : ℕ} : Gate n → Str
  | .toffoli a b c _ _ _ => [false, false] ++ encBin a.val ++ encBin b.val ++ encBin c.val
  | .hh a b _ => [false, true] ++ encBin a.val ++ encBin b.val
  | .id => [true, false]

/-- The input string of Theorem 5's algorithm: the number of qubits `n` in unary (`encNat`), `ℓ` in
self-delimiting binary, then the gate codes in order. It is injective.

**Formalization Note.** `n` is written in unary, as a circuit lists its `n` input wires, so the input
length is at least `n`; "time `poly(n)`" (p. 33, with `ℓ ≤ poly(n)`) is then polynomial time in the
input length. With `n` in binary a circuit of `16` identity gates on `n` qubits would have an input
of length `O(log n)` while the output dimension `N = 1 + 4ℓ2ⁿ` alone needs `n` bits. -/
def THCircuit.encode (U : THCircuit) : Str :=
  encNat U.n ++ encBin U.gates.length ++ U.gates.flatMap Gate.encode

end QuadSDE.Supplement


