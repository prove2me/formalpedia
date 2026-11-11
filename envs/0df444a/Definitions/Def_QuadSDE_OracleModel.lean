-- Prove2me | Definitions.Def_QuadSDE_OracleModel
-- name    : QuadSDE_OracleModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:15:06.170817+00:00
-- url     : https://prove2.me/theorems/f5b8048f-5819-4c31-8a31-6c1b25bfb0e5
-- title:
--   Index registers and the oracles $\mathsf{Val}_c$, $\mathsf{Pos}_c$, $\mathsf{Val}_Y$ of the oracle-based model
-- statement:
--   In the oracle-based input model the drift and the initial condition are given by unitaries. An **index register** has Hilbert space $\mathrm{span}\{|0\rangle,|1\rangle,\dots,|N\rangle\}$, where $0$ is a blank symbol; it uses $d=\lceil\log_2(N+1)\rceil$ qubits. Three index registers $\mathsf I,\mathsf J,\mathsf K$ and an ancilla register $\mathsf A$ of $a$ qubits carry the oracles for $c$.
--
--   1. A **value oracle** is a unitary $\mathsf{Val}_c$ on $\mathsf{IJKA}$ with, for every $i\in[N]$,
--   $$\mathsf{Val}_c|i\rangle_{\mathsf I}|0\rangle_{\mathsf J}|0\rangle_{\mathsf K}|0\rangle_{\mathsf A}=\frac1J\sum_{j,k=1}^N c_{ijk}|i\rangle_{\mathsf I}|j\rangle_{\mathsf J}|k\rangle_{\mathsf K}|0\rangle_{\mathsf A}+|\mathrm{junk}_i\rangle \qquad(18).$$
--   2. A **position oracle** is a unitary $\mathsf{Pos}_c$ on $\mathsf{IJKA}$ with, for all $j,k\in[N]$,
--   $$\mathsf{Pos}_c|0\rangle_{\mathsf I}|j\rangle_{\mathsf J}|k\rangle_{\mathsf K}|0\rangle_{\mathsf A}=\frac1{\sqrt r}\sum_{i=1}^N\chi_{ijk}|i\rangle_{\mathsf I}|j\rangle_{\mathsf J}|k\rangle_{\mathsf K}|0\rangle_{\mathsf A}+|\mathrm{junk}_{j,k}\rangle \qquad(19),$$
--   where $\chi_{ijk}=1$ if $c_{ijk}\ne0$ and $0$ otherwise.
--   3. An **initial-condition oracle** is a unitary $\mathsf{Val}_Y$ on $\mathsf I$ with
--   $$\mathsf{Val}_Y|0\rangle_{\mathsf I}=\frac1{\|Y\|}\sum_{i=1}^N Y_i|i\rangle_{\mathsf I}\qquad(20).$$
--
--   Each junk vector is orthogonal to $(\mathbb C^{N+1})^{\otimes3}\otimes|0\rangle_{\mathsf A}$ but otherwise arbitrary, as long as the oracles are unitary.
--
--   **Formalization Note** Register values are written in binary, most significant bit first (`QAlgorithms.natToBits`); the paper's index $i\in[N]$ is `i : Fin N` held as the value $i+1$. Conditions (18)–(19) are stated as the exact amplitudes of the specified column on every basis vector $|i',j',k',0_{\mathsf A}\rangle$ with $i',j',k'\le N$; components with a register value above $N$ or a nonzero ancilla, and all other columns, are unconstrained.
-- source:
--   Bravyi, Byrne, Zayats, Zhuk, Zlokapa, Quantum algorithms for stochastic nonlinear differential equations, arXiv:2606.08349 (sha256 29bd9b01…94cdf), §3.2, Eqs. (18)–(20), pp. 14–15

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuadSDE_DriftClass

open QAlgorithms

noncomputable section

namespace QuadSDE

/-- Bravyi–Byrne–Zayats–Zhuk–Zlokapa, arXiv:2606.08349 (sha256 29bd9b01…), §3.2, p. 14: an index
register has Hilbert space `span{|0⟩, |1⟩, …, |N⟩}` (`0` is a blank symbol), expressed with
`⌈log₂(N + 1)⌉` qubits. -/
def idxWidth (N : ℕ) : ℕ := Nat.clog 2 (N + 1)

/-- §3.2, p. 14: the computational basis state of an index register holding the value
`v ∈ {0, …, N}`.

**Formalization Note.** The value is written in binary, most significant bit on wire `0`
(`QAlgorithms.natToBits`). The paper's tensor index `i ∈ [N]` is held as the value `i`; with
0-based `Fin N` the index `i : Fin N` is the register value `i + 1`, and the value `0` is the
blank. -/
def idxBasis (N v : ℕ) : Qubits (idxWidth N) := natToBits (idxWidth N) v

/-- §3.2, p. 14: the basis state `|i⟩_I |j⟩_J |k⟩_K |z⟩_A` of the three index registers `I, J, K`
(values `i, j, k ∈ {0, …, N}`) followed by the ancilla register `A` of `a` qubits. Register order
`I, J, K, A`, wire `0` first. -/
def regBasis (N a i j k : ℕ) (z : Qubits a) : Qubits (idxWidth N + idxWidth N + idxWidth N + a) :=
  Fin.append (Fin.append (Fin.append (idxBasis N i) (idxBasis N j)) (idxBasis N k)) z

/-- The all-zero ancilla `|0⟩_A`. -/
def zeroAnc (a : ℕ) : Qubits a := fun _ => false

/-- §3.2, Eq. (18), p. 14: `U` is a valid *value oracle* `Val_c` for the coefficient tensor `c` with
strength normalization `J`: `U` is unitary on `I, J, K, A` (`a` ancilla qubits) and, for every
`i ∈ [N]`,
`Val_c |i⟩_I|0⟩_J|0⟩_K|0⟩_A = (1/J) Σ_{j,k} c_{ijk} |i⟩_I|j⟩_J|k⟩_K|0⟩_A + |junk_i⟩`, with `|junk_i⟩`
orthogonal to `(ℂ^{N+1})^{⊗3} ⊗ |0⟩_A`.

**Formalization Note.** Stated as the exact amplitudes of the column of `U` at the input
`|i+1, 0, 0, 0_A⟩` on every basis vector `|i', j', k', 0_A⟩` with `i', j', k' ∈ {0, …, N}`: the
amplitude is `c_{i, j'-1, k'-1}/J` if `i' = i + 1` and `j', k' ≥ 1`, and `0` otherwise. Components
outside `(ℂ^{N+1})^{⊗3} ⊗ |0⟩_A` (a register value above `N`, or a nonzero ancilla) are the junk
and are unconstrained, as are all other columns ("otherwise arbitrary, provided that the two
oracles are unitary"). -/
def IsValOracle {N : ℕ} (a : ℕ) (J : ℝ) (c : Coeff N)
    (U : Matrix (Qubits (idxWidth N + idxWidth N + idxWidth N + a))
      (Qubits (idxWidth N + idxWidth N + idxWidth N + a)) ℂ) : Prop :=
  U ∈ Matrix.unitaryGroup _ ℂ ∧
  ∀ (i : Fin N) (i' j' k' : ℕ), i' ≤ N → j' ≤ N → k' ≤ N →
    U (regBasis N a i' j' k' (zeroAnc a)) (regBasis N a (i.val + 1) 0 0 (zeroAnc a)) =
      if h : i' = i.val + 1 ∧ 0 < j' ∧ j' ≤ N ∧ 0 < k' ∧ k' ≤ N then
        ((c i ⟨j' - 1, by omega⟩ ⟨k' - 1, by omega⟩ / J : ℝ) : ℂ)
      else 0

/-- §3.2, Eq. (19), p. 14: `U` is a valid *position oracle* `Pos_c` for `c` with `r` channels:
`U` is unitary on `I, J, K, A` and, for all `j, k ∈ [N]`,
`Pos_c |0⟩_I|j⟩_J|k⟩_K|0⟩_A = (1/√r) Σ_i χ_{ijk} |i⟩_I|j⟩_J|k⟩_K|0⟩_A + |junk_{j,k}⟩`, where
`χ_{ijk} = 1` if `c_{ijk} ≠ 0` and `0` otherwise, and `|junk_{j,k}⟩` is orthogonal to
`(ℂ^{N+1})^{⊗3} ⊗ |0⟩_A`.

**Formalization Note.** Exact amplitudes of the column at `|0, j+1, k+1, 0_A⟩` on every
`|i', j', k', 0_A⟩` with `i', j', k' ∈ {0, …, N}`: `1/√r` if `i' ≥ 1`, `j' = j + 1`, `k' = k + 1`
and `c_{i'-1, j, k} ≠ 0`, and `0` otherwise. Junk and other columns are unconstrained. -/
def IsPosOracle {N : ℕ} (a : ℕ) (r : ℕ) (c : Coeff N)
    (U : Matrix (Qubits (idxWidth N + idxWidth N + idxWidth N + a))
      (Qubits (idxWidth N + idxWidth N + idxWidth N + a)) ℂ) : Prop :=
  U ∈ Matrix.unitaryGroup _ ℂ ∧
  ∀ (j k : Fin N) (i' j' k' : ℕ), i' ≤ N → j' ≤ N → k' ≤ N →
    U (regBasis N a i' j' k' (zeroAnc a)) (regBasis N a 0 (j.val + 1) (k.val + 1) (zeroAnc a)) =
      if h : 0 < i' ∧ i' ≤ N ∧ j' = j.val + 1 ∧ k' = k.val + 1 then
        (if c ⟨i' - 1, by omega⟩ j k ≠ 0 then ((1 / Real.sqrt r : ℝ) : ℂ) else 0)
      else 0

/-- §3.2, Eq. (20), p. 15: `U` is a valid *initial-condition oracle* `Val_Y` for `Y ≠ 0`: a unitary
on the index register `I` with `Val_Y |0⟩_I = ‖Y‖⁻¹ Σ_{i=1}^N Y_i |i⟩_I` (exact equality), where
`‖Y‖ = (Σ_i Y_i²)^{1/2}` is the Euclidean norm. -/
def IsInitOracle {N : ℕ} (Y : Fin N → ℝ) (U : Matrix (Qubits (idxWidth N)) (Qubits (idxWidth N)) ℂ) :
    Prop :=
  U ∈ Matrix.unitaryGroup _ ℂ ∧
  act U (zeroKet (idxWidth N)) =
    ((Real.sqrt (∑ i, Y i ^ 2))⁻¹ : ℂ) • ∑ i : Fin N, ((Y i : ℝ) : ℂ) • ket (idxBasis N (i.val + 1))

end QuadSDE


