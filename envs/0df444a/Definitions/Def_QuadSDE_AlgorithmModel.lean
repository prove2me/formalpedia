-- Prove2me | Definitions.Def_QuadSDE_AlgorithmModel
-- name    : QuadSDE_AlgorithmModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:16:59.923223+00:00
-- url     : https://prove2.me/theorems/b0ee0c78-50a8-4ff4-a4bd-13da8ccac0eb
-- title:
--   Valid hidden data, the three-oracle interface, valid oracle triples and decoding of $\hat v$
-- statement:
--   Fix the classical part $x$ of an instance.
--   1. Hidden data $(c,Y)$ are **valid** for $x$ if the drift is admissible (Eqs. (5)–(7)), has strength at most $J$ and at most $r$ channels, and $\sum_iY_i^2=\|Y\|^2$ as supplied (so $Y\ne0$).
--   2. A packed quantum program has the **interface** of $x$ if it calls exactly three oracles, $\mathsf{Val}_c$ (on three index registers and $a_V$ ancillas), $\mathsf{Pos}_c$ (three index registers and $a_P$ ancillas) and $\mathsf{Val}_Y$ (one index register), and may call each of them controlled; inverse calls are always available.
--   3. An oracle family is a **valid triple** for $(c,Y)$ if oracle 0 is a value oracle for $c$ with normalization $J$, oracle 1 a position oracle for $c$ with $r$ channels, and oracle 2 an initial-condition oracle for $Y$, with arbitrary junk.
--   4. An output bit string $b$ of length $\ell\ge1$ is read as the real number
--   $$\hat v=(-1)^{b_0}\,2^{-L}\sum_{i<2L}b_{i+1}2^{2L-1-i},\qquad L=\lfloor(\ell-1)/2\rfloor;$$
--   the empty string reads as $0$.
--
--   **Formalization Note** The sparsity $s$ and the bounds $J,s\le\mathrm{poly}(\log N)$ of Eq. (8) belong to the succinct model and are not part of validity. Oracles are matrices on qubit registers; `retype` relabels the wires along the arity equations fixed by the interface. Every dyadic rational is the value of some bit string, so the output format restricts nothing.
-- source:
--   Bravyi, Byrne, Zayats, Zhuk, Zlokapa, Quantum algorithms for stochastic nonlinear differential equations, arXiv:2606.08349 (sha256 29bd9b01…94cdf), §1 pp. 3–4; §3.2 pp. 14–15; Theorem 2, p. 16

import Mathlib
import Definitions.Def_QAlgorithms_Defs_OPIUniformity
import Definitions.Def_QuadSDE_DriftClass
import Definitions.Def_QuadSDE_OracleModel
import Definitions.Def_QuadSDE_Instance

open QAlgorithms QAlgorithms.OPI

noncomputable section

namespace QuadSDE

/-- Bravyi–Byrne–Zayats–Zhuk–Zlokapa, arXiv:2606.08349 (sha256 29bd9b01…), §1 pp. 3–4 and §3.2
pp. 14–15: the hidden data `(c, Y)` form a valid APX-SDE instance with classical part `x` in the
oracle-based model: the drift is admissible (Eqs. (5)–(7)), has strength at most `J` and at most
`r` channels, and `‖Y‖² = Σ_i Y_i²` equals the classically supplied squared norm (so `Y ≠ 0`).

**Formalization Note.** The sparsity `s` and the bounds `J, s ≤ poly(log N)` of Eq. (8) belong to
the succinct model and are not part of the oracle model (p. 13: "the oracle-based model will be
used for dense drifts that only satisfy the bound on the number of drift channels"). -/
def Valid (x : Instance) (c : Coeff x.N) (Y : Fin x.N → ℝ) : Prop :=
  IsAdmissibleDrift c ∧ strengthLE c (x.J : ℝ) ∧ channelsLE c x.r ∧
    ∑ i, Y i ^ 2 = (x.normYsq : ℝ)

/-- The number of qubits of the value oracle `Val_c`: three index registers and `a_V` ancillas. -/
def valArity (x : Instance) : ℕ := idxWidth x.N + idxWidth x.N + idxWidth x.N + x.aV

/-- The number of qubits of the position oracle `Pos_c`: three index registers and `a_P`
ancillas. -/
def posArity (x : Instance) : ℕ := idxWidth x.N + idxWidth x.N + idxWidth x.N + x.aP

/-- §3, p. 13 and p. 14: the oracle interface of an algorithm for the instance `x`. The packed
program calls exactly three oracles, `Val_c` (oracle `0`, on `valArity x` qubits), `Pos_c` (oracle
`1`, on `posArity x` qubits) and `Val_Y` (oracle `2`, on the index register), and may call each of
them controlled ("We also assume access to the inverses and controlled versions of the oracles";
inverses are always available in `AdaptiveMembershipProgram`). -/
def Interface (x : Instance) (P : PackedMembershipProgram) : Prop :=
  P.oracles = 3 ∧ (∀ k, P.control k = true) ∧
    ∀ k : Fin P.oracles,
      (k.val = 0 → P.arity k = valArity x) ∧ (k.val = 1 → P.arity k = posArity x) ∧
        (k.val = 2 → P.arity k = idxWidth x.N)

/-- A matrix on `a` qubits read as a matrix on `b` qubits along `a = b` (relabelling the wires). -/
def retype {a b : ℕ} (M : Matrix (Qubits a) (Qubits a) ℂ) (h : a = b) :
    Matrix (Qubits b) (Qubits b) ℂ :=
  M.submatrix (fun z i => z (Fin.cast h i)) (fun z i => z (Fin.cast h i))

/-- §3.2, Eqs. (18)–(20), pp. 14–15: the oracle family `O` handed to the program `P` is a valid
triple for the hidden data `(c, Y)`: oracle `0` is a value oracle `Val_c` with normalization `J`,
oracle `1` is a position oracle `Pos_c` with normalization `√r`, and oracle `2` is an
initial-condition oracle `Val_Y`, each on the arity fixed by `Interface`. Junk components and
unspecified columns are arbitrary. -/
def OracleTriple (x : Instance) (c : Coeff x.N) (Y : Fin x.N → ℝ) (P : PackedMembershipProgram)
    (O : (k : Fin P.oracles) → Matrix (Qubits (P.arity k)) (Qubits (P.arity k)) ℂ) : Prop :=
  ∀ k : Fin P.oracles,
    (k.val = 0 → ∀ h : P.arity k = valArity x, IsValOracle x.aV (x.J : ℝ) c (retype (O k) h)) ∧
    (k.val = 1 → ∀ h : P.arity k = posArity x, IsPosOracle x.aP x.r c (retype (O k) h)) ∧
    (k.val = 2 → ∀ h : P.arity k = idxWidth x.N, IsInitOracle Y (retype (O k) h))

/-- Theorem 2, p. 16 ("outputs a real number `v̂`"): the real number written by an output bit
string `b` of length `out ≥ 1`. With `L = ⌊(out − 1)/2⌋`, bit `0` is the sign and bits `1, …, 2L`
are the binary digits of `|v̂| · 2^L` (most significant first):
`v̂ = (−1)^{b₀} · (Σ_{i<2L} b_{i+1} 2^{2L−1−i}) / 2^L`. The empty string reads as `0`.

**Formalization Note.** Every dyadic rational is the value of some bit string, so the output format
restricts nothing. -/
def decodeReal {out : ℕ} (b : Fin out → Bool) : ℝ :=
  if h : 0 < out then
    (if b ⟨0, h⟩ then (-1 : ℝ) else 1) *
      (∑ i : Fin (2 * ((out - 1) / 2)),
          if b ⟨i.val + 1, by have := i.isLt; omega⟩ then
            (2 : ℝ) ^ (2 * ((out - 1) / 2) - 1 - i.val) else 0) /
        (2 : ℝ) ^ ((out - 1) / 2)
  else 0

end QuadSDE


