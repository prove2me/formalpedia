-- Prove2me | Definitions.Def_TolProdTest_acceptProbMixed
-- name    : TolProdTest_acceptProbMixed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T03:25:42.542752+00:00
-- url     : https://prove2.me/theorems/e7877567-ff2e-4f2c-8fdb-b1fb37d79189
-- title:
--   Acceptance probability of a gate circuit on encoded copies of a mixed state
-- statement:
--   The algorithm model of the mission (the paper names none). A circuit with $N$ copies is a list of gates from $\{H,S,T,X,\mathrm{CNOT}\}$ on $W=N\cdot n\cdot\lceil\log_2d\rceil+m$ qubit wires. An input $\sigma$ on $N$ copies of $(\mathbb C^d)^{\otimes n}$ (typically $\rho^{\otimes N}$) is loaded through the encoding isometry $V$, which writes each qudit level in binary on $\lceil\log_2 d\rceil$ wires (copy $j$, site $i$ on wires $(jn+i)\lceil\log_2d\rceil,\dots$); the $m$ ancillas start in $|0\rangle$; the gates' unitary $U$ is applied; and the wire `out` is measured. The acceptance probability is the Born probability of reading $1$:
--
--   $$
--   \sum_{y:\ y_{\mathrm{out}}=1}\big(U V\sigma V^\dagger U^\dagger\big)_{yy}.
--   $$
--
--   The sample complexity of such an algorithm is $N$ and its computational complexity is the number of gates.
--
--   **Formalization Note** Gates are the published `ShiShallow.Instr`. Intermediate measurements and classical post-processing are deferred into the circuit. The circuit is a fixed list, chosen before the input.
-- source:
--   Bao, Helsen, Nguyen, Fully tolerant product state testing and closest product state learning, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), Theorem 1.1, p.3; Theorem 3.8, pp.18–19 (model not named in the paper)

import Mathlib
import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

open Matrix

namespace TolProdTest

/-- Wires per qudit: `⌈log₂ d⌉ = Nat.clog 2 d`, the least `w` with `d ≤ 2^w`. -/
abbrev qd (d : ℕ) : ℕ := Nat.clog 2 d

/-- The data-wire encoding of `N` copies of an `n`-qudit basis string: copy `j`, site `i`, bit `b` is wire
`(j·n + i)·qd d + b` and carries bit `b` of the level `x j i` (little-endian binary). -/
def encodeData {N n d : ℕ} (x : Fin N → Fin n → Fin d) : ShiShallow.Bits (N * n * qd d) :=
  fun w =>
    let p := (finProdFinEquiv.symm w : Fin (N * n) × Fin (qd d))
    let ji := (finProdFinEquiv.symm p.1 : Fin N × Fin n)
    Nat.testBit (x ji.1 ji.2).val p.2.val

/-- The full input string: data wires as in `encodeData`, then `m` ancilla wires set to `0` (`false`). -/
def encodeInput {N n d m : ℕ} (x : Fin N → Fin n → Fin d) : ShiShallow.Bits (N * n * qd d + m) :=
  fun w => if h : w.val < N * n * qd d then encodeData x ⟨w.val, h⟩ else false

/-- The encoding isometry `V : (ℂ^d)^{⊗nN} → (ℂ^2)^{⊗W}`, `V|x⟩ = |encodeInput x⟩`. -/
def inputIso (N n d m : ℕ) :
    Matrix (ShiShallow.Bits (N * n * qd d + m)) (Fin N → Fin n → Fin d) ℂ :=
  Matrix.of fun y x => if y = encodeInput x then 1 else 0

/-- Apply a flat list of gates in order (first gate first). -/
noncomputable def runGates {W : ℕ} (gates : List (ShiShallow.Instr W)) (ψ : ShiShallow.QState W) :
    ShiShallow.QState W :=
  gates.foldl (fun st g => g.apply st) ψ

/-- The unitary of a gate list: column `x` is the image of the basis state `|x⟩`. -/
noncomputable def circMat {W : ℕ} (gates : List (ShiShallow.Instr W)) :
    Matrix (ShiShallow.Bits W) (ShiShallow.Bits W) ℂ :=
  Matrix.of fun y x => runGates gates (fun z => if z = x then 1 else 0) y

/-- **Acceptance probability of a quantum circuit on a mixed input** (the algorithm model of the mission; the paper
names none, see Bao, Helsen, Nguyen, *Fully tolerant product state testing and closest product state learning*, arXiv:2610.01979 (version of October 1st 2026, sha256 9e43ab25…), Theorem 1.1, p.3, and Theorem 3.8, p.18, which counts "quantum gates").

An algorithm with `N` copies is a list of gates over the published gate set `{H, S, T, X, CNOT}`
(`ShiShallow.Instr`) on `W = N·n·qd d + m` qubit wires. The input `σ` (an operator on `N` copies of
`(ℂ^d)^{⊗n}`, typically `ρ^{⊗N}`) is loaded on the data wires through the encoding `V` (`encodeData`), the `m`
ancillas start in `|0⟩`, the gates `U` are applied, and wire `out` is measured in the computational basis. The
value is the Born probability of outcome `1`: `Σ_{y : y_out = 1} Re (U V σ V† U†)_{yy}`.

**Formalization Note** Intermediate measurements and classical post-processing are deferred into the circuit; the
gate count of the algorithm is the length of the list. The circuit is fixed before the input. -/
noncomputable def acceptProbMixed {N n d m : ℕ}
    (σ : Matrix (Fin N → Fin n → Fin d) (Fin N → Fin n → Fin d) ℂ)
    (gates : List (ShiShallow.Instr (N * n * qd d + m))) (out : Fin (N * n * qd d + m)) : ℝ :=
  ∑ y : ShiShallow.Bits (N * n * qd d + m),
    if y out = true then
      ((circMat gates * inputIso N n d m * σ * (inputIso N n d m)ᴴ * (circMat gates)ᴴ) y y).re
    else 0

end TolProdTest


