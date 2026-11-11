-- Prove2me | Definitions.Def_QVolKLS_productOracles
-- name    : QVolKLS_productOracles
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:40:23.556578+00:00
-- url     : https://prove2.me/theorems/439926f3-7d17-4352-9595-f76d4ddf0b10
-- title:
--   Oracles $R_{\pi_\ell}$, $V_{Y_\ell}$, product input $|\pi_1\rangle\otimes\cdots\otimes|\pi_n\rangle$ and streaming layout of the product estimator
-- statement:
--   For a random variable $Y:\Omega\to[0,1]$ the **sample-controlled rotation** $V_Y$ is any unitary on $S\otimes Q$ ($Q$ one qubit) with
--   $$
--   V_Y(|x\rangle_S\otimes|0\rangle_Q)=|x\rangle_S\otimes\big(\sqrt{1-Y(x)}\,|0\rangle_Q+\sqrt{Y(x)}\,|1\rangle_Q\big).
--   $$
--   For laws $\pi_1,\dots,\pi_n$ on the labels $\{0,1\}^m$ of $m$-qubit sample registers, the **product input** is $|\pi_1\rangle\otimes\cdots\otimes|\pi_n\rangle\otimes|0^w\rangle$, register $S_\ell$ occupying wires $\ell m,\dots,\ell m+m-1$. The $2n$ oracles are $R_{\pi_\ell}\otimes I_Q$ and $V_{Y_\ell}$, each on $m+1$ qubits.
--
--   A circuit has the **streaming layout** if it is a concatenation prefix, $B_1,\dots,B_n$, suffix, where block $B_\ell$ calls only the two oracles of contribution $\ell$ and touches no sample register other than $S_\ell$, while prefix and suffix make no oracle call and touch no sample register. Then each qsample can be supplied when its block starts and discarded when it ends, and the remaining wires (the phase register) are shared.
--
--   These objects state the quantum product estimator (Lemma 4.1).
--
--   **Formalization Note** `sampleWire`, `sampleBlock`, `IsVYOracle`, `reflTensorI`, `productOracles`, `productInput`, `IsStreamingSplit`. $R_{\pi_\ell}\otimes I_Q$ ignores its last qubit, so it gives exactly the access of $R_{\pi_\ell}$.
-- source:
--   R. Zhang, Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation, arXiv:2610.04987 (preprint, held version, sha256 eee7a45e7117af08035a8d75fd6f145fa82ddade51ad87a6507911b6a0aa4f80), §4, p.30 (V_Y; Lemma 4.1)

import Definitions.Def_QVolKLS_fourthMomentNorm
import Definitions.Def_QVolKLS_MemAlgorithm

set_option autoImplicit false

namespace QVolKLS

open QAlgorithms

/-!
# The oracles, inputs and streaming layout of the quantum product estimator

R. Zhang, *Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation*,
arXiv:2610.04987 (held version, sha256 eee7a45e…), §4, p.30: "For a random variable `Y(x) ∈ [0, 1]`,
define `V_Y` to be the following sample-controlled rotation
`V_Y(|x⟩_S ⊗ |0⟩_Q) = |x⟩_S ⊗ (√(1 − Y(x))|0⟩_Q + √Y(x)|1⟩_Q)`", and Lemma 4.1, p.30 ("one
independent qsample from each `π_ℓ` and access to the controlled `R_{π_ℓ}` and `V_{Y_ℓ}`"; "The
qsamples may be supplied one at a time, and each is discarded before the next is needed; the phase
register is shared between contributions").

**Formalization Note.**
* Each law `π_ℓ` lives on the labels `Qubits m` of an `m`-qubit sample register (a law on any finite
  set is placed there, with zero weight on unused labels). Every oracle acts on `m + 1` qubits, the
  sample register followed by one qubit `Q` (the last wire): `V_{Y_ℓ}` on `S_ℓ ⊗ Q_ℓ`, and the
  reflection as `R_{π_ℓ} ⊗ I_Q` (a call that ignores its last qubit, so it gives exactly the access of
  `R_{π_ℓ}`). Oracle `ℓ` (first `n` indices) is `R_{π_ℓ} ⊗ I`, oracle `n + ℓ` is `V_{Y_ℓ}`.
* `V_Y` is specified only on `|x⟩|0⟩_Q`; `IsVYOracle Y V` says `V` is a unitary with that action, and
  statements quantify over every such extension.
* The `n` sample registers occupy wires `0, …, n·m − 1`, register `ℓ` the block of wires
  `ℓ·m, …, ℓ·m + m − 1` (`sampleWire`); the remaining `w` wires (phase register and workspace) start in
  `|0⟩`. `productInput π` is `|π_1⟩ ⊗ ⋯ ⊗ |π_n⟩ ⊗ |0^w⟩`.
* `IsStreamingSplit c` says the circuit is `prefix ++ B_1 ++ ⋯ ++ B_n ++ suffix`, where block `B_ℓ`
  calls only the two oracles of contribution `ℓ` and touches no sample register other than `S_ℓ`,
  and prefix and suffix make no call and touch no sample register. So `S_ℓ` is first used in `B_ℓ` and
  never after it: each qsample can be supplied when `B_ℓ` starts and discarded when it ends, and the
  remaining wires (the phase register) are shared.
-/

/-- Wire `j` of sample register `ℓ`: wire `ℓ·m + j` of the `n·m + w`-wire register. -/
def sampleWire (n m w : ℕ) (ℓ : Fin n) (j : Fin m) : Fin (n * m + w) :=
  Fin.castAdd w (finProdFinEquiv (ℓ, j))

/-- The wires of sample register `ℓ`. -/
def sampleBlock (n m w : ℕ) (ℓ : Fin n) : Set (Fin (n * m + w)) :=
  Set.range (sampleWire n m w ℓ)

/-- Zhang, p.30: `V` is a unitary on `S ⊗ Q` (`Q` the last wire) with
`V(|x⟩|0⟩) = |x⟩(√(1 − Y(x))|0⟩ + √Y(x)|1⟩)`. -/
def IsVYOracle {m : ℕ} (Y : Qubits m → ℝ) (V : Matrix (Qubits (m + 1)) (Qubits (m + 1)) ℂ) :
    Prop :=
  V ∈ Matrix.unitaryGroup (Qubits (m + 1)) ℂ ∧
    ∀ (x : Qubits m) (y : Qubits (m + 1)),
      V y (Fin.snoc x false) =
        if Fin.init y = x then
          (if y (Fin.last m) then ((Real.sqrt (Y x) : ℝ) : ℂ)
            else ((Real.sqrt (1 - Y x) : ℝ) : ℂ))
        else 0

/-- `R_π ⊗ I_Q` on `S ⊗ Q`, `Q` the last wire. -/
noncomputable def reflTensorI {m : ℕ} (π : Qubits m → ℝ) :
    Matrix (Qubits (m + 1)) (Qubits (m + 1)) ℂ :=
  Matrix.of fun y x =>
    if y (Fin.last m) = x (Fin.last m) then qsampleRefl π (Fin.init y) (Fin.init x) else 0

/-- The `2n` oracles: `R_{π_ℓ} ⊗ I` (index `ℓ`) and `V_ℓ` (index `n + ℓ`). -/
noncomputable def productOracles {n m : ℕ} (π : Fin n → Qubits m → ℝ)
    (V : Fin n → Matrix (Qubits (m + 1)) (Qubits (m + 1)) ℂ) :
    Fin (n + n) → Matrix (Qubits (m + 1)) (Qubits (m + 1)) ℂ :=
  Fin.addCases (fun ℓ => reflTensorI (π ℓ)) (fun ℓ => V ℓ)

/-- The input `|π_1⟩ ⊗ ⋯ ⊗ |π_n⟩ ⊗ |0^w⟩` on `n·m + w` wires. -/
noncomputable def productInput {n m : ℕ} (w : ℕ) (π : Fin n → Qubits m → ℝ) :
    Qubits (n * m + w) → ℂ :=
  fun z =>
    if ∀ i : Fin w, z (Fin.natAdd (n * m) i) = false then
      ∏ ℓ : Fin n, ((Real.sqrt (π ℓ (fun j => z (sampleWire n m w ℓ j))) : ℝ) : ℂ)
    else 0

/-- The streaming layout of Lemma 4.1: `c = prefix ++ B_1 ++ ⋯ ++ B_n ++ suffix`, block `B_ℓ` calling
only oracles `ℓ` and `n + ℓ` and touching no sample register but `S_ℓ`; prefix and suffix calling no
oracle and touching no sample register. -/
def IsStreamingSplit {S : Set Gate} {n m w : ℕ}
    (c : OracleCircuit S (fun _ : Fin (n + n) => m + 1) (n * m + w)) : Prop :=
  ∃ (pre suf : OracleCircuit S (fun _ : Fin (n + n) => m + 1) (n * m + w))
    (B : Fin n → OracleCircuit S (fun _ : Fin (n + n) => m + 1) (n * m + w)),
    c = pre ++ (List.ofFn B).flatten ++ suf ∧
    (∀ st ∈ pre ++ suf, stepCallsOnly ∅ st ∧ ∀ ℓ, Disjoint (stepWires st) (sampleBlock n m w ℓ)) ∧
    ∀ ℓ, ∀ st ∈ B ℓ, stepCallsOnly {Fin.castAdd n ℓ, Fin.natAdd n ℓ} st ∧
      ∀ j, j ≠ ℓ → Disjoint (stepWires st) (sampleBlock n m w j)

end QVolKLS


