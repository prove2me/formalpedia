-- Prove2me | Definitions.Def_PoQHierarchy_Main_Device
-- name    : PoQHierarchy_Main_Device
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:42:44.351091+00:00
-- url     : https://prove2.me/theorems/21b1f6c3-5bd3-499c-a1b1-e2120b58b636
-- title:
--   The quantum device: $\{CX,H,T\}$ circuits, computational-basis measurement, persistent workspace
-- statement:
--   The quantum device of Definition 4.1 holds a workspace of $W$ qubits, a state vector $\psi:\{0,1\}^W\to\mathbb C$, initialised once to $|0\cdots0\rangle$.
--
--   An **invocation** receives the classical description of a circuit: a sequence of gates from the fixed universal gate set
--   $$S=\{CX,\;H,\;T\},\qquad H=\tfrac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix},\quad T=\begin{pmatrix}1&0\\0&e^{i\pi/4}\end{pmatrix},$$
--   acting on named qubits, followed by a list of qubits to measure in the computational basis. The device applies the gates, measures those qubits, returns the classical outcome and **keeps** the post-measurement state for later invocations. A description that does not decode, or names a qubit outside the workspace (or a $CX$ with equal control and target), yields the error symbol $\perp$ and leaves the state unchanged.
--
--   States are kept unnormalized: the branch with outcome $m$ carries $\Pi_m U\psi$, where $U$ is the circuit's unitary and $\Pi_m$ the projection onto the outcome. The Born probability of a sequence of outcomes over several invocations is the squared norm of the final branch vector. A device may also expose only its first $\mathrm{addr}$ qubits; this is used for algorithms acting on part of a larger register.
--
--   The device performs no other operation: there is no arbitrary-unitary oracle and no reset, so every invocation is a polynomial-size $\{CX,H,T\}$ computation on a persistent workspace.
--
--   **Formalization Note** Gates name qubits by natural numbers; descriptions are decoded by a fixed parser (`decodeCircuit`, inverse to `circuitCode`).
-- source:
--   Kaniuar Bacho, Dominik Leichtle, Atul Singh Arora, Alexandru Cojocaru, STOC 2027 submission #1666 (October 2026), p.24 (QPT recap, gate set S = {CX, H, T}), Definition 4.1 (pp.24–25, Quantum Workspace, Classical Interface); canonical PDF sha256 3009a0afeb95e5789f4e029db39d01935081f03d75e7fa263cb4b408aed40fb1

import Mathlib
import Definitions.Def_PoQHierarchy_Main_Basic

open QAlgorithms.Complexity
set_option autoImplicit false

namespace PoQHierarchy.Main

/-!
Bacho, Leichtle, Arora, Cojocaru, STOC 2027 submission #1666, p.24 (the QPT recap) and
Definition 4.1 (pp.24–25): the quantum device.

A workspace of `W` qubits holds a state vector `ψ : {0,1}^W → ℂ`. An invocation receives the
classical description of a circuit over the fixed finite gate set `{CX, H, T}` (p.24) together with
the list of qubits to be measured in the computational basis. The device applies the gates, measures
those qubits, returns the outcome and keeps the post-measurement state.

States are kept **unnormalized**: the branch of outcome `m` carries the vector `Π_m U ψ`, and the
Born probability of a whole sequence of outcomes is the squared norm of the final branch vector.
So the semantics is a probability distribution over transcripts, computed branch by branch.
-/

/-- A (possibly unnormalized) state vector of `W` qubits. -/
abbrev QVec (W : ℕ) := (Fin W → Bool) → ℂ

/-- The all-zero state `|0…0⟩`. -/
def zeroVec (W : ℕ) : QVec W := fun z => if ∀ i, z i = false then 1 else 0

/-- The squared norm `‖ψ‖²`; for a branch vector this is the Born weight of the branch. -/
noncomputable def normSq {W : ℕ} (ψ : QVec W) : ℝ := ∑ z, Complex.normSq (ψ z)

/-- The gates of the fixed universal gate set `S = {CX, H, T}` (p.24), on qubits named by natural
numbers. `cx c t` has control `c` and target `t`. -/
inductive Gate
  | cx (c t : ℕ)
  | h (i : ℕ)
  | t (i : ℕ)
  deriving DecidableEq

/-- A gate is well formed on a workspace of `m` qubits if its qubits exist (and, for `CX`, are
distinct). -/
def Gate.WellFormed (m : ℕ) : Gate → Bool
  | .cx c d => decide (c < m ∧ d < m ∧ c ≠ d)
  | .h i => decide (i < m)
  | .t i => decide (i < m)

/-- Hadamard on qubit `i`. -/
noncomputable def applyH {W : ℕ} (i : Fin W) (ψ : QVec W) : QVec W := fun z =>
  ((Real.sqrt 2 : ℂ))⁻¹ *
    (ψ (Function.update z i false) + (if z i then -1 else 1) * ψ (Function.update z i true))

/-- `T = diag(1, e^{iπ/4})` on qubit `i`. -/
noncomputable def applyT {W : ℕ} (i : Fin W) (ψ : QVec W) : QVec W := fun z =>
  (if z i then Complex.exp ((Real.pi / 4 : ℝ) * Complex.I) else 1) * ψ z

/-- `CX` with control `c` and target `t`: `|z⟩ ↦ |z with z_t ⊕ z_c at t⟩`. -/
def applyCX {W : ℕ} (c t : Fin W) (ψ : QVec W) : QVec W := fun z =>
  ψ (Function.update z t (xor (z t) (z c)))

/-- The action of a gate on a `W`-qubit state (the identity on a gate that is not well formed,
which the device never applies). -/
noncomputable def Gate.apply {W : ℕ} : Gate → QVec W → QVec W
  | .cx c d, ψ => if hc : c < W then (if hd : d < W then applyCX ⟨c, hc⟩ ⟨d, hd⟩ ψ else ψ) else ψ
  | .h i, ψ => if hi : i < W then applyH ⟨i, hi⟩ ψ else ψ
  | .t i, ψ => if hi : i < W then applyT ⟨i, hi⟩ ψ else ψ

/-- A circuit with classical output: a sequence of gates, applied first to last, followed by the
measurement of the listed qubits in the computational basis (p.24). -/
structure Circuit where
  gates : List Gate
  meas : List ℕ

/-- A circuit is well formed on a workspace of `m` qubits. -/
def Circuit.WellFormed (C : Circuit) (m : ℕ) : Bool :=
  C.gates.all (Gate.WellFormed m) && C.meas.all (fun i => decide (i < m))

/-- The unitary part of a circuit. -/
noncomputable def applyGates {W : ℕ} (gs : List Gate) (ψ : QVec W) : QVec W :=
  gs.foldl (fun φ g => g.apply φ) ψ

/-- The unnormalized post-measurement vector for the outcome `b` (one bit per measured qubit, in
the listed order): the projection onto `z_{meas_j} = b_j` for all `j`. -/
def project {W : ℕ} (meas : List ℕ) (b : Str) (ψ : QVec W) : QVec W := fun z =>
  if (meas.zip b).all (fun p => if h : p.1 < W then decide (z ⟨p.1, h⟩ = p.2) else true)
  then ψ z else 0

/-! ### Classical descriptions of circuits -/

/-- The code of a gate. -/
def gateCode : Gate → Str
  | .h i => pack [[false, false], natCode i]
  | .t i => pack [[false, true], natCode i]
  | .cx c d => pack [[true, false], natCode c, natCode d]

/-- The code of a circuit. -/
def circuitCode (C : Circuit) : Str :=
  pack [pack (C.gates.map gateCode), pack (C.meas.map natCode)]

/-- Decoding of a gate code. -/
def decodeGate (s : Str) : Option Gate :=
  match unpack s with
  | [[false, false], a] => some (.h (bitsVal a))
  | [[false, true], a] => some (.t (bitsVal a))
  | [[true, false], a, b] => some (.cx (bitsVal a) (bitsVal b))
  | _ => none

/-- Decoding of a circuit description; `none` for a malformed description. -/
def decodeCircuit (s : Str) : Option Circuit :=
  match unpack s with
  | [gs, ms] => ((unpack gs).mapM decodeGate).map (fun gates => ⟨gates, (unpack ms).map bitsVal⟩)
  | _ => none

/-- **One invocation of the device** (Definition 4.1, *Classical Interface*). The workspace has
`W` qubits, of which the first `addr` may be addressed. On a description `c` of a well-formed
circuit the device applies its gates, measures the designated qubits and returns, for every outcome
string `m`, the branch `(some m, Π_m U ψ)`; the state is kept for later invocations. On a malformed
description it returns the error symbol `none` (written `⊥`) and leaves the state unchanged. -/
noncomputable def deviceStep (addr W : ℕ) (c : Str) (ψ : QVec W) : List (Option Str × QVec W) :=
  match decodeCircuit c with
  | none => [(none, ψ)]
  | some C =>
    if C.WellFormed (min addr W) then
      (allStrings C.meas.length).map (fun b => (some b, project C.meas b (applyGates C.gates ψ)))
    else [(none, ψ)]

end PoQHierarchy.Main


