-- Prove2me | Definitions.Def_FloatPointSynth_Gearbox_Circuit
-- name    : FloatPointSynth_Gearbox_Circuit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-23T03:58:52.260597+00:00
-- url     : https://prove2.me/theorems/b1eb4344-d6e3-48f3-9a84-5eaf49681bfa
-- title:
--   Gearbox circuit C^(d)(U¹,…,U^d), its measurement branches, the composed gearbox C◦d(U) and its level success probabilities (Fig. 1, Theorem 1, Definition 1)
-- statement:
--   This file fixes the quantum-circuit model of Sections II and III.
--
--   1. **Gates.** A qubit has computational basis $|0\rangle,|1\rangle$; a single-qubit gate is a $2\times 2$ complex matrix $U$, with $U_{1,0}=\langle 1|U|0\rangle$. $X=\begin{pmatrix}0&1\\1&0\end{pmatrix}$, and the $X$-rotation is
--   $$e^{-i\varphi X} := \cos(\varphi)\,\mathbb 1 - i\sin(\varphi)\,X .$$
--   In particular $e^{i\pi X/4}=e^{-i(-\pi/4)X}=(\mathbb 1+iX)/\sqrt 2$.
--   2. **Gearbox circuit** $C^{(d)}(U^1,\dots,U^d)$ (Fig. 1). The register consists of $d$ ancilla qubits, with basis states the bit strings $a\in\{0,1\}^d$, and one target qubit. The circuit applies $U^1\otimes\cdots\otimes U^d$ to the ancillas, then the $d$-controlled $-iX$ gate (which applies $-iX$ to the target exactly when every ancilla is $|1\rangle$), then $U^{1\dagger}\otimes\cdots\otimes U^{d\dagger}$ to the ancillas. It is applied to $|0^{\otimes d}\rangle|\psi\rangle$ and the ancillas are measured in the computational basis.
--   3. **Branches.** For an outcome $j\in\{0,1\}^d$, the branch $\beta_j(\psi)\in\mathbb C^2$ is the (unnormalized) target state $(\langle j|\otimes\mathbb 1)\,C^{(d)}(U^1,\dots,U^d)\,|0^{\otimes d}\rangle|\psi\rangle$; by the Born rule outcome $j$ has probability $\|\beta_j(\psi)\|^2$.
--   4. **Success block and composed gearbox** (Definition 1). For a single gate $V$, the success block $B(V)$ is the $2\times2$ matrix $(\langle 0|\otimes\mathbb 1)\,C^{(1)}(V)\,(|0\rangle\otimes\mathbb 1)$, and $\widehat B(V):=B(V)/\|B(V)|0\rangle\|$ is its normalization (the unitary enacted by $C^{\circ 1}(V)$ on success). The composed gearbox is defined recursively by
--   $$C^{\circ 0}(U):=U,\qquad C^{\circ (n+1)}(U):=\widehat B\big(C^{\circ n}(U)\big),$$
--   so that $C^{\circ d}(U)=C^{\circ 1}(C^{\circ (d-1)}(U))$ is the gate the composed circuit enacts when every measurement gives $0$.
--   5. **Level success probability.** For $q\ge1$, the probability that the level-$q$ measurement of $C^{\circ d}(U)$ gives $0$ is the Born probability
--   $$p_q(U):=\big\|B\big(C^{\circ(q-1)}(U)\big)|0\rangle\big\|^2 .$$
--   6. **Angles.** $\gamma(\theta):=\tan^{-1}(\tan^2\theta)$ (Theorem 1) and $\gamma_d(\theta_0):=\tan^{-1}(\tan^{2^d}\theta_0)$ (Corollary 1), both taking the value $\pi/2$ when $\cos\theta=0$ (respectively $\cos\theta_0=0$), which is the paper's $\tan^{-1}(\infty)$.
--
--   These objects are the circuit-level data on which the cost analysis of Theorem 2 is built: the level success probabilities $p_q(U)$ are computed from the circuit, not supplied as numbers.
--
--   **Formalization Note** Qubit indices are `Fin 2` ($|0\rangle$ = `0`, $|1\rangle$ = `1`); the joint basis is `(Fin d → Fin 2) × Fin 2`, ancillas first, target last. The controlled gate fires on the all-ones string. If the first column of $B(V)$ were zero (impossible for unitary $V$, by Theorem 1) the normalization returns the zero matrix. $p_q$ at $q=0$ equals $p_1$ because of natural-number subtraction and is never used. The angle functions exist because Lean's `Real.tan (π/2)` is `0`.
-- source:
--   Wiebe and Kliuchnikov, Floating Point Representations in Quantum Circuit Synthesis, arXiv:1305.5528v3, pp. 2–5, Fig. 1, Theorem 1 and its proof (Eq. (1), p. 3), Definition 1 (p. 5), Corollary 1 (p. 5)

import Mathlib

namespace FloatPointSynth.Gearbox

open Matrix Complex

/-- The Pauli matrix `X = [[0, 1], [1, 0]]` in the computational basis `|0⟩ = 0`, `|1⟩ = 1`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The `X`-rotation `e^{-iφX} = cos(φ) 𝟙 - i sin(φ) X` (the identity used on p. 3). -/
noncomputable def rotX (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.cos φ : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - (I * (Real.sin φ : ℂ)) • pauliX

/-- The tensor product `U¹ ⊗ ⋯ ⊗ U^d` of `d` single-qubit gates, acting on the `d` ancilla
qubits, whose basis states are bit strings `a : Fin d → Fin 2`. -/
def ancTensor {d : ℕ} (Us : Fin d → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin d → Fin 2) (Fin d → Fin 2) ℂ :=
  fun a b => ∏ ℓ, Us ℓ (a ℓ) (b ℓ)

/-- An operator `A` on the ancillas, extended by the identity on the target qubit. The joint
basis is `(a, s)` with the ancilla string `a` first and the target bit `s` last (Fig. 1). -/
def onAnc {d : ℕ} (A : Matrix (Fin d → Fin 2) (Fin d → Fin 2) ℂ) :
    Matrix ((Fin d → Fin 2) × Fin 2) ((Fin d → Fin 2) × Fin 2) ℂ :=
  fun p q => A p.1 q.1 * (if p.2 = q.2 then 1 else 0)

/-- The `d`-controlled `-iX` gate: it applies `-iX` to the target exactly when every ancilla is
`|1⟩`, and acts as the identity otherwise. -/
def ctrlNegIX (d : ℕ) :
    Matrix ((Fin d → Fin 2) × Fin 2) ((Fin d → Fin 2) × Fin 2) ℂ :=
  fun p q =>
    if p.1 = q.1 then
      (if p.1 = (fun _ => 1) then ((-I) • pauliX) p.2 q.2 else (if p.2 = q.2 then 1 else 0))
    else 0

/-- The gearbox circuit `C^(d)(U¹, …, U^d)` of Fig. 1 before measurement: first
`U¹ ⊗ ⋯ ⊗ U^d` on the ancillas, then the `d`-controlled `-iX`, then `U¹† ⊗ ⋯ ⊗ U^d†`. -/
noncomputable def gearbox {d : ℕ} (Us : Fin d → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix ((Fin d → Fin 2) × Fin 2) ((Fin d → Fin 2) × Fin 2) ℂ :=
  onAnc (ancTensor Us)ᴴ * ctrlNegIX d * onAnc (ancTensor Us)

/-- The input state `|0^{⊗d}⟩|ψ⟩`. -/
def inVec {d : ℕ} (ψ : Fin 2 → ℂ) : (Fin d → Fin 2) × Fin 2 → ℂ :=
  fun p => if p.1 = 0 then ψ p.2 else 0

/-- The (unnormalized) target state left when the ancilla measurement gives the bit string `j`:
the `|j⟩`-component of `C^(d)(U¹, …, U^d) |0^{⊗d}⟩|ψ⟩`. Its squared norm is the probability of
outcome `j` (Born rule). -/
noncomputable def branch {d : ℕ} (Us : Fin d → Matrix (Fin 2) (Fin 2) ℂ) (j : Fin d → Fin 2)
    (ψ : Fin 2 → ℂ) : Fin 2 → ℂ :=
  fun s => (gearbox Us *ᵥ inVec ψ) (j, s)

/-- The success block of the one-ancilla gearbox `C^(1)(V)`: the target operator enacted (before
normalization) when the ancilla is measured in `0`. -/
noncomputable def succBlock (V : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun s t => gearbox ![V] (0, s) (0, t)

/-- The success block normalized by the norm of its first column. For unitary `V`, Theorem 1
makes the success block a positive multiple of a unitary, so this is the unitary enacted by
`C◦1(V)` on success. If the first column is zero (never for unitary `V`) the value is `0`. -/
noncomputable def succUnitary (V : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt (∑ s, ‖succBlock V s 0‖ ^ 2))⁻¹ : ℂ) • succBlock V

/-- The composed gearbox circuit (Definition 1), as the unitary it enacts when every measurement
gives `0`: `composed U 0 = U` is the gate fed to the first level, and
`composed U (n + 1) = C◦1(composed U n)` on success, i.e. `composed U d` is `C◦d(U)`. -/
noncomputable def composed (U : Matrix (Fin 2) (Fin 2) ℂ) : ℕ → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => U
  | n + 1 => succUnitary (composed U n)

/-- The success probability of the level-`q` measurement of `C◦d(U)` (`q ≥ 1`): the Born
probability that the one-ancilla gearbox fed with `C◦(q-1)(U)` gives outcome `0` on the input
`|0⟩|0⟩`. (For `q = 0` the natural-number subtraction makes this the `q = 1` value; it is never
used.) -/
noncomputable def levelProb (U : Matrix (Fin 2) (Fin 2) ℂ) (q : ℕ) : ℝ :=
  ∑ s, ‖succBlock (composed U (q - 1)) s 0‖ ^ 2

/-- The angle `tan⁻¹(tan²θ)` of Theorem 1, with the paper's value `tan⁻¹(∞) = π/2` at
`θ = π/2` (where Lean's `Real.tan` would return `0`). -/
noncomputable def gearAngle (θ : ℝ) : ℝ :=
  if Real.cos θ = 0 then Real.pi / 2 else Real.arctan (Real.tan θ ^ 2)

/-- The angle `tan⁻¹(tan^{2^d}(θ0))` of Corollary 1, with the value `π/2` at `θ0 = π/2`. -/
noncomputable def composedAngle (θ0 : ℝ) (d : ℕ) : ℝ :=
  if Real.cos θ0 = 0 then Real.pi / 2 else Real.arctan (Real.tan θ0 ^ (2 ^ d))

end FloatPointSynth.Gearbox


