-- Prove2me | Definitions.Def_QVolKLS_fourthMomentNorm
-- name    : QVolKLS_fourthMomentNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:37:12.647197+00:00
-- url     : https://prove2.me/theorems/855bdb47-a5ca-4335-b925-8ee0c2086b97
-- title:
--   Joint states, qsamples $|\pi\rangle$, reflections $R_\pi$, the fourth-moment norm $\|\cdot\|_{4,\pi}$, trace distance
-- statement:
--   Let the sample register $S$ have computational basis indexed by a finite set $\Omega$, and let $A$ be an auxiliary space (any complex inner product space). A **joint vector** is
--   $$
--   |\Psi\rangle_{SA}=\sum_{x\in\Omega}|x\rangle_S\otimes|\psi_x\rangle_A ,\qquad \||\Psi\rangle\|=\Big(\sum_x\|\psi_x\|^2\Big)^{1/2},
--   $$
--   and an operator $M$ on $S$ acts as $M\otimes I_A$. For a nonnegative weight $\pi$ on $\Omega$:
--
--   1. the **qsample** is $|\pi\rangle=\sum_x\sqrt{\pi(x)}\,|x\rangle$ and the **qsample reflection** is $R_\pi=2|\pi\rangle\langle\pi|-I$; when $\pi$ vanishes off a feasible set this is $R_\pi\oplus(-I_{\mathrm{bad}})$;
--   2. the **fourth-moment norm** (13) is
--   $$
--   \||\Psi\rangle_{SA}\|_{4,\pi}=\Big(\sum_x\frac{\|\psi_x\|^4}{\pi(x)}\Big)^{1/4}\in[0,\infty],
--   $$
--   with a term $+\infty$ when $\pi(x)=0\neq\psi_x$;
--   3. a state of (control qubit)$\,\otimes S\otimes A$ is regarded as a joint vector of $S$ with auxiliary space $\mathbb C^2\otimes A$, i.e. the control is counted among the auxiliary registers.
--
--   Fresh workspace $E$ of $a$ qubits in $|0^a\rangle$ is placed on the first $a$ wires of a register. The **trace distance** of density matrices is $d_{\mathrm{tr}}(\rho,\sigma)=\frac12\|\rho-\sigma\|_1$; reduced states are obtained by discarding (partially tracing) workspace registers. A circuit over **arbitrary unitary gates** is used where a statement counts only oracle calls.
--
--   These objects are the error measure (16) of the reflection circuits and the trace-distance bookkeeping of §3.4.
--
--   **Formalization Note** `opApply`, `withZeroAnc`, `jointNorm`, `fourthMomentNorm` (in `ℝ≥0∞`), `qsample`, `qsampleRefl`, `ctrlAux`, `pureDensity`, `traceDist` (with the published `QAlgorithms.traceNorm`), `reducedSnd`, `traceOutMid`, `probWhere`, `unitaryGateSet`, `stepWires`, `stepCallsOnly`.
-- source:
--   R. Zhang, Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation, arXiv:2610.04987 (preprint, held version, sha256 eee7a45e7117af08035a8d75fd6f145fa82ddade51ad87a6507911b6a0aa4f80), §2, p.21 (registers, d_tr); §2.3, p.22 (qsample, R_π); §3.1, p.24, (13) (fourth-moment norm); §3.2, p.27 (R_π ⊕ (−I_bad))

import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_MatrixDistances

set_option autoImplicit false

namespace QVolKLS

open QAlgorithms
open scoped ComplexConjugate ENNReal

/-!
# Joint sample–auxiliary states, qsamples, reflections, fourth-moment norm, trace distance

R. Zhang, *Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation*,
arXiv:2610.04987 (held version, sha256 eee7a45e…): §2, p.21 (registers `S`, `A`, `E`; "|Ψ⟩_SA is a
joint vector on the sample and auxiliary registers"; `d_tr(ρ, σ) = ½‖ρ − σ‖₁`), §2.3, p.22 (the
qsample `|π⟩ = Σ_x √π(x)|x⟩` and the reflection `R_π = 2|π⟩⟨π| − I`), and §3.1, p.24, display (13)
(the fourth-moment norm `‖|Ψ⟩_SA‖_{4,π} = (Σ_x ‖|ψ_x⟩_A‖⁴/π(x))^{1/4}`).

**Formalization Note.**
* A joint vector `|Ψ⟩_SA = Σ_x |x⟩_S ⊗ |ψ_x⟩_A` is the function `Ψ : ι → H`, `x ↦ ψ_x`, where `ι`
  indexes the computational basis of the sample register and `H` is the auxiliary space (any complex
  inner product space). An operator `M` on the sample register acts as `M ⊗ I_A`:
  `(opApply M Ψ) y = Σ_x M y x • Ψ x`. Its norm is `jointNorm Ψ = (Σ_x ‖ψ_x‖²)^{1/2}`.
* A register of `a + n` qubits has its first `a` wires first (`regSplit`); `withZeroAnc a Ψ` is
  `|0^a⟩_E ⊗ |Ψ⟩`, the fresh workspace `E` on the first `a` wires.
* The fourth-moment norm is computed in `ℝ≥0∞`: a term with `π(x) = 0` and `ψ_x ≠ 0` is `+∞`
  (p.24: "the value is infinite when µ_Ψ is not absolutely continuous with respect to π"), and a term
  with `ψ_x = 0` is `0`.
* `qsample π` and `qsampleRefl π` are defined for every nonnegative weight `π` on `ι`. When `π`
  vanishes off a feasible set `Ω`, `qsampleRefl π` is `R_π ⊕ (−I_bad)` (p.27).
* `ctrlAux Φ` regroups a state of `(control qubit) ⊗ S ⊗ A`, the control being wire `0`, as a joint
  vector of `S` with auxiliary space `ℂ² ⊗ A = H × H` (`PiLp 2`): the control is counted among the
  auxiliary registers (Theorem 3.3, p.26).
* `traceDist ρ σ = ½ ‖ρ − σ‖₁` uses the published trace norm `QAlgorithms.traceNorm`.
-/

/-- The first `a` wires and the last `n` wires of an `(a + n)`-qubit basis string. -/
def regSplit {a n : ℕ} (z : Qubits (a + n)) : Qubits a × Qubits n :=
  (fun i => z (Fin.castAdd n i), fun j => z (Fin.natAdd a j))

/-- The `(a + n)`-qubit basis string whose first `a` wires are `e` and last `n` wires are `y`. -/
def joinReg {a n : ℕ} (e : Qubits a) (y : Qubits n) : Qubits (a + n) :=
  Fin.append e y

/-- `M ⊗ I_A` applied to the joint vector `Ψ`: `(M ⊗ I_A)Ψ (y) = Σ_x M y x • Ψ x`. -/
def opApply {ι H : Type*} [Fintype ι] [AddCommGroup H] [Module ℂ H] (M : Matrix ι ι ℂ)
    (Ψ : ι → H) : ι → H :=
  fun y => ∑ x, M y x • Ψ x

/-- `|0^a⟩_E ⊗ |Ψ⟩`: fresh workspace of `a` qubits in `|0⟩`, on the first `a` wires. -/
def withZeroAnc {H : Type*} [Zero H] (a : ℕ) {n : ℕ} (Ψ : Qubits n → H) : Qubits (a + n) → H :=
  fun z => if (regSplit z).1 = (fun _ => false) then Ψ (regSplit z).2 else 0

/-- The Hilbert norm `‖|Ψ⟩‖ = (Σ_x ‖ψ_x‖²)^{1/2}` of a joint vector. -/
noncomputable def jointNorm {ι H : Type*} [Fintype ι] [NormedAddCommGroup H] (Ψ : ι → H) : ℝ :=
  Real.sqrt (∑ x, ‖Ψ x‖ ^ 2)

/-- Zhang, §3.1, p.24, (13): the **fourth-moment norm**
`‖|Ψ⟩_SA‖_{4,π} = (Σ_x ‖ψ_x‖⁴/π(x))^{1/4}`, in `ℝ≥0∞` (a term with `π(x) = 0 ≠ ψ_x` is `∞`). -/
noncomputable def fourthMomentNorm {ι H : Type*} [Fintype ι] [NormedAddCommGroup H] (π : ι → ℝ)
    (Ψ : ι → H) : ℝ≥0∞ :=
  (∑ x, (‖Ψ x‖₊ : ℝ≥0∞) ^ 4 / ENNReal.ofReal (π x)) ^ (1 / 4 : ℝ)

/-- Zhang, §2.3, p.22: the **qsample** `|π⟩ = Σ_x √π(x) |x⟩`, as its amplitude function. -/
noncomputable def qsample {ι : Type*} (π : ι → ℝ) : ι → ℂ :=
  fun x => ((Real.sqrt (π x) : ℝ) : ℂ)

/-- Zhang, §2.3, p.22: the **qsample reflection** `R_π = 2|π⟩⟨π| − I`. -/
noncomputable def qsampleRefl {ι : Type*} [DecidableEq ι] (π : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.of fun y x => 2 * qsample π y * conj (qsample π x) - (if y = x then 1 else 0)

/-- A state of `(control) ⊗ S ⊗ A` on `n + 1` sample-side wires (control = wire `0`) as a joint
vector of `S` with auxiliary space `ℂ² ⊗ A` (the control counted among the auxiliary registers). -/
def ctrlAux {n : ℕ} {H : Type*} (Φ : Qubits (n + 1) → H) : Qubits n → PiLp 2 (fun _ : Bool => H) :=
  fun x => WithLp.toLp 2 (fun c => Φ (Fin.cons c x))

/-- The pure-state density matrix `|v⟩⟨v|`. -/
def pureDensity {ι : Type*} (v : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => v i * conj (v j)

/-- Zhang, §2.1, p.21: the **trace distance** `d_tr(ρ, σ) = ½ ‖ρ − σ‖₁`. -/
noncomputable def traceDist {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ σ : Matrix ι ι ℂ) : ℝ :=
  traceNorm (ρ - σ) / 2

/-- The reduced density matrix on the last `n` wires of the pure state `v` on `a + n` wires (the
first `a` wires discarded): `ρ(y, y′) = Σ_e v(e, y) conj(v(e, y′))`. -/
noncomputable def reducedSnd {a n : ℕ} (v : Qubits (a + n) → ℂ) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun y y' => ∑ e : Qubits a, v (joinReg e y) * conj (v (joinReg e y'))

/-- The reduced density matrix on `β × σ` of a pure state `v` on `β × ε × σ`, the middle register
`ε` (implementation workspace) discarded: `ρ((z, x), (z′, x′)) = Σ_e v(z, e, x) conj(v(z′, e, x′))`. -/
noncomputable def traceOutMid {β ε σ : Type*} [Fintype ε] (v : β × ε × σ → ℂ) :
    Matrix (β × σ) (β × σ) ℂ :=
  Matrix.of fun p q => ∑ e : ε, v (p.1, e, p.2) * conj (v (q.1, e, q.2))

/-- The probability `Σ_{z ∈ S} |Ψ(z)|²` that measuring the state `Ψ` in the computational basis
gives an outcome in `S`. -/
noncomputable def probWhere {ι : Type*} [Fintype ι] (Ψ : ι → ℂ) (S : Set ι) : ℝ :=
  ∑ z, S.indicator (fun z => ‖Ψ z‖ ^ 2) z

/-- Arbitrary unitary gates (on any number of qubits): the gate model of the statements that count
only oracle calls. -/
def unitaryGateSet : Set Gate :=
  {g | g.IsUnitary}

/-- The wires a step of an oracle circuit touches (a gate's wires; a call's wires and control). -/
def stepWires {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ} :
    OracleStep S a n → Set (Fin n)
  | .gate g => Set.range g.wires
  | .query _ _ c w _ => Set.range w ∪ {x | c = some x}

/-- A step calls no oracle outside the set `T` of oracle indices (gates call none). -/
def stepCallsOnly {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {n : ℕ} (T : Set (Fin r)) :
    OracleStep S a n → Prop
  | .gate _ => True
  | .query k _ _ _ _ => k ∈ T

end QVolKLS


