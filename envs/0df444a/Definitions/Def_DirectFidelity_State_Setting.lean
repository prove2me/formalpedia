-- Prove2me | Definitions.Def_DirectFidelity_State_Setting
-- name    : DirectFidelity_State_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:07.420878+00:00
-- url     : https://prove2.me/theorems/f1650b33-f242-4983-bac7-7181be25a62f
-- title:
--   pp. 1–2, 6 — Pauli operators $W_k$, $\chi_\rho(k)=\mathrm{tr}(\rho W_k/\sqrt d)$, $\Pr(k)=\chi_\rho(k)^2$, the estimators $X, Y, \tilde X_i, \tilde Y$, $\ell$, $m_i$, the Born law and Hoeffding's $C$
-- statement:
--   This file fixes the setting of direct fidelity estimation (Flammia–Liu, §Fidelity Estimation, pp. 1–2, and the appendix *Bounding the Failure Probabilities*, p. 6).
--
--   1. **Qubits and Pauli operators.** A system of $n$ qubits has Hilbert space $\mathbb C^{d}$ with $d = 2^n$; its computational basis is indexed by bit strings $x \in \{0,1\}^n$. A Pauli label is a string $k \in \{0,1,2,3\}^n$ (there are $d^2 = 4^n$ of them), and the Pauli operator $W_k = P_{k_1}\otimes\cdots\otimes P_{k_n}$ is the tensor product of the single-qubit matrices $P_0 = I$, $P_1 = \sigma_x = \begin{pmatrix}0&1\\1&0\end{pmatrix}$, $P_2 = \sigma_y = \begin{pmatrix}0&-i\\i&0\end{pmatrix}$, $P_3 = \sigma_z = \begin{pmatrix}1&0\\0&-1\end{pmatrix}$. Entrywise, $(W_k)_{xy} = \prod_{i} (P_{k_i})_{x_i y_i}$.
--   2. **Characteristic function.** For a $d\times d$ matrix $\rho$,
--   $$\chi_\rho(k) = \mathrm{tr}\big(\rho W_k/\sqrt d\big).$$
--   3. **States.** $\rho$ is *pure* if $\rho = |\psi\rangle\langle\psi|$ for a unit vector $\psi\in\mathbb C^d$. A general state $\sigma$ is a density operator: positive semidefinite with trace one (the referenced definition `WildeQIT.IsDensityOperator`).
--   4. **Importance sampling (3) and the ideal estimators (4).** $\Pr(k) = \chi_\rho(k)^2$, $X = \chi_\sigma(k)/\chi_\rho(k)$, and for labels $k_1,\dots,k_\ell$, $Y = \frac1\ell\sum_{i=1}^\ell X_i$ with $X_i = \chi_\sigma(k_i)/\chi_\rho(k_i)$.
--   5. **Sample sizes.** $\ell = \lceil 1/(\varepsilon^2\delta)\rceil$, and the copy number (6) for label $k_i$,
--   $$m_i = \Big\lceil \frac{2}{d\,\chi_\rho(k_i)^2\,\ell\,\varepsilon^2}\log(2/\delta)\Big\rceil .$$
--   6. **One Pauli measurement.** Measuring $W_k$ on $\sigma$ yields $+1$ with probability $(1+\mathrm{tr}(\sigma W_k))/2$ and $-1$ with probability $(1-\mathrm{tr}(\sigma W_k))/2$ (the Born rule), so its mean is $\mathrm{tr}(\sigma W_k) = \sqrt d\,\chi_\sigma(k)$.
--   7. **The run.** Given labels $k_1,\dots,k_\ell$ and copy numbers $m_1,\dots,m_\ell$, the outcomes $A_{ij}$ ($1\le i\le \ell$, $1\le j\le m_i$) are independent, $A_{ij}$ distributed as one measurement of $W_{k_i}$ on $\sigma$. The estimators (7) are
--   $$\tilde X_i = \frac{1}{m_i\sqrt d\,\chi_\rho(k_i)}\sum_{j=1}^{m_i}A_{ij},\qquad \tilde Y = \frac1\ell\sum_{i=1}^\ell \tilde X_i .$$
--   8. **Hoeffding's constant (17).** $c_i = 1/(\ell m_i\sqrt d\,\chi_\rho(k_i))$ and $C = \sum_{i=1}^\ell\sum_{j=1}^{m_i}(2c_i)^2$.
--   9. **Well-conditioned states (p. 2).** $\rho$ is well-conditioned with parameter $\alpha$ if for every $k$, either $\mathrm{tr}(\rho W_k) = 0$ or $|\mathrm{tr}(\rho W_k)|\ge\alpha$.
--
--   These objects are shared by every statement of the mission: the goal and the milestones are all about the two-stage experiment (labels drawn from (3), then independent $\pm1$ outcomes) defined here.
--
--   **Formalization Note.** Basis labels are `Q n := Fin n → Fin 2` and Pauli labels `P n := Fin n → Fin 4`; $d$ is the real number `2 ^ n`. Traces are taken as real parts of complex traces: for Hermitian matrices they are real, so nothing is lost on states. $\lceil\cdot\rceil$ is `Nat.ceil`, $\log$ is the natural logarithm `Real.log`. The outcome law is `Real.toNNReal` weights times Dirac masses at $\pm1$; the page states only $A_{ij}\in\{1,-1\}$ and $\mathbb E A_{ij} = \sqrt d\,\chi_\sigma(k_i)$, and the Born law is the unique $\pm1$ law with that mean, so it adds no assumption. The outcomes of a run live on the slots $\Sigma_{i<\ell}\,\mathrm{Fin}(m_i)$ under the product measure. The copy numbers of the run are a general vector $m$ (so (16) holds for every choice), instantiated with (6) as `mVec`. At a label with $\chi_\rho(k) = 0$ the divisions in $X$, $m_i$, $\tilde X_i$, $c_i$ return Lean's junk value $0$; every theorem either weights by $\Pr(k)$ (which is $0$ there) or assumes $\chi_\rho(k_i)\ne 0$.
-- source:
--   Flammia and Liu, Direct fidelity estimation from few Pauli measurements, arXiv:1104.4695v3, pp. 1–2, §Fidelity Estimation, (2)–(7) and the well-conditioned definition; p. 6, (17)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator

/-!
Flammia and Liu, *Direct fidelity estimation from few Pauli measurements*, arXiv:1104.4695v3,
§Fidelity Estimation, pp. 1–2, (2)–(7), and appendix *Bounding the Failure Probabilities*, p. 6, (17).

The setting of direct fidelity estimation for an `n`-qubit pure state `ρ` and an arbitrary state `σ`:
the `d² = 4ⁿ` Pauli operators `W_k`, the characteristic function `χ_ρ(k) = tr(ρ W_k / √d)`, the
importance-sampling law `Pr(k) = χ_ρ(k)²`, the ideal estimators `X`, `Y`, the copy numbers `m_i`,
the Born-rule law of one `±1` Pauli measurement, and the finite-precision estimators `X̃_i`, `Ỹ`.
-/

namespace DirectFidelity.State

open MeasureTheory

/-- Computational-basis labels of `n` qubits: `d = 2ⁿ` of them. -/
abbrev Q (n : ℕ) : Type := Fin n → Fin 2

/-- Pauli labels of `n` qubits: one of `I, σ_x, σ_y, σ_z` (`0, 1, 2, 3`) per qubit, `d² = 4ⁿ` of them. -/
abbrev P (n : ℕ) : Type := Fin n → Fin 4

/-- The single-qubit Pauli matrices `I, σ_x, σ_y, σ_z`. -/
def pauli1 : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![1, 0; 0, 1]
  | 1 => !![0, 1; 1, 0]
  | 2 => !![0, -Complex.I; Complex.I, 0]
  | 3 => !![1, 0; 0, -1]

/-- The `n`-qubit Pauli operator `W_k = P_{k_1} ⊗ ⋯ ⊗ P_{k_n}`, written entrywise. -/
def W {n : ℕ} (k : P n) : Matrix (Q n) (Q n) ℂ :=
  fun x y => ∏ i, pauli1 (k i) (x i) (y i)

/-- The Hilbert-space dimension `d = 2ⁿ`. -/
noncomputable def dim (n : ℕ) : ℝ := 2 ^ n

/-- The characteristic function `χ_ρ(k) = tr(ρ W_k / √d)` (real part; it is real for Hermitian `ρ`). -/
noncomputable def chi {n : ℕ} (ρ : Matrix (Q n) (Q n) ℂ) (k : P n) : ℝ :=
  ((ρ * W k).trace).re / Real.sqrt (dim n)

/-- `ρ` is a pure state: `ρ = |ψ⟩⟨ψ|` for a unit vector `ψ`. -/
def IsPure {n : ℕ} (ρ : Matrix (Q n) (Q n) ℂ) : Prop :=
  ∃ ψ : Q n → ℂ, star ψ ⬝ᵥ ψ = 1 ∧ ρ = Matrix.vecMulVec ψ (star ψ)

/-- The importance-sampling law (3): `Pr(k) = χ_ρ(k)²`. -/
noncomputable def prob {n : ℕ} (ρ : Matrix (Q n) (Q n) ℂ) (k : P n) : ℝ := chi ρ k ^ 2

/-- The ideal estimator (4): `X = χ_σ(k) / χ_ρ(k)`. -/
noncomputable def X {n : ℕ} (ρ σ : Matrix (Q n) (Q n) ℂ) (k : P n) : ℝ := chi σ k / chi ρ k

/-- The averaged ideal estimator `Y = (1/ℓ) Σ_i X_i` for the labels `k_1, …, k_ℓ`. -/
noncomputable def Y {n ℓ : ℕ} (ρ σ : Matrix (Q n) (Q n) ℂ) (ks : Fin ℓ → P n) : ℝ :=
  (1 / (ℓ : ℝ)) * ∑ i, X ρ σ (ks i)

/-- The number of Pauli observables `ℓ = ⌈1/(ε²δ)⌉`. -/
noncomputable def ell (ε δ : ℝ) : ℕ := ⌈1 / (ε ^ 2 * δ)⌉₊

/-- The number of copies (6) used for a label `k`: `⌈2/(d χ_ρ(k)² ℓ ε²) · log(2/δ)⌉`. -/
noncomputable def mDFE {n : ℕ} (ρ : Matrix (Q n) (Q n) ℂ) (ε δ : ℝ) (ℓ : ℕ) (k : P n) : ℕ :=
  ⌈2 / (dim n * chi ρ k ^ 2 * (ℓ : ℝ) * ε ^ 2) * Real.log (2 / δ)⌉₊

/-- The copy numbers `m_i = mDFE(k_i)` of (6) along the labels `k_1, …, k_ℓ`. -/
noncomputable def mVec {n ℓ : ℕ} (ρ : Matrix (Q n) (Q n) ℂ) (ε δ : ℝ) (ks : Fin ℓ → P n) :
    Fin ℓ → ℕ :=
  fun i => mDFE ρ ε δ ℓ (ks i)

/-- The law of one measurement of the Pauli observable `W_k` on `σ` (Born rule): the outcome is
`+1` with probability `(1 + tr(σ W_k))/2` and `-1` with probability `(1 - tr(σ W_k))/2`. -/
noncomputable def outcomeLaw {n : ℕ} (σ : Matrix (Q n) (Q n) ℂ) (k : P n) : Measure ℝ :=
  Real.toNNReal ((1 + ((σ * W k).trace).re) / 2) • Measure.dirac (1 : ℝ) +
    Real.toNNReal ((1 - ((σ * W k).trace).re) / 2) • Measure.dirac (-1 : ℝ)

/-- The measurement slots `(i, j)`, `i = 1, …, ℓ`, `j = 1, …, m_i`. -/
abbrev Slot {ℓ : ℕ} (m : Fin ℓ → ℕ) : Type := Σ i : Fin ℓ, Fin (m i)

/-- The law of all outcomes `A_ij` given the labels `k_1, …, k_ℓ` and the copy numbers `m`:
independent, with `A_ij` distributed as one measurement of `W_{k_i}` on `σ`. -/
noncomputable def outcomes {n ℓ : ℕ} (σ : Matrix (Q n) (Q n) ℂ) (ks : Fin ℓ → P n)
    (m : Fin ℓ → ℕ) : Measure (Slot m → ℝ) :=
  Measure.pi (fun s : Slot m => outcomeLaw σ (ks s.1))

/-- The finite-precision estimator (7): `X̃_i = (1/(m_i √d χ_ρ(k_i))) Σ_j A_ij`. -/
noncomputable def Xt {n ℓ : ℕ} (ρ : Matrix (Q n) (Q n) ℂ) (ks : Fin ℓ → P n) (m : Fin ℓ → ℕ)
    (A : Slot m → ℝ) (i : Fin ℓ) : ℝ :=
  (1 / ((m i : ℝ) * Real.sqrt (dim n) * chi ρ (ks i))) * ∑ j : Fin (m i), A ⟨i, j⟩

/-- The estimate `Ỹ = (1/ℓ) Σ_i X̃_i`. -/
noncomputable def Yt {n ℓ : ℕ} (ρ : Matrix (Q n) (Q n) ℂ) (ks : Fin ℓ → P n) (m : Fin ℓ → ℕ)
    (A : Slot m → ℝ) : ℝ :=
  (1 / (ℓ : ℝ)) * ∑ i, Xt ρ ks m A i

/-- Hoeffding's coefficient (17): `c_i = 1/(ℓ m_i √d χ_ρ(k_i))`. -/
noncomputable def cHoef {n ℓ : ℕ} (ρ : Matrix (Q n) (Q n) ℂ) (ks : Fin ℓ → P n) (m : Fin ℓ → ℕ)
    (i : Fin ℓ) : ℝ :=
  1 / ((ℓ : ℝ) * (m i : ℝ) * Real.sqrt (dim n) * chi ρ (ks i))

/-- Hoeffding's constant (17): `C = Σ_i Σ_{j ≤ m_i} (2 c_i)²`. -/
noncomputable def Chof {n ℓ : ℕ} (ρ : Matrix (Q n) (Q n) ℂ) (ks : Fin ℓ → P n) (m : Fin ℓ → ℕ) :
    ℝ :=
  ∑ i, ∑ _j : Fin (m i), (2 * cHoef ρ ks m i) ^ 2

/-- `ρ` is well-conditioned with parameter `α` (p. 2): for every Pauli label `k`, either
`tr(ρ W_k) = 0` or `|tr(ρ W_k)| ≥ α`. -/
def IsWellConditioned {n : ℕ} (ρ : Matrix (Q n) (Q n) ℂ) (α : ℝ) : Prop :=
  ∀ k : P n, ((ρ * W k).trace).re = 0 ∨ α ≤ |((ρ * W k).trace).re|

end DirectFidelity.State


