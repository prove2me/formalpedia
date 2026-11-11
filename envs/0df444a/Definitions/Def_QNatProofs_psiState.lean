-- Prove2me | Definitions.Def_QNatProofs_psiState
-- name    : QNatProofs_psiState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T22:01:16.352057+00:00
-- url     : https://prove2.me/theorems/414e9a68-9861-4a30-a162-431838cec978
-- title:
--   The states $|\psi_{f,\gamma}\rangle$, the ensembles $D_{\mathrm{rf}}$ and $D_F$, and TVD of amplitude lists
-- statement:
--   For $f:\{0,1\}^n\to\mathbb C$ and a threshold $\gamma$, with $N=2^n$ and $\|f\|$ the $\ell^2$ norm,
--   $$
--   |\psi_{f,\gamma}\rangle=\begin{cases}\frac1{\|f\|}\sum_x f(x)|x\rangle,&\|f\|\ge\gamma\sqrt N,\\ |0^n\rangle,&\text{otherwise.}\end{cases}\tag{6}
--   $$
--   For a sampler $\mathrm{Samp}$ and $H:\{0,1\}^n\to\{0,1\}^R$, $f_H(x)=\mathrm{Samp}(H(x))$ (5) and $|\psi_{H,\gamma}\rangle=|\psi_{f_H,\gamma}\rangle$ (7).
--
--   - $D_{\mathrm{rf}}$ is the law of $|\psi_{H,\gamma}\rangle$ for a uniformly random function $H$.
--   - For a keyed family $F=\{F_k:\{0,1\}^n\to\{0,1\}^R\}_k$, $D_F$ is the law of $|\psi_{F_k,\gamma}\rangle$ for a uniformly random key $k$.
--   - $\mathrm{TVD}(\mathrm{al}_T(\mu),\mathrm{al}_T(\nu))=\tfrac12\sum_s|\mu\{\mathrm{al}_T=s\}-\nu\{\mathrm{al}_T=s\}|$ over the strings $s$ of length $T2^{n+1}$.
--   - A real $C$ is **a constant for which Theorem 3.1 holds** if for every $n\ge1$, $\gamma\in(0,1]$, every $(s,\xi,\eta)$-complex Gaussian sampler and every $\beta\in(0,1)$ with $s\gamma+\xi\le\beta$, for every $T$,
--   $$\mathrm{TVD}(\mathrm{al}_T(D_{\mathrm{rf}}),\mathrm{al}_T(\mathrm{Haar}_n))\le N\eta+e^{-N(1-\beta^2)^2/2}+CN^{3/2}2^T\cdot\frac{2\xi}{\beta}.$$
--
--   These are the state ensembles of §3 and the statistical distance in which their pseudorandomness is measured.
--
--   **Formalization Note** The first case of (6) also requires $\|f\|\neq0$, which follows from $\|f\|\ge\gamma\sqrt N$ when $\gamma>0$; it only excludes the undefined case. $D_{\mathrm{rf}}$ and $D_F$ are uniform mixtures of point masses and include the $|0^n\rangle$ branch.
-- source:
--   Li, Parham, Natural proofs for quantum state preparation lower bounds, arXiv:2610.06826 (held copy sha256 b604fa11…), (5)–(7), p.11; Theorem 3.1, (8), p.12; Theorem 3.3, p.15; Corollary 3.2.1, p.15

import Mathlib
import Definitions.Def_QNatProofs_haar
import Definitions.Def_QNatProofs_al
import Definitions.Def_QNatProofs_complexGaussian

set_option autoImplicit false

namespace QNatProofs

open QAlgorithms MeasureTheory
open scoped ENNReal

/-- The amplitude vector `Σ_x f(x)|x⟩` of a function `f : {0,1}ⁿ → ℂ`; its norm is the `ℓ²` norm
`‖f‖ = (Σ_x |f(x)|²)^{1/2}`. -/
noncomputable def ampVec {n : ℕ} (f : Qubits n → ℂ) : EuclideanSpace ℂ (Qubits n) :=
  WithLp.toLp 2 f

/-- **The state `|ψ_{f,γ}⟩`** (Li, Parham, arXiv:2610.06826 (held copy sha256 b604fa11…), (6),
p.11): for `f : {0,1}ⁿ → ℂ` and a threshold `γ ∈ (0, 1]`, with `N = 2ⁿ`,
`|ψ_{f,γ}⟩ = (1/‖f‖) Σ_x f(x)|x⟩` if `‖f‖ ≥ γ√N`, and `|0ⁿ⟩` otherwise.

**Formalization Note** The first case also requires `‖f‖ ≠ 0`, which follows from `‖f‖ ≥ γ√N`
for every `γ > 0`; it only excludes the undefined case `f = 0`, `γ ≤ 0`. -/
noncomputable def psiState {n : ℕ} (f : Qubits n → ℂ) (γ : ℝ) : sphere n :=
  if h : γ * Real.sqrt ((2 : ℝ) ^ n) ≤ ‖ampVec f‖ ∧ ‖ampVec f‖ ≠ 0 then
    ⟨((‖ampVec f‖ : ℂ))⁻¹ • ampVec f, by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _)]
      exact inv_mul_cancel₀ h.2⟩
  else ⟨zeroKet n, by simp [zeroKet, ket]⟩

/-- `f_H(x) = Samp(H(x))` ((5), p.11), as complex amplitudes: the sampler output on the tape
`H(x)`, read as the complex number it encodes. -/
noncomputable def fH {n R q : ℕ} (Samp : Sampler R q) (H : Qubits n → Fin R → Bool) :
    Qubits n → ℂ :=
  fun x => polarVal (Samp (H x))

/-- **`D_rf`** (p.11): the law of `|ψ_{H,γ}⟩ = |ψ_{f_H,γ}⟩` ((7)) for a uniformly random function
`H : {0,1}ⁿ → {0,1}^R`. -/
noncomputable def Drf (n : ℕ) (γ : ℝ) {R q : ℕ} (Samp : Sampler R q) : Measure (sphere n) :=
  (Fintype.card (Qubits n → Fin R → Bool) : ℝ≥0∞)⁻¹ •
    ∑ H : Qubits n → Fin R → Bool, Measure.dirac (psiState (fH Samp H) γ)

/-- **`D_F`** (Theorem 3.3, p.15): the law of `|ψ_{F_k,γ}⟩` for a uniformly random key `k` of a
keyed family `F = {F_k : {0,1}ⁿ → {0,1}^R}_k`. -/
noncomputable def DF {n : ℕ} (γ : ℝ) {R q : ℕ} (Samp : Sampler R q) {κ : Type} [Fintype κ]
    (F : κ → Qubits n → Fin R → Bool) : Measure (sphere n) :=
  (Fintype.card κ : ℝ≥0∞)⁻¹ • ∑ k : κ, Measure.dirac (psiState (fH Samp (F k)) γ)

/-- **`TVD(al_T(μ), al_T(ν))`**: the total variation distance between the laws of the amplitude
list `al_T(ψ)` under `ψ ∼ μ` and `ψ ∼ ν`,
`½ Σ_s |μ{al_T = s} − ν{al_T = s}|` over the strings `s` of length `T 2^{n+1}`. -/
noncomputable def tvdAl {n : ℕ} (T : ℕ) (μ ν : Measure (sphere n)) : ℝ :=
  (1 / 2 : ℝ) * ∑ s : Fin (T * 2 ^ (n + 1)) → Bool,
    |(μ {ψ | al T (ψ : EuclideanSpace ℂ (Qubits n)) = List.ofFn s}).toReal -
      (ν {ψ | al T (ψ : EuclideanSpace ℂ (Qubits n)) = List.ofFn s}).toReal|

/-- `C` is **a constant for which Theorem 3.1 holds** (Li, Parham, arXiv:2610.06826 (held copy
sha256 b604fa11…), Theorem 3.1, (8), p.12; used as a hypothesis in Corollary 3.2.1, p.15): for
every `n ≥ 1` (`N = 2ⁿ`), `γ ∈ (0, 1]`, every `(s, ξ, η)`-complex Gaussian sampler and every
`β ∈ (0, 1)` with `sγ + ξ ≤ β`, for every `T ∈ ℕ`,
`TVD(al_T(D_rf), al_T(Haar_n)) ≤ Nη + e^{-N(1−β²)²/2} + C N^{3/2} 2^T · 2ξ/β`. -/
def Thm31Const (C : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ γ : ℝ, 0 < γ → γ ≤ 1 →
    ∀ (R q : ℕ) (Samp : Sampler R q) (s ξ η : ℝ), IsComplexGaussianSampler s ξ η Samp →
      ∀ β : ℝ, 0 < β → β < 1 → s * γ + ξ ≤ β → ∀ T : ℕ,
        tvdAl T (Drf n γ Samp) (haar n) ≤
          (2 : ℝ) ^ n * η + Real.exp (-((2 : ℝ) ^ n * (1 - β ^ 2) ^ 2 / 2)) +
            C * ((2 : ℝ) ^ n) ^ ((3 : ℝ) / 2) * (2 : ℝ) ^ T * (2 * ξ / β)

end QNatProofs


