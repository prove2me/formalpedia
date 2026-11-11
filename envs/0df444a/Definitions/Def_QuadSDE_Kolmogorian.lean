-- Prove2me | Definitions.Def_QuadSDE_Kolmogorian
-- name    : QuadSDE_Kolmogorian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:16:07.727147+00:00
-- url     : https://prove2.me/theorems/52675c98-2cfb-436a-9b7a-6face681dd8f
-- title:
--   Kolmogorian $K(t)$, projected evolution (36), initial vector (34) and the weighted norms (39), (47)
-- statement:
--   The **Kolmogorian** is
--   $$K(t)=-\lambda(t)M+\sqrt{\rho(t)}\,C_0\qquad(32),$$
--   and the **projected Kolmogorian** is $K_k(t)=\Pi_kK(t)\Pi_k$ (35). The initial vector is
--   $$|\psi(0)\rangle=\sum_{\mathbf m\ne0}\frac{y^{\mathbf m}}{\sqrt{\mathbf m!}}|\mathbf m\rangle\in\mathcal F_0\qquad(34),$$
--   with $y=Y/\sqrt p$, $y^{\mathbf m}=\prod_iy_i^{m_i}$ and $\mathbf m!=\prod_im_i!$. A **projected solution** with cutoff $k$ on $[0,T]$ is a function $\psi_k$ with values in $\mathcal H_k$ such that
--   $$\psi_k'(t)=K_k(t)\psi_k(t),\qquad\psi_k(0)=\Pi_k\psi(0)\qquad(36).$$
--   The **weighted norm** is $\|v\|_S^2=\sum_{n\ge1}e^{2S(n)}\|Q_nv\|^2$ (39), and Theorem 3's uniqueness class uses $\sum_{n\ge1}(n+1)^3\|Q_nv\|^2$ (47).
--
--   **Formalization Note** Projected solutions take values in the Fock space $\ell^2$, with derivatives in the $\ell^2$ norm (one-sided at $0$ and $T$); every solution is covered, not only "the unique" one. The weighted sums are in $[0,\infty]$, so a divergent sum is $\infty$, never $0$.
-- source:
--   Bravyi, Byrne, Zayats, Zhuk, Zlokapa, Quantum algorithms for stochastic nonlinear differential equations, arXiv:2606.08349 (sha256 29bd9b01…94cdf), §4.2 Eqs. (32), (34)–(36), pp. 19–20; §4.3 Eq. (39), p. 21; Eq. (47), p. 22

import Mathlib
import Definitions.Def_QuadSDE_DriftClass
import Definitions.Def_QuadSDE_Frame
import Definitions.Def_QuadSDE_Fock

open scoped ENNReal

noncomputable section

namespace QuadSDE

/-- Bravyi–Byrne–Zayats–Zhuk–Zlokapa, arXiv:2606.08349 (sha256 29bd9b01…), Eq. (32), p. 19: the
Kolmogorian `K(t) = −A(t) + C(t)`, `A(t) = λ(t) M`, `C(t) = √ρ(t) C₀`, with `ρ(t) = p + qt`,
`λ(t) = q/(2ρ(t))`, acting coefficientwise. -/
def Kop {N : ℕ} (c : Coeff N) (p q t : ℝ) (v : MIdx N → ℂ) : MIdx N → ℂ :=
  fun m => -((lam p q t : ℝ) : ℂ) * numOp v m + ((Real.sqrt (rho p q t) : ℝ) : ℂ) * C0 c v m

/-- Eq. (35), p. 20: the projected Kolmogorian `K_k(t) = Π_k K(t) Π_k`. -/
def Kk {N : ℕ} (c : Coeff N) (p q : ℝ) (k : ℕ) (t : ℝ) (v : MIdx N → ℂ) : MIdx N → ℂ :=
  Pik k (Kop c p q t (Pik k v))

/-- Eq. (34), p. 20: the initial vector `|ψ(0)⟩ = Σ_{m ≠ 0} y^m/√m! |m⟩` in `𝓕₀`, with
`y = Y/√p`, `y^m = Π_i y_i^{m_i}` and `m! = Π_i m_i!`; its vacuum coefficient is `0`. -/
def psi0 {N : ℕ} (p : ℝ) (Y : Fin N → ℝ) : MIdx N → ℂ :=
  fun m => if m = 0 then 0 else
    (((∏ i, yvec p Y i ^ m i) / Real.sqrt (∏ i, ((m i).factorial : ℝ)) : ℝ) : ℂ)

/-- Eq. (36), p. 20: `ψ_k` is a solution of the projected evolution on `[0, T]`:
`ψ_k(t) ∈ 𝓗_k` for all `t`, `ψ_k(0) = Π_k ψ(0)`, and `ψ_k′(t) = K_k(t) ψ_k(t)` for `t ∈ [0, T]`
(one-sided derivatives at the endpoints).

**Formalization Note.** `ψ_k` takes values in the Fock space `ℓ²`; the derivative is taken in the
`ℓ²` norm, which on the finite-dimensional `𝓗_k` is the usual derivative. Every such solution is
covered; the paper's "It has a unique solution" is not assumed. -/
def IsProjSol {N : ℕ} (c : Coeff N) (p q : ℝ) (Y : Fin N → ℝ) (T : ℝ) (k : ℕ)
    (ψk : ℝ → Fock N) : Prop :=
  (∀ t (m : MIdx N), ¬ (1 ≤ mdeg m ∧ mdeg m ≤ k) → ψk t m = 0) ∧
  (⇑(ψk 0) = Pik k (psi0 p Y)) ∧
  ∀ t ∈ Set.Icc (0 : ℝ) T, ∃ w : Fock N,
    ⇑w = Kk c p q k t ⇑(ψk t) ∧ HasDerivWithinAt ψk w (Set.Icc 0 T) t

/-- Eq. (39), p. 21: the weighted norm `‖v‖_S² = Σ_{n ≥ 1} e^{2S(n)} ‖Q_n v‖²`, `S(n) = 2θ(√n − 1)`.

**Formalization Note.** Summed in `ℝ≥0∞`, so that a divergent sum is `∞` and never `0`. -/
def wNormSq {N : ℕ} (θ : ℝ) (v : MIdx N → ℂ) : ℝ≥0∞ :=
  ∑' n : ℕ, if 1 ≤ n then ENNReal.ofReal (Real.exp (2 * Sexp θ n) * degNormSq n v) else 0

/-- Eq. (47), p. 22: the cubic-weighted norm `Σ_{n ≥ 1} (n + 1)³ ‖Q_n v‖²` of Theorem 3's
uniqueness class, summed in `ℝ≥0∞`. -/
def cubicNormSq {N : ℕ} (v : MIdx N → ℂ) : ℝ≥0∞ :=
  ∑' n : ℕ, if 1 ≤ n then ENNReal.ofReal (((n : ℝ) + 1) ^ 3 * degNormSq n v) else 0

end QuadSDE


