-- Prove2me | Definitions.Def_Arxiv2507_15035_Basic
-- name    : Arxiv2507_15035_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T18:33:23.662941+00:00
-- url     : https://prove2.me/theorems/a9b66bb1-e2d0-44d4-afba-e6472f46a4b3
-- title:
--   Helmholtz operator, FWI Lagrangian and point-source adjoint equation
-- statement:
--   Objects of Section III of Zeng et al. (2025), *OpenBreastUS*, for the frequency-domain acoustic model of ultrasound computed tomography.
--
--   1. **Space and sound speed (Section III-A).** Points are $x\in\mathbb{R}^n$. A sound-speed distribution is a measurable function $c:\mathbb{R}^n\to\mathbb{R}$ with $c(x)\ge m$ for some constant $m>0$. Its variation is confined to a bounded region of interest $\mathrm{ROI}$, and outside it $c(x)=c_0$ for a constant $c_0>0$.
--   2. **Helmholtz operator (eqs. (1), (5)).** At angular frequency $\omega$, for a complex field $u:\mathbb{R}^n\to\mathbb{C}$,
--   $$\mathcal S_c u(x)=\nabla^2u(x)+\Big(\frac{\omega}{c(x)}\Big)^2u(x).$$
--   3. **Pairing (p. 4).** $\langle f,g\rangle=\operatorname{Re}\int_{\mathbb{R}^n}\overline{f(x)}\,g(x)\,dx$ is the real part of the $L^2$ inner product.
--   4. **Misfit (eq. (3)).** For transducer locations $x_f^{(1)},\dots,x_f^{(M)}$ and measurements $y\in\mathbb{C}^M$, the misfit is $\|y-u(x_f)\|_2^2=\sum_{i=1}^M|y^{(i)}-u(x_f^{(i)})|^2$.
--   5. **Lagrangian (eq. (4)).** For a source $s$ and a multiplier $\lambda$, one term of the Lagrangian is
--   $$\mathcal L(c,u,\lambda)=\|y-u(x_f)\|_2^2-\langle\lambda,\mathcal S_cu+s\rangle.$$
--   The paper's full Lagrangian is the sum of these terms over frequencies $\omega_j$ and sources $s_k$.
--   6. **Test functions.** A test function is a smooth function with compact support. Test functions serve as the directions of variation.
--   7. **Adjoint equation with point sources (eq. (7)).** A function $\lambda$ solves $\mathcal S_c\lambda=\sum_i a_i\,\delta(x_f^{(i)})$ in the sense of distributions if $\lambda$ is locally integrable and, for every complex test function $\varphi$,
--   $$\int\lambda\,\mathcal S_c\varphi\,dx=\sum_{i=1}^M a_i\,\varphi(x_f^{(i)}).$$
--
--   **Formalization Note** The Laplacian is Mathlib's Laplacian on $\mathbb{R}^n$ (the trace of the second derivative). The integrals are Lebesgue integrals over $\mathbb{R}^n$. Statements 1–3 assume that $\overline\lambda\,(\mathcal S_cu+s)$ is integrable, so that the pairing is defined. The goal does not need this hypothesis: there the forward equation makes the integrand vanish almost everywhere. The paper gives no lower bound on $c$; the bound $c\ge m>0$ is added as the physical convention that makes $(\omega/c)^2$ locally bounded.
-- source:
--   Zeng et al., OpenBreastUS: Benchmarking Neural Operators for Wave Imaging Using Breast Ultrasound Computed Tomography, arXiv:2507.15035v1 (2025), Section III-A, eqs. (1)-(3), PDF p. 3; Section III-B, eqs. (4), (5), (7), PDF p. 4

import Mathlib

/-!
Zeng, Zheng, Hu, Dong, Zheng, Liu, Wang, Shi, Zhang, Li and Sun, *OpenBreastUS: Benchmarking
Neural Operators for Wave Imaging Using Breast Ultrasound Computed Tomography*,
arXiv:2507.15035v1 (2025): the Helmholtz forward model of Section III-A (eqs. (1)-(3)) and the
Lagrangian of the full-waveform-inversion problem of Section III-B (eqs. (4)-(5), (7)).
-/

open MeasureTheory

noncomputable section

namespace Arxiv2507_15035

/-- The physical space `ℝⁿ` (Section III-A, eq. (2), which is written in dimension `n`). -/
abbrev Pt (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Section III-A, p. 3: `c` is a sound-speed distribution whose variation is confined to a
bounded region of interest `ROI`, outside of which it equals the constant `c0 > 0`. The sound
speed is measurable and bounded below by a positive constant (the physical convention implicit
in the division by `c(x)` in eq. (1)). -/
def IsSoundSpeed {n : ℕ} (c : Pt n → ℝ) (ROI : Set (Pt n)) (c0 : ℝ) : Prop :=
  Measurable c ∧ (∃ m : ℝ, 0 < m ∧ ∀ x, m ≤ c x) ∧ Bornology.IsBounded ROI ∧ 0 < c0 ∧
    ∀ x, x ∉ ROI → c x = c0

/-- Eq. (5) (and the left side of eq. (1)): the Helmholtz operator
`S_c u = ∇²u + (ω / c(x))² u` at angular frequency `ω`. -/
def helmholtzOp {n : ℕ} (ω : ℝ) (c : Pt n → ℝ) (u : Pt n → ℂ) (x : Pt n) : ℂ :=
  Laplacian.laplacian u x + (((ω / c x) ^ 2 : ℝ) : ℂ) * u x

/-- The pairing `⟨f, g⟩` of eq. (4), "the real part of the inner product of `f` and `g` in
`L²`" (p. 4): `Re ∫ conj(f x) g(x) dx`. -/
def realPairing {n : ℕ} (f g : Pt n → ℂ) : ℝ :=
  (∫ x, (starRingEnd ℂ) (f x) * g x).re

/-- Eq. (3): the data misfit `‖y - u(x_f)‖₂² = ∑ᵢ |yᵢ - u(x_f⁽ⁱ⁾)|²` of a field `u` against the
measurements `y` at the transducer locations `x_f⁽¹⁾, …, x_f⁽ᴹ⁾`. -/
def misfit {n M : ℕ} (xf : Fin M → Pt n) (y : Fin M → ℂ) (u : Pt n → ℂ) : ℝ :=
  ∑ i, ‖y i - u (xf i)‖ ^ 2

/-- Eq. (4): one term `L_k^j = ‖y_k^j - u_k^j(x_f)‖₂² - ⟨λ_k^j, S_c^j u_k^j + s_k⟩` of the
Lagrangian of the FWI problem, for frequency `ω = ω_j`, source `s = s_k`, measurements
`y = y_k^j`, field `u = u_k^j` and multiplier `lam = λ_k^j`. -/
def lagrangianTerm {n M : ℕ} (ω : ℝ) (c : Pt n → ℝ) (s : Pt n → ℂ) (xf : Fin M → Pt n)
    (y : Fin M → ℂ) (u lam : Pt n → ℂ) : ℝ :=
  misfit xf y u - realPairing lam (fun x => helmholtzOp ω c u x + s x)

/-- Test functions (directions of variation in eqs. (6)-(8)): smooth functions with compact
support. -/
def IsTestFn {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (φ : Pt n → F) :
    Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ

/-- Eq. (7), p. 4: `lam` solves `S_c lam = ∑ᵢ aᵢ δ(x_f⁽ⁱ⁾)` in the sense of distributions, with
`δ(x_f⁽ⁱ⁾)` the unit point source (Dirac mass) at the transducer `x_f⁽ⁱ⁾`: `lam` is locally
integrable and `∫ lam · S_c φ = ∑ᵢ aᵢ φ(x_f⁽ⁱ⁾)` for every test function `φ` (`S_c` has real
coefficients and is formally symmetric). -/
def IsWeakPointSourceSol {n M : ℕ} (ω : ℝ) (c : Pt n → ℝ) (lam : Pt n → ℂ)
    (xf : Fin M → Pt n) (a : Fin M → ℂ) : Prop :=
  LocallyIntegrable lam ∧
    ∀ φ : Pt n → ℂ, IsTestFn φ → ∫ x, lam x * helmholtzOp ω c φ x = ∑ i, a i * φ (xf i)

end Arxiv2507_15035


