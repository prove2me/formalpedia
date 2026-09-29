-- Prove2me | Definitions.Def_AKR2008_HybridDefs
-- name    : AKR2008_HybridDefs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-27T22:23:55.507977+00:00
-- url     : https://prove2.me/theorems/521c48ab-8e15-483a-ae02-635a487b4545
-- title:
--   Albers–Kiefer–Reginatto (2008) Sec. IV A / App. A: mode kernels and oscillator ensemble
-- statement:
--   Mode coefficients of the non-interacting solution of the two-dimensional hybrid Nordström model (Sec. IV A) and the classical oscillator ensemble (Appendix A) of Albers, Kiefer and Reginatto (2008).
--
--   Throughout, kernels of Sec. IV A are written in the real orthonormal eigenbasis $f^{(k)}$ of $-\partial_x^2$ (eigenvalue $k^2$): a kernel $A_{xy}=\sum_k A_k f^{(k)}_x f^{(k)}_y$ is represented by its mode coefficient $A_k$, so $\int dx\,A_{yx}B_{xz}\mapsto A_kB_k$, $\partial_z^2\delta(y-z)\mapsto -k^2$ and $\int dx\,A_{xx}\mapsto\sum_k A_k$. With this convention the file defines:
--
--   1. $F_k(t) = -k\tan(kt)$ — Eq. (49);
--   2. $G_k = \sqrt{k^2+m^2}$ — Eq. (50);
--   3. $K_k(t) = \dfrac{\tau_k}{\cos^2(kt)}$ with an arbitrary constant $\tau_k$ — Eq. (51);
--   4. $\beta_k(t) = w_k\cos(kt)$ with an arbitrary constant $w_k$ — Eq. (54);
--   5. $N^c(t) = \dfrac{1}{\prod_k \cos(kt)}$ for a finite family of modes — Eq. (55);
--   6. $S_{\mathrm{osc}}(x,t) = -\dfrac{\omega x^2}{2}\tan(\omega t)$ — Appendix A;
--   7. the Gaussian ensemble
--   $$P_{\mathrm{osc}}(x,t)=\sqrt{\frac{\tau}{2\pi\cos^2(\omega t)}}\,\exp\Bigl\{-\frac12\,\frac{\tau}{\cos^2(\omega t)}\,\bigl(x-w\cos(\omega t)\bigr)^2\Bigr\}$$ — Appendix A.
--
--   These are the objects every statement of the mission is phrased in.
--
--   **Formalization Note** All quantities are real-valued functions of real arguments. Lean's `Real.tan` and division return junk values ($0$) where $\cos=0$; every theorem that uses them assumes $\cos\neq0$ at the relevant time. The product in $N^c$ runs over a finite index type (a truncation of the paper's infinite product, which is only formal in the paper).
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), https://doi.org/10.1103/PhysRevD.78.064051, Sec. IV A (Eqs. (49)–(55)) and Appendix A

import Mathlib

/-!
# Albers–Kiefer–Reginatto (2008), Sec. IV A and Appendix A: mode kernels of the
non-interacting hybrid Nordström model and the classical oscillator ensemble.

Sec. IV A expands every kernel in real orthonormal eigenfunctions `f⁽ᵏ⁾` of `-∂ₓ²`
(eigenvalue `k²`).  In this basis a kernel `A_{xy} = ∑ₖ Aₖ f⁽ᵏ⁾ₓ f⁽ᵏ⁾_y` is recorded by its
mode coefficient `Aₖ`, products `∫ dx A_{yx} B_{xz}` become `Aₖ Bₖ`, `∂_z² δ(y - z)` becomes `-k²`,
and a trace `∫ dx A_{xx}` becomes `∑ₖ Aₖ`.  The definitions below are the mode coefficients of
Eqs. (49)–(51), (54) and the normalization (55).
-/

namespace AKR2008

/-- Eq. (49), mode coefficient of `F_{xy}`: `Fₖ(t) = -k tan(k t)`. -/
noncomputable def hybridModeF (k t : ℝ) : ℝ :=
  -k * Real.tan (k * t)

/-- Eq. (50), mode coefficient of `G_{xy}`: `Gₖ = √(k² + m²)`. -/
noncomputable def hybridModeG (m k : ℝ) : ℝ :=
  Real.sqrt (k ^ 2 + m ^ 2)

/-- Eq. (51), mode coefficient of `K_{yx}` with arbitrary constant `τₖ`:
`Kₖ(t) = τₖ / cos²(k t)`. -/
noncomputable def hybridModeK (τk k t : ℝ) : ℝ :=
  τk / Real.cos (k * t) ^ 2

/-- Eq. (54), mode coefficient of `β_x` with arbitrary constant `wₖ`: `βₖ(t) = wₖ cos(k t)`. -/
noncomputable def hybridModeBeta (wk k t : ℝ) : ℝ :=
  wk * Real.cos (k * t)

/-- Eq. (55), the normalization `N^c(t) = 1 / ∏ₖ cos(k t)` for a finite family of modes
`k : ι → ℝ`. -/
noncomputable def hybridNc {ι : Type*} [Fintype ι] (k : ι → ℝ) (t : ℝ) : ℝ :=
  1 / ∏ i, Real.cos (k i * t)

/-- Appendix A: Hamilton–Jacobi function of the classical oscillator ensemble,
`S_osc(x, t) = -(ω x² / 2) tan(ω t)`. -/
noncomputable def oscS (ω x t : ℝ) : ℝ :=
  -(ω * x ^ 2 / 2) * Real.tan (ω * t)

/-- Appendix A: the Gaussian probability density
`P_osc(x, t) = √(τ / (2π cos²(ω t))) · exp(-(1/2) (τ / cos²(ω t)) (x - w cos(ω t))²)`. -/
noncomputable def oscP (ω τ w x t : ℝ) : ℝ :=
  Real.sqrt (τ / (2 * Real.pi * Real.cos (ω * t) ^ 2)) *
    Real.exp (-(1 / 2) * (τ / Real.cos (ω * t) ^ 2) * (x - w * Real.cos (ω * t)) ^ 2)

end AKR2008


