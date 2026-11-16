-- Prove2me | Definitions.Def_QuadSDE_Supplement_Kolmogorov
-- name    : QuadSDE_Supplement_Kolmogorov
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:11:56.293453+00:00
-- url     : https://prove2.me/theorems/52f74fdf-0abf-4d11-9934-de6a758689ea
-- title:
--   Hermite series $\sum_m a_mH_m$, Laplacian, $\nabla\cdot(xu)$ and the right-hand side of the Kolmogorov equation (54)
-- statement:
--   Let $\psi$ be a vector of the bosonic Fock space, indexed by multi-indices $\mathbf m\in\mathbb Z_{\ge0}^N$. Its **real coefficient sequence** is $a_{\mathbf m}=\operatorname{Re}\psi_{\mathbf m}$ for $\mathbf m\neq0$ and $a_0=0$. For a real sequence $a$, the **Hermite sum** is
--   $$\sum_{\mathbf m}a_{\mathbf m}H_{\mathbf m}(x),\qquad x\in\mathbb R^N,$$
--   with $H_{\mathbf m}$ the normalized multivariate Hermite polynomials; it is the series of Eq. (52).
--
--   For a function $u:\mathbb R^N\to\mathbb R$ the **Laplacian** is $\Delta u=\sum_i\partial^2u/\partial x_i^2$ and $\nabla\cdot(xu)=\sum_i\partial(x_iu)/\partial x_i$. With $\rho(t)=p+qt$, $\lambda(t)=q/(2\rho(t))$ and the quadratic drift $f_i(x)=\sum_{j,k}c_{ijk}x_jx_k$, the **right-hand side of the Kolmogorov forward equation** (54) is
--   $$\lambda(t)\big[\Delta u+\nabla\cdot(xu)\big]-\sqrt{\rho(t)}\,f\cdot\nabla u .$$
--
--   These objects state Theorem 4: the series (52) is the density of the rescaled process and solves this equation.
--
--   **Formalization Note** The Hermite sum is an unconditional sum (`tsum`) over all multi-indices; Theorem 4 states separately that its partial sums converge, so the junk value of a divergent sum never enters. Real parts are taken because Lemma 7 identifies $\psi_{\mathbf m}(t)$ with a real Hermite coefficient. Second derivatives are iterated Fréchet derivatives applied to $(e_i,e_i)$; $f\cdot\nabla u(x)$ is the Fréchet derivative of $u$ at $x$ applied to $f(x)$.
-- source:
--   Bravyi, Byrne, Zayats, Zhuk, Zlokapa, Quantum algorithms for stochastic nonlinear differential equations, arXiv:2606.08349 (sha256 29bd9b01…94cdf), §4.4, Eq. (52) p. 24; Theorem 4, Eq. (54) p. 25

import Mathlib
import Definitions.Def_QuadSDE_DriftClass
import Definitions.Def_QuadSDE_Frame
import Definitions.Def_QuadSDE_GaussHermite
import Definitions.Def_QuadSDE_Fock

noncomputable section

namespace QuadSDE.Supplement

/-- Bravyi, Byrne, Zayats, Zhuk, Zlokapa, *Quantum algorithms for stochastic nonlinear differential
equations*, arXiv:2606.08349 (sha256 29bd9b01…), §4.4, Eq. (52), p. 24: the real coefficient
sequence `m ↦ ψ_m` of a Fock vector `ψ` used in the Hermite series `Σ_{m ≠ 0} ψ_m H_m`; the vacuum
coefficient (`m = 0`) is excluded.

**Formalization Note.** The Fock space is complex; Lemma 7 (p. 24) identifies `ψ_m(t)` with the real
Hermite coefficient `⟨H_m, h_t⟩_µ`, so the real part is taken, exactly as the published
`QuadSDE.lemma_7` does. -/
def coeffRe {N : ℕ} (v : Fock N) (m : MIdx N) : ℝ :=
  if m = 0 then 0 else (v m).re

/-- Eq. (52), p. 24: the Hermite sum `Σ_m a_m H_m(x)` of a real coefficient sequence `a`, as an
unconditional sum over all multi-indices.

**Formalization Note.** A `tsum`; it is used only together with explicit statements that the
partial sums over finite sets of multi-indices converge, so its junk value `0` on a non-summable
family never enters. For a finitely supported `a` (a projected solution `ψ_k`) it is a finite sum. -/
def hermiteSum {N : ℕ} (a : MIdx N → ℝ) (x : Fin N → ℝ) : ℝ :=
  ∑' m : MIdx N, a m * hermiteMulti m x

/-- The Laplacian `Δu(x) = Σ_i ∂²u/∂x_i²(x)` of a function `u : ℝ^N → ℝ`, written with the second
iterated Fréchet derivative applied to the pair `(e_i, e_i)` of unit vectors. -/
def laplacian {N : ℕ} (u : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, iteratedFDeriv ℝ 2 u x (fun _ => Pi.single i 1)

/-- The divergence `∇ · (x u)(x) = Σ_i ∂(x_i u(x))/∂x_i` of the vector field `x ↦ x u(x)`. -/
def divXTimes {N : ℕ} (u : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, fderiv ℝ (fun z : Fin N → ℝ => z i * u z) x (Pi.single i 1)

/-- Theorem 4, Eq. (54), p. 25: the right-hand side of the Kolmogorov forward equation of the
rescaled process,
`λ(t) [Δu + ∇ · (x u)] − √ρ(t) f · ∇u`,
with `ρ(t) = p + qt`, `λ(t) = q/(2ρ(t))` and `f` the quadratic drift with coefficients `c`. The
directional term `f · ∇u (x) = Σ_i f_i(x) ∂u/∂x_i (x)` is the Fréchet derivative of `u` at `x`
applied to the vector `f(x)`. -/
def kolmogorovRHS {N : ℕ} (c : Coeff N) (p q t : ℝ) (u : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) : ℝ :=
  lam p q t * (laplacian u x + divXTimes u x) - Real.sqrt (rho p q t) * fderiv ℝ u x (drift c x)

end QuadSDE.Supplement


