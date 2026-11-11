-- Prove2me | Definitions.Def_QuadSDE_Frame
-- name    : QuadSDE_Frame
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:19.771554+00:00
-- url     : https://prove2.me/theorems/5f3b8a89-25ad-4a38-9ab9-c48423c8a117
-- title:
--   Expanding frame $\rho(t)=p+qt$, $\lambda(t)$, and the constants $R_0$, $R_*$, $\lambda_*$, $\theta$, $S(n)$
-- statement:
--   For noise rates $p,q$ and a final time $T$, the **expanding frame** of §4.1 uses
--   $$\rho(t)=p+qt,\qquad \lambda(t)=\frac{q}{2\rho(t)},\qquad y=\frac{Y}{\sqrt p}\qquad(27).$$
--   The analysis uses the constants
--   $$R_0=\sqrt{e^{\|y\|^2}-1}\ (30),\qquad \lambda_*=\frac{q}{2\rho(T)},\qquad R_*=\sqrt{e^{2\|y\|^2}-1}\ (37),$$
--   $$\theta=\min\Big\{\frac{\log2}4,\ \operatorname{arsinh}\Big(\frac{\lambda_*}{4J\sqrt{r\rho(T)}}\Big)\Big\},\qquad S(n)=2\theta(\sqrt n-1)\ (38),$$
--   and the projection-error bound of Theorem 3,
--   $$R_*\Big[1+\frac{J\sqrt{r\rho(T)}}{\lambda_*}\Big(1+\frac1{e\theta}\Big)\Big]e^{-\theta(\sqrt{k+1}-1)}\qquad(45).$$
--
--   **Formalization Note** These are plain real-valued definitions; they are used only under the paper's hypotheses $0<p$, $0<q$, $T\ge0$, $J>0$, $r\ge1$, where no denominator vanishes.
-- source:
--   Bravyi, Byrne, Zayats, Zhuk, Zlokapa, Quantum algorithms for stochastic nonlinear differential equations, arXiv:2606.08349 (sha256 29bd9b01…94cdf), §4.1 Eq. (27) p. 17; Eq. (30) p. 18; §4.3 Eqs. (37)–(38) p. 21; Eq. (45) p. 22

import Mathlib

noncomputable section

namespace QuadSDE

/-- Bravyi–Byrne–Zayats–Zhuk–Zlokapa, arXiv:2606.08349 (sha256 29bd9b01…), §4.1, Eq. (27), p. 17:
the expanding-frame scale `ρ(t) = p + q t`. -/
def rho (p q t : ℝ) : ℝ := p + q * t

/-- Eq. (27), p. 17: the damping rate `λ(t) = q / (2ρ(t))`. -/
def lam (p q t : ℝ) : ℝ := q / (2 * rho p q t)

/-- Eq. (27), p. 17: the rescaled noise-free initial condition `y = Y/√p`. -/
def yvec {N : ℕ} (p : ℝ) (Y : Fin N → ℝ) : Fin N → ℝ := fun i => Y i / Real.sqrt p

/-- The squared Euclidean norm `‖y‖² = Σ_i y_i²`. -/
def normSq {N : ℕ} (y : Fin N → ℝ) : ℝ := ∑ i, y i ^ 2

/-- Eq. (30), p. 18: `R₀ = (e^{‖y‖²} − 1)^{1/2}`, with `y = Y/√p`. -/
def R0 {N : ℕ} (p : ℝ) (Y : Fin N → ℝ) : ℝ := Real.sqrt (Real.exp (normSq (yvec p Y)) - 1)

/-- Eq. (37), p. 21: `λ_* = q / (2ρ(T))`. -/
def lamStar (p q T : ℝ) : ℝ := q / (2 * rho p q T)

/-- Eq. (37), p. 21: `R_* = (e^{2‖y‖²} − 1)^{1/2}`, with `y = Y/√p`. -/
def Rstar {N : ℕ} (p : ℝ) (Y : Fin N → ℝ) : ℝ :=
  Real.sqrt (Real.exp (2 * normSq (yvec p Y)) - 1)

/-- Eq. (38), p. 21: `θ = min{log 2 / 4, arsinh(λ_* / (4 J (r ρ(T))^{1/2}))}`. -/
def theta (J : ℝ) (r : ℕ) (p q T : ℝ) : ℝ :=
  min (Real.log 2 / 4) (Real.arsinh (lamStar p q T / (4 * J * Real.sqrt (r * rho p q T))))

/-- Eq. (38), p. 21: the weight exponent `S(n) = 2θ(√n − 1)` (used for `n ≥ 1`). -/
def Sexp (θ : ℝ) (n : ℕ) : ℝ := 2 * θ * (Real.sqrt n - 1)

/-- Theorem 3, Eq. (45), p. 22: the projection-error bound
`R_* [1 + (J (r ρ(T))^{1/2} / λ_*)(1 + 1/(eθ))] e^{−θ(√(k+1) − 1)}`. -/
def projErrBound {N : ℕ} (J : ℝ) (r : ℕ) (p q T : ℝ) (Y : Fin N → ℝ) (k : ℕ) : ℝ :=
  Rstar p Y *
    (1 + J * Real.sqrt (r * rho p q T) / lamStar p q T *
      (1 + 1 / (Real.exp 1 * theta J r p q T))) *
    Real.exp (-(theta J r p q T * (Real.sqrt (k + 1) - 1)))

end QuadSDE


