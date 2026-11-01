-- Prove2me | Definitions.Def_SmoothNestedSim_matern
-- name    : SmoothNestedSim_matern
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:37:25.762909+00:00
-- url     : https://prove2.me/theorems/70367829-b9db-4b47-9ed8-eef7a67f6d99
-- title:
--   Matérn function $\Psi$ of smoothness $\nu$, formula (3)
-- statement:
--   Let $\nu>0$, $\ell>0$ and $d\ge 1$. The **Matérn function** of smoothness $\nu$ and length-scale $\ell$ is
--
--   $$
--   \Psi(\mathbf x) := \frac{1}{\Gamma(\nu)\,2^{\nu-1}}\Bigl(\frac{\sqrt{2\nu}\,\|\mathbf x\|}{\ell}\Bigr)^{\nu} K_\nu\Bigl(\frac{\sqrt{2\nu}\,\|\mathbf x\|}{\ell}\Bigr),\qquad \mathbf x\in\mathbb R^d\setminus\{0\},
--   $$
--
--   and $\Psi(0):=1$. Here $\Gamma$ is the gamma function, $K_\nu$ the modified Bessel function of the second kind of order $\nu$, and $\|\cdot\|$ the Euclidean norm. For $\nu=1/2$ it is $e^{-\|\mathbf x\|/\ell}$ and for $\nu=3/2$ it is $(1+\sqrt3\|\mathbf x\|/\ell)e^{-\sqrt3\|\mathbf x\|/\ell}$.
--
--   The Matérn kernel $k(\mathbf x,\tilde{\mathbf x})=\Psi(\mathbf x-\tilde{\mathbf x})$ is the kernel of the paper's kernel ridge regression; the smoothness $\nu$ controls the smoothness of the functions in its RKHS.
--
--   **Formalization Note** $K_\nu(z)$ for $z>0$ is the real part of the published `RamanujanLostNotebook.PartIV.besselKC` (the integral $\int_0^\infty e^{-z\cosh t}\cosh(\nu t)\,dt$). Formula (3) reads $0\cdot\infty$ at $\mathbf x=0$; the value $\Psi(0)=1$ is its continuous extension, which (EC.6.2) uses.
-- source:
--   Wang, Wang, Zhang, Smooth Nested Simulation: Bridging Cubic and Square Root Convergence Rates in High Dimensions, arXiv:2201.02958v6, §3.1, (3), p.11

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIV_shared_besselKC

namespace SmoothNestedSim

/-- **The Matérn function `Ψ` of smoothness `ν` and length-scale `ℓ`** (Wang, Wang, Zhang,
*Smooth Nested Simulation*, arXiv:2201.02958v6, §3.1, (3), p.11):
`Ψ(x) := 1/(Γ(ν) 2^{ν−1}) · (√(2ν)‖x‖/ℓ)^ν · K_ν(√(2ν)‖x‖/ℓ)` for `x ∈ ℝ^d`, where `ℓ > 0`,
`Γ` is the gamma function and `K_ν` the modified Bessel function of the second kind of order
`ν`. The Matérn kernel is `k(x, x̃) = Ψ(x − x̃)`.

**Formalization Note.** `ℝ^d` is `EuclideanSpace ℝ (Fin d)` with its Euclidean norm. `K_ν(z)`
for `z > 0` is the real part of the published `RamanujanLostNotebook.PartIV.besselKC ν z`
(the integral `∫_0^∞ exp(−z cosh t) cosh(νt) dt`, DLMF 10.32.9). At `x = 0` formula (3) reads
`0 · ∞`; the Matérn function is its continuous extension there, `Ψ(0) := 1` (the closed forms
`exp(−‖x‖/ℓ)` for `ν = 1/2` and `(1 + √3‖x‖/ℓ) exp(−√3‖x‖/ℓ)` for `ν = 3/2` on p.11 give `1`,
and (EC.6.2), p.ec13 uses `Ψ(x − x) = Ψ(0)`). The value is meaningful for `ν > 0` and `ℓ > 0`,
which every statement of the mission assumes. -/
noncomputable def matern (ν ℓ : ℝ) {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  if x = 0 then 1 else
    1 / (Real.Gamma ν * (2 : ℝ) ^ (ν - 1)) * (Real.sqrt (2 * ν) * ‖x‖ / ℓ) ^ ν *
      (RamanujanLostNotebook.PartIV.besselKC (ν : ℂ)
        ((Real.sqrt (2 * ν) * ‖x‖ / ℓ : ℝ) : ℂ)).re

end SmoothNestedSim


