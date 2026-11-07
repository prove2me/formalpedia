-- Prove2me | Definitions.Def_SysBathGibbs_Stationary
-- name    : SysBathGibbs_Stationary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:36:13.397788+00:00
-- url     : https://prove2.me/theorems/75c91996-bfc0-484b-bd52-da11b89e98f9
-- title:
--   The correction kernel $\nu_{T_0}$ and the approximate stationary state $\rho_*$
-- statement:
--   With $\hat\mu_{T_0}(\omega)=e^{i\omega T_0}(1-i\omega T_0)^{-4}$ the Fourier transform of the interaction-time law and $\hat\mu_0=\hat\mu_1$, (7.7) sets
--   $$
--   h(\omega)=\frac{\omega\hat\mu_0(\omega)}{1-\hat\mu_0(2\omega)},\quad h(0)=\frac i{10},\qquad \nu_0(t)=\frac1{2\pi}\int_{\mathbb R}e^{-i\omega t}h(\omega)\,d\omega,\qquad \nu_{T_0}(t)=T_0^{-2}\nu_0(t/T_0).
--   $$
--   Each $B^{\mathrm{Lamb}}_x$ is first replaced by its Gibbs-centered version $B^{\mathrm{Lamb}}_x-\operatorname{Tr}(\rho_\beta B^{\mathrm{Lamb}}_x)\mathbf 1$ (p.55), and with the resulting $H_{\mathrm{Lamb}}$,
--   $$
--   Y_0=-i\int_{-\beta/2}^{\beta/2}H_{\mathrm{Lamb}}(-iu)\,du,\qquad X=-\int_{\mathbb R}\mathcal U(t)(Y_0)\,\nu_{T_0}(t)\,dt,\qquad \rho_*=\rho_\beta+\alpha^2\Gamma(X).
--   $$
--   The matrix $\rho_*$ is the approximate stationary state of Theorem 7.1.
--
--   **Formalization Note** The value $h(0)=i/10$ is set by hand, since the quotient is $0/0$ there. The uncentered $H_{\mathrm{Lamb}}$ of (3.25) would give a different $\rho_*$, of trace different from one.
-- source:
--   Ding, Li, Zhang, Efficient thermalization of one-dimensional noncommuting Hamiltonians via system-bath interactions with Θ(n) ancilla qubits, arXiv:2611.03422 (held file sha256 a60a3c09826df3b5399a5589f83ef3a1d2ea768d74c5e39e8a3b29d1323f024f), §7.1 eqs. (1.6), (7.1), (7.4), (7.7), (7.8), pp.54–56

import Definitions.Def_SysBathGibbs_Generator

open Matrix MeasureTheory

namespace SysBathGibbs

/-!
# The approximate stationary state

Ding, Li, Zhang, arXiv:2611.03422 (held file sha256 a60a3c09…), §7.1, (1.6), (7.1), (7.4), (7.7),
(7.8), pp.54–56.

**Formalization Note.** The state `ρ∗` is built from the Gibbs-centered `B^Lamb_x`, as prescribed on
p.55. The uncentered `H_Lamb` of (3.25) is a different matrix and does not give `Tr ρ∗ = 1`. The
multiplier `h` has its value at `ω = 0` set by hand to its continuous extension `i/10`, (7.7),
since the quotient is `0/0` there.
-/

variable {n q : ℕ}

/-- The Fourier transform of the time law, `μ̂_{T₀}(ω) = e^{iωT₀}(1 - iωT₀)^{-4}`, (1.6). -/
noncomputable def muHat (T₀ w : ℝ) : ℂ :=
  Complex.exp (Complex.I * w * T₀) * ((1 - Complex.I * w * T₀) ^ 4)⁻¹

/-- `h(ω) = ω μ̂₀(ω) / (1 - μ̂₀(2ω))`, `h(0) = i/10`, (7.7), with `μ̂₀ = μ̂₁`. -/
noncomputable def hKernel (w : ℝ) : ℂ :=
  if w = 0 then Complex.I / 10 else (w : ℂ) * muHat 1 w / (1 - muHat 1 (2 * w))

/-- `ν₀(t) = (1/2π) ∫ e^{-iωt} h(ω) dω`, (7.7). -/
noncomputable def nu0 (t : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ w : ℝ, Complex.exp (-(Complex.I * w * t)) * hKernel w

/-- `ν_{T₀}(t) = T₀^{-2} ν₀(t/T₀)`, (7.7). -/
noncomputable def nuT (T₀ t : ℝ) : ℂ := ((T₀ ^ 2)⁻¹ : ℝ) * nu0 (t / T₀)

/-- The Gibbs-centered Lamb shift `∑_x (B^Lamb_x - Tr(ρ_β B^Lamb_x) 1)`, p.55. -/
noncomputable def HLambCentered (β : ℝ) (h : Fin (n - 1) → SysMat n q) : SysMat n q :=
  ∑ x, (siteLamb β h x -
    Matrix.trace (gibbs β (chainHam h) * siteLamb β h x) • (1 : SysMat n q))

/-- `Y₀ = -i ∫_{-β/2}^{β/2} H_Lamb(-iu) du`, (7.4), with the centered `H_Lamb`. -/
noncomputable def Y0 (β : ℝ) (h : Fin (n - 1) → SysMat n q) : SysMat n q :=
  (-Complex.I) •
    matInt (volume.restrict (Set.Icc (-(β / 2)) (β / 2))) fun u =>
      evo (chainHam h) (-(Complex.I * u)) (HLambCentered β h)

/-- `X = -∫ U(t)(Y₀) ν_{T₀}(t) dt`, (7.8). -/
noncomputable def Xcorr (β : ℝ) (h : Fin (n - 1) → SysMat n q) (T₀ : ℝ) : SysMat n q :=
  -matInt volume fun t => nuT T₀ t • fwd (chainHam h) t (Y0 β h)

/-- `ρ∗ = ρ_β + α² ξ`, `ξ = Γ(X)`, (7.8). -/
noncomputable def rhoStar (β : ℝ) (h : Fin (n - 1) → SysMat n q) (α T₀ : ℝ) : SysMat n q :=
  gibbs β (chainHam h) + ((α ^ 2 : ℝ) : ℂ) • Gam β (chainHam h) 1 (Xcorr β h T₀)

end SysBathGibbs


