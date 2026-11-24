-- Prove2me | Definitions.Def_Arxiv1801_00461_Basic
-- name    : Arxiv1801_00461_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T04:06:52.890174+00:00
-- url     : https://prove2.me/theorems/02703c64-ff46-46b4-a6c9-f426e0e642ba
-- title:
--   Causal Fourier transforms, Hilbert transform, admittance and apparent parameters (Bédard-Destexhe 2018)
-- statement:
--   Objects of Sections 2 and 3.1 of Bédard and Destexhe (2018). The position $\vec r$ is fixed and omitted; all kernels are real-valued functions of time, and causality (a kernel vanishes for $t<0$) is built in by integrating over $t>0$.
--
--   1. **One-sided Fourier transform.** For a real kernel $g$ and a complex frequency $\omega=\omega'+i\omega''$, $\hat g(\omega)=\int_0^\infty g(\tau)e^{-i\omega\tau}\,d\tau$. The full-line transform of a field is $\hat f(\omega)=\int_{-\infty}^{\infty}f(t)e^{-i\omega t}\,dt$.
--   2. **Permittivity (eqs. (10)-(11)).** With the vacuum permittivity $\varepsilon_o$ and the susceptibility kernel $\chi$ of $\varepsilon(t)=\varepsilon_o[\delta(t)+\chi(t)]$: $\varepsilon(\omega)=\varepsilon_o\big[1+\int_0^\infty\chi(\tau)e^{-i\omega\tau}d\tau\big]$ and $\bar\Delta\varepsilon(\omega)=\int_0^\infty\varepsilon_o\chi(\tau)e^{-i\omega\tau}d\tau$.
--   3. **Conductivity (eqs. (21)-(24)).** The kernel $\sigma_e(t)=\sigma_\infty(t)[1+\bar\Delta_e(t)]$, the free-charge current $j(t)=\int_0^\infty\sigma_e(\tau)E(t-\tau)\,d\tau$, the deviation $\bar\Delta\sigma_e(\omega)=\int_0^\infty d(\tau)e^{-i\omega\tau}d\tau$ of a deviation kernel $d=\sigma_e-\sigma_\infty=\sigma_\infty\bar\Delta_e$, and $\sigma_e(\omega)=\sigma_\infty(\omega)+\bar\Delta\sigma_e(\omega)$ for a given frequency-domain asymptote $\sigma_\infty(\omega)$.
--   4. **Admittance and apparent parameters (eqs. (27)-(28), (35)-(36)).** $\gamma=\sigma_e+i\omega\varepsilon$, $\gamma_\infty=\sigma_\infty(\omega)+i\omega\varepsilon_o$, $\bar\Delta\gamma=\gamma-\gamma_\infty$; $\sigma_A=\operatorname{Re}\gamma$ and $\varepsilon_A=\operatorname{Im}\gamma/\omega$, with high-frequency values $\operatorname{Re}\gamma_\infty$ and $\operatorname{Im}\gamma_\infty/\omega$.
--   5. **Hilbert transform (eq. (16)).** For real $\omega$ and $\delta>0$ let $P_\delta(\omega)=\{\omega_a:\ \delta<|\omega_a-\omega|,\ \delta<|\omega_a|,\ |\omega_a|<1/\delta\}$. The statement $\mathcal H(f)(\omega)=v$ means that for all small $\delta>0$ the function $f(\omega_a)/(\omega_a-\omega)$ is integrable on $P_\delta(\omega)$ and
--   $$\frac1\pi\int_{P_\delta(\omega)}\frac{f(\omega_a)}{\omega_a-\omega}\,d\omega_a\longrightarrow v\qquad(\delta\to0^+).$$
--   $\mathcal H(f)(\omega)$ also denotes this limit as a number.
--   6. **Permittivity models (eqs. (38)-(42), (47), (50), (51)).** $\varepsilon_A(\omega)=\varepsilon_o+\kappa/|\omega|^{2+x}$ and $\varepsilon_A(\omega)=\varepsilon_o+\sum_{j=1}^N\kappa_j/|\omega|^{2+x_j}$; $\bar\Delta(\omega\varepsilon_A)=\omega(\varepsilon_A-\varepsilon_o)$; the truncated integral $\int_\delta^{1-\delta}+\int_{1+\delta}^{1/\delta}\frac{dy}{(y^2-1)y^x}$ of eq. (42); $\kappa_1=\frac{2\kappa}{\pi}\lim_{\delta\to0^+}$ of that integral (eq. (40)); $\bar\Delta\sigma_A=-\mathcal H(\bar\Delta(\omega\varepsilon_A))$ (eq. (30b)); $\gamma_A=\sigma_A(\infty)+\bar\Delta\sigma_A+i\omega\varepsilon_A$ and $\gamma_A(\omega=\infty)=\sigma_A(\infty)+i\omega\varepsilon_o$ for a constant $\sigma_A(\infty)$.
--
--   **Formalization Note** The paper's Fig. 1 excises a half-circle of radius $\delta$ about $\omega_a=\omega$ and closes with a half-circle of radius $R=1/\delta$, so the principal value is taken with the coupled truncation $(\delta,1/\delta)$. The extra symmetric excision about $\omega_a=0$ does not change the value for functions that are locally integrable at $0$. For the power-law models it is the excision the paper uses in eq. (42). Limits written $\lim$ in a definition are Lean's `limUnder`, and every statement that uses them also asserts that the limit exists. The asymptote $\sigma_\infty(\omega)$ is a free frequency-domain function, because the paper allows it to be the transform of a distribution, such as the constant $k$ of a resistive medium.
-- source:
--   Bédard and Destexhe, Kramers-Kronig relations and the properties of conductivity and permittivity in heterogeneous media, arXiv:1801.00461v1 (2018), Sec. 2.2 (eqs. (7), (10)-(11), (16)), Sec. 2.3 (eqs. (21)-(26)), Sec. 2.4 (eqs. (27)-(28), (35)-(36)), Sec. 3.1.2 (eqs. (38)-(42), (47), (50), (51)), Fig. 1

import Mathlib

/-!
Bédard and Destexhe, *Kramers-Kronig relations and the properties of conductivity and
permittivity in heterogeneous media*, arXiv:1801.00461v1 (2018): the one-sided Fourier transforms
of the causal permittivity and conductivity kernels (Sec. 2.2-2.3, eqs. (10)-(11), (21)-(25)),
the principal-value Hilbert transform of eqs. (16), (26), (30), the admittance and the apparent
conductivity and permittivity (Sec. 2.4, eqs. (27)-(28), (35)-(36)), and the permittivity models of
Sec. 3.1.2 (eqs. (38)-(40), (42), (47), (50), (51)).

The position `r` is fixed throughout and suppressed. Kernels are real-valued functions of time;
causality (a kernel vanishes for negative time) is built in by integrating over `t > 0` only.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace Arxiv1801_00461

/-- Eqs. (10), (11), (24), (25): the one-sided Fourier transform
`∫_0^∞ g(τ) e^{-iωτ} dτ` of a causal real kernel `g`, at a complex frequency `ω = ω' + iω''`
(real frequencies are the case `ω'' = 0`). -/
def causalFT (g : ℝ → ℝ) (ω : ℂ) : ℂ :=
  ∫ τ in Set.Ioi (0 : ℝ), (g τ : ℂ) * Complex.exp (-(Complex.I * ω * τ))

/-- Sec. 2.3.3, Fourier transform over the whole time axis, `∫_{-∞}^{∞} f(t) e^{-iωt} dt`, used for
the electric field and the free-charge current in eq. (23). -/
def fourierFT (f : ℝ → ℝ) (ω : ℝ) : ℂ :=
  ∫ t, (f t : ℂ) * Complex.exp (-(Complex.I * ω * t))

/-- Eq. (10): the permittivity in frequency space,
`ε(ω) = ε_o [1 + ∫_0^∞ χ(τ) e^{-iωτ} dτ]`, where `χ` is the time-domain susceptibility of
eq. (7), `ε(t) = ε_o [δ(t) + χ(t)]`. -/
def permittivity (eps0 : ℝ) (chi : ℝ → ℝ) (ω : ℂ) : ℂ :=
  eps0 * (1 + causalFT chi ω)

/-- Eq. (11): the deviation of the permittivity from that of vacuum,
`Δ̄ε(ω) = ∫_0^∞ ε_o χ(τ) e^{-iωτ} dτ`. -/
def permDev (eps0 : ℝ) (chi : ℝ → ℝ) (ω : ℂ) : ℂ :=
  causalFT (fun τ => eps0 * chi τ) ω

/-- Eq. (21): the conductivity kernel `σ_e(t) = σ_∞(t) [1 + Δ̄_e(t)]`. -/
def condKernel (sigmaInf DeltaE : ℝ → ℝ) (t : ℝ) : ℝ :=
  sigmaInf t * (1 + DeltaE t)

/-- Eq. (22): the free-charge current of a causal medium,
`j^free(t) = ∫_0^∞ σ_∞(τ) [1 + Δ̄_e(τ)] E(t - τ) dτ` (one Cartesian component). -/
def freeCurrent (sigmaInf DeltaE E : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ τ in Set.Ioi (0 : ℝ), condKernel sigmaInf DeltaE τ * E (t - τ)

/-- Eqs. (24)-(25): the deviation `Δ̄σ_e(ω) = σ_e(ω) - σ_∞(ω)` of the conductivity from its
high-frequency asymptote, the Fourier transform `∫_0^∞ d(τ) e^{-iωτ} dτ` of the time-domain
deviation kernel `d(t) = σ_e(t) - σ_∞(t) = σ_∞(t) Δ̄_e(t)`. -/
def condDev (dsig : ℝ → ℝ) (ω : ℂ) : ℂ :=
  causalFT dsig ω

/-- Eq. (24): the conductivity in frequency space, `σ_e(ω) = σ_∞(ω) + Δ̄σ_e(ω)`. The asymptote
`σ_∞(ω)` is a frequency-domain datum `sigInf`, because the paper allows it to be the transform of
a distribution (for a resistive asymptote, the constant `k` of Sec. 3.1.1). -/
def condFreq (sigInf : ℝ → ℂ) (dsig : ℝ → ℝ) (ω : ℝ) : ℂ :=
  sigInf ω + condDev dsig ω

/-- Eq. (27): the admittance of the medium, `γ(ω) = σ_e(ω) + iω ε(ω)`. -/
def admittance (sigInf : ℝ → ℂ) (dsig : ℝ → ℝ) (eps0 : ℝ) (chi : ℝ → ℝ) (ω : ℝ) : ℂ :=
  condFreq sigInf dsig ω + Complex.I * ω * permittivity eps0 chi ω

/-- Eq. (28): `γ_∞(ω) = σ(∞) + iω ε(∞)`, with `σ(∞) = σ_∞(ω)` and `ε(∞) = ε_o`. -/
def admittanceInf (sigInf : ℝ → ℂ) (eps0 : ℝ) (ω : ℝ) : ℂ :=
  sigInf ω + Complex.I * ω * eps0

/-- Eq. (28): the admittance variation `Δ̄γ = γ(ω) - γ_∞(ω)`. -/
def admDev (sigInf : ℝ → ℂ) (dsig : ℝ → ℝ) (eps0 : ℝ) (chi : ℝ → ℝ) (ω : ℝ) : ℂ :=
  admittance sigInf dsig eps0 chi ω - admittanceInf sigInf eps0 ω

/-- Eq. (35): the apparent conductivity `σ_A = γ' = σ_e' - ω ε''`. -/
def appCond (sigInf : ℝ → ℂ) (dsig : ℝ → ℝ) (eps0 : ℝ) (chi : ℝ → ℝ) (ω : ℝ) : ℝ :=
  (admittance sigInf dsig eps0 chi ω).re

/-- Eq. (36): the apparent permittivity, `ω ε_A = γ'' = ω ε' + σ_e''`, i.e. `ε_A = γ''/ω`
(`ω ≠ 0`). -/
def appPerm (sigInf : ℝ → ℂ) (dsig : ℝ → ℝ) (eps0 : ℝ) (chi : ℝ → ℝ) (ω : ℝ) : ℝ :=
  (admittance sigInf dsig eps0 chi ω).im / ω

/-- Eqs. (28), (35): the high-frequency value of the apparent conductivity, `Re γ_∞(ω)`. -/
def appCondInf (sigInf : ℝ → ℂ) (eps0 : ℝ) (ω : ℝ) : ℝ :=
  (admittanceInf sigInf eps0 ω).re

/-- Eqs. (28), (36): the high-frequency value of the apparent permittivity, `Im γ_∞(ω) / ω`. -/
def appPermInf (sigInf : ℝ → ℂ) (eps0 : ℝ) (ω : ℝ) : ℝ :=
  (admittanceInf sigInf eps0 ω).im / ω

/-- Fig. 1 and eqs. (15)-(16): the integration set of the principal value at the singular point
`ω_a = ω`, for the half-circles of radius `δ` about `ω` and `R = 1/δ` about the origin:
`{ω_a : δ < |ω_a - ω|, δ < |ω_a|, |ω_a| < 1/δ}`. The point `ω_a = 0` is also excised
symmetrically, as in eq. (42). -/
def pvRegion (ω δ : ℝ) : Set ℝ :=
  {a | δ < |a - ω| ∧ δ < |a| ∧ |a| < 1 / δ}

/-- Eq. (16): the truncated Hilbert transform
`(1/π) ∫_{pvRegion ω δ} f(ω_a) / (ω_a - ω) dω_a`. -/
def hilbertTrunc (f : ℝ → ℝ) (ω δ : ℝ) : ℝ :=
  1 / Real.pi * ∫ a in pvRegion ω δ, f a / (a - ω)

/-- Eq. (16): `H(f)(ω) = v`, i.e. the principal value
`(1/π) ⨍_{-∞}^{∞} f(ω_a) / (ω_a - ω) dω_a` exists and equals `v`: the truncated integrals are
(eventually) Lebesgue integrals and tend to `v` as `δ → 0⁺`. -/
def HasHilbert (f : ℝ → ℝ) (ω v : ℝ) : Prop :=
  (∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      IntegrableOn (fun a => f a / (a - ω)) (pvRegion ω δ)) ∧
    Tendsto (hilbertTrunc f ω) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds v)

/-- Eq. (16): the Hilbert transform `H(f)(ω)` as a number, the limit of the truncations as
`δ → 0⁺`. It is meaningful where `HasHilbert f ω v` holds for some `v`. -/
def hilbert (f : ℝ → ℝ) (ω : ℝ) : ℝ :=
  limUnder (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (hilbertTrunc f ω)

/-- Eq. (38): the apparent-permittivity model `ε_A(ω) = ε_o + κ / |ω|^{2+x}`. -/
def epsModel (eps0 kappa x : ℝ) (ω : ℝ) : ℝ :=
  eps0 + kappa / |ω| ^ (2 + x)

/-- Sec. 3.1.2: `Δ̄(ω ε_A)(ω) = ω (ε_A(ω) - ε_o)` for the model (38), the deviation of `ω ε_A` from
its value `ω ε_o` at infinite frequency. -/
def omegaEpsDev (eps0 kappa x : ℝ) (ω : ℝ) : ℝ :=
  ω * (epsModel eps0 kappa x ω - eps0)

/-- Eq. (42): the truncated principal-value integral (the bracket of eq. (42))
`∫_δ^{1-δ} dy / ((y²-1) y^x) + ∫_{1+δ}^{1/δ} dy / ((y²-1) y^x)`. -/
def kernelTrunc (x δ : ℝ) : ℝ :=
  (∫ y in δ..(1 - δ), 1 / ((y ^ 2 - 1) * y ^ x)) +
    ∫ y in (1 + δ)..(1 / δ), 1 / ((y ^ 2 - 1) * y ^ x)

/-- Eqs. (40), (42): `κ_1 = (2κ/π) ⨍_0^∞ dy / ((y²-1) y^x)`, the principal value being the limit
of `kernelTrunc x δ` as `δ → 0⁺`. -/
def kappaOne (kappa x : ℝ) : ℝ :=
  2 * kappa / Real.pi * limUnder (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (kernelTrunc x)

/-- Eq. (30b) applied to the model (38), as in eq. (39):
`Δ̄σ_A(ω) = -H(Δ̄(ω ε_A))(ω)`. -/
def appCondDevModel (eps0 kappa x : ℝ) (ω : ℝ) : ℝ :=
  -hilbert (omegaEpsDev eps0 kappa x) ω

/-- Eqs. (47), (50): the apparent admittance of the model (38),
`γ_A(ω) = σ_A(ω) + iω ε_A(ω)` with `σ_A(ω) = σ_A(∞) + Δ̄σ_A(ω)`, where `s = σ_A(∞)`. -/
def appAdmModel (s eps0 kappa x : ℝ) (ω : ℝ) : ℂ :=
  ((s + appCondDevModel eps0 kappa x ω : ℝ) : ℂ) + Complex.I * ω * epsModel eps0 kappa x ω

/-- Eqs. (47), (50): `γ_A(ω = ∞) = σ_A(∞) + iω ε_o`, the apparent admittance with the
high-frequency values of the apparent parameters (`s = σ_A(∞)`, `ε_A(∞) = ε_o`). -/
def appAdmModelInf (s eps0 : ℝ) (ω : ℝ) : ℂ :=
  (s : ℂ) + Complex.I * ω * eps0

/-- Eq. (51): the apparent-permittivity model `ε_A(ω) = ε_o + Σ_{j=1}^N κ_j / |ω|^{2+x_j}`. -/
def epsMultiModel {N : ℕ} (eps0 : ℝ) (kappa x : Fin N → ℝ) (ω : ℝ) : ℝ :=
  eps0 + ∑ j, kappa j / |ω| ^ (2 + x j)

end Arxiv1801_00461


