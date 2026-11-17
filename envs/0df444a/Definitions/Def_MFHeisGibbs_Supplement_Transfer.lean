-- Prove2me | Definitions.Def_MFHeisGibbs_Supplement_Transfer
-- name    : MFHeisGibbs_Supplement_Transfer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:16:35.166365+00:00
-- url     : https://prove2.me/theorems/40c14b95-e533-4952-832f-110cef2d0f7d
-- title:
--   The Gaussian filters $h_{\omega,\pm}$, the weight $w$ and the constant $c_{\mathrm{eff}}(\omega_{\mathrm{trn}})$ of the gap transfer
-- statement:
--   Let $0<\beta<\infty$, $\sigma>0$, $\Lambda\ge0$, and let $\hat g_\sigma(\omega)=\sqrt{\beta/(\sigma\sqrt{2\pi})}\,e^{-\beta^2\omega^2/(4\sigma^2)}$ be the Gaussian of (11). For $\omega\in\mathbb R$ define
--
--   $$k_{\omega,\pm}(x)=\frac1{\sqrt2}\Big(e^{\pm i\pi/4}\hat g_\sigma\big(\omega-\tfrac x\beta\big)+e^{\mp i\pi/4}\hat g_\sigma\big(\omega+\tfrac x\beta\big)\Big),\qquad h_{\omega,\pm}(x)=e^{-x/4}k_{\omega,\pm}(x),$$
--
--   the weight $w(\omega)=e^{-\sigma^2/8}|f_M(\beta\omega)|^2e^{\beta\omega/2}$ with $f_M$ the Metropolis filter, and for $\omega_{\mathrm{trn}}\in(0,\infty]$
--
--   $$c_{\mathrm{eff}}(\omega_{\mathrm{trn}})=\int_{|\omega|\le\omega_{\mathrm{trn}}}w(\omega)\min_{x\in[-\Lambda,0]}|h_{\omega,+}(x)|^2\,d\omega .$$
--
--   These are the filters, the weight and the constant of the linear gap-transfer theorem.
--
--   **Formalization Note** The sign $\pm$ is a Boolean (`true` for $+$). $\omega_{\mathrm{trn}}$ is an extended nonnegative real, and $\omega_{\mathrm{trn}}=\infty$ integrates over all of $\mathbb R$. The minimum is an infimum over the compact interval $[-\Lambda,0]$ of a continuous function. The integrand is nonnegative, continuous and bounded by a multiple of $e^{-\beta|\omega|/2}$, so the Bochner integral is a genuine integral.
-- source:
--   Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…), Theorem 4, (122), (123), (125), p.53 (PDF 54)

import Definitions.Def_MFHeisGibbs_Supplement_Generators

open Set MeasureTheory
open scoped ENNReal

namespace MFHeisGibbs

namespace Supplement

/-!
# The Gaussian KMS filters `h_{ω,±}`, the weight `w` and the constant `c_eff` of Theorem 4

Raikovich, Mák, Czabán, Gilyén, arXiv:2610.06818 (version dated November 3, 2026, sha256 164d57ba…),
Theorem 4, (122), (123), (125), p.53 (PDF 54).

**Formalization Note.** `ĝ_σ` is the published `gHat β s` of (11) (width `σ` is `s`). The sign `±` is a
`Bool`, `true` for `+`. `minSqOn Λ h = min_{x ∈ [−Λ, 0]} |h(x)|²` is an infimum over the compact interval;
for continuous `h` and `Λ ≥ 0` it is attained. The truncation `ω_trn ∈ (0, ∞]` is an extended
nonnegative real; `ω_trn = ∞` makes the region of integration all of `ℝ`. `c_eff` is the Bochner integral
of a nonnegative continuous function bounded by a multiple of `e^{−β|ω|/2}`, so it is integrable and
never a junk value.
-/

/-- The phase `±iπ/4`: `iπ/4` for `+` (`true`), `−iπ/4` for `−` (`false`). -/
noncomputable def pmPhase (pm : Bool) : ℂ :=
  if pm then Complex.I * (Real.pi / 4 : ℝ) else -(Complex.I * (Real.pi / 4 : ℝ))

/-- `k_{ω,±}(x) = 2^{−1/2} (e^{±iπ/4} ĝ_σ(ω − x/β) + e^{∓iπ/4} ĝ_σ(ω + x/β))`, (122). -/
noncomputable def kOm (β s ω : ℝ) (pm : Bool) (x : ℝ) : ℂ :=
  ((Real.sqrt 2)⁻¹ : ℝ) * (Complex.exp (pmPhase pm) * (gHat β s (ω - x / β) : ℂ) +
    Complex.exp (-pmPhase pm) * (gHat β s (ω + x / β) : ℂ))

/-- `h_{ω,±}(x) = e^{−x/4} k_{ω,±}(x)`, (122). -/
noncomputable def hOm (β s ω : ℝ) (pm : Bool) (x : ℝ) : ℂ :=
  (Real.exp (-x / 4) : ℂ) * kOm β s ω pm x

/-- The weight `w(ω) = e^{−σ²/8} |f_M(βω)|² e^{βω/2}`, (123), first expression. -/
noncomputable def wM (β s ω : ℝ) : ℝ :=
  Real.exp (-s ^ 2 / 8) * ‖fM (β * ω)‖ ^ 2 * Real.exp (β * ω / 2)

/-- `min_{x ∈ [−Λ, 0]} |h(x)|²`, (124), (125). -/
noncomputable def minSqOn (Λ : ℝ) (h : ℝ → ℂ) : ℝ :=
  sInf ((fun x => ‖h x‖ ^ 2) '' Icc (-Λ) 0)

/-- `c_eff(ω_trn) = ∫_{|ω| ≤ ω_trn} w(ω) min_{x ∈ [−Λ, 0]} |h_{ω,+}(x)|² dω`, (125). -/
noncomputable def ceff (β s Λ : ℝ) (ωt : ℝ≥0∞) : ℝ :=
  ∫ ω in {ω : ℝ | ENNReal.ofReal |ω| ≤ ωt}, wM β s ω * minSqOn Λ (hOm β s ω true)

end Supplement

end MFHeisGibbs


