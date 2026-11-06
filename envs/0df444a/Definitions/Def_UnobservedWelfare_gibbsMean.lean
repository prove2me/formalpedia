-- Prove2me | Definitions.Def_UnobservedWelfare_gibbsMean
-- name    : UnobservedWelfare_gibbsMean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:46.229586+00:00
-- url     : https://prove2.me/theorems/586d7c5f-dd64-471a-93a4-924d3ca0251d
-- title:
--   Gibbs normalizer, Gibbs distribution and Gibbs mean on $\mathbb R^m_{++}$
-- statement:
--   For a temperature $\tau>0$ and an energy $V:\mathbb R^m_{++}\to\mathbb R$,
--   $$Z_\tau(V)=\int_{\mathbb R^m_{++}}e^{-V(z)/\tau}\,dz,\qquad \pi^V_\tau(dz)=\frac{e^{-V(z)/\tau}}{Z_\tau(V)}\,dz,\qquad \bar z^V_\tau=\mathbb E_{\pi^V_\tau}[Z]=\frac{1}{Z_\tau(V)}\int_{\mathbb R^m_{++}}z\,e^{-V(z)/\tau}\,dz,$$
--   with $dz$ Lebesgue measure. Gibbs distributions are the soft minimizers from which Algorithm 1 builds its prices.
--
--   **Formalization Note** The normalizer is a Bochner integral, so `0 < gibbsZ τ V` means positive and finite. The Gibbs measure is written in the Boltzmann form of the platform theorem `OAI.RadialTransition.gibbs_bogoliubov`.
-- source:
--   Cheng–Tao–Xing, Maximizing Unobserved Welfare: Logarithmic Regret from Purchases, manuscript (STOC 2027 submission; held artifact sha256 cfd42fa2b0b4d51bad26ff5715acac275b66e830e1391d884542854ddde215fe), §2 "Gibbs Distributions and Energy Bounds", p.19 (PDF p.21)

import Mathlib
import Definitions.Def_UnobservedWelfare_IsRC

open MeasureTheory
open scoped ENNReal

namespace UnobservedWelfare

/-- The Gibbs normalizer `Z_τ(V) = ∫_{ℝ^m_{++}} e^{−V(z)/τ} dz` of an energy `V` at temperature `τ`
(Cheng–Tao–Xing manuscript, §2 "Gibbs Distributions and Energy Bounds", p.19 (PDF p.21)).

**Formalization Note** A Bochner integral against Lebesgue measure restricted to the open orthant;
it is `0` when the integrand is not integrable, so `0 < gibbsZ τ V` says that the normalizer is
positive and finite. -/
noncomputable def gibbsZ {m : ℕ} (τ : ℝ) (V : (Fin m → ℝ) → ℝ) : ℝ :=
  ∫ z in posOrthant m, Real.exp (-V z / τ)

/-- The Gibbs distribution `π^V_τ(dz) = e^{−V(z)/τ} dz / Z_τ(V)` on `ℝ^m_{++}` (Cheng–Tao–Xing
manuscript, p.19 (PDF p.21)).

**Formalization Note** Written in the Boltzmann form of the platform theorem
`OAI.RadialTransition.gibbs_bogoliubov`: the inverse normalizer times Lebesgue measure on the
orthant with density `e^{−V/τ}`. It is a probability measure exactly when `0 < gibbsZ τ V`. -/
noncomputable def gibbsMeasure {m : ℕ} (τ : ℝ) (V : (Fin m → ℝ) → ℝ) : Measure (Fin m → ℝ) :=
  (ENNReal.ofReal (gibbsZ τ V))⁻¹ •
    (volume.restrict (posOrthant m)).withDensity (fun z => ENNReal.ofReal (Real.exp (-V z / τ)))

/-- The Gibbs mean `z̄^V_τ = E_{π^V_τ}[Z] = ∫_{ℝ^m_{++}} z e^{−V(z)/τ} dz / Z_τ(V)`
(Cheng–Tao–Xing manuscript, p.19 (PDF p.21)). -/
noncomputable def gibbsMean {m : ℕ} (τ : ℝ) (V : (Fin m → ℝ) → ℝ) : Fin m → ℝ :=
  (gibbsZ τ V)⁻¹ • ∫ z in posOrthant m, Real.exp (-V z / τ) • z

end UnobservedWelfare


