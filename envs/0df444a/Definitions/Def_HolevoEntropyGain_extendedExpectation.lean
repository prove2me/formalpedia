-- Prove2me | Definitions.Def_HolevoEntropyGain_extendedExpectation
-- name    : HolevoEntropyGain_extendedExpectation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:17:28.873963+00:00
-- url     : https://prove2.me/theorems/554e86f3-e8c9-44a2-91af-ce32413f904d
-- title:
--   Extended expectation $\operatorname{Tr}\rho(-\log A)$
-- statement:
--   Let $A$ be a positive bounded operator and $\rho$ a density operator. The operator $-\log A$ is selfadjoint, bounded from below by $-\log\|A\|$, and takes the value $+\infty$ on the kernel of $A$. Its **extended quantum expectation** is
--
--   $$
--   \operatorname{Tr}\rho(-\log A) = \sup_{\varepsilon>0}\ \operatorname{Tr}\rho\big(-\log(A+\varepsilon I)\big)\ \in (-\infty,+\infty],
--   $$
--
--   which coincides with the paper's definition (3), $\sum_k\lambda_k\langle e_k|{-\log A}|e_k\rangle$ through the spectral measure, by monotone convergence. It appears in (4) with $A = \sigma$ and in Proposition 1 with $A = \Phi[I]$.
--
--   **Formalization Note** For each $\varepsilon>0$, $-\log(A+\varepsilon I)$ is defined by the continuous functional calculus (the spectrum of $A+\varepsilon I$ lies in $[\varepsilon,\|A\|+\varepsilon]$); the supremum is in `EReal`. `Real.log 0 = 0` never stands in for $-\log$ on the kernel.
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §2, eq. (3), p.2; eq. (4), p.3; eq. (7), p.3

import Mathlib
import Definitions.Def_HolevoEntropyGain_tracePairing

open QAlgorithms.RealRegisters (Hilbert)

namespace HolevoEntropyGain

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-- The extended quantum expectation `Tr X(-log A)` of `-log A`, for a positive bounded operator `A`
(Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §2, eq. (3), p.2, eq. (4), p.3, eq. (7), p.3, PDF pp.2–3).

**Formalization Note** (R4) `-log A` is selfadjoint, bounded from below, and takes the value `+∞` on
`ker A`, so it lies in the class `F(R₊)` shifted by a constant. Here the expectation is
`sup_{ε > 0} Tr X(-log(A + ε))` in `EReal`, with the complex continuous functional calculus for each `ε`, whose
argument `A + ε` is selfadjoint with spectrum in `[ε, ‖A‖ + ε]`, where `z ↦ -log(Re z)` is continuous.
This is (3) by monotone convergence in the spectral measure of `A`. In particular `Real.log 0 = 0` never
stands in for `-log` on a kernel: `A + ε ≥ ε`. Only used for positive `A` and density `X`. -/
noncomputable def extendedExpectation {I : Type} (X : Matrix I I ℂ)
    (A : Hilbert I →L[ℂ] Hilbert I) : EReal :=
  ⨆ ε : {ε : ℝ // 0 < ε},
    (((tracePairing X (cfc (fun z : ℂ => ((-Real.log z.re : ℝ) : ℂ)) (A + (ε.1 : ℂ) • 1))).re : ℝ) : EReal)

end HolevoEntropyGain


