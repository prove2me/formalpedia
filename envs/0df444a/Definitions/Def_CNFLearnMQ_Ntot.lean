-- Prove2me | Definitions.Def_CNFLearnMQ_Ntot
-- name    : CNFLearnMQ_Ntot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:35.799494+00:00
-- url     : https://prove2.me/theorems/96787621-ebd3-4602-a186-6876e462289d
-- title:
--   Parameters $T$, $\lceil k/(t+1)\rceil$, $N_{\mathrm{tot}}$, $\eta$, $N_{\mathrm{seed}}$, $N_{\mathrm{pool}}$, $\phi$, $N_{\mathrm{ext}}$, $\zeta$, $\rho$
-- statement:
--   The parameters of the algorithms, with $\log$ the base-2 and $\ln$ the natural logarithm:
--
--   1. LearnCore stops after $T=\lceil 2(16dk)^k\ln(nd/\zeta)\rceil$ consecutive unsuccessful iterations.
--   2. Seeds have size $\lceil k/(t+1)\rceil$.
--   3. $N_{\mathrm{tot}}=\left\lceil 2^{40dk^4(1+\Xi(t))}\,n^{1+\Xi(t)}\,(\ln(n/\varepsilon))^k\right\rceil$ and $\eta=\varepsilon/(3N_{\mathrm{tot}})$ (eq. (7)).
--   4. $N_{\mathrm{seed}}=k\lceil\log(6dkn/\delta)\rceil$.
--   5. $N_{\mathrm{pool}}=\left\lceil 2^{4dk^2+8}k\ln(n/\delta)/\eta\right\rceil$ (eq. (8)).
--   6. $\phi=2^{-2dk^2}$ and $N_{\mathrm{ext}}=\lceil 144k\phi^{-2}\ln(n/\delta)\rceil$.
--   7. $\zeta=\delta/(6N_{\mathrm{ext}}N_{\mathrm{tot}})$.
--   8. $\rho=2^{-k}(1-2^{1-k})^{-dk}$.
--
--   **Formalization Note** The ceilings are natural-number ceilings of positive reals. Exponents involving $\Xi(t)$ are natural numbers.
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), Algorithm 1 p.18; p.22; eq. (7) p.24; p.24; eq. (8) p.25; p.26; p.28

import Mathlib
import Definitions.Def_CNFLearning873_Valiant_Thresholds
import Definitions.Def_CNFLearnMQ_Xi

set_option autoImplicit false

namespace CNFLearnMQ

open CNFLearning873.Valiant

/-- The number of consecutive unsuccessful main-loop iterations after which LearnCore stops,
`T = ⌈2(16dk)^k · ln(nd/ζ)⌉` (Feng, Yu, Zhang, STOC 2027 submission (manuscript sha256 519ee6d4…),
Algorithm 1 line 2, p.18, and proof of Theorem 4.5, p.19). -/
noncomputable def coreRounds (n k d : ℕ) (ζ : ℝ) : ℕ :=
  ⌈2 * (16 * (d : ℝ) * k) ^ k * Real.log ((n : ℝ) * d / ζ)⌉₊

/-- The seed size `⌈k/(t + 1)⌉` (§5.1, p.22). -/
noncomputable def seedSize (k : ℕ) (t : ℝ) : ℕ := ⌈(k : ℝ) / (t + 1)⌉₊

/-- The truncation threshold `N_tot = ⌈2^{40dk⁴(1+Ξ(t))} n^{1+Ξ(t)} (ln(n/ε))^k⌉`, eq. (7), p.24. -/
noncomputable def Ntot (n k d : ℕ) (t ε : ℝ) : ℕ :=
  ⌈(2 : ℝ) ^ (40 * d * k ^ 4 * (1 + Xi t)) * (n : ℝ) ^ (1 + Xi t) *
    Real.log ((n : ℝ) / ε) ^ k⌉₊

/-- The acceptance parameter `η = ε/(3N_tot)`, eq. (7), p.24. -/
noncomputable def eta (n k d : ℕ) (t ε : ℝ) : ℝ := ε / (3 * (Ntot n k d t ε : ℝ))

/-- The seed sample size `N_seed = k⌈log(6dkn/δ)⌉` (base-2 logarithm), p.24. -/
noncomputable def Nseed (n k d : ℕ) (δ : ℝ) : ℕ :=
  k * ⌈log₂ (6 * (d : ℝ) * k * n / δ)⌉₊

/-- The pool size `N_pool = ⌈2^{4dk²+8} k ln(n/δ)/η⌉`, eq. (8), p.25. -/
noncomputable def Npool (n k d : ℕ) (t ε δ : ℝ) : ℕ :=
  ⌈(2 : ℝ) ^ (4 * d * k ^ 2 + 8) * k * Real.log ((n : ℝ) / δ) / eta n k d t ε⌉₊

/-- The error tolerance `ϕ = 2^{−2dk²}`, p.26. -/
noncomputable def phi (d k : ℕ) : ℝ := ((2 : ℝ) ^ (2 * d * k ^ 2))⁻¹

/-- The number of selected samples `N_ext = ⌈144kϕ^{−2} ln(n/δ)⌉`, p.26. -/
noncomputable def Next (n k d : ℕ) (δ : ℝ) : ℕ :=
  ⌈144 * (k : ℝ) * (phi d k)⁻¹ ^ 2 * Real.log ((n : ℝ) / δ)⌉₊

/-- The failure parameter of the LearnCore calls inside ExtendSubclause,
`ζ = δ/(6 N_ext N_tot)`, p.26. -/
noncomputable def zeta (n k d : ℕ) (t ε δ : ℝ) : ℝ :=
  δ / (6 * (Next n k d δ : ℝ) * (Ntot n k d t ε : ℝ))

/-- `ρ = 2^{−k}(1 − 2^{1−k})^{−dk}` (p.28; Lemma 5.13, p.29). -/
noncomputable def rho (k d : ℕ) : ℝ := ((2 : ℝ) ^ k)⁻¹ * ((1 - 2 / (2 : ℝ) ^ k)⁻¹) ^ (d * k)

end CNFLearnMQ


