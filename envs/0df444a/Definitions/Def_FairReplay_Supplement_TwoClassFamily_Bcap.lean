-- Prove2me | Definitions.Def_FairReplay_Supplement_TwoClassFamily_Bcap
-- name    : FairReplay_Supplement_TwoClassFamily_Bcap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:50:35.173174+00:00
-- url     : https://prove2.me/theorems/39577557-2cc4-41d1-8767-44404c37a3eb
-- title:
--   $J_{\mathrm{bnd}}$, $H_0$, $H_1$ and the truncation budget $B_\eta$
-- statement:
--   With $r=1-p-s-\tau$ and $m=|U|$:
--   $$J_{\mathrm{bnd}}(\tau,d)=(\tau+d)\log\frac{\tau+d}{\tau}+(r-d)\log\frac{r-d}{r},$$
--   $$H_0=\frac{\log(1/\delta)+\log(r/(r-d))}{K_{\mathrm{bnd}}(\tau,d)},\qquad H_1=\frac{\log(m/\delta)+\log(1+d/\tau)}{J_{\mathrm{bnd}}(\tau,d)},$$
--   and, for $\eta\in(0,\delta)$, with $H_0(\eta),H_1(\eta)$ the same quantities at level $\eta$,
--   $$B_\eta=\frac{1}{\delta-\eta}\max_{x\in U}\Big\{H_0(\eta)\sum_{z\in U\setminus\{x\}}\bar c_z+H_1(\eta)\,\bar c_x\Big\}.$$
--   These are the expected stopping costs of the sequential boundary block and the Markov truncation budget of Theorem 10.9(vi)–(vii).
--
--   **Formalization Note** The maximum over $U$ is a real supremum over its elements, a genuine maximum when $U\neq\varnothing$.
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), Theorem 10.9(vi), eqs. (74)–(75), p.20 and (vii), eq. (80), p.21 (PDF pp.22–23)

import Mathlib
import Definitions.Def_FairReplay_Supplement_TwoClassFamily
import Definitions.Def_FairReplay_Supplement_TwoClassFamily_coverLP
import Definitions.Def_FairReplay_Supplement_TwoClassFamily_QLB

namespace FairReplay.Supplement

/-- The reverse boundary divergence `J_bnd(τ, d) = (τ + d) log((τ + d)/τ) + (r − d) log((r − d)/r)`,
`r = 1 − p − s − τ` (Theorem 10.9(vi), eq. (74), p.20). -/
noncomputable def Jbnd (p s τ d : ℝ) : ℝ :=
  (τ + d) * Real.log ((τ + d) / τ) +
    ((1 - p - s - τ) - d) * Real.log (((1 - p - s - τ) - d) / (1 - p - s - τ))

/-- `H0 = (log(1/δ) + log(r/(r − d)))/K_bnd(τ, d)` (Theorem 10.9(vi), eq. (75), p.20). -/
noncomputable def H0 (p s τ d δ : ℝ) : ℝ :=
  (Real.log (1 / δ) + Real.log ((1 - p - s - τ) / ((1 - p - s - τ) - d))) / Kbnd p s τ d

/-- `H1 = (log(m/δ) + log(1 + d/τ))/J_bnd(τ, d)` (Theorem 10.9(vi), eq. (75), p.20). -/
noncomputable def H1 (p s τ d δ : ℝ) (m : ℕ) : ℝ :=
  (Real.log (m / δ) + Real.log (1 + d / τ)) / Jbnd p s τ d

namespace TwoClassFamily

/-- **The Markov truncation budget** `B_η` (Sah, Zhang, Lian, *Testing Fairness of Evolving Software
under Uncertainty*, STOC 2027 submission, manuscript of 2026-11-03, sha256 e23940a0…, Theorem
10.9(vii), eq. (80), p.21 (PDF p.23)):
`B_η = (δ − η)⁻¹ max_{x ∈ U} { H0(η) Σ_{z ∈ U∖{x}} c̄_z + H1(η) c̄_x }`, with `m = |U|`.

**Formalization Note** The maximum over the finite set `U` is a real `iSup` over its elements; it is
a genuine maximum when `U ≠ ∅`, the only case in which it is used. -/
noncomputable def Bcap (F : TwoClassFamily) (p s τ d δ η : ℝ) : ℝ :=
  (δ - η)⁻¹ * ⨆ x : F.unmatched,
    (H0 p s τ d η * ∑ z ∈ F.unmatched.erase x, F.cbar z +
      H1 p s τ d η F.unmatched.card * F.cbar x)

end TwoClassFamily

end FairReplay.Supplement


