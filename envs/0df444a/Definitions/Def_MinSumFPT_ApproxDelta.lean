-- Prove2me | Definitions.Def_MinSumFPT_ApproxDelta
-- name    : MinSumFPT_ApproxDelta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:38.458877+00:00
-- url     : https://prove2.me/theorems/71d04082-f43e-4a96-8f4f-1692731f5739
-- title:
--   Definitions 2–3: $\gamma$-approximations of $|C|$, $\mathrm{OPT}$ and $\Delta_C$
-- statement:
--   For $\gamma>0$, a number $\hat x$ **$\gamma$-approximates** $x$ if $x\le\hat x\le(1+\gamma)x$ (Definition 2: this is (2) for $\widehat{|C|}$ and (3) for $\widehat{\mathrm{OPT}}$).
--
--   A number $\widehat{\Delta}_C$ **$\gamma$-approximates** $\Delta_C$ (Definition 3) if
--
--   $$
--   \Delta_C\le\widehat{\Delta}_C\le(1+\gamma)\Delta_C
--   \quad\text{or}\quad
--   \Delta_C\le\gamma\cdot\frac{\mathrm{OPT}}{k|C|^2}\le\widehat{\Delta}_C\le(1+\gamma)\cdot\gamma\cdot\frac{\mathrm{OPT}}{k|C|^2}. \tag{4}
--   $$
--
--   The second alternative lets clusters of negligible cost be estimated at the floor $\gamma\,\mathrm{OPT}/(k|C|^2)$, so that only polynomially many cost values need to be enumerated.
--
--   **Formalization Note** In (4), $\mathrm{OPT}$, $|C|$ and $\Delta_C$ are arguments; the statements pass the optimal cost, the cluster size and $\Delta_C$ of a nonempty cluster.
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Definition 2, Eqs. (2)–(3), p.9; Definition 3, Eq. (4), p.10

import Mathlib

namespace MinSumFPT

/-!
# Definitions 2 and 3: γ-approximations of |C|, OPT and Δ_C

Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation
Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256
12e81235…), Definition 2, Eqs. (2)–(3), p.9, and Definition 3, Eq. (4), p.10.

This module bundles `GammaApprox` (Definition 2, used both for |Ĉ| and for ÔPT) and `ApproxDelta`
(Definition 3).

**Formalization Note.** `ApproxDelta γ k opt c Δhat Δ` is (4) with `OPT := opt`, `|C| := c` and
`Δ_C := Δ`; the statements apply it with `opt = optCost d k`, `c = |C|` and `Δ = Delta d C` for a
nonempty cluster `C`. -/

/-- Definition 2: `x̂` γ-approximates `x` iff `x ≤ x̂ ≤ (1 + γ) x` ((2) for `|C|`, (3) for OPT). -/
def GammaApprox (γ xhat x : ℝ) : Prop :=
  x ≤ xhat ∧ xhat ≤ (1 + γ) * x

/-- Definition 3, Eq. (4): `Δ̂` γ-approximates `Δ_C` iff `Δ_C ≤ Δ̂ ≤ (1+γ)Δ_C` or
`Δ_C ≤ γ ⋅ OPT/(k|C|²) ≤ Δ̂ ≤ (1+γ) ⋅ γ ⋅ OPT/(k|C|²)`. -/
def ApproxDelta (γ : ℝ) (k : ℕ) (opt c Δhat Δ : ℝ) : Prop :=
  (Δ ≤ Δhat ∧ Δhat ≤ (1 + γ) * Δ) ∨
    (Δ ≤ γ * (opt / (k * c ^ 2)) ∧ γ * (opt / (k * c ^ 2)) ≤ Δhat ∧
      Δhat ≤ (1 + γ) * γ * (opt / (k * c ^ 2)))

end MinSumFPT


