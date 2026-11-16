-- Prove2me | Definitions.Def_FairTeamContracts_Supplement_GammaConst
-- name    : FairTeamContracts_Supplement_GammaConst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:08:34.933681+00:00
-- url     : https://prove2.me/theorems/d09ee7b1-9e8c-49e1-aa17-81b080804477
-- title:
--   The constants $H(C)$, $\widetilde\psi(P)$ and $\Gamma$ of (17)–(18)
-- statement:
--   For $C\ge0$ the benchmark
--   $$H(C)=\max_{0\le r\le1}r(1-Cr)$$
--   measures the trade-off between preserving reward and paying shares. For $P\ge0$ the conversion factor is
--   $$\widetilde\psi(P)=\Bigl(\int_0^1\frac{dz}{H(Pz)}\Bigr)^{-1},$$
--   and the approximation constant of the submodular algorithm is
--   $$\Gamma:=\max_{t>0}\,(1-e^{-t})\,\widetilde\psi\Bigl(\frac{t^2}{1-e^{-t}}\Bigr).$$
--
--   Theorem 5.13 asserts that $H$ has the closed form $1-C$ for $C\le\frac12$ and $(4C)^{-1}$ for $C\ge\frac12$, that the maximum defining $\Gamma$ is attained, and that $\Gamma\ge0.24988$.
--
--   **Formalization Note** $H(C)$ is the supremum of $r(1-Cr)$ over $r\in[0,1]$ (a maximum, by compactness). $\widetilde\psi$ uses the interval integral over $[0,1]$. $\Gamma$ is the supremum of the objective over $t>0$; that this supremum is attained is a conclusion of Theorem 5.13, not part of the definition.
-- source:
--   Chen, Castiglioni, Li, Fair Team Contracts, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Theorem 5.13, eqs. (17)–(18), p.25

import Mathlib

namespace FairTeamContracts.Supplement

/-- The benchmark `H(C) = max_{0 ≤ r ≤ 1} r(1 − C r)` of (18) (Chen, Castiglioni, Li, *Fair Team
Contracts*, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), Theorem 5.13, eq. (18), p.25).

**Formalization Note.** Defined as the supremum `sSup` of `r(1 − C r)` over `r ∈ [0, 1]`; the
image of the compact interval under a continuous map is nonempty and bounded, so this is the
maximum. It is read for `C ≥ 0`. -/
noncomputable def Hfun (C : ℝ) : ℝ :=
  sSup ((fun r : ℝ => r * (1 - C * r)) '' Set.Icc 0 1)

/-- The conversion factor `ψ̃(P) = (∫₀¹ dz / H(P z))⁻¹` of (18) (*Fair Team Contracts*,
Theorem 5.13, eq. (18), p.25), read for `P ≥ 0`.

**Formalization Note.** The integral is the interval integral over `[0, 1]`. For `P ≥ 0` the
integrand is positive and continuous (`H > 0` on `[0, ∞)`). -/
noncomputable def psiTilde (P : ℝ) : ℝ :=
  (∫ z in (0 : ℝ)..1, 1 / Hfun (P * z))⁻¹

/-- The objective `(1 − e^{−t}) · ψ̃(t² / (1 − e^{−t}))` maximized in (17) (*Fair Team
Contracts*, Theorem 5.13, eq. (17), p.25). -/
noncomputable def gammaObj (t : ℝ) : ℝ :=
  (1 - Real.exp (-t)) * psiTilde (t ^ 2 / (1 - Real.exp (-t)))

/-- The approximation constant `Γ := max_{t > 0} (1 − e^{−t}) ψ̃(t² / (1 − e^{−t}))` of (17)
(Chen, Castiglioni, Li, *Fair Team Contracts*, arXiv:2512.19388 (manuscript sha256 b8a12d9b…),
Theorem 5.13, eq. (17), p.25).

**Formalization Note.** Defined as the supremum `sSup` of `gammaObj` over `t > 0`; that the
supremum is attained (so it is the paper's maximum) is a conclusion of Theorem 5.13, not part of
the definition. -/
noncomputable def GammaConst : ℝ :=
  sSup (gammaObj '' Set.Ioi 0)

end FairTeamContracts.Supplement


