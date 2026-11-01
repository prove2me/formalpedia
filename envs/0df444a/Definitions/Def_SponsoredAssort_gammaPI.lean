-- Prove2me | Definitions.Def_SponsoredAssort_gammaPI
-- name    : SponsoredAssort_gammaPI
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:54:31.690918+00:00
-- url     : https://prove2.me/theorems/a41e1089-66ea-49d1-9342-b1b27b8f4ba5
-- title:
--   Prior-independent competitive ratio $\gamma^{PI}(r)$
-- statement:
--   The **prior-independent competitive ratio** of deterministic mechanisms is
--
--   $$
--   \gamma^{PI}(r)=\sup_{m\in M}\ \inf_{F\in\mathcal P(\mathbb R^n_+)}\ \frac{\mathbb E_{v\sim F}[R(m,v)]}{\mathbb E_{v\sim F}[R(m^{FB},v)]},
--   $$
--
--   where $M$ is the set of deterministic mechanisms satisfying (IC) and (IR). A value $\gamma^{PI}(r)>0$ means the platform can guarantee a fraction $\gamma^{PI}(r)$ of first-best welfare under every prior with a single truthful mechanism.
--
--   **Formalization Note** A supremum in $[0,\infty]$; $M$ carries no measurability condition (see the expected welfare) and the inner infimum excludes the prior $\delta_0$ (see the worst-case ratio).
-- source:
--   Balseiro, Désir, Incentive-Compatible Assortment Optimization for Sponsored Products, SSRN 3821382 (Feb. 21, 2022), Definition 2.2, p.12

import Mathlib
import Definitions.Def_SponsoredAssort_worstCaseRatio
import Definitions.Def_SponsoredAssort_IsIC
import Definitions.Def_SponsoredAssort_IsIR

open scoped NNReal ENNReal
open MeasureTheory

namespace SponsoredAssort

/-- The **prior-independent competitive ratio** of deterministic mechanisms (Balseiro, Désir,
SSRN 3821382 (Feb. 21, 2022), Definition 2.2, p.12):
`γ^PI(r) = sup_{m ∈ M} inf_{F ∈ P(ℝⁿ₊)} E_{v∼F}[R(m, v)] / E_{v∼F}[R(m^FB, v)]`, where `M` is the
set of deterministic mechanisms satisfying (IC) and (IR) (p.11).

**Formalization Note.** A supremum in `ℝ≥0∞` of `worstCaseRatio` over all mechanisms that are IC
and IR; `M` carries no measurability condition. -/
noncomputable def gammaPI {n : ℕ} (r : Fin n → ℝ) : ℝ≥0∞ :=
  ⨆ (m : Mechanism n) (_ : IsIC r m) (_ : IsIR r m), worstCaseRatio r m

end SponsoredAssort


