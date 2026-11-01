-- Prove2me | Definitions.Def_CongestionTaxes_rhoSup
-- name    : CongestionTaxes_rhoSup
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:32:31.309181+00:00
-- url     : https://prove2.me/theorems/e273627e-9bc7-43de-b30d-4e9460492821
-- title:
--   Worst hardness factor $\sup_{\ell\in\mathcal L}\rho_\ell$
-- statement:
--   For a set $\mathcal L$ of resource costs, $\rho=\sup_{\ell\in\mathcal L}\rho_\ell\in[0,\infty]$ is the worst hardness factor over the set. Theorem 3 assumes it is finite and bounds the price of anarchy of the optimal taxes by it.
--
--   **Formalization Note** Computed in `ℝ≥0∞`; the supremum over the empty set is $0$.
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, Theorem 3, p.19; proof of Theorem 3, p.19

import Mathlib
import Definitions.Def_CongestionTaxes_rho

open scoped ENNReal

namespace CongestionTaxes

/-- The worst hardness factor `sup_{ℓ ∈ 𝓛} ρ_ℓ` of a set `𝓛` of resource costs (Paccagnan,
Gairing, arXiv:2105.07480v2, Theorem 3, p.19, and its proof, p.19: "Denote ρ = sup_{ℓ∈𝓛} ρ_ℓ").

**Formalization Note** Computed in `ℝ≥0∞`; the supremum over the empty set is `0`. -/
noncomputable def rhoSup (L : Set (ℕ → ℝ)) : ℝ≥0∞ :=
  ⨆ ℓ ∈ L, rho ℓ

end CongestionTaxes


