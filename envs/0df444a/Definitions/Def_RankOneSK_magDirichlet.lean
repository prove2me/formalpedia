-- Prove2me | Definitions.Def_RankOneSK_magDirichlet
-- name    : RankOneSK_magDirichlet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:58.744083+00:00
-- url     : https://prove2.me/theorems/040c1961-592c-45d9-96d3-920e06c9aca6
-- title:
--   Weighted Dirichlet form $\mathcal D(f)=\sum_i\mathbb E[\bar X_i^2(L_if)^2]$
-- statement:
--   For the SK Gibbs measure $\mu_J$ and $f:\{\pm1\}^n\to\mathbb R$,
--   $$\mathcal D(f)=\sum_{i=1}^n\mathbb E_{\mu_J}\big[\bar X_i(X_{-i})^2\,(L_if)(X)^2\big],$$
--   where $\bar X_i$ is the conditional magnetization of spin $i$ and $L_i=I-P_i$.
--
--   It appears in (26) and Lemma 3.2 as the correction to the Dirichlet form $\mathcal E(f)=\sum_i\mathbb E[(L_if)^2]$ (the published `OAI.SKGap.dirichlet J 0 f`).
--
--   **Formalization Note** Configurations are the published `OAI.SKGap.Spin n` (maps $[n]\to\{\text{true},\text{false}\}$ read as $\pm1$), sites are indexed from $0$, and the interaction matrix $J$ is the published `OAI.SKGap.Disorder n` (its entries above the diagonal; the full matrix `coupling J` is symmetric with zero diagonal).
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, display (26), p.20

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_RankOneSK_siteLap
import Definitions.Def_RankOneSK_condMag

open OAI.SKGap

namespace RankOneSK

/-- The weighted Dirichlet form `𝒟(f) = Σ_i E_µ[X̄_i² (L_i f)²]` of (26), where `X̄_i = X̄_i(x_{−i})`
is the conditional magnetization of spin `i`.

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, §3, display (26), p.20.

**Formalization Note** Spins are `OAI.SKGap.Spin n = Fin n → Bool` (read as ±1 through `spinValue`), sites are
0-based `Fin n`, and the interaction matrix `J` is the published `OAI.SKGap.Disorder n` (entries
above the diagonal; `coupling J` is symmetric with zero diagonal). Expectation under the zero-field SK Gibbs measure
(`OAI.SKGap.expectation J 0`). The unweighted form `E(f) = Σ_i E_µ[(L_i f)²]` of (1) is the
published `OAI.SKGap.dirichlet J 0 f`. -/
noncomputable def magDirichlet {n : ℕ} (J : Disorder n) (f : Spin n → ℝ) : ℝ :=
  ∑ i : Fin n, expectation J 0 (fun x => condMag J i x ^ 2 * siteLap J i f x ^ 2)

end RankOneSK


