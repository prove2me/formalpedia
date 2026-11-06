-- Prove2me | Definitions.Def_RankOneSK_lap
-- name    : RankOneSK_lap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:32.479976+00:00
-- url     : https://prove2.me/theorems/e391846a-34dc-4c2b-8aa7-fccb4f38bc21
-- title:
--   The operator $L_J=\sum_i(I-P_i)$
-- statement:
--   With $L_i=I-P_i$ the single-site operators of the SK Gibbs measure $\mu_J$ (see `RankOneSK.siteLap`),
--   $$L_Jf(x)=\sum_{i=1}^nL_if(x)=\sum_{i=1}^n\big(f(x)-P_if(x)\big).$$
--
--   The transition matrix of Glauber dynamics is $\tfrac1n P$ with $P=\sum_iP_i$, so $L_J=nI-P$ is $n$ times its generator. Theorem 1.5 is a Bochner-type inequality for $L_J$.
--
--   **Formalization Note** Configurations are the published `OAI.SKGap.Spin n` (maps $[n]\to\{\text{true},\text{false}\}$ read as $\pm1$), sites are indexed from $0$, and the interaction matrix $J$ is the published `OAI.SKGap.Disorder n` (its entries above the diagonal; the full matrix `coupling J` is symmetric with zero diagonal).
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, §1, p.2 ($L=\sum_iL_i$) and Theorem 1.5, p.4

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_RankOneSK_siteLap

open OAI.SKGap

namespace RankOneSK

/-- The operator `L_J = Σ_i L_i = Σ_i (I − P_i)` of the SK Glauber dynamics; `(1/n)(nI − L_J)` is
the Glauber transition matrix.

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, §1, p.2 (`L = Σ_i L_i`) and Theorem 1.5, p.4 (`L_J = Σ_i L_i = Σ_i (I − P_i)`).

**Formalization Note** Spins are `OAI.SKGap.Spin n = Fin n → Bool` (read as ±1 through `spinValue`), sites are
0-based `Fin n`, and the interaction matrix `J` is the published `OAI.SKGap.Disorder n` (entries
above the diagonal; `coupling J` is symmetric with zero diagonal). -/
noncomputable def lap {n : ℕ} (J : Disorder n) (f : Spin n → ℝ) (x : Spin n) : ℝ :=
  ∑ i : Fin n, siteLap J i f x

end RankOneSK


