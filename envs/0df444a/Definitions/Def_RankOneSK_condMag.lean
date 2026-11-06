-- Prove2me | Definitions.Def_RankOneSK_condMag
-- name    : RankOneSK_condMag
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:37.634133+00:00
-- url     : https://prove2.me/theorems/4309c66d-9c46-4ae8-94a2-6bb03b095273
-- title:
--   Conditional magnetization $\bar X_i(x_{-i})$
-- statement:
--   For the SK Gibbs measure $\mu_J$ and a site $i$,
--   $$\bar X_i(x_{-i})=\mathbb E_{\mu_J}\big[X_i\,\big|\,X_{-i}=x_{-i}\big]=P_i(x_i)(x),$$
--   which equals $\tanh\big(\sum_{k\neq i}J_{ik}x_k\big)$ and does not depend on $x_i$.
--
--   It enters the rank-one matrix $M_{ij}$ of Lemma 3.2, the vector $w$ and the weighted form $\mathcal D(f)$ of (26).
--
--   **Formalization Note** Configurations are the published `OAI.SKGap.Spin n` (maps $[n]\to\{\text{true},\text{false}\}$ read as $\pm1$), sites are indexed from $0$, and the interaction matrix $J$ is the published `OAI.SKGap.Disorder n` (its entries above the diagonal; the full matrix `coupling J` is symmetric with zero diagonal).
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, Lemma 3.2, p.20 ($\bar X_i(x_{-i})$); p.10

import Mathlib
import Definitions.Def_SKHighTemperature

open OAI.SKGap

namespace RankOneSK

/-- The conditional magnetization `X̄_i(x_{−i}) = E_µ[X_i | X_{−i} = x_{−i}] = P_i(x_i)(x)` of spin `i`
under the SK Gibbs measure `µ_J` (no external field). It equals `tanh(Σ_{k≠i} J_ik x_k)` and does
not depend on `x_i`.

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, §3, Lemma 3.2, p.20 (`X̄_i(x_{−i})`) and p.10 (`X̄_i = tanh(Σ_{k≠i} J_ik x_k)`).

**Formalization Note** Spins are `OAI.SKGap.Spin n = Fin n → Bool` (read as ±1 through `spinValue`), sites are
0-based `Fin n`, and the interaction matrix `J` is the published `OAI.SKGap.Disorder n` (entries
above the diagonal; `coupling J` is symmetric with zero diagonal). The conditional mean is the published
`conditionalExpectation J 0 i` applied to the spin `x ↦ spinValue (x i)`. -/
noncomputable def condMag {n : ℕ} (J : Disorder n) (i : Fin n) (x : Spin n) : ℝ :=
  conditionalExpectation J 0 i (fun y => spinValue (y i)) x

end RankOneSK


