-- Prove2me | Definitions.Def_RankOneSK_magShift
-- name    : RankOneSK_magShift
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:39.570117+00:00
-- url     : https://prove2.me/theorems/3de3b7c8-d731-4a40-a58e-1da5cd39d3e5
-- title:
--   Shifted spin $x_i+s\bar X_i(x_{-i})$
-- statement:
--   For a real parameter $s$ and a site $i$,
--   $$m_i(x)=x_i+s\,\bar X_i(x_{-i}),$$
--   where $\bar X_i$ is the conditional magnetization. The rank-one matrix of Lemma 3.2 is $M_{ij}(x)=m_i(x)m_j(x)$, and the vector $w$ of Lemma 3.2 has entries $w_i(x)=m_i(x)\,L_if(x)$.
--
--   **Formalization Note** Configurations are the published `OAI.SKGap.Spin n` (maps $[n]\to\{\text{true},\text{false}\}$ read as $\pm1$), sites are indexed from $0$, and the interaction matrix $J$ is the published `OAI.SKGap.Disorder n` (its entries above the diagonal; the full matrix `coupling J` is symmetric with zero diagonal).
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, Lemma 3.2 and its proof, p.20

import Mathlib
import Definitions.Def_SKHighTemperature
import Definitions.Def_RankOneSK_condMag

open OAI.SKGap

namespace RankOneSK

/-- The shifted spin `x_i + s X̄_i(x_{−i})`. The rank-one matrix of Lemma 3.2 is
`M_ij(x) = (x_i + sX̄_i(x_{−i}))(x_j + sX̄_j(x_{−j}))`, and the vector `w` of Lemma 3.2 has entries
`w_i(x) = (x_i + sX̄_i(x_{−i})) · L_i f(x)`.

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, §3, Lemma 3.2 and its proof, p.20.

**Formalization Note** Spins are `OAI.SKGap.Spin n = Fin n → Bool` (read as ±1 through `spinValue`), sites are
0-based `Fin n`, and the interaction matrix `J` is the published `OAI.SKGap.Disorder n` (entries
above the diagonal; `coupling J` is symmetric with zero diagonal). `s` is an arbitrary real parameter. -/
noncomputable def magShift {n : ℕ} (J : Disorder n) (s : ℝ) (i : Fin n) (x : Spin n) : ℝ :=
  spinValue (x i) + s * condMag J i x

end RankOneSK


