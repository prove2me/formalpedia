-- Prove2me | Definitions.Def_StrategicAlloc_EFXTwoThirds_vstar
-- name    : StrategicAlloc_EFXTwoThirds_vstar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T15:57:29.280889+00:00
-- url     : https://prove2.me/theorems/0bacf82f-5aa1-45d4-be40-f58c9eb8a534
-- title:
--   p. 21 — the auxiliary valuation v∗ of the proof of Theorem 4.7
-- statement:
--   Fix goods $h_1,\dots,h_m$ and a parameter $\varepsilon$. The auxiliary valuation $v^*$ used in the proof of Theorem 4.7 is
--
--   $$v^*(h_j)=\begin{cases}1.2 & j=1,\\ 1 & j\in\{2,3\},\\ \varepsilon & j\in\{4,\dots,m\}.\end{cases}$$
--
--   The paper takes $\varepsilon>0$ with $(m-3)\cdot\varepsilon<0.2$; together with the identical profile $\mathbf v^*=(v^*,v^*)$ it is the instance whose only EFX allocations are $(\{h_1,h_4,\dots,h_m\},\{h_2,h_3\})$ and its symmetric.
--
--   **Formalization Note** The good $h_j$ is `j - 1` in `Fin m`, and $1.2$ is written `6 / 5`. The constraints on $\varepsilon$ are hypotheses of the statements that use $v^*$, not part of the definition.
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, p. 21, §4.2, proof of Theorem 4.7, definition of v∗

import Mathlib

namespace StrategicAlloc.EFXTwoThirds

/-- The auxiliary valuation `v∗` of the proof of Theorem 4.7 (p. 21), on the goods `Fin m`
with `h_j` the good `j - 1`: `v∗(h_1) = 1.2`, `v∗(h_2) = v∗(h_3) = 1`, and `v∗(h_j) = ε`
for `j ∈ {4, …, m}`. The page takes `ε > 0` with `(m - 3) · ε < 0.2`; statements using `vstar`
carry those hypotheses. -/
noncomputable def vstar {m : ℕ} (ε : ℝ) (g : Fin m) : ℝ :=
  if g.val = 0 then 6 / 5 else if g.val = 1 ∨ g.val = 2 then 1 else ε

end StrategicAlloc.EFXTwoThirds


