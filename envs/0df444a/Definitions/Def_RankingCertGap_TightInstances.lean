-- Prove2me | Definitions.Def_RankingCertGap_TightInstances
-- name    : RankingCertGap_TightInstances
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:49:14.603696+00:00
-- url     : https://prove2.me/theorems/c55dd89a-d765-4801-bb91-4fff2b37a98e
-- title:
--   The instances $G^\star$, $C_6$ and the long cycles
-- statement:
--   Three explicit instances carry the extremal values on two-regular graphs.
--
--   1. $G^\star$ has arrival order $j_1\prec\dots\prec j_8$ and neighbourhoods $j_1\{i_2,i_3\}$, $j_2\{\tilde i_2,\tilde i_3\}$, $j_3\{i_1,i_2\}$, $j_4\{i_3,i_4\}$, $j_5\{\tilde i_1,\tilde i_2\}$, $j_6\{\tilde i_3,\tilde i_4\}$, $j_7\{i_4,\tilde i_1\}$, $j_8\{\tilde i_4,i_1\}$.
--   2. $C_6$ has arrival order $j_1\prec j_2\prec j_3$ and $N(j_1)=\{i_1,i_2\}$, $N(j_2)=\{i_1,i_3\}$, $N(j_3)=\{i_2,i_3\}$.
--   3. The long cycle, for $m\ge1$, has offline nodes $i_0,\dots,i_m,\tilde i_0,\dots,\tilde i_m$, with $N(j_0)=\{i_0,\tilde i_0\}$, $N(j^\star)=\{i_m,\tilde i_m\}$, $N(j_r)=\{i_{r-1},i_r\}$, $N(\tilde j_r)=\{\tilde i_{r-1},\tilde i_r\}$ for $r\in[m]$, and arrival order $j_0\prec j_1\prec\dots\prec j_m\prec\tilde j_1\prec\dots\prec\tilde j_m\prec j^\star$.
--
--   **Formalization Note** Vertices are renumbered from $0$ as the docstrings record. The verification file proves that $G^\star$, $C_6$ and the long cycles with $m\le3$ are two-regular and that $\mathrm{OPT}(G^\star)=8$.
-- source:
--   Xu, Certifying Capacity and Gaps of the Rank-Dependent Gain-Sharing Framework for Ranking, arXiv:2610.17545 (held file sha256 75896dd9…), App. J.3, p.78; p.87; App. I.1, p.75

import Mathlib
import Definitions.Def_RankingCertGap_Inst

namespace RankingCertGap

/-- The tight two-regular instance `G★`. Xu, arXiv:2610.17545 (held file sha256 75896dd9…), App. J.3,
p.78: arrival order `j₁ ≺ ⋯ ≺ j₈` with neighbourhoods `j₁ {i₂,i₃}`, `j₂ {ĩ₂,ĩ₃}`, `j₃ {i₁,i₂}`,
`j₄ {i₃,i₄}`, `j₅ {ĩ₁,ĩ₂}`, `j₆ {ĩ₃,ĩ₄}`, `j₇ {i₄,ĩ₁}`, `j₈ {ĩ₄,i₁}`.

**Formalization Note.** Offline `i₁, …, i₄` are `0, …, 3` and `ĩ₁, …, ĩ₄` are `4, …, 7`; online
`j₁, …, j₈` are `0, …, 7`. -/
def gStar : Inst 8 8 where
  N := ![{1, 2}, {5, 6}, {0, 1}, {2, 3}, {4, 5}, {6, 7}, {3, 4}, {7, 0}]

/-- The six-cycle `C₆`, p.87: `j₁ ≺ j₂ ≺ j₃` with `N(j₁) = {i₁, i₂}`, `N(j₂) = {i₁, i₃}`,
`N(j₃) = {i₂, i₃}`. Offline `i₁, i₂, i₃` are `0, 1, 2`; online `j₁, j₂, j₃` are `0, 1, 2`. -/
def sixCycle : Inst 3 3 where
  N := ![{0, 1}, {0, 2}, {1, 2}]

/-- The long-cycle instance of App. I.1, p.75: for `m ≥ 1`, offline `i₀, …, i_m, ĩ₀, …, ĩ_m`,
`N(j₀) = {i₀, ĩ₀}`, `N(j★) = {i_m, ĩ_m}`, `N(j_r) = {i_{r−1}, i_r}`, `N(j̃_r) = {ĩ_{r−1}, ĩ_r}` for
`r ∈ [m]`, with order `j₀ ≺ j₁ ≺ ⋯ ≺ j_m ≺ j̃₁ ≺ ⋯ ≺ j̃_m ≺ j★`.

**Formalization Note.** Offline: `i_r = r` and `ĩ_r = m + 1 + r`. Online: `j_r = r`, `j̃_r = m + r`,
`j★ = 2m + 1`. The page takes `m ≥ 1`; every statement about this family carries that hypothesis. -/
def longCycle (m : ℕ) : Inst (2 * m + 2) (2 * m + 2) where
  N j := Finset.univ.filter fun i =>
    if j.val = 0 then i.val = 0 ∨ i.val = m + 1
    else if j.val ≤ m then i.val + 1 = j.val ∨ i.val = j.val
    else if j.val ≤ 2 * m then i.val = j.val ∨ i.val = j.val + 1
    else i.val = m ∨ i.val = 2 * m + 1

/-- The distinguished offline endpoint `i_m` of `longCycle m`. -/
def longCycle.iLast (m : ℕ) : Fin (2 * m + 2) := ⟨m, by omega⟩

/-- The final online node `j★` of `longCycle m`. -/
def longCycle.jStar (m : ℕ) : Fin (2 * m + 2) := ⟨2 * m + 1, by omega⟩

end RankingCertGap


