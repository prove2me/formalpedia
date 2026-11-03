-- Prove2me | Definitions.Def_MobilePromo_Season
-- name    : MobilePromo_Season
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:15:08.44926+00:00
-- url     : https://prove2.me/theorems/832f4bd9-3121-4c00-b64a-935790ed5b9e
-- title:
--   Seasons, campaigns, active campaigns and first-end-first-serve allocation
-- statement:
--   A **season** has $T$ periods and $m\ge1$ campaigns. Campaign $j$ asks for $W_j>0$ impressions and runs from its start $\bar t_j\ge1$ to its end $\underline t_j\ge\bar t_j$; the campaigns are ordered by end time, $\underline t_1\le\dots\le\underline t_m=T$.
--
--   In period $t$, in a state $\boldsymbol c=(c_1,\dots,c_m)$ of unmet impressions, the set of **active** campaigns is
--
--   $$
--   \mathcal F=\{j:\bar t_j\le t\le\underline t_j,\ c_j\ge 1\}.
--   $$
--
--   Under **first-end-first-serve** (FEFS), an impression won in the period goes to the active campaign $g=\min\mathcal F$, so $c_g$ falls by one and the other coordinates stay; if $\mathcal F=\emptyset$ nothing changes. The state $\boldsymbol c_i(\hat x)$ reached after the within-season outcomes $\hat x$ starts from $\boldsymbol W$ and follows this rule.
--
--   A **schedule** is a sequence of seasons, of which the first $I$ are used for a horizon of $I$ seasons. An **outcome** of a period is either "no arrival" ($\zeta=0$) or an arrival from $l$ with a win indicator $d$.
--
--   **Formalization Note** Campaigns are `Fin m`, seasons are numbered from $0$ in the schedule, and periods stay $1,\dots,T$. `Season 0` is empty, so $T\ge1$ always. The condition $m\ge1$ is implicit in the paper.
-- source:
--   Feng, Dawande, Janakiraman & Qi, An Asymptotically Tight Learning Algorithm for Mobile-Promotion Platforms, SSRN 3523491, §2, pp.7–8; FEFS, p.11; Appendix B, A1 (PDF 35)

import Mathlib

set_option autoImplicit false

namespace MobilePromo

/-- One season of `T` periods and its campaigns (SSRN 3523491, p.7): for `j < m` the target `W j > 0`,
the start `st j` and the end `en j`, with `1 ≤ st j ≤ en j`, the campaigns ordered by end time, and the
last one ending at `T`.

**Formalization Note** Campaigns are `Fin m` (campaign `j` of the paper is `j - 1` here) and periods
stay `1, …, T` as in the paper. `m_pos` is implicit in the paper ("the last campaign"). `Season 0` is
empty, so every statement over a `Season T` has `T ≥ 1`. -/
structure Season (T : ℕ) where
  /-- The number of campaigns. -/
  m : ℕ
  m_pos : 0 < m
  /-- The target numbers of impressions. -/
  W : Fin m → ℕ
  W_pos : ∀ j, 0 < W j
  /-- The start periods `t̄`. -/
  st : Fin m → ℕ
  /-- The end periods `t̲`. -/
  en : Fin m → ℕ
  st_pos : ∀ j, 1 ≤ st j
  st_le_en : ∀ j, st j ≤ en j
  en_mono : Monotone en
  en_last : en ⟨m - 1, Nat.sub_lt m_pos Nat.one_pos⟩ = T

/-- The sequence of seasons (SSRN 3523491, p.7).

**Formalization Note** Seasons are numbered `0, 1, …`, so season `i` of the paper is `i - 1` here. The
regret after `I` seasons reads the first `I` entries, as `C_I` does on p.7; `BidAlloc` needs no `I`. -/
abbrev Schedule (T : ℕ) := ℕ → Season T

/-- What happens in one period (SSRN 3523491, pp.7–8): `none` if no impression arrives (`ζ = 0`), and
`some (l, d)` if one arrives from `l`, with `d` the win indicator `d_{i,t}`. -/
abbrev Outcome (L : ℕ) := Option (Fin L × Bool)

namespace Season

variable {T : ℕ} (S : Season T)

/-- The set `F` of active campaigns of period `t` in state `c` (SSRN 3523491, p.8):
`t̄ ≤ t ≤ t̲` and `c_j ≥ 1`. -/
def activeSet (t : ℕ) (c : Fin S.m → ℕ) : Finset (Fin S.m) :=
  Finset.univ.filter fun j => S.st j ≤ t ∧ t ≤ S.en j ∧ 1 ≤ c j

/-- The state after an impression is won in period `t` from state `c` under FEFS (SSRN 3523491, p.11,
and Appendix B, A1, PDF 35): the active campaign `g = min F` loses one unmet impression, and nothing
changes if `F = ∅`. -/
def afterWin (t : ℕ) (c : Fin S.m → ℕ) : Fin S.m → ℕ :=
  if h : (S.activeSet t c).Nonempty then
    Function.update c ((S.activeSet t c).min' h) (c ((S.activeSet t c).min' h) - 1)
  else c

/-- The recursion of Appendix B, started from state `c` in period `t`. -/
def stateFrom {L : ℕ} : ℕ → (Fin S.m → ℕ) → List (Outcome L) → Fin S.m → ℕ
  | _, c, [] => c
  | t, c, some (_, true) :: xs => stateFrom (t + 1) (S.afterWin t c) xs
  | t, c, _ :: xs => stateFrom (t + 1) c xs

/-- The state `c_i(x̂)` after the outcomes `x̂` of the season so far, starting from `c(∅) = W`
(SSRN 3523491, p.15, and Appendix B, A1, PDF 35). -/
def state {L : ℕ} (x : List (Outcome L)) : Fin S.m → ℕ := S.stateFrom 1 S.W x

end Season

end MobilePromo


