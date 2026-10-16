-- Prove2me | Definitions.Def_InterdepSOS_KSS_Setting
-- name    : InterdepSOS_KSS_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T12:36:00.358549+00:00
-- url     : https://prove2.me/theorems/2572cdda-d6db-4fc7-a0ca-02d04db2dea7
-- title:
--   Definition 2.14, p. 12 — strong-SOS valuations (d = 1) on the signal grid {0,…,k−1}^n
-- statement:
--   Agents $1,\dots,n$ hold signals $s_i\in\{0,1,\dots,k-1\}$; $\mathbf s=(s_1,\dots,s_n)$ is the signal profile and $\{0,\dots,k-1\}^n$ is called the **grid**. Profiles are compared coordinate-wise.
--
--   A real function $w$ of the profile is **strong-SOS** on the grid (Definition 2.14 with $d=1$, inequality (2)) if for every coordinate $j$, every $\delta\ge0$ and all grid profiles $\mathbf s'\le\mathbf s$ coordinate-wise (coordinate $j$ included) with $s_j+\delta<k$,
--   $$w(\mathbf s_{-j},s_j+\delta)-w(\mathbf s)\le w(\mathbf s'_{-j},s'_j+\delta)-w(\mathbf s').$$
--   Raising one signal by $\delta$ from its current value helps at least as much at the lower profile as at the higher one. Unlike SOS (Definition 2.13), the raised coordinate itself may be lower in $\mathbf s'$, so in particular the effect of an agent's own signal is concave.
--
--   The rest of the model (signals, combinatorial valuations with their standing hypotheses, SOS, feasible allocations, welfare, utility, ex-post IC and IR, and the terms OTHER and SELF of display (7)) is the shared definition module `InterdepSOS.KHL.Setting`, which this module imports. A combinatorial valuation is strong-SOS when every $v_{iT}$ is.
--
--   **Formalization Note** Signals are natural numbers and the condition is quantified over grid profiles only (the paper's signal space is $\{0,\dots,k-1\}$); $s'_j+\delta\le s_j+\delta<k$, so both shifted profiles stay in the grid. The paper's second profile is printed "$s=(s'_1,\dots,s'_n)$"; it is $\mathbf s'$.
-- source:
--   Eden, Feldman, Fiat, Goldner, Karlin, Combinatorial Auctions with Interdependent Valuations: SOS to the Rescue, arXiv:1903.08384v2 (2019), pp. 11–12, Definition 2.14; p. 19, §6.1 signal space

import Mathlib
import Definitions.Def_InterdepSOS_KHL_Setting
import Definitions.Def_InterdepSOS_RSV_Setting

namespace InterdepSOS.KSS

/-- Strong-SOS on the grid (Definition 2.14, inequality (2) with `d = 1`): for profiles
`s' ≤ s` coordinate-wise (coordinate `j` included), raising coordinate `j` by `δ` from its
current value helps at least as much at `s'` as at `s`. -/
def IsStrongSOS {n : ℕ} (k : ℕ) (w : InterdepSOS.KHL.Signal n → ℝ) : Prop :=
  ∀ (j : Fin n) (δ : ℕ) (s s' : InterdepSOS.KHL.Signal n), InterdepSOS.KHL.InGrid k s → InterdepSOS.KHL.InGrid k s' → s' ≤ s → s j + δ < k →
    w (Function.update s j (s j + δ)) - w s ≤ w (Function.update s' j (s' j + δ)) - w s'

end InterdepSOS.KSS


