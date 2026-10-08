-- Prove2me | Definitions.Def_OceanicGames_Limit_Basic
-- name    : OceanicGames_Limit_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:07.160208+00:00
-- url     : https://prove2.me/theorems/a095dceb-b1a3-4550-bb9c-34412b0aac0f
-- title:
--   Oceanic pivot values, finite approximants, predecessor cells, and the limit expression
-- statement:
--   Let $M$ be a finite set of major players with weights $w_i$. For a position vector $x\in[0,1]^M$, let $P(t)=\{j:x_j<t\}$ and $w(S)=\sum_{j\in S}w_j$. Player $i$ is pivotal when
--
--   $$w(P(x_i))+\alpha x_i\le c\le w(P(x_i))+w_i+\alpha x_i.$$
--
--   Its **oceanic value** $\phi_i$ is the Lebesgue volume of this event in the unit cube. The finite approximant places the major players before the minor players in its player list and gives major player $i$ the Shapley value of the quota game $v_{c,u}$. The predecessor cell $B_{i,S}$ fixes which major players precede $i$; the clamp $\langle t\rangle$ is the median of $0,t,1$.
--
--   The auxiliary limit expression is
--
--   $$L_i(c,w,\alpha)=\sum_{S\subseteq M\setminus\{i\}}\int_{[0,1]\cap[(c-w(S)-w_i)/\alpha,(c-w(S))/\alpha]}t^{|S|}(1-t)^{m-|S|-1}\,dt.$$
--
--   It records the appendix's target independently of the oceanic value. The relation $L_i=\phi_i$ is a mathematical result, not a definition.
--
--   **Formalization Note** Major players are indexed by `Fin m`; a uniform random insertion vector is represented by product Lebesgue volume on $[0,1]^m$. The strict comparison in $P(t)$ follows §2. The value is defined for all real input parameters, while positive ocean weight and nonnegative voting weights are theorem hypotheses. The Shapley-value definition in the published platform library is reused.
-- source:
--   Milnor & Shapley, Values of Large Games II: Oceanic Games, RAND RM-2649 (1961), §2 (2.1)–(2.4), pp. 2–5; §3 (3.3), p. 8; Appendix (A.1)–(A.4), pp. 25–26; https://www.rand.org/pubs/research_memoranda/RM2649.html

import Mathlib
import Definitions.Def_OceanicGames_Limit_WeightedMajority
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue
import Definitions.Def_OceanicGames_Interior_Basic

namespace OceanicGames.Limit

open MeasureTheory Set Finset Filter

variable {m : ℕ}

/-- The finite game's Shapley OceanicGames.Interior.value to major player i; the major players come
first in the concatenated player list. -/
noncomputable def finiteValue {n : ℕ} (c : ℝ) (w : Fin m → ℝ)
    (a : Fin n → ℝ) (i : Fin m) : ℝ :=
  Supermodularity.Cooperative.ShapleyValue (wmGame c (Fin.append w a)) (Fin.castAdd n i)

/-- B_{i,S} of (3.3), including its ambient OceanicGames.Interior.cube. -/
def orderSet (i : Fin m) (S : Finset (Fin m)) : Set (Fin m → ℝ) :=
  {x | x ∈ OceanicGames.Interior.cube m ∧ (∀ j ∈ S, x j < x i) ∧ ∀ j ∉ S, x i ≤ x j}

/-- The bracket of p. 8: the median of 0, t, and 1. -/
def clamp01 (t : ℝ) : ℝ := max 0 (min t 1)

/-- The expression (A.3), with the integral over the intersection of the
two closed intervals specified on p. 26. -/
noncomputable def limitFormula (c alpha : ℝ) (w : Fin m → ℝ) (i : Fin m) : ℝ :=
  ∑ S ∈ (Finset.univ.erase i).powerset,
    ∫ t in Set.Icc (0 : ℝ) 1 ∩
      Set.Icc ((c - OceanicGames.Interior.wsum w S - w i) / alpha) ((c - OceanicGames.Interior.wsum w S) / alpha),
      t ^ S.card * (1 - t) ^ (m - S.card - 1)

end OceanicGames.Limit


