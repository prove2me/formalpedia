-- Prove2me | Definitions.Def_CycleCanceling_MinMean_EpsOptimal
-- name    : CycleCanceling_MinMean_EpsOptimal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T21:11:10.565989+00:00
-- url     : https://prove2.me/theorems/7a9a807f-1397-4fb6-adbf-a69b27cc10a9
-- title:
--   Reduced costs, $\varepsilon$-optimality (5), $\varepsilon(f)$ and $\varepsilon$-fixed arcs
-- statement:
--   This file fixes the approximate-optimality notions of Goldberg and Tarjan's Section 3.
--
--   1. A **price function** is a function $p:V\to\mathbb R$; the **reduced cost** of an arc is $c_p(v,w)=c(v,w)+p(v)-p(w)$.
--   2. A circulation $f$ is **$\varepsilon$-optimal with respect to $p$** if
--   $$
--   u_f(v,w)>0\ \Longrightarrow\ c_p(v,w)\ge-\varepsilon\qquad\forall (v,w)\in E\qquad(\varepsilon\text{-optimality constraints (5)}).
--   $$
--   3. For $\varepsilon\ge 0$, a circulation $f$ is **$\varepsilon$-optimal** if it is $\varepsilon$-optimal with respect to some price function.
--   4. For a circulation $f$, $\varepsilon(f)$ is the minimum $\varepsilon$ such that $f$ is $\varepsilon$-optimal.
--   5. An arc $(v,w)$ is **$\varepsilon$-fixed** if the flow through it is the same for all $\varepsilon$-optimal circulations.
--
--   The quantity $\varepsilon(f)$ measures how far $f$ is from optimal and is the potential function of the whole analysis.
--
--   **Formalization Note** $\varepsilon(f)$ is the infimum `sInf` of the set of $\varepsilon$ for which $f$ is $\varepsilon$-optimal. For a circulation this set is nonempty ($p=0$ and $\varepsilon=\sum_{E}|c|$) and bounded below by $0$, so the infimum is a genuine one; that it is attained is a fact to be proved, not an assumption. Being $\varepsilon$-optimal includes being a circulation of the network, so an $\varepsilon$-fixed arc compares circulations of the same network only.
-- source:
--   Goldberg, Tarjan, Finding Minimum-Cost Circulations by Canceling Negative Cycles, J. ACM 36(4), 1989, p. 877 (price functions, reduced costs, Eq. (5), ε(f)) and p. 879 (ε-fixed arcs)

import Mathlib
import Definitions.Def_CycleCanceling_MinMean_Network

namespace CycleCanceling.MinMean

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Reduced cost `c_p(v, w) = c(v, w) + p(v) - p(w)` for a price function `p : V → ℝ` (p. 877). -/
def reducedCost (N : CircNetwork V) (p : V → ℝ) (v w : V) : ℝ :=
  N.c v w + p v - p w

/-- `f` satisfies the `ε`-optimality constraints (5) with respect to the price function `p`:
`u_f(v, w) > 0 ⇒ c_p(v, w) ≥ -ε` for all `(v, w) ∈ E` (p. 877). -/
def IsEpsOptimalWrt (N : CircNetwork V) (f : V → V → ℝ) (ε : ℝ) (p : V → ℝ) : Prop :=
  ∀ v w, (v, w) ∈ N.E → 0 < resCap N f v w → -ε ≤ reducedCost N p v w

/-- For `ε ≥ 0`, a circulation `f` is `ε`-optimal if there is a price function `p` with respect
to which it satisfies the `ε`-optimality constraints (5) (p. 877). -/
def IsEpsOptimal (N : CircNetwork V) (f : V → V → ℝ) (ε : ℝ) : Prop :=
  IsCirculation N f ∧ 0 ≤ ε ∧ ∃ p : V → ℝ, IsEpsOptimalWrt N f ε p

/-- `ε(f)`, the minimum `ε` such that the circulation `f` is `ε`-optimal (p. 877), as the
infimum of the set of such `ε`. For a circulation this set is nonempty and bounded below by `0`. -/
noncomputable def epsOpt (N : CircNetwork V) (f : V → V → ℝ) : ℝ :=
  sInf {ε : ℝ | IsEpsOptimal N f ε}

/-- An arc `(v, w)` is `ε`-fixed (p. 879) if the flow through it is the same for all
`ε`-optimal circulations. -/
def IsEpsFixed (N : CircNetwork V) (ε : ℝ) (v w : V) : Prop :=
  ∀ g g' : V → V → ℝ, IsEpsOptimal N g ε → IsEpsOptimal N g' ε → g v w = g' v w

end CycleCanceling.MinMean


