-- Prove2me | Definitions.Def_GeneralizedUniformServer_UnitWeights_Supplement_Weighted
-- name    : GeneralizedUniformServer_UnitWeights_Supplement_Weighted
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:39:25.163196+00:00
-- url     : https://prove2.me/theorems/b812d69e-313c-40bf-9ba9-989ea2427f43
-- title:
--   Weighted uniform metrics $d_w$, the weighted offline optimum $\mathrm{OPT}_w$ and the expected weighted cost
-- statement:
--   Let the distinct points of $M_i$ be at distance $w_i\ge0$. Moving the servers from $x$ to $y$ costs
--   $$d_w(x,y)=\sum_{i=1}^k w_i\,\mathbf 1[x_i\ne y_i].$$
--   For a finite request sequence $\rho=(r_1,\dots,r_T)$ of tuples $r_t\in X$, an offline solution $o_0,\dots,o_T$ (with $o_t$ serving $r_t$ for $t\ge1$) costs $\sum_{t=1}^T d_w(o_{t-1},o_t)$, and
--   $$\mathrm{OPT}_w(\rho)=\min\Bigl\{\textstyle\sum_{t=1}^T d_w(o_{t-1},o_t): o\text{ an offline solution with } o_0=a\Bigr\}.$$
--   For a randomized online algorithm $A$ started at $a$, $\mathbb E[\mathrm{ALG}_w(\rho)]$ is the expectation of $\sum_{t=1}^T d_w(X_{t-1},X_t)$ under its trajectory law.
--
--   These are the weighted objects of §2 used by Theorem 1.3; with all $w_i=1$ they reduce to the unit-weight model.
--
--   **Formalization Note** Weights are `Fin k → ℝ≥0`, which encodes $w_i\ge0$. $\mathrm{OPT}_w$ is an infimum in $[0,\infty]$ over all offline solutions from $a$. For $k\ge1$ the feasible set is nonempty ($o_t=r_t$) and the cost of a $T$-step solution takes finitely many values (sums of the $w_i$), so the infimum is attained and is the minimum; an empty feasible set, possible only for $k=0$, would give $+\infty$ rather than a default $0$. Requests, service and offline solutions are the published model's.
-- source:
--   Junho Hwang, STOC 2027 submission #428 (October 2026), pp. 7–8, §2 (weighted cost $d_w$, offline solutions, OPT)

import Mathlib
import Definitions.Def_GeneralizedUniformServer_UnitWeights_Supplement_Online

open scoped NNReal

noncomputable section

namespace GeneralizedUniformServer.UnitWeights.Supplement

variable {k : ℕ} {M : Fin k → Type*}

/-- The weighted movement cost (source §2, p. 7): `d_w(x, y) = ∑ᵢ wᵢ · 1[xᵢ ≠ yᵢ]`, where
distinct points of `Mᵢ` are at distance `wᵢ ≥ 0`. -/
def wdist (w : Fin k → ℝ≥0) (x y : Config M) : ℝ≥0 := by
  classical
  exact ∑ i : Fin k, if x i ≠ y i then w i else 0

/-- Weighted movement cost of a reversed trajectory `[X_t, …, X₀]`: `∑ d_w(X_{s-1}, X_s)`. -/
def wPathCost (w : Fin k → ℝ≥0) : List (Config M) → ℝ≥0
  | x :: y :: rest => wdist w y x + wPathCost w (y :: rest)
  | _ => 0

/-- The weighted cost `∑_{t=1}^T d_w(o_{t-1}, o_t)` of an offline solution (source §2, p. 8). -/
def wOfflineCost (w : Fin k → ℝ≥0) (ρ : List (Config M))
    (o : Fin (ρ.length + 1) → Config M) : ℝ≥0 :=
  ∑ s : Fin ρ.length, wdist w (o s.castSucc) (o s.succ)

/-- `OPT_w(ρ)` (source §2, p. 8): the least weighted cost of an offline solution with `o₀ = a`,
over all offline solutions. Taken in `ℝ≥0∞`: for `k ≥ 1` the feasible set is nonempty
(`o_t = r_t`) and the cost takes finitely many values, so the infimum is attained and is the
minimum; an empty feasible set (only possible for `k = 0`) gives `⊤`, never a default `0`. -/
def optCostW (w : Fin k → ℝ≥0) (a : Config M) (ρ : List (Config M)) : ENNReal :=
  ⨅ (o : Fin (ρ.length + 1) → Config M) (_ : IsOfflineSolution ρ o) (_ : o 0 = a),
    ((wOfflineCost w ρ o : ℝ≥0) : ENNReal)

/-- `E[ALG_w(ρ)]`: the expected weighted movement cost of `A` on the whole finite sequence
`ρ`, under the joint trajectory law, computed in `ℝ≥0∞`. -/
def genExpectedCostW (w : Fin k → ℝ≥0) (A : GenOnlineAlg M (Config M)) (a : Config M)
    (ρ : List (Config M)) : ENNReal :=
  ∑' p : List (Config M), genTrajLaw A a ρ ρ.length p * ((wPathCost w p : ℝ≥0) : ENNReal)

end GeneralizedUniformServer.UnitWeights.Supplement


