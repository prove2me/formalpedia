-- Prove2me | Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ConsecutiveChains
-- name    : ConsistentSubmodular_Randomized_AdaptivityGap_ConsecutiveChains
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:08:14.563203+00:00
-- url     : https://prove2.me/theorems/b488806f-627b-4bbd-96bb-fdde7c225aa9
-- title:
--   Edge value, two-edge ratio, collapse bound and descending chains for nonincreasing consecutive intervals
-- statement:
--   With $q=(1-\xi^\star)/\xi^\star$ (`qStar`), the following real functions and sets are used to bound the adaptivity gap of nonincreasing consecutive intervals with the equalizing distribution.
--
--   - `edgeValue` $x\,y$: $\varphi(x,y)=1-\dfrac yx-q\,(x-1)$.
--   - `twoEdgeRatio` $x\,y$: $R(x,y)=\dfrac{2-y/x-1/y}{x+y-1}$ (division by zero follows the Lean convention $a/0=0$).
--   - `ratioRegion`: the compact set $\{(x,y):1\le y\le x\le 8\}\subseteq\mathbb R^2$, which contains the maximum of $R$.
--   - `collapseBound`: $L=1/(1-q)$, the collapse threshold.
--   - `threeEdgeBound` $y$: $F(y)=3+3q-q\,y-2\sqrt{q\,y}-2\sqrt{q+1/y}$, the bound on three-edge chains through $y$.
--   - `chainValue` $L$: for a list $d_0,\dots,d_N$ of reals, $\sum_{j<N}\varphi(d_j,d_{j+1})$, and $0$ for lists of length at most one.
--   - `IsDescendingChain` $L$: the list is a chain $d_0\ge d_1\ge\dots\ge d_N=1$, i.e. consecutive entries are nonincreasing, every entry is at least $1$, and the last entry equals $1$.
--
--   These definitions encode the potential-function argument of Appendix A (Lemma 4): the adaptivity gap of an instance with interval lengths $d_0\ge\dots\ge d_N=1$ is expressed through the sum of edge values, which is then bounded using the two-edge ratio, the collapse threshold and the three-edge bound.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/ConsecutiveChains.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Constants

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Chains

/-- The edge value `φ(x, y) = 1 - y/x - q (x - 1)`. -/
def edgeValue (x y : ℝ) : ℝ := 1 - y / x - qStar * (x - 1)

/-- The ratio `R(x, y) = (2 - y/x - 1/y) / (x + y - 1)`. -/
def twoEdgeRatio (x y : ℝ) : ℝ := (2 - y / x - 1 / y) / (x + y - 1)

/-- The compact region `{1 ≤ y ≤ x ≤ 8}`, which contains the maximum of `R`. -/
def ratioRegion : Set (ℝ × ℝ) := {p | 1 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 8}

/-- The collapse threshold `L = 1/(1 - q)`. -/
def collapseBound : ℝ := 1 / (1 - qStar)

/-- The bound `F(y) = 3 + 3q - q y - 2 √(q y) - 2 √(q + 1/y)` on three-edge chains
through `y`. -/
def threeEdgeBound (y : ℝ) : ℝ :=
  3 + 3 * qStar - qStar * y - 2 * Real.sqrt (qStar * y) - 2 * Real.sqrt (qStar + 1 / y)

/-- The value `Σ_j φ(d_j, d_{j+1})` of the chain `d_0, ..., d_N`. -/
def chainValue : List ℝ → ℝ
  | x :: y :: rest => edgeValue x y + chainValue (y :: rest)
  | _ => 0

/-- A chain `d_0 ≥ d_1 ≥ ... ≥ d_N = 1`. -/
def IsDescendingChain (L : List ℝ) : Prop :=
  L.IsChain (fun a b => b ≤ a) ∧ (∀ w ∈ L, 1 ≤ w) ∧ L.getLast? = some 1

end ConsistentSubmodular.Chains

end


