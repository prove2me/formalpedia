-- Prove2me | Definitions.Def_CompactRouting_Labeled_LevelLP
-- name    : CompactRouting_Labeled_LevelLP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:06:46.286205+00:00
-- url     : https://prove2.me/theorems/cb053d02-cbf4-40f9-a6f9-03db1bfa52bc
-- title:
--   The fallback level $\tau$, Algorithm 1's route for a level, $M$, $\Theta$, the LP (3) and the normalized-height properties
-- statement:
--   For a source $u$ and destination $v$ the **fallback level** is $\tau=\min\{i\in[k]:p_i(v)\in B(u)\}$. If the source picks level $i\in[\tau]$, Algorithm 1 routes $u\rightsquigarrow p_i(u)$ in the cluster tree $T(C(p_i(u)))$; if $v\in C(p_i(u))$ it continues $p_i(u)\rightsquigarrow v$ in the same tree, otherwise it returns $p_i(u)\rightsquigarrow u$ and takes the **fallback route** $u\rightsquigarrow v$ in $T(C(p_\tau(v)))$. We write
--   $$\mathrm{route}_i=\begin{cases}d(u,p_i(u))+d(p_i(u),v)&v\in C(p_i(u)),\\ d(u,p_i(u))+d(p_i(u),u)+d(u,p_\tau(v))+d(p_\tau(v),v)&\text{otherwise,}\end{cases}$$
--   the length of these legs with the fallback leg taken through the root $p_\tau(v)$ of its shortest-path tree; it is at least the length $\hat d(u,v)$ of the actual walk. The lower bound $M=\max\{h_1(v),\max_{0\le i<\tau}(h_{i+1}(u)-h_i(v)),\max_{1\le i\le\tau}|h_i(u)-h_i(v)|\}$ and the candidate set $\Theta=\{M\}\cup\{h_{i+1}(v)-h_i(u): i\in[\tau],\ h_{i+1}(v)-h_i(u)>M\}$ define the linear program (3)
--   $$z^*=\min\Big\{z\ \Big|\ \sum_{i\in[\tau]}\pi_i\big(2h_i(u)+2h_\tau(v)\,\mathbf 1[d\ge h_{i+1}(v)-h_i(u)]\big)\le z\,d\ \ \forall d\in\Theta,\ \pi\in\mathcal P([\tau])\Big\}.$$
--   Finally, `NormalizedHeights x y τ` is the list of properties of Lemma 21 for sequences $x_0,\dots,x_\tau$, $y_0,\dots,y_\tau$ with $H=y_\tau$: both nondecreasing, $x_0=y_0=0$, $0<H\le2\tau-1$, (N1) $x_1\le1$, $y_1\le1$, (N2) $x_{i+1}\le y_i+1$, (N3) $|x_i-y_i|\le1$, (N4) $0\le y_{i+1}-y_i\le2$.
--
--   **Formalization Note.** `IsFallbackLevel A p u v τ` characterizes the minimum ($\tau<k$, $p_\tau(v)\in B(u)$, $p_i(v)\notin B(u)$ for $i<\tau$). $\pi$ is a function $\mathbb N\to\mathbb R$ of which only $\pi_0,\dots,\pi_{\tau-1}$ matter. `lpValue` is the infimum of the feasible values $z$; under the standing assumptions of §4.2 the feasible set is nonempty, closed and bounded below by $0$ (because $M>0$), so it is the minimum $z^*$.
-- source:
--   Lifshitz, Chechik, Kadria, Roditty, Optimal (Randomized) Compact Routing Schemes, arXiv:2611.04744 (held version, sha256 d7e0fc67…), pp. 12–13 (§4.2, τ, Algorithm 1), p. 13 (§4.3, M, Θ), p. 14 (§4.4, LP (3)), p. 35 (Appendix B, Lemma 21)

import Mathlib
import Definitions.Def_CompactRouting_Labeled_Clusters

/-!
# The fallback level, Algorithm 1's route for a level, `M`, `Θ`, the LP (3) and the
normalized heights

Lifshitz, Chechik, Kadria, Roditty, *Optimal (Randomized) Compact Routing Schemes*,
arXiv:2611.04744 (held version, sha256 d7e0fc67…), §4.2 p. 12 (fallback level `τ`,
Algorithm 1 p. 13), §4.3 p. 13 (`M`, `Θ`), §4.4 p. 14 (LP (3)), Appendix B p. 35
(normalized heights `x_i`, `y_i`, `H`, Lemma 21's list (N1)–(N4)).

Conventions.
* `IsFallbackLevel A p u v τ` characterizes `τ = min{i ∈ [k] | p_i(v) ∈ B(u)}`.
* `levelRoute A p u v τ i` is the length of Algorithm 1's legs when the source picks level `i`:
  `u ⇝ p_i(u)` (to the root of `T(C(p_i(u)))`, length `d(u, p_i(u))`); then, if
  `v ∈ C(p_i(u))`, `p_i(u) ⇝ v` (from the root, length `d(p_i(u), v)`); otherwise
  `p_i(u) ⇝ u` (length `d(p_i(u), u)`) and the fallback `u ⇝ v` in `T(C(p_τ(v)))`, whose
  length is counted as `d(u, p_τ(v)) + d(p_τ(v), v)`, the length of the walk through the root
  `p_τ(v)`. In a shortest-path tree rooted at `w` the legs from and to the root have exactly
  these lengths, and the tree path `u ⇝ v` is at most the walk through the root; stopping at the
  first visit of `v` only shortens the walk. So `levelRoute` is an upper bound on `d̂(u, v)`.
* `M`, `Θ` and the LP use the real heights `height A i x = h_i(x)`; the indicator
  `1[d ≥ h_{i+1}(v) − h_i(u)]` is an `if`.
* `π : ℕ → ℝ` is a distribution on `[τ] = {0, …, τ − 1}` (its other values are ignored).
* `lpValue` is `z* = min{z | (π, z) feasible}`: the feasible set is nonempty and, under the
  standing assumptions of §4.2 (which give `M > 0`), bounded below by `0` and closed, so the
  infimum is the minimum.
-/

namespace CompactRouting.Labeled

open TZLevelsADO

variable {G : Graph} {k : ℕ}

/-- §4.2, p. 12: `τ = min{i ∈ [k] | p_i(v) ∈ B(u)}`, the fallback level. -/
def IsFallbackLevel (A : Hierarchy G k) (p : ℕ → Fin G.n → Fin G.n) (u v : Fin G.n)
    (τ : ℕ) : Prop :=
  τ < k ∧ p τ v ∈ bunch A u ∧ ∀ i < τ, p i v ∉ bunch A u

/-- §4.2, Algorithm 1, pp. 12–13: the length of the route of Algorithm 1 when the source picks
the level `i ∈ [τ]`, with the fallback leg measured through the root `p_τ(v)` of its tree (an
upper bound on the tree path; see the module note). -/
noncomputable def levelRoute (A : Hierarchy G k) (p : ℕ → Fin G.n → Fin G.n) (u v : Fin G.n)
    (τ i : ℕ) : ℝ := by
  classical
  exact if v ∈ cluster A (p i u) then dist G u (p i u) + dist G (p i u) v
    else dist G u (p i u) + dist G (p i u) u + (dist G u (p τ v) + dist G (p τ v) v)

/-- §4.3, p. 13: `M = max{h_1(v), max_{0≤i<τ}(h_{i+1}(u) − h_i(v)), max_{1≤i≤τ}|h_i(u) − h_i(v)|}`. -/
noncomputable def lowerM (A : Hierarchy G k) (u v : Fin G.n) (τ : ℕ) : ℝ := by
  classical
  exact (insert (height A 1 v)
      ((Finset.range τ).image (fun i => height A (i + 1) u - height A i v) ∪
        (Finset.Icc 1 τ).image (fun i => |height A i u - height A i v|))).max'
    (Finset.insert_nonempty _ _)

/-- §4.3, p. 13: `Θ = {M} ∪ {h_{i+1}(v) − h_i(u) | i ∈ [τ], h_{i+1}(v) − h_i(u) > M}`. -/
noncomputable def thetaSet (A : Hierarchy G k) (u v : Fin G.n) (τ : ℕ) : Finset ℝ := by
  classical
  exact insert (lowerM A u v τ)
    (((Finset.range τ).filter fun i => lowerM A u v τ < height A (i + 1) v - height A i u).image
      fun i => height A (i + 1) v - height A i u)

/-- §4.4, p. 14: the left side of the constraint of (3) for the possible distance `d`:
`∑_{i∈[τ]} π_i (2h_i(u) + 2h_τ(v)·1[d ≥ h_{i+1}(v) − h_i(u)])`. -/
noncomputable def lpCost (A : Hierarchy G k) (u v : Fin G.n) (τ : ℕ) (π : ℕ → ℝ) (d : ℝ) :
    ℝ := by
  classical
  exact ∑ i ∈ Finset.range τ, π i *
    (2 * height A i u + 2 * height A τ v * (if height A (i + 1) v - height A i u ≤ d then 1 else 0))

/-- §4.4, p. 14: `(π, z)` is feasible for (3): `π ∈ P([τ])` and the constraint holds for
every `d ∈ Θ`. -/
def LPFeasible (A : Hierarchy G k) (u v : Fin G.n) (τ : ℕ) (π : ℕ → ℝ) (z : ℝ) : Prop :=
  (∀ i < τ, 0 ≤ π i) ∧ (∑ i ∈ Finset.range τ, π i) = 1 ∧
    ∀ d ∈ thetaSet A u v τ, lpCost A u v τ π d ≤ z * d

/-- §4.4, p. 14, (3): the value `z*` of the linear program. -/
noncomputable def lpValue (A : Hierarchy G k) (u v : Fin G.n) (τ : ℕ) : ℝ :=
  sInf {z : ℝ | ∃ π : ℕ → ℝ, LPFeasible A u v τ π z}

/-- Appendix B, p. 35, Lemma 21: the list of properties of normalized heights
`x_0, …, x_τ`, `y_0, …, y_τ` with `H = y_τ`: nondecreasing, `x_0 = y_0 = 0`, `0 < H ≤ 2τ − 1`,
(N1) `x_1 ≤ 1` and `y_1 ≤ 1`, (N2) `x_{i+1} ≤ y_i + 1` (`0 ≤ i < τ`), (N3) `|x_i − y_i| ≤ 1`
(`0 ≤ i ≤ τ`), (N4) `0 ≤ y_{i+1} − y_i ≤ 2` (`0 ≤ i < τ`). -/
structure NormalizedHeights (x y : ℕ → ℝ) (τ : ℕ) : Prop where
  x_mono : ∀ i < τ, x i ≤ x (i + 1)
  y_mono : ∀ i < τ, y i ≤ y (i + 1)
  x_zero : x 0 = 0
  y_zero : y 0 = 0
  H_pos : 0 < y τ
  H_le : y τ ≤ 2 * (τ : ℝ) - 1
  N1 : x 1 ≤ 1 ∧ y 1 ≤ 1
  N2 : ∀ i < τ, x (i + 1) ≤ y i + 1
  N3 : ∀ i ≤ τ, |x i - y i| ≤ 1
  N4 : ∀ i < τ, 0 ≤ y (i + 1) - y i ∧ y (i + 1) - y i ≤ 2

end CompactRouting.Labeled


