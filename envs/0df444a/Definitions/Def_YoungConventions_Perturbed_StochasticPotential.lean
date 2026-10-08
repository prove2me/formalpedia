-- Prove2me | Definitions.Def_YoungConventions_Perturbed_StochasticPotential
-- name    : YoungConventions_Perturbed_StochasticPotential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T16:00:26.550467+00:00
-- url     : https://prove2.me/theorems/3349ce3e-5570-42ef-83e8-793bf0c8d7c6
-- title:
--   The potential $\gamma(z)$ (9), the class resistances $r_{ij}$ and the stochastic potential $\gamma_j$
-- statement:
--   Let $P^\varepsilon$ be a family of chains on the finite set $X$ with graph $G$ and resistances $r(x,y)$, and let $X_1, \dots, X_J$ be the recurrent communication classes of $P^0$.
--
--   1. A **path** in $G$ from $x$ to $y$ is a sequence $x = w_0, w_1, \dots, w_n = y$ with every $(w_k, w_{k+1})$ an edge of $G$; its resistance is $\sum_{k<n} r(w_k, w_{k+1})$.
--   2. For $i \ne j$, $r_{ij}$ is the least resistance among all directed paths in $G$ that begin in $X_i$ and end in $X_j$.
--   3. For $z \in X$, a **$z$-tree in $G$** is a spanning in-tree rooted at $z$ all of whose edges are edges of $G$, and the **potential** of $z$ is
--   $$\gamma(z) = \min_{T \in \mathcal T_z} \sum_{(x,y) \in T} r(x, y). \tag{9}$$
--   4. Let $\mathcal G$ be the complete directed graph on the classes $\{1, \dots, J\}$ with edge $(i, j)$ of weight $r_{ij}$. The **stochastic potential** of $X_j$ is
--   $$\gamma_j = \min_{\tau \in \mathcal T_j} \sum_{(i, i') \in \tau} r_{ii'},$$
--   the least total resistance of a $j$-tree in $\mathcal G$.
--
--   Theorem 4 characterizes the stochastically stable states as the states of the classes minimizing $\gamma_j$; Lemma 1 characterizes them through $\gamma(z)$, and Lemma 2 shows $\gamma(x) = \gamma_j$ for $x \in X_j$.
--
--   **Formalization Note** All three minima are infima in the extended reals `EReal`, where the infimum of an empty set is $+\infty$; no junk value $0$ arises. For a regular perturbation $G$ is strongly connected, so every path set and tree set is nonempty and every value is a finite nonnegative real. Trees are parent maps (edges $(v, \tau(v))$ point toward the root). $\gamma_j$ is computed on $\mathcal G$ with the weights $r_{ij}$, not defined as $\gamma(x)$ for some $x \in X_j$.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, Appendix, p. 78 (PDF p. 23): r_ij, the graph 𝒢, j-trees and γ_j, z-trees and γ(z) of (9)

import Mathlib
import Definitions.Def_YoungConventions_Perturbed_FiniteChain
import Definitions.Def_YoungConventions_Perturbed_InTree
import Definitions.Def_YoungConventions_Perturbed_RegularPerturbation

open Finset

namespace YoungConventions.Perturbed

/-!
The potential `γ(z)` of a state (9), the least resistances `r_ij` between recurrent classes, and
the stochastic potential `γ_j` of a recurrent class.
Young (1993), *The Evolution of Conventions*, Econometrica 61:57–84, Appendix, p. 78, PDF p. 23.

**Formalization Note.** All three quantities are minima of nonnegative resistances and take
values in `EReal`, where an infimum over an empty set is `⊤ = +∞` (no path or no tree means
infinite resistance), so no junk value `0` can arise. For a regular perturbation the graph `G`
is strongly connected (by (6) and (8)), so every set minimized over is nonempty and every value
is a finite real number; the sums never involve `⊥`.
-/

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- `w` is a directed path of length `n` from `x` to `y` in the graph `G` of the family `P`:
`w 0 = x`, `w n = y` and every step `(w k, w (k+1))`, `k < n`, is an edge of `G`. -/
def IsGPath (P : ℝ → Matrix X X ℝ) (x y : X) (n : ℕ) (w : ℕ → X) : Prop :=
  w 0 = x ∧ w n = y ∧ ∀ k < n, IsEdge P (w k) (w (k + 1))

/-- The resistance of a path: the sum `∑_{k<n} r(w k, w (k+1))` of its edge resistances. -/
noncomputable def pathResistance (P : ℝ → Matrix X X ℝ) (n : ℕ) (w : ℕ → X) : ℝ :=
  ∑ k ∈ range n, resistance P (w k) (w (k + 1))

/-- `r_ij` (Young 1993, Appendix, p. 78, PDF p. 23): the least resistance among all directed
paths in `G` that begin in the class `Ci` and end in the class `Cj`.

**Formalization Note.** An infimum in `EReal` over all `G`-paths (of any length) from a state of
`Ci` to a state of `Cj`; it is attained because resistances are nonnegative and a shortest path
may be taken simple. Used only for `Ci ≠ Cj`. -/
noncomputable def classResistance (P : ℝ → Matrix X X ℝ) (Ci Cj : Finset X) : EReal :=
  ⨅ (x ∈ Ci) (y ∈ Cj) (n : ℕ) (w : ℕ → X) (_ : IsGPath P x y n w),
    ((pathResistance P n w : ℝ) : EReal)

/-- `T` is a `z`-tree in `G` (Young 1993, Appendix, p. 78, PDF p. 23): a spanning in-tree rooted
at `z` (from every `x ≠ z` a unique directed path to `z`) all of whose edges `(x, T x)`, `x ≠ z`,
are edges of `G`. -/
def IsGTree (P : ℝ → Matrix X X ℝ) (z : X) (T : X → X) : Prop :=
  IsInTree z T ∧ ∀ x, x ≠ z → IsEdge P x (T x)

/-- The potential `γ(z)` of the state `z`, equation (9) (Young 1993, Appendix, p. 78, PDF p. 23):
$$\gamma(z) = \min_{T \in \mathcal T_z} \sum_{(x,y) \in T} r(x, y),$$
the least total resistance of a `z`-tree in `G`. -/
noncomputable def statePotential (P : ℝ → Matrix X X ℝ) (z : X) : EReal :=
  ⨅ (T : X → X) (_ : IsGTree P z T), ((∑ x ∈ univ.erase z, resistance P x (T x) : ℝ) : EReal)

/-- The stochastic potential `γ_j` of the recurrent class `X_j` of `P⁰` (Young 1993, Appendix,
p. 78, PDF p. 23): the least total resistance `∑_{(i,i') ∈ τ} r_{ii'}` of a `j`-tree `τ` in the
complete directed graph `𝒢` whose vertices are the recurrent classes of `P⁰` and whose edge
`(i, i')` has weight `r_{ii'}`.

**Formalization Note.** `j`-trees are parent maps on the class index type `RecClass P0` with
`IsInTree j τ`; their edges are `(i, τ i)`, `i ≠ j`. The set of `j`-trees is finite and nonempty
(the star `τ ≡ j`), so the infimum is a minimum. `γ_j` is defined on the reduced graph `𝒢` with
the weights `r_ij`, not as `γ(x)` for some `x ∈ X_j`: their equality is Lemma 2. -/
noncomputable def classPotential (P0 : Matrix X X ℝ) (P : ℝ → Matrix X X ℝ)
    (j : RecClass P0) : EReal :=
  ⨅ (τ : RecClass P0 → RecClass P0) (_ : IsInTree j τ),
    ∑ i ∈ univ.erase j, classResistance P i.1 (τ i).1

end YoungConventions.Perturbed


