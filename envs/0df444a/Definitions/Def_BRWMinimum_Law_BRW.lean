-- Prove2me | Definitions.Def_BRWMinimum_Law_BRW
-- name    : BRWMinimum_Law_BRW
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T23:43:03.900992+00:00
-- url     : https://prove2.me/theorems/4eec5b20-5452-400a-b46c-87b436c443a5
-- title:
--   Branching random walk on Ulam–Harris labels: positions V, minima Mₙ and Mₙ^kill, derivative martingale Dₙ, D_∞, 𝒵[A]
-- statement:
--   This file builds the branching random walk and the random quantities that the mission's theorems are about.
--
--   **The process.** Vertices are Ulam–Harris labels $u=(i_0,\dots,i_{k-1})$, finite words over $\{0,1,2,\dots\}$; $|u|=k$ is the generation and $u_j=(i_0,\dots,i_{j-1})$ the ancestor of $u$ at generation $j\le|u|$. On a probability space $(\Omega,\mathbf P)$ we are given a family $(\xi_u)_u$ of point configurations which is mutually independent, each $\xi_u$ measurable with law $L$; $\xi_u$ is the point process of the children of $u$. Then:
--
--   1. $u\in\mathbb T$ (the genealogical tree, a Galton–Watson tree) iff, for every $j<|u|$, $i_j$ is an index of a point of $\xi_{u_j}$;
--   2. the position started at $a\in\mathbb R$ is $V(u)=a+\sum_{j<|u|}(\text{position of point } i_j \text{ of } \xi_{u_j})$, so $V(\varnothing)=a$ and $(V(x),|x|=1)$ is $a+\mathcal L$.
--
--   **Derived quantities** (start $a$ where indicated, otherwise $0$):
--
--   - $M_n=\min\{V(x):|x|=n\}$, with $\min\varnothing=+\infty$;
--   - $\mathbb T^{\rm kill}=\{u\in\mathbb T: V(u_k)\ge0,\ \forall\,0\le k\le|u|\}$ and $M_n^{\rm kill}=\min\{V(u):u\in\mathbb T^{\rm kill},|u|=n\}$ (3.1);
--   - the derivative martingale (1.5) $D_n=\sum_{|x|=n}V(x)e^{-V(x)}$ and $D_\infty=\lim_n D_n$;
--   - non-extinction: every generation of $\mathbb T$ is nonempty;
--   - the particles absorbed at level $A$: $\mathcal Z[A]=\{u\in\mathbb T:V(u)\ge A,\ V(u_k)<A\ \forall k<|u|\}$;
--   - $C_1$ is **a constant of Proposition 1.2** if $\limsup_{z\to\infty}\limsup_{n\to\infty}\big|e^z\,\mathbf P\big(M_n^{\rm kill}<\tfrac32\ln n-z\big)-C_1\big|=0$.
--
--   **Formalization Note** Labels are `List ℕ`, a countable type, so every minimum and sum over vertices is over a countable set. $M_n$ and $M_n^{\rm kill}$ are infima in the extended reals, equal to $+\infty$ on an empty generation, matching $\min\varnothing=\infty$. $D_n$ and the sums over $\mathcal Z[A]$ are real `tsum`s: they are absolutely summable almost surely (by the many-to-one lemma, $\mathbf E\sum_{|x|=n}|V(x)|e^{-V(x)}=\mathbf E|S_n|<\infty$), and the junk value $0$ on a null set does not affect any almost-sure or probabilistic statement. $D_\infty$ is the pointwise `limUnder`; that the limit exists almost surely is a theorem of the mission, not an assumption. Proposition 1.2's iterated limsup is written in the equivalent $\varepsilon$–$Z$–$N$ form: for every $\varepsilon>0$ there is $Z$ such that for each $z\ge Z$ there is $N$ with the absolute value at most $\varepsilon$ for $n\ge N$.
-- source:
--   Aïdékon, Convergence in law of the minimum of a branching random walk, arXiv:1101.1810v6 (Ann. Probab. 41 (2013)), p. 1 §1 (model); p. 2 (Mₙ); p. 3 eq. (1.5), Proposition 1.2; pp. 11–12 eq. (3.1); p. 47 (𝒵[A])

import Mathlib
import Definitions.Def_BRWMinimum_Law_PointProcess

namespace BRWMinimum.Law

open MeasureTheory ProbabilityTheory Filter

/-- `ξ` realises the branching random walk with offspring law `L` on `(Ω, P)`:
`ξ u` is the point process of the children of the Ulam–Harris label `u : List ℕ`; the family
`(ξ u)_u` is measurable, mutually independent, and each `ξ u` has law `L`. -/
structure IsBRW {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : List ℕ → Ω → PointConfig) (L : Measure PointConfig) : Prop where
  measurable : ∀ u, Measurable (ξ u)
  indep : iIndepFun ξ P
  law : ∀ u, Measure.map (ξ u) P = L

variable {Ω : Type*}

/-- The label `u = [i₀, …, i_{k-1}]` is a vertex of the genealogical tree `𝕋`: for each
`j < |u|`, `i_j` is a child index of the ancestor `u_j = u.take j`. The root `[]` is always
in `𝕋`; `|u| = u.length` is the generation and `u.take k` the ancestor at generation `k`. -/
def InTree (ξ : List ℕ → Ω → PointConfig) (u : List ℕ) (ω : Ω) : Prop :=
  ∀ j : Fin u.length, ((u.get j : ℕ) : ℕ∞) < (ξ (u.take j) ω).1

/-- Position `V(u)` of the label `u` for the walk started at `a`:
`V([]) = a` and `V(u ++ [i]) = V(u) + (position of the i-th point of ξ u)`. -/
noncomputable def pos (ξ : List ℕ → Ω → PointConfig) (a : ℝ) (u : List ℕ) (ω : Ω) : ℝ :=
  a + ∑ j : Fin u.length, (ξ (u.take j) ω).2 (u.get j)

/-- The minimum at time `n`, `M_n = min{V(x), |x| = n}`, as an extended real
(`min ∅ = +∞`), for the walk started at `a`. -/
noncomputable def minPos (ξ : List ℕ → Ω → PointConfig) (a : ℝ) (n : ℕ) (ω : Ω) : EReal :=
  ⨅ (u : List ℕ) (_ : InTree ξ u ω ∧ u.length = n), ((pos ξ a u ω : ℝ) : EReal)

/-- `u ∈ 𝕋^kill`: `u ∈ 𝕋` and `V(u_k) ≥ 0` for every `0 ≤ k ≤ |u|` (walk started at `a`). -/
def InKilledTree (ξ : List ℕ → Ω → PointConfig) (a : ℝ) (u : List ℕ) (ω : Ω) : Prop :=
  InTree ξ u ω ∧ ∀ k ≤ u.length, 0 ≤ pos ξ a (u.take k) ω

/-- `M_n^kill = min{V(u), u ∈ 𝕋^kill, |u| = n}` (3.1), with `min ∅ = +∞`. -/
noncomputable def minPosKilled (ξ : List ℕ → Ω → PointConfig) (a : ℝ) (n : ℕ) (ω : Ω) : EReal :=
  ⨅ (u : List ℕ) (_ : InKilledTree ξ a u ω ∧ u.length = n), ((pos ξ a u ω : ℝ) : EReal)

/-- The derivative martingale (1.5), `D_n = Σ_{|x|=n} V(x) e^{-V(x)}`, for the walk started at 0
(a real `tsum` over the countable random set of generation-`n` vertices). -/
noncomputable def derivMart (ξ : List ℕ → Ω → PointConfig) (n : ℕ) (ω : Ω) : ℝ :=
  ∑' u : {u : List ℕ // InTree ξ u ω ∧ u.length = n},
    pos ξ 0 u.1 ω * Real.exp (-pos ξ 0 u.1 ω)

/-- `D_∞ := lim_{n→∞} D_n` (pointwise `limUnder`). -/
noncomputable def derivMartLim (ξ : List ℕ → Ω → PointConfig) (ω : Ω) : ℝ :=
  limUnder atTop (fun n : ℕ => derivMart ξ n ω)

/-- Non-extinction of `𝕋`: every generation is nonempty. -/
def Survives (ξ : List ℕ → Ω → PointConfig) (ω : Ω) : Prop :=
  ∀ n : ℕ, ∃ u : List ℕ, InTree ξ u ω ∧ u.length = n

/-- `𝒵[A] = {u ∈ 𝕋 : V(u) ≥ A, V(u_k) < A ∀ k < |u|}`, the particles absorbed at level `A`
(walk started at 0). -/
def absorbed (ξ : List ℕ → Ω → PointConfig) (A : ℝ) (ω : Ω) : Set (List ℕ) :=
  {u | InTree ξ u ω ∧ A ≤ pos ξ 0 u ω ∧ ∀ k < u.length, pos ξ 0 (u.take k) ω < A}

/-- `C₁` is a constant of Proposition 1.2:
`limsup_{z→∞} limsup_{n→∞} |e^z P(M_n^kill < (3/2) ln n − z) − C₁| = 0`, written in the
equivalent `ε`–`Z`–`N` form (walk started at 0). -/
def IsKilledTailConst [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : List ℕ → Ω → PointConfig) (C₁ : ℝ) : Prop :=
  ∀ ε > 0, ∃ Z : ℝ, ∀ z ≥ Z, ∃ N : ℕ, ∀ n ≥ N,
    |Real.exp z * (P {ω | minPosKilled ξ 0 n ω <
        (((3 / 2 : ℝ) * Real.log n - z : ℝ) : EReal)}).toReal - C₁| ≤ ε

end BRWMinimum.Law


