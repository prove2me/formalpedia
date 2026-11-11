-- Prove2me | Definitions.Def_RobustKZClust_Main_Cost
-- name    : RobustKZClust_Main_Cost
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:10:55.916039+00:00
-- url     : https://prove2.me/theorems/1bd02dd3-bd7f-4dd4-b99b-c965ab750777
-- title:
--   Euclidean (k, z)-clustering cost of a weight vector, opt, the grid [∆]^d, and ε-oracles
-- statement:
--   Fix a dimension $d$ and an integer $z \ge 1$. Points live in $\mathbb R^d$ with the Euclidean distance $\mathrm{dist}(x,y)=\|x-y\|_2$. For a nonempty finite **center set** $C\subseteq\mathbb R^d$, $\mathrm{dist}(x,C)=\min_{c\in C}\mathrm{dist}(x,c)$.
--
--   A dataset is a **weight (frequency) vector** $\mu$: a finitely supported function $\mathbb R^d\to\mathbb R$, where $\mu_x$ is the number of copies of $x$ (repeated points are multiplicities; real and negative weights are allowed where a statement needs them). Its $(k,z)$-clustering **cost** is
--
--   $$\mathrm{cost}(\mu,C)=\sum_{x}\mu_x\,\mathrm{dist}(x,C)^z .$$
--
--   A center set is **admissible** if it is nonempty and has at most $k$ points, and for $\mu\ge0$
--
--   $$\mathrm{opt}(\mu)=\min_{C\subseteq\mathbb R^d,\ 1\le|C|\le k}\mathrm{cost}(\mu,C).$$
--
--   The input grid is $X=[\Delta]^d$ with $[\Delta]=\{1,\dots,\Delta\}$. Given $\varepsilon\in(0,1)$, a function $\widehat{\mathrm{cost}}$ on center sets is an **$\varepsilon$-oracle** for $\mu$ (Definition 1.2) if
--
--   $$(1-\varepsilon)\,\mathrm{cost}(\mu,C)\le\widehat{\mathrm{cost}}(C)\le(1+\varepsilon)\,\mathrm{cost}(\mu,C)\quad\text{for every nonempty } C\subseteq\mathbb R^d,\ |C|\le k.$$
--
--   These are the objects every statement of the mission is about: $k$-Median is $z=1$, $k$-Means is $z=2$.
--
--   **Formalization Note.** Points are `EuclideanSpace ℝ (Fin d)`; integer points are embedded by `gridPt`. `distSet x C` is the minimum over a nonempty `Finset` (its value `0` on the empty set is never used: every statement requires $C$ nonempty). `opt` is the infimum (`sInf`) of the costs of admissible center sets; for $k\ge1$ and $\mu\ge0$ this set is nonempty and bounded below by $0$. The paper's $\min$ over "$|C|\le k$" is read over nonempty $C$, since $\mathrm{dist}(x,\emptyset)$ is undefined.
-- source:
--   Guo, Jiang, Krauthgamer, Xie, Zhou, Adversarially Robust Streaming Algorithms for (k, z)-Clustering, STOC 2027 submission (manuscript sha256 7d9aadba…), p. 1 (cost), p. 2 Definition 1.2, p. 13 §2 (cost(λ, C), opt, X = [∆]^d)

import Mathlib

namespace RobustKZClust.Main

/-! Euclidean `(k, z)`-clustering costs of weighted point sets (§1, p. 1; §2, p. 13 of Guo, Jiang,
Krauthgamer, Xie, Zhou, *Adversarially Robust Streaming Algorithms for (k, z)-Clustering*),
`opt`, the input grid `X = [∆]^d`, and ε-oracles (Definition 1.2, p. 2). -/

/-- Euclidean space `ℝ^d` with the Euclidean distance. -/
abbrev Pt (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The point of `ℝ^d` with the given integer coordinates. -/
noncomputable def gridPt {d : ℕ} (x : Fin d → ℤ) : Pt d :=
  WithLp.toLp 2 (fun i => (x i : ℝ))

/-- The input grid `X = [∆]^d`, `[∆] = {1, …, ∆}`, as a set of points of `ℝ^d`. -/
def grid (d Δ : ℕ) : Set (Pt d) :=
  {p | ∃ x : Fin d → ℤ, (∀ i, 1 ≤ x i ∧ x i ≤ (Δ : ℤ)) ∧ p = gridPt x}

/-- `dist(x, C) = min_{c ∈ C} ‖x − c‖` for a nonempty finite center set `C`
(the value `0` on the empty set is never used: every statement requires `C` nonempty). -/
noncomputable def distSet {d : ℕ} (x : Pt d) (C : Finset (Pt d)) : ℝ :=
  if h : C.Nonempty then C.inf' h (fun c => dist x c) else 0

/-- `cost(µ, C) = ∑_x µ_x · dist(x, C)^z` for a finitely supported real weight vector `µ`
on `ℝ^d` (a frequency vector; repeated points are multiplicities). -/
noncomputable def cost {d : ℕ} (z : ℕ) (μ : Pt d →₀ ℝ) (C : Finset (Pt d)) : ℝ :=
  μ.sum (fun x w => w * distSet x C ^ z)

/-- The admissible center sets: nonempty finite subsets of `ℝ^d` with at most `k` points. -/
def Admissible {d : ℕ} (k : ℕ) (C : Finset (Pt d)) : Prop :=
  C.Nonempty ∧ C.card ≤ k

/-- `opt(µ) = min_{C ⊆ ℝ^d, 1 ≤ |C| ≤ k} cost(µ, C)`, written as the infimum of the costs of the
admissible center sets (nonempty and bounded below by `0` when `k ≥ 1` and `µ ≥ 0`). -/
noncomputable def opt {d : ℕ} (k z : ℕ) (μ : Pt d →₀ ℝ) : ℝ :=
  sInf {r | ∃ C : Finset (Pt d), Admissible k C ∧ r = cost z μ C}

/-- `f` is an ε-oracle for the weight vector `µ` (Definition 1.2): for every nonempty
`C ⊆ ℝ^d` with `|C| ≤ k`, `(1 − ε) cost(µ, C) ≤ f(C) ≤ (1 + ε) cost(µ, C)`. -/
def IsOracle {d : ℕ} (k z : ℕ) (ε : ℝ) (μ : Pt d →₀ ℝ) (f : Finset (Pt d) → ℝ) : Prop :=
  ∀ C : Finset (Pt d), Admissible k C →
    (1 - ε) * cost z μ C ≤ f C ∧ f C ≤ (1 + ε) * cost z μ C

end RobustKZClust.Main


