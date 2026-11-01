-- Prove2me | Definitions.Def_DRSubmodHull_Zset
-- name    : DRSubmodHull_Zset
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:23:38.433584+00:00
-- url     : https://prove2.me/theorems/39373fad-dacb-4118-9246-763fed5043e4
-- title:
--   Directed rooted forests, standing conditions, the mixed-integer set $\mathcal Z(\mathcal G,u)$ and the epigraph $\mathcal P_f$
-- statement:
--   1. A **directed rooted forest** on a finite vertex set $\mathcal V$ is an arc set $\mathcal A$ in which every vertex has at most one parent and there is no directed cycle; equivalently a disjoint union of directed rooted trees with all arcs pointing away from the roots. $R^+(i)$ (descendants) and $R^-(i)$ (ascendants) both contain $i$.
--   2. The **standing conditions** on $(\mathcal G,N,u)$ (pp.4–5): $\mathcal G$ is a directed rooted forest, $u_i\in\mathbb Z$ for every integer variable $i\in N$, $u_i>0$ for all $i$, and $u_i\le u_j$ for every arc $(i,j)\in\mathcal A$.
--   3. The **feasible set** (eq. (2))
--   $$
--   \mathcal Z(\mathcal G,u)=\{z\in\mathbb R^{\mathcal V}: z_i\in\mathbb Z\ (i\in N),\ 0\le z\le u,\ z_i\le z_j\ \forall (i,j)\in\mathcal A\}.
--   $$
--   4. The **epigraph** of $f$ over it (p.4)
--   $$
--   \mathcal P_f^{\mathcal Z(\mathcal G,u)}=\{(z,w)\in\mathcal Z(\mathcal G,u)\times\mathbb R : w\ge f(z)\}.
--   $$
--
--   These are the objects of the paper's problem $\min_{z\in\mathcal Z(\mathcal G,u)} f(z)$, a DR-submodular minimization under box and monotonicity constraints with integer and continuous variables.
--
--   **Formalization Note** Arcs are a relation `A : V → V → Prop`; $N$ is any subset of $V$ (the paper lists the integer variables first). The upper bounds are real numbers, the paper's reduction to $u<\infty$ on p.5. The page prints $\mathcal Z(\mathcal G,z)$ in the epigraph, a typo for $\mathcal Z(\mathcal G,u)$.
-- source:
--   Yu, Küçükyavuz, On Constrained Mixed-Integer DR-Submodular Minimization, arXiv:2211.07726v2 (preprint, 5 Sep 2023), https://arxiv.org/abs/2211.07726v2, §2, pp.3–5, eq. (2) and the epigraph on p.4

import Mathlib

set_option autoImplicit false

namespace DRSubmodHull

/-- **Directed rooted forest** (arXiv:2211.07726v2, §2, p.4): a disjoint union of directed rooted
trees whose arcs all point away from the roots.

**Formalization Note.** The arc set `𝒜 ⊆ 𝒱 × 𝒱` is a relation `A : V → V → Prop` (`A i j` is the
arc `(i, j)`). On a finite vertex set, "every vertex has at most one parent and there is no directed
cycle" is equivalent to the paper's definition: following parents from any vertex ends at a root,
and an undirected cycle in which every vertex has in-degree at most one is a directed cycle.
The descendants `R⁺(i)` are `{j | Relation.ReflTransGen A i j}` and the ascendants `R⁻(i)` are
`{j | Relation.ReflTransGen A j i}` (both contain `i`, as on p.4). -/
def IsDirectedRootedForest {V : Type*} (A : V → V → Prop) : Prop :=
  (∀ i i' j : V, A i j → A i' j → i = i') ∧ (∀ i : V, ¬ Relation.TransGen A i i)

/-- **Standing conditions on the data** (arXiv:2211.07726v2, §2, pp.4–5): `𝒢 = (V, A)` is a directed
rooted forest; `u_i ∈ ℤ` for every integer variable `i ∈ N`; `u_i > 0` for every `i`; and
`u_i ≤ u_j` for every arc `(i, j)`. (The fifth standing condition, `f(0) = 0`, is a hypothesis on
`f` and is stated separately.)

**Formalization Note.** `u : V → ℝ` is finite: the paper's reduction to `u_i < ∞` (p.5) is built
into the type. `N : Set V` is the set of integer coordinates (the paper lists them first,
`z ∈ ℤⁿ × ℝᵐ`); `M = Nᶜ`. `V`, `N` and `Nᶜ` may each be empty ("We allow n or m to be zero"). -/
def StandingConditions {V : Type*} (A : V → V → Prop) (N : Set V) (u : V → ℝ) : Prop :=
  IsDirectedRootedForest A ∧ (∀ i ∈ N, ∃ k : ℤ, u i = k) ∧ (∀ i : V, 0 < u i) ∧
    (∀ i j : V, A i j → u i ≤ u j)

/-- **The mixed-integer feasible set** `𝒵(𝒢, u)` (arXiv:2211.07726v2, §2, p.3, eq. (2)):
`{z ∈ ℤⁿ × ℝᵐ : 0 ≤ z ≤ u, z_i ≤ z_j ∀ (i, j) ∈ 𝒜}`, i.e. the vectors `z : V → ℝ` whose
coordinates in `N` are integers, with `0 ≤ z ≤ u` and `z` monotone along every arc. -/
def Zset {V : Type*} (A : V → V → Prop) (N : Set V) (u : V → ℝ) : Set (V → ℝ) :=
  {z | (∀ i ∈ N, ∃ k : ℤ, z i = k) ∧ 0 ≤ z ∧ z ≤ u ∧ ∀ i j : V, A i j → z i ≤ z j}

/-- **The epigraph** `𝒫_f^{𝒵(𝒢,u)} := {(z, w) ∈ 𝒵(𝒢, u) × ℝ : w ≥ f(z)}` (arXiv:2211.07726v2, §2,
p.4; the page prints `𝒵(𝒢, z)`, a typo for `𝒵(𝒢, u)`). -/
def epigraph {V : Type*} (A : V → V → Prop) (N : Set V) (u : V → ℝ) (f : (V → ℝ) → ℝ) :
    Set ((V → ℝ) × ℝ) :=
  {p | p.1 ∈ Zset A N u ∧ f p.1 ≤ p.2}

end DRSubmodHull


