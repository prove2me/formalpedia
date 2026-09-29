-- Prove2me | Definitions.Def_LovaszSchrijver_NPlus_StableSet
-- name    : LovaszSchrijver_NPlus_StableSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:58:12.054614+00:00
-- url     : https://prove2.me/theorems/fe07fed3-d429-4158-a8e6-ac06351df50e
-- title:
--   STAB(G), FRAC(G), FR(G), the relaxations N₊ʳ(G), valid inequalities and contraction (Sections 2.a–2.b)
-- statement:
--   Let $G = (V, E)$ be a finite graph. For $A \subseteq V$, $\chi^A \in \mathbb R^V$ denotes its incidence vector.
--
--   1. **Stable set polytope** (p. 175): $\mathrm{STAB}(G) = \mathrm{conv}\{\chi^A : A \text{ is stable}\}$.
--   2. **Fractional stable set polytope** (p. 175): $\mathrm{FRAC}(G)$ is the solution set of (1) $x_i \ge 0$ for each $i \in V$ and (2) $x_i + x_j \le 1$ for each $ij \in E$.
--   3. **The cone** $\mathrm{FR}(G) \subseteq \mathbb R^{V \cup \{0\}}$ (p. 177), "determined by the constraints" $x_i \ge 0$ for each $i \in V$ and $x_i + x_j \le x_0$ for each $ij \in E$.
--   4. **The relaxations** (p. 177): "we shall use the notation $N(\mathrm{FRAC}(G)) = N(\mathrm{FR}(G)) \cap H_0$, and similarly for $N_+$", where $H_0$ is the hyperplane $x_0 = 1$. So
--   $$N_+^r(G) = \{x \in \mathbb R^V : (1, x) \in N_+^r(\mathrm{FR}(G))\}.$$
--   In particular $N_+^0(G) = \mathrm{FRAC}(G)$.
--   5. **Valid inequality.** $a^{\mathsf T}x \le b$ (with $a \in \mathbb R^V$, $b \in \mathbb R$) is valid for $S \subseteq \mathbb R^V$ if $\sum_i a_i x_i \le b$ for every $x \in S$.
--   6. **Contraction** (p. 177). If $a^{\mathsf T}x \le b$ is valid for $\mathrm{STAB}(G)$, then $a_{V-\Gamma(v)-v}^{\mathsf T}x \le b - a_v$ is valid for $\mathrm{STAB}(G - \Gamma(v) - v)$; this inequality "arises from $a^{\mathsf T}x \le b$ by the contraction of node $v$". Here $\Gamma(v)$ is the neighbourhood of $v$. It is written on the same graph $G$: the coefficient vector $a'$ with $a'_w = 0$ for $w = v$ and for $w \in \Gamma(v)$, and $a'_w = a_w$ otherwise, with right-hand side $b - a_v$.
--
--   The $N_+$-index of an inequality valid for $\mathrm{STAB}(G)$ (p. 179) is the least $r$ for which it is valid for $N_+^r(G)$.
--
--   **Formalization Note** $\mathrm{FR}(G)$ is defined by its constraints. The page defines it as the cone spanned by the vectors $(1, x)$ with $x \in \mathrm{FRAC}(G)$; the two agree because $G$ has no isolated nodes, the standing assumption of Section 2, which every theorem using these objects carries as a hypothesis. The coordinate $x_0$ is `none` in `Option V`, and $(1,x)$ is `hom x`. The contraction is stated on the same graph $G$ as a zeroed coefficient vector: an inequality with zero coefficients outside $W$ is valid for $\mathrm{STAB}(G)$ exactly when its restriction to $W$ is valid for $\mathrm{STAB}(G[W])$, and the same-graph form avoids subgraphs with isolated nodes.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), pp. 175, 177, 179, Sections 2.a–2.c

import Mathlib
import Definitions.Def_LovaszSchrijver_NPlus_MatrixCone

namespace LovaszSchrijver.NPlus

/-- The incidence vector `χ^A ∈ ℝ^V` of a set `A ⊆ V`. -/
def chi {V : Type} [DecidableEq V] (A : Finset V) : V → ℝ :=
  fun i => if i ∈ A then 1 else 0

/-- `STAB(G) = conv{χ^A : A is stable}` (p. 175). -/
def STAB {V : Type} [DecidableEq V] (G : SimpleGraph V) : Set (V → ℝ) :=
  convexHull ℝ {x | ∃ A : Finset V, G.IsIndepSet (A : Set V) ∧ x = chi A}

/-- `FRAC(G)`: the solution set of (1) `xᵢ ≥ 0` for `i ∈ V` and (2) `xᵢ + xⱼ ≤ 1` for
`ij ∈ E` (p. 175). -/
def FRAC {V : Type} (G : SimpleGraph V) : Set (V → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∀ i j, G.Adj i j → x i + x j ≤ 1}

/-- `FR(G) ⊆ ℝ^{V ∪ {0}}`, given by the constraints `xᵢ ≥ 0` for `i ∈ V` and
`xᵢ + xⱼ ≤ x₀` for `ij ∈ E` (p. 177). Coordinate `none` is `x₀`. -/
def FR {V : Type} (G : SimpleGraph V) : Set (Option V → ℝ) :=
  {x | (∀ i, 0 ≤ x (some i)) ∧ ∀ i j, G.Adj i j → x (some i) + x (some j) ≤ x none}

/-- Homogenization `x ↦ (1, x)`: the vector with `x₀ = 1` and `xᵢ` for `i ∈ V`. -/
def hom {V : Type} (x : V → ℝ) : Option V → ℝ :=
  fun o => o.elim 1 x

/-- `N₊ʳ(G) = N₊ʳ(FR(G)) ∩ H₀` in the original coordinates (p. 177): the `x ∈ ℝ^V` with
`(1, x) ∈ N₊ʳ(FR(G))`. -/
def NplusG {V : Type} [Fintype V] [DecidableEq V] (r : ℕ) (G : SimpleGraph V) :
    Set (V → ℝ) :=
  {x | hom x ∈ NplusIter r (FR G)}

/-- The inequality `aᵀx ≤ b` is valid for `S`. -/
def Valid {V : Type} [Fintype V] (S : Set (V → ℝ)) (a : V → ℝ) (b : ℝ) : Prop :=
  ∀ x ∈ S, ∑ i, a i * x i ≤ b

/-- Coefficient vector of the contraction of node `v` (p. 177), written on the same graph:
the coefficients of `v` and of its neighbours are set to `0` (the right-hand side becomes
`b - a v`). -/
def contractCoeff {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq V]
    (a : V → ℝ) (v : V) : V → ℝ :=
  fun w => if w = v ∨ G.Adj v w then 0 else a w

end LovaszSchrijver.NPlus


