-- Prove2me | Definitions.Def_LovaszSchrijver_OddHole_StableSetCones
-- name    : LovaszSchrijver_OddHole_StableSetCones
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:45:25.941957+00:00
-- url     : https://prove2.me/theorems/2b51b039-a877-4e13-9832-1fca374a297b
-- title:
--   FRAC(G), its homogenization FR(G), the polytope N(G), and valid inequalities (Sections 2.a–2.b)
-- statement:
--   Let $G = (V, E)$ be a finite graph.
--
--   1. $\mathrm{FRAC}(G)$ (p. 175, "fractional stable sets") is the solution set in $\mathbb{R}^V$ of
--      $$x_i \ge 0 \ (i \in V), \qquad x_i + x_j \le 1 \ (ij \in E).$$
--   2. $\mathrm{FR}(G)$ (p. 177) is "the cone spanned by the vectors $(1, x)$, where $x \in \mathrm{FRAC}(G)$. Then $\mathrm{FR}(G)$ is determined by the constraints $x_i \ge 0$ for each $i \in V$, and $x_i + x_j \le x_0$ for each $ij \in E$." Here it is defined by these constraints, as a subset of $\mathbb{R}^{V \cup \{0\}}$.
--   3. The homogenization of $x \in \mathbb{R}^V$ is the vector $(1, x) \in \mathbb{R}^{V\cup\{0\}}$ with $0$th coordinate $1$.
--   4. $N(G) = N(\mathrm{FRAC}(G)) = N(\mathrm{FR}(G)) \cap H_0$, read in the original space (p. 177): the set of $x \in \mathbb{R}^V$ with $(1, x) \in N(\mathrm{FR}(G))$, where $N(K) = N(K, Q)$ is the projected matrix cone.
--   5. An inequality $a^{\mathsf T} x \le b$ ($a \in \mathbb{R}^V$, $b \in \mathbb{R}$) is **valid** for $S \subseteq \mathbb{R}^V$ if $\sum_{i \in V} a_i x_i \le b$ for every $x \in S$.
--
--   $N(G)$ is the relaxation of the stable set polytope obtained by one round of the $N$ operator applied to $\mathrm{FRAC}(G)$.
--
--   **Formalization Note** $\mathrm{FR}(G)$ is defined by its constraints. For a graph with at least one node and no isolated nodes (the paper's standing assumption in Section 2.a) the constraints imply $x_0 \ge 0$ and the constraint description coincides with the cone over $\mathrm{FRAC}(G)$; the theorems carry that assumption. Coordinates of $\mathbb{R}^{V \cup \{0\}}$ are indexed by `Option V`, with `none` the coordinate $x_0$.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 175, Section 2.a, (1)–(2); p. 177, Section 2.b

import Mathlib
import Definitions.Def_LovaszSchrijver_OddHole_MatrixCone

namespace LovaszSchrijver.OddHole

/-- `FRAC(G)` (p. 175): the solution set of `xᵢ ≥ 0` (i ∈ V) and `xᵢ + xⱼ ≤ 1` (ij ∈ E). -/
def FRAC {V : Type} (G : SimpleGraph V) : Set (V → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∀ i j, G.Adj i j → x i + x j ≤ 1}

/-- `FR(G)` (p. 177), given by its constraints: `xᵢ ≥ 0` for `i ∈ V` and
`xᵢ + xⱼ ≤ x₀` for `ij ∈ E`. Coordinates are `Option V`, with `none` the coordinate `x₀`. -/
def FR {V : Type} (G : SimpleGraph V) : Set (Option V → ℝ) :=
  {x | (∀ i, 0 ≤ x (some i)) ∧ ∀ i j, G.Adj i j → x (some i) + x (some j) ≤ x none}

/-- Homogenization `x ↦ (1, x)`: the vector of `ℝ^{V ∪ {0}}` with `x₀ = 1`. -/
def hom {V : Type} (x : V → ℝ) : Option V → ℝ :=
  fun o => o.elim 1 x

/-- `N(G) = N(FRAC(G)) = N(FR(G)) ∩ H₀`, read in the original space `ℝ^V` (p. 177). -/
def NG {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Set (V → ℝ) :=
  {x | hom x ∈ N (FR G)}

/-- The inequality `aᵀx ≤ b` is valid for `S ⊆ ℝ^V`. -/
def Valid {V : Type} [Fintype V] (S : Set (V → ℝ)) (a : V → ℝ) (b : ℝ) : Prop :=
  ∀ x ∈ S, ∑ i, a i * x i ≤ b

end LovaszSchrijver.OddHole


