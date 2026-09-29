-- Prove2me | Definitions.Def_LovaszSchrijver_Defect_StableSet
-- name    : LovaszSchrijver_Defect_StableSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:52:07.132298+00:00
-- url     : https://prove2.me/theorems/4678fba9-1c5c-44d9-9899-0a5765ecc295
-- title:
--   STAB(G), FRAC(G), FR(G), the relaxations Nʳ(G), valid inequalities, and deletion and contraction of a node (Sections 2.a–2.b)
-- statement:
--   Let $G = (V, E)$ be a finite graph. Throughout Section 2 the paper assumes that $G$ has no isolated nodes (p. 175).
--
--   1. **Incidence vectors and $\mathrm{STAB}(G)$** (p. 175). For $A \subseteq V$, $\chi^A \in \mathbb R^V$ is its incidence vector, and the stable set polytope is
--   $$\mathrm{STAB}(G) = \operatorname{conv}\{\chi^A : A \text{ is stable}\}.$$
--   2. **$\mathrm{FRAC}(G)$** (p. 175), the "fractional stable sets": the solution set of (1) $x_i \ge 0$ for each $i \in V$ and (2) $x_i + x_j \le 1$ for each $ij \in E$.
--   3. **$\mathrm{FR}(G)$** (p. 177). "Let $\mathrm{FR}(G)$ denote the cone spanned by the vectors $\binom{1}{x}$, where $x \in \mathrm{FRAC}(G)$. Then $\mathrm{FR}(G)$ is determined by the constraints $x_i \ge 0$ for each $i \in V$, and $x_i + x_j \le x_0$ for each $ij \in E$." It lives in $\mathbb R^{V \cup \{0\}}$.
--   4. **The relaxations $N^r(G)$** (p. 177). "We shall use the notation $N(\mathrm{FRAC}(G)) = N(\mathrm{FR}(G)) \cap H_0$, and similarly for $N_+$, $\hat N$, etc. We shall also abbreviate $N(\mathrm{FRAC}(G))$ by $N(G)$", where $H_0$ is the hyperplane $x_0 = 1$. In the same way, for $r \ge 0$,
--   $$N^r(G) = \{x \in \mathbb R^V : \tbinom{1}{x} \in N^r(\mathrm{FR}(G))\},$$
--   so that $N^0(G) = \mathrm{FRAC}(G)$.
--   5. **Valid inequalities.** For $S \subseteq \mathbb R^V$, $a \in \mathbb R^V$ and $b \in \mathbb R$, the inequality $a^{\mathsf T}x \le b$ is valid for $S$ if it holds for every $x \in S$.
--   6. **Deletion and contraction** (p. 177). For a node $v$ with neighbourhood $\Gamma(v)$, the deletion of $v$ turns $a^{\mathsf T}x \le b$ into $a_{V-v}^{\mathsf T}x \le b$ and the contraction of $v$ turns it into $a_{V-\Gamma(v)-v}^{\mathsf T}x \le b - a_v$, where $a_W$ is the restriction of $a$ to $W$. Here the restricted coefficient vectors are extended by zeros to all of $V$: the deletion has coefficients $a$ with $a_v$ replaced by $0$, and the contraction has coefficients $a$ with $a_w$ replaced by $0$ for $w \in \{v\} \cup \Gamma(v)$.
--
--   These are the objects of the paper's application of the $N$ operator to the stable set problem: $\mathrm{STAB}(G) \subseteq N^r(G) \subseteq \mathrm{FRAC}(G)$, and deletion and contraction are the two branches of the recursion on a node.
--
--   **Formalization Note** Coordinates of $\mathbb R^{V\cup\{0\}}$ are indexed by `Option V`, `none` being $x_0$; $\binom{1}{x}$ is `hom x`. $\mathrm{FR}(G)$ is defined by the two constraint families the page says determine it; this equals the cone spanned by the vectors $\binom{1}{x}$, $x\in\mathrm{FRAC}(G)$, because $G$ has no isolated nodes (a point with $x_0 = 0$ is then $0$). Deletion and contraction are stated on the same graph $G$ with zeroed coefficients: validity for $\mathrm{STAB}$ of the subgraph and validity for $\mathrm{STAB}(G)$ of the zero-extended inequality are the same thing, and this form avoids subgraphs with isolated nodes. The paper's integer vectors $a \in \mathbb Z_+^V$ are cast into $\mathbb R^V$ by the theorems that need them.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 175, Section 2.a (STAB, FRAC); p. 177, Section 2.b (FR(G), N(G), deletion and contraction)

import Mathlib
import Definitions.Def_LovaszSchrijver_Defect_MatrixCone

namespace LovaszSchrijver.Defect

/-- The incidence vector `χ^A ∈ ℝ^V` of a vertex set `A` (p. 175). -/
def chi {V : Type} [DecidableEq V] (A : Finset V) : V → ℝ :=
  fun i => if i ∈ A then 1 else 0

/-- `STAB(G) = conv{χ^A : A is stable}` (p. 175). -/
def STAB {V : Type} [DecidableEq V] (G : SimpleGraph V) : Set (V → ℝ) :=
  convexHull ℝ {x | ∃ A : Finset V, G.IsIndepSet (A : Set V) ∧ x = chi A}

/-- `FRAC(G)`: the solution set of (1) `xᵢ ≥ 0` for each `i ∈ V` and (2) `xᵢ + xⱼ ≤ 1` for
each `ij ∈ E` (p. 175). -/
def FRAC {V : Type} (G : SimpleGraph V) : Set (V → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∀ i j, G.Adj i j → x i + x j ≤ 1}

/-- `FR(G) ⊆ ℝ^{V ∪ {0}}`, by the constraints `xᵢ ≥ 0` (`i ∈ V`) and `xᵢ + xⱼ ≤ x₀` (`ij ∈ E`)
(p. 177). The coordinate `none` is `x₀`. -/
def FR {V : Type} (G : SimpleGraph V) : Set (Option V → ℝ) :=
  {x | (∀ i, 0 ≤ x (some i)) ∧ ∀ i j, G.Adj i j → x (some i) + x (some j) ≤ x none}

/-- Homogenization `x ↦ (1, x)`: the point of the hyperplane `H₀ = {x₀ = 1}` over `x`. -/
def hom {V : Type} (x : V → ℝ) : Option V → ℝ :=
  fun o => o.elim 1 x

/-- `N^r(G) = N^r(FR(G)) ∩ H₀`, read in the original coordinates (p. 177). -/
def NG {V : Type} [Fintype V] [DecidableEq V] (r : ℕ) (G : SimpleGraph V) : Set (V → ℝ) :=
  {x | hom x ∈ Niter r (FR G)}

/-- The inequality `aᵀx ≤ b` is valid for `S`. -/
def Valid {V : Type} [Fintype V] (S : Set (V → ℝ)) (a : V → ℝ) (b : ℝ) : Prop :=
  ∀ x ∈ S, a ⬝ᵥ x ≤ b

/-- Coefficients of the deletion of node `v` (p. 177): `a` with `a_v` replaced by `0`; the
right-hand side stays `b`. -/
def deletion {V : Type} [DecidableEq V] (a : V → ℝ) (v : V) : V → ℝ :=
  Function.update a v 0

/-- Coefficients of the contraction of node `v` (p. 177): `a` with the coordinates of `v` and
of its neighbours `Γ(v)` replaced by `0`; the right-hand side is `b - a_v`. -/
def contraction {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V → ℝ) (v : V) : V → ℝ :=
  fun w => if w = v ∨ G.Adj v w then 0 else a w

end LovaszSchrijver.Defect


