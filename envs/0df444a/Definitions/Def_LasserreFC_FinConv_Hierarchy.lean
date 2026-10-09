-- Prove2me | Definitions.Def_LasserreFC_FinConv_Hierarchy
-- name    : LasserreFC_FinConv_Hierarchy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T05:32:32.755727+00:00
-- url     : https://prove2.me/theorems/548d0805-62ef-4c9c-a339-1832fdad02de
-- title:
--   (1.2), pp. 1–2, §2.2 — truncated ideal, truncated quadratic module, Lasserre's hierarchy and the archimedean condition
-- statement:
--   This file defines Lasserre's hierarchy of SOS relaxations for problem (1.1).
--
--   A polynomial is SOS if it equals $p_1^2 + \dots + p_k^2$ for polynomials $p_i$; the set of SOS polynomials is $\Sigma\mathbb R[x]^2$. Put $g_0 := 1$. For $k \in \mathbb N$:
--
--   1. the **$2k$-th truncated ideal** is $\langle h\rangle_{2k} = \{\sum_{i=1}^{m_1} \phi_i h_i : \phi_i \in \mathbb R[x],\ \deg(\phi_i h_i) \le 2k\}$;
--   2. the **$k$-th truncated quadratic module** is $Q_k(g) = \{\sum_{j=0}^{m_2} \sigma_j g_j : \sigma_j \in \Sigma\mathbb R[x]^2,\ \deg(\sigma_j g_j) \le 2k\}$;
--   3. the **quadratic module** is $Q(g) = \bigcup_{k} Q_k(g)$.
--
--   The order-$k$ relaxation (1.2) and its optimal value are
--
--   $$f_k = \sup\{\gamma \in \mathbb R : f - \gamma \in \langle h\rangle_{2k} + Q_k(g)\}.$$
--
--   The **archimedean condition** holds if $R - \sum_{i=1}^n x_i^2 \in \langle h\rangle_{2t} + Q_t(g)$ for some $t \in \mathbb N$ and $R > 0$. Lasserre's hierarchy has **finite convergence** if $f_k = f_{\min}$ for some $k$, where $f_{\min}$ is the minimum value of (1.1).
--
--   These are the objects of the finite-convergence theorem (Theorem 1.1) and of Marshall's representation theorem (Theorem 2.4).
--
--   **Formalization Note** The degree bounds are imposed term by term, on each $\phi_i h_i$ and each $\sigma_j g_j$ (including $\sigma_0$), as on the page; a bound on the sum alone would admit cancellation and change $f_k$. SOS is Mathlib's `IsSumSq`. The value $f_k$ is a supremum in `EReal`, so it is $-\infty$ when (1.2) is infeasible and need not be attained. The archimedean condition is the page's truncated form (p. 2); since $\langle h\rangle + Q(g) = \bigcup_k (\langle h\rangle_{2k} + Q_k(g))$, it is the same as §2.2's "$\langle h\rangle + Q(g)$ is archimedean".
-- source:
--   J. Nie, Optimality conditions and finite convergence of Lasserre's hierarchy, arXiv:1206.0319v2, pp. 1–2, ⟨h⟩_{2k}, Q_k(g), (1.2), archimedean condition, finite convergence; p. 4, §2.2, Q(g)

import Mathlib
import Definitions.Def_LasserreFC_FinConv_Setting

namespace LasserreFC.FinConv

open MvPolynomial

variable {n m1 m2 : ℕ}

/-- The `2k`-th truncated ideal `⟨h⟩_{2k}` (p. 1): sums `∑ᵢ φᵢ hᵢ` with arbitrary `φᵢ ∈ ℝ[x]` and
`deg(φᵢ hᵢ) ≤ 2k` for each `i`. -/
def truncIdeal (P : POP n m1 m2) (k : ℕ) : Set (MvPolynomial (Fin n) ℝ) :=
  {p | ∃ φ : Fin m1 → MvPolynomial (Fin n) ℝ,
    p = ∑ i, φ i * P.h i ∧ ∀ i, (φ i * P.h i).totalDegree ≤ 2 * k}

/-- The `k`-th truncated quadratic module `Q_k(g)` (p. 1): sums `∑_{j=0}^{m₂} σⱼ gⱼ` with `g₀ = 1`,
each `σⱼ` a sum of squares and `deg(σⱼ gⱼ) ≤ 2k` for each `j` (including `j = 0`). -/
def truncQM (P : POP n m1 m2) (k : ℕ) : Set (MvPolynomial (Fin n) ℝ) :=
  {p | ∃ (σ0 : MvPolynomial (Fin n) ℝ) (σ : Fin m2 → MvPolynomial (Fin n) ℝ),
    IsSumSq σ0 ∧ σ0.totalDegree ≤ 2 * k ∧
    (∀ j, IsSumSq (σ j) ∧ (σ j * P.g j).totalDegree ≤ 2 * k) ∧
    p = σ0 + ∑ j, σ j * P.g j}

/-- The Minkowski sum `⟨h⟩_{2k} + Q_k(g)`. -/
def trunc (P : POP n m1 m2) (k : ℕ) : Set (MvPolynomial (Fin n) ℝ) :=
  {p | ∃ a ∈ truncIdeal P k, ∃ b ∈ truncQM P k, p = a + b}

/-- The quadratic module `Q(g) = ⋃_{k ∈ ℕ} Q_k(g)` (§2.2, p. 4). -/
def qmod (P : POP n m1 m2) : Set (MvPolynomial (Fin n) ℝ) :=
  ⋃ k, truncQM P k

/-- The archimedean condition (p. 2): `R − ∑ᵢ xᵢ² ∈ ⟨h⟩_{2t} + Q_t(g)` for some `t ∈ ℕ` and `R > 0`. -/
def IsArchimedean (P : POP n m1 m2) : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∃ t : ℕ, C R - ∑ i, X i ^ 2 ∈ trunc P t

/-- The optimal value `f_k` of the order-`k` SOS relaxation (1.2), `max γ s.t. f − γ ∈ ⟨h⟩_{2k} + Q_k(g)`,
as a supremum in `EReal` (it is `⊥ = −∞` when (1.2) is infeasible). -/
noncomputable def lasserreValue (P : POP n m1 m2) (k : ℕ) : EReal :=
  sSup ((fun γ : ℝ => (γ : EReal)) '' {γ : ℝ | P.f - C γ ∈ trunc P k})

end LasserreFC.FinConv


