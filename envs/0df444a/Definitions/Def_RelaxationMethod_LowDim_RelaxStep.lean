-- Prove2me | Definitions.Def_RelaxationMethod_LowDim_RelaxStep
-- name    : RelaxationMethod_LowDim_RelaxStep
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:28:04.859513+00:00
-- url     : https://prove2.me/theorems/fd88fa9a-928c-492b-8211-b4b5a7ab932e
-- title:
--   The half-spaces (1.3), the polytope (1.4) and the relaxation step (1.5)–(1.7)
-- statement:
--   Work in the Euclidean space $E_n$ ($\mathbb R^n$ with the Euclidean distance). A system of $m$ linear inequalities
--   $$\sum_{j=1}^n a_{ij}x_j + b_i \geqslant 0 \qquad (i = 1,\dots,m)$$
--   is given by the rows $a_i = (a_{i1},\dots,a_{in}) \in E_n$ and the constants $b_i \in \mathbb R$. Each inequality defines the **closed half-space**
--   $$H_i = \{x \in E_n : \langle a_i, x\rangle + b_i \geqslant 0\},$$
--   and the solution set of the system is the **polytope** $A = \bigcap_{i=1}^m H_i$.
--
--   Given a relaxation parameter $\lambda$ and a point $p$, a point $p'$ is obtained from $p$ by a **relaxation step through the half-space $H_j$** if
--
--   1. $H_j$ is at maximal distance from $p$: $\operatorname{dist}(p, H_i) \leqslant \operatorname{dist}(p, H_j)$ for every $i$ (this is (1.5));
--   2. there is a point $q \in H_j$ with $|p - q| = \operatorname{dist}(p, H_j)$ (this is (1.6));
--   3. $p' = p + \lambda (q - p)$ (this is (1.7)).
--
--   A point $p'$ is obtained from $p$ by a **relaxation step** if this holds for some index $j$. For $0 < \lambda < 2$ this is the relaxation method of Agmon and of Motzkin–Schoenberg; $\lambda = 2$ is the reflexion method, in which $p'$ is the mirror image of $p$ in the boundary hyperplane of $H_j$.
--
--   These objects are the whole model of the paper's first three sections: a run of the method is a sequence $p_0, p_1, \dots$ in which every point outside $A$ is followed by a relaxation step.
--
--   **Formalization Note** The space is `EuclideanSpace ℝ (Fin n)`, and $\sum_j a_{ij}x_j$ is the inner product `inner ℝ (a i) x`. Distances to half-spaces are `Metric.infDist`. The paper makes $F_\lambda$ single-valued by a pre-assigned rule for choosing $j$ when (1.5) has ties (footnote 1 suggests the smallest $j$). Here the step is a relation that allows every maximizing $j$, so every theorem stated about all runs holds under every tie-breaking rule. `IsRelaxStepVia a b lam j p p'` records the index $j$ used; `IsRelaxStep` quantifies it existentially. $\lambda$ is named `lam` because `λ` is a Lean keyword.
-- source:
--   Motzkin and Schoenberg, The relaxation method for linear inequalities, Canad. J. Math. 6 (1954), DOI 10.4153/CJM-1954-038-x, pp. 393–394, (1.2)–(1.9)

import Mathlib

namespace RelaxationMethod.LowDim

/-- The closed half-space `H_i : Σ_j a_{ij} x_j + b_i ⩾ 0` of (1.3), written with the row
`a_i = (a_{i1}, …, a_{in})` of the coefficient matrix as a vector, so that
`Σ_j a_{ij} x_j = inner ℝ a_i x`. -/
def halfSpace {n : ℕ} (ai : EuclideanSpace ℝ (Fin n)) (bi : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | 0 ≤ inner ℝ ai x + bi}

/-- The solution set `A = ⋂_{i=1}^m H_i` of the system (1.2), i.e. the convex polytope (1.4). -/
def polytope {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  ⋂ i, halfSpace (a i) (b i)

/-- One relaxation step (1.5)–(1.7) from `p` to `p'` using the half-space `H_j`:
`H_j` is one of the half-spaces farthest from `p` (1.5), `q` is a point of `H_j` nearest to `p`
(1.6), and `p' = p + λ (q - p)` (1.7). The relaxation parameter `λ` is called `lam`
(`λ` is a Lean keyword). -/
def IsRelaxStepVia {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (lam : ℝ) (j : Fin m) (p p' : EuclideanSpace ℝ (Fin n)) : Prop :=
  (∀ i, Metric.infDist p (halfSpace (a i) (b i)) ≤ Metric.infDist p (halfSpace (a j) (b j))) ∧
    ∃ q ∈ halfSpace (a j) (b j),
      dist p q = Metric.infDist p (halfSpace (a j) (b j)) ∧ p' = p + lam • (q - p)

/-- `p'` is obtained from `p` by one relaxation step (1.5)–(1.7) of the process of §1 with
parameter `lam`, for **some** half-space index `j` attaining the maximum in (1.5). Quantifying
over every maximizing `j` covers every pre-assigned tie-breaking rule of (1.8). -/
def IsRelaxStep {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (lam : ℝ) (p p' : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ j, IsRelaxStepVia a b lam j p p'

end RelaxationMethod.LowDim


