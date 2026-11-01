-- Prove2me | Definitions.Def_PWDB_ConvexProgram
-- name    : PWDB_ConvexProgram
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:37:51.598775+00:00
-- url     : https://prove2.me/theorems/17c34884-2e3f-4d94-a2df-4b6391105ecf
-- title:
--   The primal problem (P) and its dual (D)
-- statement:
--   Let $E$ be a real inner product space, $I$ a finite index set, and $f_0, f_i : E \to \overline{\mathbb R}$. Problem (P) is
--   $$
--   \inf_x\ f_0(x) \quad\text{s.t.}\quad f_i(x) \le 0\ \ \forall i \in I,
--   $$
--   and its dual (D) is
--   $$
--   \sup\ -f_0^*(w_0) - \sum_{i\in I} \lambda_i f_i^*(w_i/\lambda_i) \quad\text{s.t.}\quad w_0 + \sum_{i \in I} w_i = 0,\ \ \lambda \ge 0,
--   $$
--   where $\lambda_i f_i^*(w_i/\lambda_i)$ is the convex perspective of $f_i^*$.
--
--   The module defines the feasible regions (`pFeas`, `dFeas`, excluding the objective values $+\infty$ and $-\infty$ respectively), the optimal values `pVal` $= \inf$ and `dVal` $= \sup$ in $\overline{\mathbb R}$, the dual objective `dObj`, and the constraints of (D) in the form of Definition 1 (`dIneq`: $-\lambda_i \le 0$; `dEq`: $\langle v, w_0 + \sum_i w_i\rangle = 0$ for every $v \in E$).
--
--   **Formalization Note** A dual point is $(w_0, w, \lambda) \in E \times E^I \times \mathbb R^I$.
-- source:
--   Zhen, Kuhn & Wiesemann, A Unified Theory of Robust and Distributionally Robust Optimization via the Primal-Worst-Equals-Dual-Best Principle, arXiv:2105.00760v2 (19 Jul 2023), problems (P) and (D), p.7; conventions p.40

import Mathlib
import Definitions.Def_PWDB_conj
import Definitions.Def_PWDB_persp

open scoped InnerProductSpace

namespace PWDB

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

/-- **Feasible region of (P)** (Zhen, Kuhn & Wiesemann, arXiv:2105.00760v2, problem (P), p.7:
`inf f0(x) s.t. fi(x) ≤ 0 ∀i ∈ I, x free`; feasibility as on p.40: all constraints hold and the
objective is not `+∞`). -/
def pFeas (f₀ : E → EReal) (f : ι → E → EReal) : Set E :=
  {x | (∀ i, f i x ≤ 0) ∧ f₀ x ≠ ⊤}

/-- **Optimal value (infimum) of (P)** (arXiv:2105.00760v2, p.7), in `EReal`; it is `+∞` when (P)
is infeasible. Points with `f₀ x = +∞` would not change the infimum, so taking it over `pFeas` is
the same as taking it over all points satisfying the constraints. -/
noncomputable def pVal (f₀ : E → EReal) (f : ι → E → EReal) : EReal :=
  ⨅ x ∈ pFeas f₀ f, f₀ x

/-- **Objective of the dual problem (D)** (arXiv:2105.00760v2, p.7):
`−f0∗(w0) − Σ_{i∈I} λi fi∗(wi/λi)`, at a point `p = (w₀, w, λ)` with `w₀ ∈ E`, `w : I → E`,
`λ : I → ℝ`.

**Formalization Note** `λi fi∗(wi/λi)` is the convex perspective `persp (conj (f i)) (w i) (λ i)`
(Definition A.2 applied to `fi∗`, p.39 and p.7), so at `λi = 0` it is the support function of
`dom(fi∗∗)`, not `0`. The objective is written `−(f0∗(w0) + Σ …)`; for proper `fi` none of these
terms is `−∞`, so the `EReal` sum never meets `⊤ + ⊥`. -/
noncomputable def dObj (f₀ : E → EReal) (f : ι → E → EReal) (p : E × (ι → E) × (ι → ℝ)) :
    EReal :=
  -(conj f₀ p.1 + ∑ i, persp (conj (f i)) (p.2.1 i) (p.2.2 i))

/-- **Feasible region of (D)** (arXiv:2105.00760v2, p.7: `Σ_{i∈I0} wi = 0`, `wi` free, `λ ≥ 0`;
feasibility as on p.40 excludes the objective value `−∞`). `I0 = {0} ∪ I`: the `w₀` term is
`p.1`. -/
def dFeas (f₀ : E → EReal) (f : ι → E → EReal) : Set (E × (ι → E) × (ι → ℝ)) :=
  {p | p.1 + ∑ i, p.2.1 i = 0 ∧ (∀ i, 0 ≤ p.2.2 i) ∧ dObj f₀ f p ≠ ⊥}

/-- **Optimal value (supremum) of (D)** (arXiv:2105.00760v2, p.7), in `EReal`; `−∞` when (D) is
infeasible. -/
noncomputable def dVal (f₀ : E → EReal) (f : ι → E → EReal) : EReal :=
  ⨆ p ∈ dFeas f₀ f, dObj f₀ f p

/-- **Inequality constraints of (D)**, written as in Definition 1 (arXiv:2105.00760v2, p.6–7):
`λ ≥ 0` is the family of affine constraints `−λi ≤ 0`, `i ∈ I`. -/
def dIneq (ι : Type*) {E : Type*} : ι → (E × (ι → E) × (ι → ℝ)) → EReal :=
  fun i p => ((-(p.2.2 i) : ℝ) : EReal)

/-- **Equality constraints of (D)**, written as in Definition 1 (arXiv:2105.00760v2, p.6–7): the
vector equation `Σ_{i∈I0} wi = 0` is the family of scalar linear equations
`⟨v, w₀ + Σ_i wi⟩ = 0`, one for each `v ∈ E`.

**Formalization Note** In `ℝ^{dx}` the paper's vector equation stands for its `dx` coordinate
equations; indexing by every `v ∈ E` describes the same set, and all these functions are linear and
finite, so the Slater conditions (i)–(iii) of Definition 1 are the same for both
representations. -/
def dEq (ι : Type*) {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι] :
    E → (E × (ι → E) × (ι → ℝ)) → EReal :=
  fun v p => ((⟪v, p.1 + ∑ i, p.2.1 i⟫_ℝ : ℝ) : EReal)

end PWDB


