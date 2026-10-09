-- Prove2me | Definitions.Def_DynTypeMatching_Priority_Relations
-- name    : DynTypeMatching_Priority_Relations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:58:38.892303+00:00
-- url     : https://prove2.me/theorems/b74bc491-2975-459a-941a-472fb77cccba
-- title:
--   Definitions 1–4, pp. 11, 28 — the relation ≻M, the modified Monge condition, compatibility and weak compatibility
-- statement:
--   **Dominance between neighbouring pairs and compatible decisions.** Fix a dynamic type matching model with horizon $T$, rewards $r^t_{ij}$ and carry-over fractions $\alpha,\beta$.
--
--   1. **Column dominance** (Definition 1). For demand types $i'\ne i$ and a supply type $j$, $(i,j)\succ_{\mathcal M}(i',j)$ means
--      $$r^t_{ij}>r^t_{i'j}\ \ (1\le t\le T),\qquad r^t_{ij}-r^t_{i'j}\ge\alpha\big(r^{t+1}_{ij''}-r^{t+1}_{i'j''}\big)\ \ (1\le t\le T-1,\ j''\in\mathcal S).$$
--   2. **Row dominance** (Definition 1). For supply types $j'\ne j$, $(i,j)\succ_{\mathcal M}(i,j')$ means $r^t_{ij}>r^t_{ij'}$ for $1\le t\le T$ and $r^t_{ij}-r^t_{ij'}\ge\beta(r^{t+1}_{i''j}-r^{t+1}_{i''j'})$ for $1\le t\le T-1$ and all $i''\in\mathcal D$.
--   3. **Modified Monge condition** (Definition 2). Whenever $(i,j)\succ_{\mathcal M}(i',j)$ and $(i,j)\succ_{\mathcal M}(i,j')$,
--      $$r^t_{ij}+r^t_{i'j'}\ge r^t_{ij'}+r^t_{i'j}\qquad(1\le t\le T).$$
--      Under this condition the paper writes $\succ_{\mathcal M_s}$ for $\succ_{\mathcal M}$.
--   4. **Residuals.** For a state $(\mathbf x,\mathbf y)$, a decision $\mathbf Q$ and a pair $(i,j)$, let $\mathcal B_{ij,L}=\{(i,j')\mid(i,j)\succ(i,j')\}$ and $\mathcal B_{ij,R}=\{(i',j)\mid(i,j)\succ(i',j)\}$, and
--      $$a_i=x_i-\sum_{j'':(i,j'')\notin\mathcal B_{ij,L}}q_{ij''},\qquad b_j=y_j-\sum_{i'':(i'',j)\notin\mathcal B_{ij,R}}q_{i''j}.$$
--   5. **Compatibility** (Definition 3). $\mathbf Q$ respects the relation if (i) for all $(i,j)\succ(i',j)$, $q_{i'j}=0$ or $a_i=0$; and (ii) for all $(i,j)\succ(i,j')$, $q_{ij'}=0$ or $b_j=0$.
--   6. **Weak compatibility** (Definition 4). $\mathbf Q$ weakly respects the relation if (i) for all $(i,j)\succ(i',j)$, $q_{i'j}=0$ or $u_i=0$; and (ii) for all $(i,j)\succ(i,j')$, $q_{ij'}=0$ or $v_j=0$, where $\mathbf u,\mathbf v$ are the post-matching levels.
--
--   A policy respects (weakly respects) the relation when its decision does so in every period and every state; the priority theorems of the paper assert the existence of an optimal policy with that property.
--
--   **Formalization Note** Two disclosed repairs of Definition 1: (i) is **strict**, and the neighbours are **distinct** ($i'\ne i$, $j'\ne j$). With the printed weak inequality, two pairs with equal rewards dominate each other and Theorems 1 and 2 fail: $m=3$, $n=1$, $T=1$, all rewards $2$, $\mathbf x=(0,1,1)$, $\mathbf y=(1)$; Definition 3 then requires $q_{31}=0$ or $q_{21}=1$, and $q_{21}=0$ or $q_{31}=1$, while every optimal decision matches the single supply unit, $q_{21}+q_{31}=1$; no decision satisfies all three. Without distinctness, Definition 3 at $i'=i$ would be false already for $m=n=1$. Condition (ii) is quantified over $t+1\le T$, since $r^{T+1}$ is not part of the model; with strict (i) this is equivalent to the paper's appendix convention $r^{T+1}:=0$. The relations are global (they quantify over all periods), and the Monge condition is a hypothesis rather than a separate relation $\succ_{\mathcal M_s}$.
-- source:
--   Hu, Zhou, Dynamic Type Matching, arXiv:1811.07048v1, p. 11, Definitions 1–3 and (2); p. 28, Definition 4

import Mathlib
import Definitions.Def_DynTypeMatching_Priority_Model

namespace DynTypeMatching.Priority

open Classical

/-- `(i, j) ≻_M (i', j)` (Definition 1, first half, with strict (i) and `i' ≠ i`):
(i) `r^t_{i'j} < r^t_{ij}` for `t = 1, …, T`, and
(ii) `α (r^{t+1}_{ij''} − r^{t+1}_{i'j''}) ≤ r^t_{ij} − r^t_{i'j}` for `t = 1, …, T − 1` and all `j''`. -/
def DomCol {m n : ℕ} (M : Model m n) (i i' : Fin m) (j : Fin n) : Prop :=
  i' ≠ i ∧ (∀ t, 1 ≤ t → t ≤ M.T → M.r t i' j < M.r t i j) ∧
    (∀ t, 1 ≤ t → t + 1 ≤ M.T → ∀ j'' : Fin n,
      M.α * (M.r (t + 1) i j'' - M.r (t + 1) i' j'') ≤ M.r t i j - M.r t i' j)

/-- `(i, j) ≻_M (i, j')` (Definition 1, second half, with strict (i) and `j' ≠ j`):
(i) `r^t_{ij'} < r^t_{ij}` for `t = 1, …, T`, and
(ii) `β (r^{t+1}_{i''j} − r^{t+1}_{i''j'}) ≤ r^t_{ij} − r^t_{ij'}` for `t = 1, …, T − 1` and all `i''`. -/
def DomRow {m n : ℕ} (M : Model m n) (i : Fin m) (j j' : Fin n) : Prop :=
  j' ≠ j ∧ (∀ t, 1 ≤ t → t ≤ M.T → M.r t i j' < M.r t i j) ∧
    (∀ t, 1 ≤ t → t + 1 ≤ M.T → ∀ i'' : Fin m,
      M.β * (M.r (t + 1) i'' j - M.r (t + 1) i'' j') ≤ M.r t i j - M.r t i j')

/-- The modified Monge condition (Definition 2, (2)): whenever `(i, j) ≻_M (i', j)` and
`(i, j) ≻_M (i, j')`, `r^t_{ij} + r^t_{i'j'} ≥ r^t_{ij'} + r^t_{i'j}` for all `t = 1, …, T`.
Under it the relation `≻_{M_s}` of the paper is `≻_M` itself. -/
def MongeCondition {m n : ℕ} (M : Model m n) : Prop :=
  ∀ (i i' : Fin m) (j j' : Fin n), DomCol M i i' j → DomRow M i j j' →
    ∀ t, 1 ≤ t → t ≤ M.T → M.r t i j' + M.r t i' j ≤ M.r t i j + M.r t i' j'

/-- `a^t_i` for the pair `(i, j)`: `x_i − ∑_{j'' : (i, j'') ∉ B_{ij,L}} q_{ij''}`, where
`B_{ij,L} = {(i, j') | (i, j) ≻ (i, j')}`. -/
noncomputable def resD {m n : ℕ} (M : Model m n) (x : Fin m → ℝ) (Q : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) : ℝ :=
  x i - ∑ j'' ∈ Finset.univ.filter (fun j'' => ¬ DomRow M i j j''), Q i j''

/-- `b^t_j` for the pair `(i, j)`: `y_j − ∑_{i'' : (i'', j) ∉ B_{ij,R}} q_{i''j}`, where
`B_{ij,R} = {(i', j) | (i, j) ≻ (i', j)}`. -/
noncomputable def resS {m n : ℕ} (M : Model m n) (y : Fin n → ℝ) (Q : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) : ℝ :=
  y j - ∑ i'' ∈ Finset.univ.filter (fun i'' => ¬ DomCol M i i'' j), Q i'' j

/-- Definition 3 (Compatibility) at one period and state: (i) for all `(i, j) ≻ (i', j)`,
`q_{i'j} = 0` or `a_i = 0`; (ii) for all `(i, j) ≻ (i, j')`, `q_{ij'} = 0` or `b_j = 0`. -/
def Respects {m n : ℕ} (M : Model m n) (x : Fin m → ℝ) (y : Fin n → ℝ)
    (Q : Fin m → Fin n → ℝ) : Prop :=
  (∀ (i i' : Fin m) (j : Fin n), DomCol M i i' j → Q i' j = 0 ∨ resD M x Q i j = 0) ∧
    (∀ (i : Fin m) (j j' : Fin n), DomRow M i j j' → Q i j' = 0 ∨ resS M y Q i j = 0)

/-- Definition 4 (Weak compatibility) at one period and state: (i) for all `(i, j) ≻ (i', j)`,
`q_{i'j} = 0` or `u_i = 0`; (ii) for all `(i, j) ≻ (i, j')`, `q_{ij'} = 0` or `v_j = 0`. -/
def WeaklyRespects {m n : ℕ} (M : Model m n) (x : Fin m → ℝ) (y : Fin n → ℝ)
    (Q : Fin m → Fin n → ℝ) : Prop :=
  (∀ (i i' : Fin m) (j : Fin n), DomCol M i i' j → Q i' j = 0 ∨ postD x Q i = 0) ∧
    (∀ (i : Fin m) (j j' : Fin n), DomRow M i j j' → Q i j' = 0 ∨ postS y Q j = 0)

end DynTypeMatching.Priority


