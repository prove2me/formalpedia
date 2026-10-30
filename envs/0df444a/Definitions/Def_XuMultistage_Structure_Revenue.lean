-- Prove2me | Definitions.Def_XuMultistage_Structure_Revenue
-- name    : XuMultistage_Structure_Revenue
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T00:24:19.001652+00:00
-- url     : https://prove2.me/theorems/4e99605b-0948-4c82-a038-f98a029d1762
-- title:
--   Exact choice probabilities, expected revenue, and global optimality
-- statement:
--   Fix two-stage product data and a feasible path matrix $X$. Write
--   $$A_i=1+\sum_{j>0:X_{ij}=1}e^{\mu_j^{(2)}},\qquad
--   w_i=\begin{cases}e^{\mu_i^{(1)}}A_i^\gamma&X_{i0}=1,\\0&X_{i0}=0,\end{cases}\qquad D=\sum_i w_i.$$
--   For an active row, the continuation utility is $V_i=\log A_i$, and conditional second-stage probabilities are $P_{0\mid i}=1/A_i$ and $P_{j\mid i}=e^{\mu_j^{(2)}}/A_i$ for offered ordinary products, zero for unavailable ones. For an inactive row all conditional probabilities and $V_i$ are zero. Define
--   $$r_i=\begin{cases}p_i^{(1)}+\sum_jP_{j\mid i}p_j^{(2)}&X_{i0}=1,\\0&X_{i0}=0,\end{cases}\qquad
--   P_i=w_i/D,\qquad P_{ij}=P_iP_{j\mid i},\qquad R_\gamma(X)=\sum_iP_ir_i.$$
--   This revenue also equals $\sum_{i,j}P_{ij}(p_i^{(1)}+p_j^{(2)})$. Only customer utility is discounted; revenue is not. Every $A_i\ge1$, and feasibility makes $D>0$ through the active outside row. For $\gamma=0$, $A_i^0=1$; no divided deterministic utility is used.
--
--   An optimal matrix is feasible and has revenue at least that of every feasible matrix. A policy's revenue is the revenue of its offered-path matrix; an optimal policy has revenue at least that of every deterministic policy. These are concrete comparisons, with no supremum convention and no assumed structural property.
--
--   **Formalization Note** The published finite logit-share formula supplies the ordinary conditional probabilities. Its input vector has a dummy zero-weight index zero, and the formula adds the true outside weight one separately. Thus unavailable products have zero weight and the always available outside option is counted exactly once. Values of the formulas on infeasible matrices are not used in the source targets. The parameters in this definition are total real numbers; theorem binders impose $0\le\gamma\le1$ or fix $\gamma=1$.
-- source:
--   Xu and Wang, Assortment Optimization for a Multi-Stage Choice Model, https://doi.org/10.1287/msom.2023.1224, held source.pdf (published citation basis; SSRN footer 3243742; catalog label 2018, PDF metadata 2023; PDF pages equal printed pages), (1)–(2), p. 12; (5), p. 14; (9), pp. 18–19; Appendix C, pp. 38–39

import Definitions.Def_FlagshipMEA_Monopoly_LogitChoice
import Definitions.Def_XuMultistage_Structure_Model
import Definitions.Def_XuMultistage_Structure_Policy

open scoped BigOperators

namespace XuMultistage.Structure

/-- Ordinary-product attractions in row i. The dummy index zero has weight zero
because the imported logit formula adds the actual outside weight one separately. -/
noncomputable def rowAttraction {n₁ n₂ : ℕ} (M : Model n₁ n₂)
    (X : PathMatrix n₁ n₂) (i : Fin (n₁ + 1)) (j : Fin (n₂ + 1)) : ℝ :=
  if j ≠ 0 ∧ X i j = true then Real.exp (M.μ₂ j) else 0

/-- A_i; the compulsory outside option contributes one. -/
noncomputable def rowMass {n₁ n₂ : ℕ} (M : Model n₁ n₂)
    (X : PathMatrix n₁ n₂) (i : Fin (n₁ + 1)) : ℝ :=
  (∑ j, rowAttraction M X i j) + 1

/-- Appendix C's V_i, with the specified inactive-row convention. -/
noncomputable def continuationUtility {n₁ n₂ : ℕ} (M : Model n₁ n₂)
    (X : PathMatrix n₁ n₂) (i : Fin (n₁ + 1)) : ℝ :=
  if X i 0 = true then Real.log (rowMass M X i) else 0

/-- Conditional second-stage probabilities; zero on inactive or unavailable paths. -/
noncomputable def secondProbability {n₁ n₂ : ℕ} (M : Model n₁ n₂)
    (X : PathMatrix n₁ n₂) (i : Fin (n₁ + 1)) (j : Fin (n₂ + 1)) : ℝ :=
  if X i 0 = true then
    if j = 0 then 1 / rowMass M X i
    else FlagshipMEA.Monopoly.logitShare (rowAttraction M X i) j
  else 0

/-- Appendix C's r_i, including the stage-one price and zero on inactive rows. -/
noncomputable def conditionalRevenue {n₁ n₂ : ℕ} (M : Model n₁ n₂)
    (X : PathMatrix n₁ n₂) (i : Fin (n₁ + 1)) : ℝ :=
  if X i 0 = true then M.p₁ i + ∑ j, secondProbability M X i j * M.p₂ j else 0

/-- First-stage attraction from (1), with no divided utilities at gamma zero. -/
noncomputable def firstWeight {n₁ n₂ : ℕ} (M : Model n₁ n₂) (γ : ℝ)
    (X : PathMatrix n₁ n₂) (i : Fin (n₁ + 1)) : ℝ :=
  if X i 0 = true then Real.exp (M.μ₁ i) * (rowMass M X i) ^ γ else 0

noncomputable def firstProbability {n₁ n₂ : ℕ} (M : Model n₁ n₂) (γ : ℝ)
    (X : PathMatrix n₁ n₂) (i : Fin (n₁ + 1)) : ℝ :=
  firstWeight M γ X i / ∑ k, firstWeight M γ X k

/-- P_ij in (1). -/
noncomputable def pathProbability {n₁ n₂ : ℕ} (M : Model n₁ n₂) (γ : ℝ)
    (X : PathMatrix n₁ n₂) (i : Fin (n₁ + 1)) (j : Fin (n₂ + 1)) : ℝ :=
  firstProbability M γ X i * secondProbability M X i j

/-- Expected undiscounted two-stage revenue (2), expressed by conditional revenues. -/
noncomputable def revenue {n₁ n₂ : ℕ} (M : Model n₁ n₂) (γ : ℝ)
    (X : PathMatrix n₁ n₂) : ℝ :=
  ∑ i, firstProbability M γ X i * conditionalRevenue M X i

/-- Global optimality over every feasible binary path matrix. -/
def IsOptimal {n₁ n₂ : ℕ} (M : Model n₁ n₂) (γ : ℝ)
    (X : PathMatrix n₁ n₂) : Prop :=
  Feasible X ∧ ∀ Y : PathMatrix n₁ n₂, Feasible Y → revenue M γ Y ≤ revenue M γ X

noncomputable def policyRevenue {n₁ n₂ : ℕ} (M : Model n₁ n₂) (γ : ℝ)
    (π : Policy n₁ n₂) : ℝ := revenue M γ π.paths

/-- Global optimality over all deterministic policies, including empty assortments. -/
def IsOptimalPolicy {n₁ n₂ : ℕ} (M : Model n₁ n₂) (γ : ℝ)
    (π : Policy n₁ n₂) : Prop :=
  ∀ σ : Policy n₁ n₂, policyRevenue M γ σ ≤ policyRevenue M γ π

end XuMultistage.Structure


