-- Prove2me | Definitions.Def_MostlyExplorationFree_GreedyBandit_Supplement_PositiveDefiniteness
-- name    : MostlyExplorationFree_GreedyBandit_Supplement_PositiveDefiniteness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T18:45:51.711864+00:00
-- url     : https://prove2.me/theorems/52a249e6-9a82-4b6e-bc09-f8e2b6f0ee78
-- title:
--   Assumption 4 — optimal regions and positive definite second moments
-- statement:
--   Partition the arms into $K_{\rm sub}$ and its complement $K_{\rm opt}$. For positive constants $h$ and $\lambda_1$, each suboptimal arm is worse than some other arm by more than $h$, almost surely under the context law. For an optimal arm define
--   $$U_i=\{x: x^\top\beta_i>x^\top\beta_j+h\ \text{for every }j\ne i\},\qquad \Sigma_i=\mathbb E[XX^\top\mathbb I_{U_i}(X)].$$
--   Assumption 4 requires $\lambda_{\min}(\Sigma_i)\ge\lambda_1$ for every $i\in K_{\rm opt}$.
--
--   This is the positive-definiteness condition used when covariate diversity is unavailable. The partition is represented by the finite set of suboptimal arms, so disjointness and exhaustiveness hold by construction.
--
--   **Formalization Note** The page's support restriction is expressed almost surely under $\mu$. Each matrix integral is entrywise; Assumption 1 in the results makes the integrands integrable. The smallest eigenvalue is the published Rayleigh infimum, used only for $d\ge1$.
-- source:
--   Bastani, Bayati & Khosravi, arXiv:1704.09011v8, p. 19, Assumption 4

import Mathlib
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Supplement_Environment

namespace MostlyExplorationFree.GreedyBandit.Supplement

open Matrix MeasureTheory

/-- The set U_i on which arm i wins by more than h against every other arm. -/
def optimalRegion {d K : ℕ} (β : Fin K → Fin d → ℝ) (h : ℝ) (i : Fin K) :
    Set (Fin d → ℝ) := {x | ∀ j, j ≠ i → x ⬝ᵥ β j + h < x ⬝ᵥ β i}

noncomputable def optimalSecondMoment {d K : ℕ} (μ : Measure (Fin d → ℝ))
    (β : Fin K → Fin d → ℝ) (h : ℝ) (i : Fin K) : Matrix (Fin d) (Fin d) ℝ :=
  fun a b => ∫ x, (optimalRegion β h i).indicator (fun y => y a * y b) x ∂μ

/-- Assumption 4. The optimal arms are exactly the complement of Ksub. -/
def PositiveDefiniteness {d K : ℕ} (μ : Measure (Fin d → ℝ))
    (β : Fin K → Fin d → ℝ) (Ksub : Finset (Fin K)) (h lam1 : ℝ) : Prop :=
  0 < h ∧ 0 < lam1 ∧
    (∀ i ∈ Ksub, ∀ᵐ x ∂μ, ∃ j, j ≠ i ∧ x ⬝ᵥ β i < x ⬝ᵥ β j - h) ∧
    ∀ i, i ∉ Ksub → lam1 ≤ lambdaMin (optimalSecondMoment μ β h i)

end MostlyExplorationFree.GreedyBandit.Supplement


