-- Prove2me | Definitions.Def_KallMayerSLP_ProbConstr_feasibleSet
-- name    : KallMayerSLP_ProbConstr_feasibleSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:11:13.736189+00:00
-- url     : https://prove2.me/theorems/3793f9a6-110e-4675-9bbe-0b12243821f3
-- title:
--   The feasible set $\mathcal B(\alpha)=\{x\mid G(x)\ge\alpha\}$ of a joint probability constraint
-- statement:
--   For a level $\alpha\in\mathbb R$, the feasible set of the joint probability constraint $G(x)\ge\alpha$ (2.12) is
--   $$
--   \mathcal B(\alpha)=\{x\in\mathbb R^n \mid G(x)\ge\alpha\},
--   $$
--   where $G(x)=\mathbb P_\xi(T(\xi)x\ge h(\xi))$ is the probability function. Whether $\mathcal B(\alpha)$ is closed and convex decides whether the chance-constrained problem $\max\{c^{\mathsf T}x : x\in\mathcal B(\alpha)\cap\mathcal B\}$ is a convex program.
--
--   **Formalization Note** Defined directly from $G$ for every real $\alpha$. The forms $\{x\mid S(x)\in\mathcal G_\alpha\}$ and the union representations (2.13), (2.17), (2.18) are theorems of the mission, not definitions.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, Chapter 2, (2.9), p.95 (PDF 105) and §2.1, p.96 (PDF 106)

import Mathlib
import Definitions.Def_KallMayerSLP_ProbConstr_probFun

open MeasureTheory

namespace KallMayerSLP.ProbConstr

/-- The feasible set of the joint probability constraint (2.12), `B(α) = {x | G(x) ≥ α}`.

Kall & Mayer 2005, Chapter 2, (2.9), p.95 (PDF 105), and §2.1, p.96 (PDF 106).

**Formalization Note.** Defined directly through the probability function `G` (`probFun`), for
every real level `α`; the book's equivalent forms `{x | S(x) ∈ 𝒢_α}` and the representations
(2.13), (2.17), (2.18) are theorems of the mission, not definitions. -/
def feasibleSet {r m n : ℕ} (μ : Measure (Fin r → ℝ))
    (T : (Fin r → ℝ) → Matrix (Fin m) (Fin n) ℝ) (h : (Fin r → ℝ) → Fin m → ℝ) (α : ℝ) :
    Set (Fin n → ℝ) :=
  {x | α ≤ probFun μ T h x}

end KallMayerSLP.ProbConstr


