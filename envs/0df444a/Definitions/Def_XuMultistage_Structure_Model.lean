-- Prove2me | Definitions.Def_XuMultistage_Structure_Model
-- name    : XuMultistage_Structure_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T00:23:39.226431+00:00
-- url     : https://prove2.me/theorems/ac43ad2b-7034-4da9-aad3-3f8145e6e6b9
-- title:
--   Two-stage product data and weak price order
-- statement:
--   There are two finite, independently indexed product catalogs $N^1=\{1,\ldots,n_1\}$ and $N^2=\{1,\ldots,n_2\}$. Stage $t$ has exogenous real prices $p_i^{(t)}$ and arbitrary real deterministic utilities $\mu_i^{(t)}$. The always available outside option is labeled $0$, with price and deterministic utility both zero. Ordinary products are ranked so that $p_1^{(t)}\ge\cdots\ge p_{n_t}^{(t)}$; ties are allowed and no sign restriction is imposed. The path price is $\widetilde p_{ij}=p_i^{(1)}+p_j^{(2)}$.
--
--   These data fix the customer's deterministic preferences and the seller's revenue from each two-stage purchase path. The price-order predicate is separate from the data and does not rank option zero against the products.
--
--   **Formalization Note** Each stage uses its own type `Fin (n_t + 1)`, with zero reserved for no purchase. Dimensions are arbitrary natural numbers, including zero. The fields normalizing the outside option are equalities, not assumptions about an optimum.
-- source:
--   Xu and Wang, Assortment Optimization for a Multi-Stage Choice Model, https://doi.org/10.1287/msom.2023.1224, held source.pdf (published citation basis; SSRN footer 3243742; catalog label 2018, PDF metadata 2023; PDF pages equal printed pages), §3, pp. 8–10; §4.2, p. 14

import Mathlib

namespace XuMultistage.Structure

/-- Stage-specific data; index zero is always the no-purchase option. -/
structure Model (n₁ n₂ : ℕ) where
  p₁ : Fin (n₁ + 1) → ℝ
  p₂ : Fin (n₂ + 1) → ℝ
  μ₁ : Fin (n₁ + 1) → ℝ
  μ₂ : Fin (n₂ + 1) → ℝ
  p₁_zero : p₁ 0 = 0
  p₂_zero : p₂ 0 = 0
  μ₁_zero : μ₁ 0 = 0
  μ₂_zero : μ₂ 0 = 0

/-- Prices of ordinary products are weakly decreasing; zero is not ranked. -/
def Model.Ordered {n₁ n₂ : ℕ} (M : Model n₁ n₂) : Prop :=
  (∀ i k : Fin (n₁ + 1), 0 < i → i ≤ k → M.p₁ k ≤ M.p₁ i) ∧
  (∀ j k : Fin (n₂ + 1), 0 < j → j ≤ k → M.p₂ k ≤ M.p₂ j)

/-- Total, undiscounted revenue of a two-stage choice path. -/
def Model.pathPrice {n₁ n₂ : ℕ} (M : Model n₁ n₂)
    (i : Fin (n₁ + 1)) (j : Fin (n₂ + 1)) : ℝ := M.p₁ i + M.p₂ j

end XuMultistage.Structure


