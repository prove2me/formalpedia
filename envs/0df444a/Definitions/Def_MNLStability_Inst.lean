-- Prove2me | Definitions.Def_MNLStability_Inst
-- name    : MNLStability_Inst
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:27:22.225711+00:00
-- url     : https://prove2.me/theorems/4201e446-ef3f-4e80-ab14-ab4ca9b0de97
-- title:
--   An instance of dynamic assortment planning under the MNL model
-- statement:
--   An **instance** consists of $n$ products, each with a preference weight $w_i$ and a per-unit selling price $r_i$, the no-purchase weight $w_0$, a capacity $C$ on the total number of units stocked, and the law $p_M$ of the number of customers $M$.
--
--   An instance is **valid** when
--
--   1. $n\ge1$ and $C\ge1$;
--   2. $w_0>0$ and $w_i>0$ for every product;
--   3. $r_i\ge0$ for every product;
--   4. $p_M$ is a finitely supported probability law on $\mathbb N$.
--
--   Every statement of the mission about whole instances assumes validity.
--
--   **Formalization Note** $n\ge1$ and $C\ge1$ exclude the empty instances, where the printed running-time bound $(nC)^{\dots}$ is $0$. $w_0>0$ excludes the $0/0$ of a customer facing an empty assortment.
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), §1.1, pp.3–4

import Mathlib
import Definitions.Def_MNLStability_Weights
import Definitions.Def_MNLStability_IsLaw

namespace MNLStability

/-- An instance of dynamic assortment planning under the MNL choice model (SSRN:3498325, §1.1,
pp.3–4): `n` products with weights and prices, the no-purchase weight `w₀`, the capacity `C` on the
total number of units, and the law `pM` of the number of customers `M`. -/
structure Inst (n : ℕ) where
  /-- The preference weights `(w₀, w₁, …, w_n)`. -/
  wts : Weights n
  /-- The per-unit selling price `rᵢ`. -/
  r : Fin n → ℝ
  /-- The capacity bound `C`. -/
  C : ℕ
  /-- The probability mass function of `M`. -/
  pM : ℕ →₀ ℝ

/-- A valid instance: at least one product, `C ≥ 1`, positive preference weights (including `w₀`),
non-negative prices, and `pM` a finitely supported probability law on `ℕ`.

**Formalization Note.** `1 ≤ n` and `1 ≤ C` exclude the empty instances, where the printed time
bound `(nC)^{…}` is `0`; `0 < w₀` excludes the `0/0` of a customer facing an empty assortment. -/
def Inst.Valid {n : ℕ} (I : Inst n) : Prop :=
  1 ≤ n ∧ 1 ≤ I.C ∧ I.wts.Pos ∧ (∀ i, 0 ≤ I.r i) ∧ IsLaw I.pM

end MNLStability


