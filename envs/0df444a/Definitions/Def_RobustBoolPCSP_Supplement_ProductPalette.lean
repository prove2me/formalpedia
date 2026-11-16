-- Prove2me | Definitions.Def_RobustBoolPCSP_Supplement_ProductPalette
-- name    : RobustBoolPCSP_Supplement_ProductPalette
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:27:20.083943+00:00
-- url     : https://prove2.me/theorems/fde07a67-311b-487f-bc1f-e5cd26ed1492
-- title:
--   The fixed product-test architecture of §7.5
-- statement:
--   A **palette** consists of finitely many test types with nonnegative weights summing to one: $J$ four-query types, each with a fixed distribution $\lambda_j$ on $\{0,1\}^4$, and unary types, each with a bit probability and a pin. For code length $N$ a four-query test samples $N$ independent columns from $\lambda_j$, applies the same Boolean function to the four query strings (up to coordinate permutations) and checks the tuple against $Q$ of $T^*$; a unary test samples a biased product query and checks the pin. With $\delta_j=\lambda_j(\{0,1\}^4\setminus P)$, and $\delta_j$ the dictator's pin error for a unary type, a common dictator has strong error $\epsilon=\sum_jw_j\delta_j$.
--
--   The module also defines the weak error of a code function and the resampling influence of a coordinate under a product measure.
--
--   This is the architecture of the limitation result Theorem 7.16.
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), §7.5, p.66

import Mathlib
import Definitions.Def_RobustBoolPCSP_Supplement_Witness
import Definitions.Def_RobustBoolPCSP_Supplement_BalanceTester

set_option autoImplicit false

namespace RobustBoolPCSP.Supplement

/-- A **fixed product-test architecture** ("palette") for `T∗`.
Cai, Jiang, Zou, *On Robust Promise CSPs*, STOC 2027 submission (manuscript of 2026-11-03, sha256
fd1be0d0…), §7.5, p.66: "In this architecture, there are finitely many test types, with nonnegative
weights summing to one. Each of the J arity-four types is assigned a fixed distribution λ_j on
{0, 1}⁴. For code length N, a test samples N independent columns from its distribution. It applies
the same Boolean function to the four query strings and checks the resulting tuple against Q. Unary
types may sample a product query with a specified bit probability and test a specified pin. The
distributions, weights, and types remain fixed as N → ∞ … Query coordinate permutations are
allowed."

**Formalization Note.** `J` four-query types `j : Fin J` with column distributions `lam j` and
weights `w4 j`; `K` unary types `k : Fin K` with bit probability `pu k`, pin value `pin k` and weight
`wu k`. The query coordinate permutations depend on `N` and are arguments of `paletteWeakErr`. -/
structure Palette where
  /-- The number `J` of arity-four test types. -/
  J : ℕ
  /-- The column distribution `λ_j` on `{0,1}⁴` of each arity-four type. -/
  lam : Fin J → (Fin 4 → Bool) → ℝ
  lam_nonneg : ∀ j x, 0 ≤ lam j x
  lam_sum : ∀ j, ∑ x, lam j x = 1
  /-- The weight of each arity-four type. -/
  w4 : Fin J → ℝ
  w4_nonneg : ∀ j, 0 ≤ w4 j
  /-- The number of unary (pin) test types. -/
  K : ℕ
  /-- The bit probability of the product query of each unary type. -/
  pu : Fin K → ℝ
  pu_mem : ∀ k, 0 ≤ pu k ∧ pu k ≤ 1
  /-- The pin tested by each unary type. -/
  pin : Fin K → Bool
  /-- The weight of each unary type. -/
  wu : Fin K → ℝ
  wu_nonneg : ∀ k, 0 ≤ wu k
  /-- The weights sum to one. -/
  w_sum : ∑ j, w4 j + ∑ k, wu k = 1

/-- `δ_j = λ_j({0,1}⁴ \ P)` for an arity-four type (p.66). -/
noncomputable def Palette.delta4 (pal : Palette) (j : Fin pal.J) : ℝ :=
  ∑ x, outside PStar x * pal.lam j x

/-- For a unary type, `δ_k` is "the strong pin error of a dictator" (p.66): the probability that a
`pu k`-biased bit differs from the pin. -/
def Palette.deltaU (pal : Palette) (k : Fin pal.K) : ℝ :=
  if pal.pin k then 1 - pal.pu k else pal.pu k

/-- `ϵ = Σ_j w_j δ_j`, the strong error of a common dictator (p.66). -/
noncomputable def Palette.eps (pal : Palette) : ℝ :=
  ∑ j, pal.w4 j * pal.delta4 j + ∑ k, pal.wu k * pal.deltaU k

/-- The weak error of the code function `F : {0,1}^N → {0,1}` in the palette, with query coordinate
permutations `σ j i` for query `i` of type `j`: each arity-four type samples `N` independent columns
from `λ_j`, forms the four query strings (query `i` reads its coordinate `n` from column
`σ j i n`), applies `F` to each, and rejects when the tuple is outside `Q` of `T∗`; each unary type
samples a `pu k`-biased product query and rejects when `F` differs from the pin. -/
noncomputable def paletteWeakErr (pal : Palette) (N : ℕ) (F : (Fin N → Bool) → Bool)
    (σ : Fin pal.J → Fin 4 → Equiv.Perm (Fin N)) : ℝ :=
  ∑ j, pal.w4 j * ∑ cols : Fin N → Fin 4 → Bool,
      (∏ n, pal.lam j (cols n)) * outside QStar (fun i => F (fun n => cols (σ j i n) i)) +
  ∑ k, pal.wu k * ∑ X : Fin N → Bool, wordProb (pal.pu k) X * (if F X = pal.pin k then 0 else 1)

/-- The query bit probabilities of the palette: the coordinate marginals `λ_j({x : x_i = 1})` of the
arity-four types and the bit probabilities of the unary types. -/
def Palette.queryBias (pal : Palette) : Set ℝ :=
  {p | (∃ j i, p = ∑ x, (if x i then pal.lam j x else 0)) ∨ ∃ k, p = pal.pu k}

/-- The (resampling) influence of coordinate `i` on `F` under the product measure `μ_p^N`:
`P[F(X) ≠ F(X')]`, where `X ∼ μ_p^N` and `X'` is `X` with coordinate `i` redrawn independently from
Bernoulli(`p`). It vanishes for degenerate `p ∈ {0, 1}`. -/
noncomputable def resampInf {N : ℕ} (p : ℝ) (F : (Fin N → Bool) → Bool) (i : Fin N) : ℝ :=
  ∑ X : Fin N → Bool, ∑ b : Bool,
    wordProb p X * bitProb p b * (if F X = F (Function.update X i b) then 0 else 1)

end RobustBoolPCSP.Supplement


