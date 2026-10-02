-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialB_CondD
-- name    : DiscreteConvex_CombinatorialB_CondD
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:33:42.919542+00:00
-- url     : https://prove2.me/theorems/1d06fbc7-1174-47e6-b367-300e7b6e253d
-- title:
--   Axiom (M♮-EXCd[R]) / Theorem 2.12 condition (d)
-- statement:
--   Axiom $(\mathrm{M}^\natural\text{-EXC}_d[\mathbb R])$: for $x,y$ and $i\in\operatorname{supp}^+(x-y)$, $\min_{j\in\operatorname{supp}^-(x-y)\cup\{0\}}[f'(x;-\chi_i+\chi_j)+f'(y;\chi_i-\chi_j)]\le 0$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.69, and Theorem 2.12(d), p.70.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.69, and Theorem 2.12(d), p.70

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialB_CharVec
import Definitions.Def_DiscreteConvex_CombinatorialB_DirDeriv
import Definitions.Def_DiscreteConvex_CombinatorialB_SuppPosR
import Definitions.Def_DiscreteConvex_CombinatorialB_SuppNegR

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.69, axiom (M♮-EXCd[R]) / Theorem 2.12
condition (d), in `DiscreteConvex.CombinatorialB`.
-/

namespace DiscreteConvex.CombinatorialB

/-- Axiom **(M-natural-EXCd[R])** (the book's `(M♮-EXCd[R])`) / Theorem 2.12 condition
**(d)**: for `x, y` and `i ∈ supp⁺(x-y)`,
`min_{j ∈ supp⁻(x-y) ∪ {0}} [f'(x;-χ_i+χ_j) + f'(y;χ_i-χ_j)] ≤ 0`, unfolded as an existential
disjunction over the same index set as `MNatExchangeR` (the `j = 0` case is the second
disjunct, `χ_0 = 0`). -/
def CondD {V : Type*} [Fintype V] [DecidableEq V] (M : Matrix V V ℝ) : Prop :=
  ∀ x y : V → ℝ, ∀ i ∈ SuppPosR (x - y),
    (∃ j ∈ SuppNegR (x - y),
      DirDeriv M x (-(CharVec i) + CharVec j) + DirDeriv M y (CharVec i - CharVec j) ≤ 0) ∨
    (DirDeriv M x (-(CharVec i)) + DirDeriv M y (CharVec i) ≤ 0)

end DiscreteConvex.CombinatorialB


