-- Prove2me | Definitions.Def_STOC2027BoolCSP_Approximation_Supplement_ConjOpt
-- name    : STOC2027BoolCSP_Approximation_Supplement_ConjOpt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:30:36.410204+00:00
-- url     : https://prove2.me/theorems/0642bd70-4007-4d80-ac67-7d80ab0db9b0
-- title:
--   Value and optimum of a signed-conjunction instance; the all-sign-pattern gap instance
-- statement:
--   Let $I$ be a weighted instance of signed $k$-conjunctions on variables $x_1,\dots,x_n\in\{-1,1\}$: each clause $C$ is a conjunction $x_i=\sigma_{C,i}$ for $i\in C$, over $k$ distinct variables, with rational weight $w_C$. For an assignment $x$,
--   $$\mathrm{val}_I(x)=\sum_C w_C\,\mathbf 1[x_i=\sigma_{C,i}\ \text{for all } i\in C],\qquad \mathrm{OPT}(I)=\max_{x\in\{-1,1\}^n}\mathrm{val}_I(x).$$
--
--   The **gap instance** of Section 9 has $n=k$ variables and, for every sign vector $\sigma\in\{-1,1\}^k$, the clause
--   $$C_\sigma:\quad x_i=\sigma_i\quad(1\le i\le k),$$
--   all $2^k$ clauses carrying the same weight $w$. Every assignment satisfies exactly one of them.
--
--   These objects state the exact relaxation gap, Theorem 1.3: $\mathrm{OPT}$ is compared with the value of the common-reference relaxation (5) of the live mission.
--
--   **Formalization Note** The $2^k$ clauses are indexed by $\sigma\in\{0,\dots,2^k-1\}$, position $j$ carrying binary digit $j$ of $\sigma$ (`true` is $+1$); this is a bijection onto $\{-1,1\}^k$. The maximum is `Finset.sup'` over all $2^n$ assignments.
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, Approximation and Even Arity Hardness for Boolean Constraint Satisfaction, STOC 2027 submission #40 (October 2026), printed p. 6, 21 (PDF 9, 24), Section 3 and Section 9

import Mathlib
import Definitions.Def_STOC2027BoolCSP_Approximation_Instance
import Definitions.Def_STOC2027BoolCSP_Approximation_SDP

namespace STOC2027BoolCSP.Approximation.Supplement

open STOC2027BoolCSP.Approximation

/-- The value `Σ_C w_C 1[C satisfied by x]` of an assignment `x ∈ {-1,1}^n` of a weighted
signed-conjunction instance; clause `C` is satisfied when `x_{vars j} = σ_{C,j}` for every `j`. -/
noncomputable def conjVal {k : ℕ} (C : ConjInstance k) (x : Fin C.n → Bool) : ℝ :=
  ∑ c, if (∀ j, x ((C.clause c).vars j) = (C.clause c).sign j) then (C.w c : ℝ) else 0

/-- `OPT(I)` of a conjunction instance: the maximum of `conjVal` over all `2^n` assignments. -/
noncomputable def conjOpt {k : ℕ} (C : ConjInstance k) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (conjVal C)

/-- The sign pattern with index `σ < 2^k`: position `j` carries bit `j` of `σ` (`true ↦ +1`).
This is a bijection `Fin (2^k) → {-1,1}^k`. -/
def signPattern (k : ℕ) (σ : Fin (2 ^ k)) : Fin k → Bool := fun j => Nat.testBit σ.val j.val

/-- The gap instance of Section 9: `k` variables and, for every sign vector `σ ∈ {-1,1}^k`, the
conjunction `x_i = σ_i (1 ≤ i ≤ k)` on all `k` variables, every clause with the same weight `w`. -/
def allSignInstance (k : ℕ) (w : ℚ) : ConjInstance k where
  n := k
  M := 2 ^ k
  clause σ := { vars := id, vars_inj := Function.injective_id, sign := signPattern k σ }
  w _ := w

end STOC2027BoolCSP.Approximation.Supplement


