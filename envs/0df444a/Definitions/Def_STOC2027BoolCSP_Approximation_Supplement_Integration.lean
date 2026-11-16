-- Prove2me | Definitions.Def_STOC2027BoolCSP_Approximation_Supplement_Integration
-- name    : STOC2027BoolCSP_Approximation_Supplement_Integration
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:30:09.818825+00:00
-- url     : https://prove2.me/theorems/e3fdc187-62c9-4b70-be48-a1fdfa79addb
-- title:
--   Orthant events, rational means and the input code of Lemma 8.2
-- statement:
--   Let $m\ge 0$. For a sign pattern $s\in\{-1,1\}^m$ the **closed orthant** of $s$ is
--   $$O_s=\{x\in\mathbb R^m:\ s_j x_j\ge 0\ \text{for every } j\}.$$
--   Its **antipodal pair** is $O_s\cup O_{-s}$. The target event of Lemma 8.2 is either $O_s$ (mode $0$) or $O_s\cup O_{-s}$ (mode $1$).
--
--   A rational vector $a\in\mathbb Q^m$ is viewed as a point of Euclidean space $\mathbb R^m$, the mean of the Gaussian law $N(a,V)$.
--
--   The **input code** of Lemma 8.2 is the bit string formed by the list of the $m$ rational entries of $a$, the rational $m\times m$ matrix $V$ (its size in unary and its entries row by row), the rational accuracy $\tau$, the $m$ sign bits of $s$, and one mode bit. Its length is the rational input bit length of the lemma.
--
--   These objects state the constant-dimensional Gaussian integration oracle used in the deterministic algorithm of Section 8.
--
--   **Formalization Note** Signs are Booleans (`true` is $+1$). Rationals, lists and matrices use the published codes `ratCode`, `listCode` and `sqMatCode` of the live mission. Orthants are closed; since $V\succeq I_m/4$ in Lemma 8.2, their boundaries are null sets and open orthants would give the same probabilities.
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, Approximation and Even Arity Hardness for Boolean Constraint Satisfaction, STOC 2027 submission #40 (October 2026), printed p. 18 (PDF 21), Lemma 8.2 and §8.3, equation (42)

import Mathlib
import Definitions.Def_STOC2027BoolCSP_Approximation_Instance
import Definitions.Def_STOC2027BoolCSP_Approximation_Encoding
import Definitions.Def_STOC2027BoolCSP_Approximation_SDP

namespace STOC2027BoolCSP.Approximation.Supplement

open STOC2027BoolCSP.Approximation

/-- The closed orthant `O_s = {x ∈ ℝ^m : sgn(s_j) x_j ≥ 0 for every j}` of the sign pattern
`s ∈ {-1,1}^m` (`true ↦ +1`). -/
def orthant {m : ℕ} (s : Fin m → Bool) : Set (EuclideanSpace ℝ (Fin m)) :=
  {x | ∀ j, 0 ≤ sgnOf (s j) * x j}

/-- The target event of Lemma 8.2: the single orthant `O_s` (`pair = false`) or the pair of
antipodal orthants `O_s ∪ O_{-s}` (`pair = true`). -/
def targetSet {m : ℕ} (s : Fin m → Bool) (pair : Bool) : Set (EuclideanSpace ℝ (Fin m)) :=
  if pair then orthant s ∪ orthant (fun j => !s j) else orthant s

/-- A rational vector as a point of Euclidean space `ℝ^m`. -/
noncomputable def ratVec {m : ℕ} (a : Fin m → ℚ) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun j => (a j : ℝ))

/-- The input code of Lemma 8.2: the mean `a` (list of rationals), the covariance `V` (rational
`m × m` matrix), the accuracy `τ`, the `m` sign bits of `s`, and one mode bit (`true` for the
antipodal pair). -/
def integrationCode {m : ℕ} (a : Fin m → ℚ) (V : Matrix (Fin m) (Fin m) ℚ) (τ : ℚ)
    (s : Fin m → Bool) (pair : Bool) : List Bool :=
  listCode ratCode (List.ofFn a) ++ sqMatCode V ++ ratCode τ ++ List.ofFn s ++ [pair]

end STOC2027BoolCSP.Approximation.Supplement


