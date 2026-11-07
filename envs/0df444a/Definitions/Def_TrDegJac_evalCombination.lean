-- Prove2me | Definitions.Def_TrDegJac_evalCombination
-- name    : TrDegJac_evalCombination
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:35:43.073718+00:00
-- url     : https://prove2.me/theorems/eca536ab-56d5-4073-aa01-542e9fb99f7a
-- title:
--   The evaluation map $\varphi(A_1,\dots,A_m)=\sum_i A_i(f)\,g_i$
-- statement:
--   Let $f_1,\dots,f_k,g_1,\dots,g_m\in\mathbb F[x_1,\dots,x_n]$. The map
--   $$
--   \varphi:\mathbb F[y_1,\dots,y_k]^m\to\mathbb F[x],\qquad (A_1,\dots,A_m)\mapsto\sum_{i=1}^m A_i(f)\cdot g_i,
--   $$
--   substitutes $f$ for $y$ in each $A_i$ and forms the combination with multipliers $g_i$. It is $\mathbb F$-linear.
--
--   It turns linear dependence of the $g_i$ over $\mathbb F(f)$ into a dimension count (Lemma 3.22).
--
--   **Formalization Note** $A_i(f)$ is `MvPolynomial.aeval f (A i)`; the map is bundled as an `F`-linear map.
-- source:
--   Forbes and Staicu, Approximating Transcendence Degree in Medium Characteristic, STOC 2027 submission (manuscript sha256 3ab72a42…), Lemma 3.22, p.17

import Mathlib

set_option autoImplicit false

namespace TrDegJac

/-- **The evaluation map of Lemma 3.22** — Forbes and Staicu, *Approximating Transcendence Degree in
Medium Characteristic*, STOC 2027 submission (manuscript sha256 3ab72a42…), Lemma 3.22, p.17:
"Consider the linear map φ : F[y]^m → F[x] defined by (A₁, …, A_m) ↦ ∑_{i=1}^m A_i(f) · g_i."

Here `f = (f₁, …, f_k)` are substituted for the variables `y₁, …, y_k` and `g = (g₁, …, g_m)` are
the multipliers; the map is `F`-linear.

**Formalization Note.** `F[y]` is `MvPolynomial (Fin k) F` and `A_i(f)` is `MvPolynomial.aeval f (A i)`.
-/
noncomputable def evalCombination {F : Type*} [Field F] {n k m : ℕ}
    (f : Fin k → MvPolynomial (Fin n) F) (g : Fin m → MvPolynomial (Fin n) F) :
    (Fin m → MvPolynomial (Fin k) F) →ₗ[F] MvPolynomial (Fin n) F where
  toFun A := ∑ i, MvPolynomial.aeval f (A i) * g i
  map_add' A B := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c A := by simp [Finset.mul_sum, MvPolynomial.smul_eq_C_mul, mul_assoc]

end TrDegJac


