-- Prove2me | Definitions.Def_AvgCaseTI_AlgIso
-- name    : AvgCaseTI_AlgIso
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:08.815549+00:00
-- url     : https://prove2.me/theorems/10005bb2-bcf1-4782-b0bf-51490d9a08d9
-- title:
--   Isomorphism of algebras given by structure constants
-- statement:
--   Two algebras $A,B\in T(n\times n\times n,\mathbb F)$ (structure tensors, with multiplications $g_A,g_B$) are **isomorphic** when there is an invertible linear map $\varphi:\mathbb F^n\to\mathbb F^n$ with
--   $$
--   \varphi\bigl(g_A(x,y)\bigr)=g_B\bigl(\varphi(x),\varphi(y)\bigr)\qquad\text{for all }x,y\in\mathbb F^n .
--   $$
--   This is the paper's relation "$B=(T\otimes T\otimes T^{-t})\cdot A$ for some $T\in\mathrm{GL}(n,q)$", the natural action of $\mathrm{GL}(U)$ on $U\otimes U\otimes U^*$: the linear bijection $\varphi$ plays the role of $T$.
--
--   Algebra isomorphism is the decision problem of Theorem 1.1.
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), §3.1, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_AvgCaseTI_Tensor3

set_option autoImplicit false

namespace AvgCaseTI

/-- **Isomorphism of algebras given by structure constants.**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), §3.1, p.16 (PDF p.18):
"We see that A and B are isomorphic as algebras if and only if there exists T ∈ GL(n, q) such that
B = (T ⊗ T ⊗ T^{−t}) · A."

`AlgIso A B` holds when some linear bijection `φ` of `K^n` carries the multiplication of `A` to that of
`B`: `φ(g_A(x, y)) = g_B(φ x, φ y)` for all `x, y`.

**Formalization Note.** This is the action of `GL(U)` on `U ⊗ U ⊗ U*` without index conventions:
`B = (T ⊗ T ⊗ T^{−t}) · A` says exactly that `T` (or `T^{-1}`, by symmetry of the relation) is such a
`φ`. -/
def AlgIso {K : Type*} [Field K] {n : ℕ} (A B : Tensor3 K n) : Prop :=
  ∃ φ : (Fin n → K) ≃ₗ[K] (Fin n → K), ∀ x y : Fin n → K, φ (mulMap A x y) = mulMap B (φ x) (φ y)

end AvgCaseTI


