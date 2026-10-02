-- Prove2me | Definitions.Def_TeschlODE_SturmLiouville_IsSymmetricOp
-- name    : TeschlODE_SturmLiouville_IsSymmetricOp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T11:19:55.906013+00:00
-- url     : https://prove2.me/theorems/947c496b-324e-4a70-a39d-c31dc8101e64
-- title:
--   Symmetric linear operator on a dense domain (5.36)
-- statement:
--   Let $H_0$ be a complex inner product space, with scalar product $\langle f, g\rangle$ conjugate linear in $f$ and linear in $g$ (5.19); $H_0$ is **not** assumed complete. A **linear operator** is a linear map $A : D(A) \to H_0$ defined on a linear subspace $D(A) \subseteq H_0$, its **domain**. The operator is **symmetric** if its domain is dense in $H_0$ and
--   $$\langle g, A f\rangle = \langle A g, f\rangle, \qquad f, g \in D(A). \qquad (5.36)$$
--
--   This is the notion under which the eigenvalue theory of Chapter 5 is developed; the Sturm–Liouville operator $L$ on its domain $D(L)$ is the main example.
--
--   **Formalization Note.** $H_0$ is a type `E` with `[NormedAddCommGroup E] [InnerProductSpace ℂ E]` (no `CompleteSpace`); the domain is a `Submodule ℂ E` and $A$ a `ℂ`-linear map from it to `E`. Mathlib's `inner ℂ` is conjugate linear in the first argument, as in the book. For operators defined on all of $H_0$ the later statements use Mathlib's `LinearMap.IsSymmetric`, which is the same condition (density of $H_0$ in itself is automatic).
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 149, §5.2, Eq. (5.35)–(5.36)

import Mathlib

namespace TeschlODE.SturmLiouville

/-- Teschl §5.2, p. 149, (5.35)–(5.36): a linear operator `A : D(A) → H₀`, defined on a linear
subspace `D(A)` of the inner product space `H₀`, is *symmetric* if its domain is dense and
`⟨g, A f⟩ = ⟨A g, f⟩` for all `f, g ∈ D(A)`. The inner product is conjugate linear in the first
argument, as in (5.19). -/
def IsSymmetricOp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (D : Submodule ℂ E) (A : D →ₗ[ℂ] E) : Prop :=
  Dense (D : Set E) ∧ ∀ f g : D, inner ℂ (g : E) (A f) = inner ℂ (A g) (f : E)

end TeschlODE.SturmLiouville


