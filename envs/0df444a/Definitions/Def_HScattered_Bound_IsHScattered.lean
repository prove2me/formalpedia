-- Prove2me | Definitions.Def_HScattered_Bound_IsHScattered
-- name    : HScattered_Bound_IsHScattered
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:41.060989+00:00
-- url     : https://prove2.me/theorems/31823fc2-05f4-49a5-963f-72472dfdf3ea
-- title:
--   h-scattered 𝔽_q-subspaces of V(r, qⁿ) (Definition 1.1)
-- statement:
--   Let $\mathbb F_q \subseteq \mathbb F_{q^n}$ be finite fields and let $V$ be an $r$-dimensional vector space over $\mathbb F_{q^n}$; by restriction of scalars $V$ is also an $\mathbb F_q$-vector space. For an $\mathbb F_q$-subspace $U$ of $V$ write $\langle U\rangle_{\mathbb F_{q^n}}$ for its $\mathbb F_{q^n}$-span.
--
--   For an integer $h$ with $0 < h \le r-1$, the $\mathbb F_q$-subspace $U$ is called **$h$-scattered** if $\langle U\rangle_{\mathbb F_{q^n}} = V$ and every $h$-dimensional $\mathbb F_{q^n}$-subspace $S$ of $V$ meets $U$ in an $\mathbb F_q$-subspace of dimension at most $h$:
--
--   $$
--   \dim_{\mathbb F_q}(S \cap U) \le h \qquad\text{for every } S \le_{\mathbb F_{q^n}} V \text{ with } \dim_{\mathbb F_{q^n}} S = h .
--   $$
--
--   For $h = 1$ these are the scattered subspaces (with respect to the Desarguesian spread) that span $V$; for $h = r-1$ the condition concerns the hyperplanes of $V$. This is the central notion of the paper, shared by every statement of the mission.
--
--   **Formalization Note** $\mathbb F_q$ is a field `F`, $\mathbb F_{q^n}$ a field `K` with `[Algebra F K]`, and $V$ a `K`-module that is also an `F`-module through `[IsScalarTower F K V]`; $r$ is `Module.finrank K V`. The range $0 < h < r$ is part of the definition: without it every spanning subspace would be "$h$-scattered" for $h \ge r$, since $V$ has no $h$-dimensional subspaces then. The intersection $S\cap U$ is `S.restrictScalars F ⊓ U`. The definition itself is stated for arbitrary fields; finiteness of $\mathbb F_q$, $\mathbb F_{q^n}$ and of $\dim_{\mathbb F_{q^n}} V$ is assumed by the theorems that use it (if $V$ were infinite-dimensional, `Module.finrank K V = 0` and the range condition makes the predicate false, never vacuously true).
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 2, Definition 1.1

import Mathlib

namespace HScattered.Bound

/-- Definition 1.1 (Csajbók–Marino–Polverino–Zullo, arXiv:1906.10590v2, p. 2).
`V` is an `r`-dimensional `K`-vector space (`K = 𝔽_{qⁿ}`, `F = 𝔽_q`, `r = finrank K V`).
An `F`-subspace `U` of `V` is `h`-scattered, `0 < h ≤ r − 1`, if `⟨U⟩_K = V` and every
`h`-dimensional `K`-subspace `S` of `V` meets `U` in an `F`-subspace of dimension at most `h`.
The range `0 < h < r` is part of the definition. -/
def IsHScattered (F K : Type*) {V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    (h : ℕ) (U : Submodule F V) : Prop :=
  0 < h ∧ h < Module.finrank K V ∧
  Submodule.span K (U : Set V) = ⊤ ∧
  ∀ S : Submodule K V, Module.finrank K S = h →
    Module.finrank F ↥(S.restrictScalars F ⊓ U) ≤ h

end HScattered.Bound


