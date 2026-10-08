-- Prove2me | Definitions.Def_HScattered_Construction_IsHScattered
-- name    : HScattered_Construction_IsHScattered
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:28:22.666045+00:00
-- url     : https://prove2.me/theorems/eb467f74-1ee4-4288-8624-63eb7641432a
-- title:
--   h-scattered and maximum h-scattered 𝔽_q-subspaces (Definition 1.1)
-- statement:
--   Let $\mathbb F_q \subseteq \mathbb F_{q^n}$ be finite fields and let $V$ be an $r$-dimensional vector space over $\mathbb F_{q^n}$, regarded also as a vector space over $\mathbb F_q$ by restriction of scalars. For an integer $h$ with $0<h\le r-1$, an $\mathbb F_q$-subspace $U$ of $V$ is called **$h$-scattered** if
--
--   1. $U$ spans $V$ over the larger field, $\langle U\rangle_{\mathbb F_{q^n}} = V$, and
--   2. every $h$-dimensional $\mathbb F_{q^n}$-subspace $S$ of $V$ meets $U$ in an $\mathbb F_q$-subspace of small dimension:
--
--   $$
--   \dim_{\mathbb F_q}(S\cap U)\le h .
--   $$
--
--   An $h$-scattered subspace is **maximum $h$-scattered** if no $h$-scattered $\mathbb F_q$-subspace of $V$ has larger $\mathbb F_q$-dimension.
--
--   For $h=1$ these are the scattered subspaces (with respect to the Desarguesian spread) that span $V$. The notion interpolates between scattered subspaces and, for $h=r-1$, subspaces meeting every hyperplane in dimension at most $r-1$, which correspond to MRD codes.
--
--   **Formalization Note** $\mathbb F_q$ is a finite field `F`, $\mathbb F_{q^n}$ a finite field `K` with `Algebra F K`, and $V$ a `K`-module with a compatible `F`-module structure (`IsScalarTower F K V`). The range $0<h<r$, $r=\dim_{\mathbb F_{q^n}}V$, is part of the definition: without it every spanning $U$ would be $h$-scattered for $h\ge r$. "Maximum" compares $\mathbb F_q$-dimensions over all $h$-scattered subspaces of the same $V$.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 2, Definition 1.1

import Mathlib
import Definitions.Def_HScattered_Bound_IsHScattered

namespace HScattered.Construction

/-- Definition 1.1 (p. 2): an h-scattered subspace of highest possible dimension. -/
def IsMaximumHScattered (F K : Type*) {V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    (h : ℕ) (U : Submodule F V) : Prop :=
  HScattered.Bound.IsHScattered F K h U ∧
    ∀ U' : Submodule F V, HScattered.Bound.IsHScattered F K h U' → Module.finrank F U' ≤ Module.finrank F U

end HScattered.Construction


