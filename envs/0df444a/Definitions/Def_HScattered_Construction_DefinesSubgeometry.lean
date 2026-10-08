-- Prove2me | Definitions.Def_HScattered_Construction_DefinesSubgeometry
-- name    : HScattered_Construction_DefinesSubgeometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:43.40517+00:00
-- url     : https://prove2.me/theorems/a6bed2d2-0d7a-49e0-b65d-1e1b390afed5
-- title:
--   An 𝔽_q-subspace defining a subgeometry of PG(V, 𝔽_{qⁿ})
-- statement:
--   Let $V$ be a vector space over $\mathbb F_{q^n}$ and $U$ an $\mathbb F_q$-subspace of $V$. We say that $U$ **defines a subgeometry** of the projective space $\mathrm{PG}(V,\mathbb F_{q^n})$ if some $\mathbb F_q$-basis of $U$ is also an $\mathbb F_{q^n}$-basis of $V$: there is a set $s\subseteq U$ with
--
--   $$
--   \langle s\rangle_{\mathbb F_q}=U,\qquad s \text{ is } \mathbb F_{q^n}\text{-linearly independent},\qquad \langle s\rangle_{\mathbb F_{q^n}} = V .
--   $$
--
--   Then the points $\langle u\rangle_{\mathbb F_{q^n}}$, $u\in U\setminus\{0\}$, form a copy of $\mathrm{PG}(r-1,q)$ inside $\mathrm{PG}(r-1,q^n)$. This is the first alternative of the paper's Theorem 2.3: an $h$-scattered subspace either defines a subgeometry or obeys the bound $rn/(h+1)$.
--
--   **Formalization Note** The paper uses the phrase without a displayed definition; this is the standard meaning (an $\mathbb F_q$-form of $V$). The set $s$ is automatically $\mathbb F_q$-linearly independent, hence an $\mathbb F_q$-basis of $U$, so $\dim_{\mathbb F_q}U=\dim_{\mathbb F_{q^n}}V$. For an $\mathbb F_q$-subspace of dimension $r=\dim_{\mathbb F_{q^n}}V$ that spans $V$ over $\mathbb F_{q^n}$ it holds automatically.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 4, Theorem 2.3 (first alternative)

import Mathlib

namespace HScattered.Construction

/-- An `𝔽_q`-subspace `U` of the `𝔽_{qⁿ}`-space `V` defines a subgeometry of `PG(V, 𝔽_{qⁿ})`
(arXiv:1906.10590v2, Theorem 2.3, p. 4) if some `𝔽_q`-basis of `U` is an `𝔽_{qⁿ}`-basis of `V`:
there is a set `s ⊆ U` that spans `U` over `𝔽_q`, is linearly independent over `𝔽_{qⁿ}` and
spans `V` over `𝔽_{qⁿ}`. Here `𝔽_q = F`, `𝔽_{qⁿ} = K`. -/
def DefinesSubgeometry (F K : Type*) {V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    (U : Submodule F V) : Prop :=
  ∃ s : Set V, s ⊆ (U : Set V) ∧ Submodule.span F s = U ∧
    LinearIndependent K (Subtype.val : s → V) ∧ Submodule.span K s = ⊤

end HScattered.Construction


