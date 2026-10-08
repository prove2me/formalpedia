-- Prove2me | Definitions.Def_HScattered_Hyperplanes_IsHScattered
-- name    : HScattered_Hyperplanes_IsHScattered
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:47.589977+00:00
-- url     : https://prove2.me/theorems/af610fde-8fcc-4dcf-91c0-451b7fa042ae
-- title:
--   h-scattered and maximum h-scattered 𝔽_q-subspaces (Definition 1.1)
-- statement:
--   Let $\mathbb F_q \subseteq \mathbb F_{q^n}$ be finite fields and let $V = V(r,q^n)$ be an $r$-dimensional vector space over $\mathbb F_{q^n}$, regarded also as a vector space over $\mathbb F_q$.
--
--   An $\mathbb F_q$-subspace $U$ of $V$ is called **$h$-scattered**, where $0 < h \le r-1$, if
--
--   1. $U$ spans $V$ over the larger field: $\langle U\rangle_{\mathbb F_{q^n}} = V$, and
--   2. every $h$-dimensional $\mathbb F_{q^n}$-subspace $S$ of $V$ meets $U$ in an $\mathbb F_q$-subspace of dimension at most $h$:
--   $$\dim_{\mathbb F_q}(S \cap U) \le h .$$
--
--   An $h$-scattered subspace is **maximum $h$-scattered** if its $\mathbb F_q$-dimension is the largest among all $h$-scattered $\mathbb F_q$-subspaces of $V$.
--
--   For $h = 1$ this is the classical notion of a scattered subspace; the definition is the basic object of the whole paper.
--
--   **Formalization Note** The field $\mathbb F_q$ is `F`, $\mathbb F_{q^n}$ is `K`, and $V$ carries compatible `F`- and `K`-module structures (`IsScalarTower F K V`); $r$ is `Module.finrank K V`. The range $0 < h < r$ is part of the predicate, so for $h \ge r$ nothing is $h$-scattered.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 2, Definition 1.1

import Mathlib

namespace HScattered.Hyperplanes

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

/-- Definition 1.1 (p. 2): a maximum `h`-scattered subspace is an `h`-scattered `F`-subspace
of `V` of highest possible `F`-dimension among all `h`-scattered `F`-subspaces of `V`. -/
def IsMaximumHScattered (F K : Type*) {V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    (h : ℕ) (U : Submodule F V) : Prop :=
  IsHScattered F K h U ∧
    ∀ U' : Submodule F V, IsHScattered F K h U' → Module.finrank F U' ≤ Module.finrank F U

end HScattered.Hyperplanes


