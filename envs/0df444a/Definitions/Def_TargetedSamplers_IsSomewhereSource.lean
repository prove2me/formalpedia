-- Prove2me | Definitions.Def_TargetedSamplers_IsSomewhereSource
-- name    : TargetedSamplers_IsSomewhereSource
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:05:59.833327+00:00
-- url     : https://prove2.me/theorems/7dea1c87-223c-4b1f-9dc4-f985289f701b
-- title:
--   Somewhere-sources (Definition 4.6)
-- statement:
--   An **elementary $\ell$-wise somewhere-$(n,b)$-source** is a vector $(X_1,\dots,X_\ell)$ of random $n$-bit strings, some coordinate $X_i$ of which is an $(n,b)$-source. An **$\ell$-wise somewhere-$(n,b)$-source**, or $(n,b)^{1:\ell}$-source, is a convex combination of elementary ones.
--
--   **Formalization Note** The $\ell$ coordinates are indexed by a finite type (in the paper $[\ell]$). Convex combinations are finite; on the finite space $(\{0,1\}^n)^\ell$ this is no restriction (Carathéodory).
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Definition 4.6, p.21 (pdf p.23)

import Mathlib
import Definitions.Def_TargetedSamplers_IsSource

namespace TargetedSamplers

/-- An elementary somewhere-`(n, b)`-source over the index set `ι`: a distribution of a vector
`(X_i)_{i ∈ ι}` of `n`-bit strings some coordinate `X_i` of which is an `(n, b)`-source. -/
def IsElemSomewhereSource (ι : Type) (n : ℕ) (b : ℝ) (Z : PMF (ι → Fin n → Bool)) : Prop :=
  ∃ i : ι, IsSource n b (Z.map fun v => v i)

/-- A somewhere-`(n, b)`-source, `(n, b)^{1:ℓ}`-source, over the index set `ι` with `|ι| = ℓ`
(Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission, manuscript sha256 599d0a59…,
Definition 4.6, p.21): a convex combination of elementary `ℓ`-wise somewhere-`(n, b)`-sources.

**Formalization Note** The `ℓ` coordinates are indexed by a finite type `ι` (in the paper `[ℓ]`);
the convex combination is finite, which is no restriction on the finite space `({0,1}ⁿ)^ℓ`
(Carathéodory). -/
def IsSomewhereSource (ι : Type) (n : ℕ) (b : ℝ) (Z : PMF (ι → Fin n → Bool)) : Prop :=
  ∃ (N : ℕ) (c : PMF (Fin N)) (Y : Fin N → PMF (ι → Fin n → Bool)),
    (∀ j, IsElemSomewhereSource ι n b (Y j)) ∧ Z = c.bind Y

end TargetedSamplers


