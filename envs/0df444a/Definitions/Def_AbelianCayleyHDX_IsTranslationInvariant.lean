-- Prove2me | Definitions.Def_AbelianCayleyHDX_IsTranslationInvariant
-- name    : AbelianCayleyHDX_IsTranslationInvariant
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:25:54.107402+00:00
-- url     : https://prove2.me/theorems/700d9d4d-7b3b-47ac-b603-99ed3a7885d3
-- title:
--   Translation-invariant triangle set
-- statement:
--   A triangle set $T$ in $\mathbb F_2^n$ is **translation invariant** if $\tau + g \in T$ for every $\tau \in T$ and $g \in \mathbb F_2^n$. For the uniform top-face distribution on $T$ this is exactly the paper's condition that the top-face distribution be invariant under translations by $\mathbb F_2^n$.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.3, p.9

import Mathlib
import Definitions.Def_ReplParity_Vec
open ReplParity (Vec)

namespace AbelianCayleyHDX

/-- **Translation invariance** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.3, p.9): "its top-face distribution is invariant
under translations by `𝔽₂ⁿ`".

**Formalization Note** The top-face distribution is uniform on the triangle set `T`, so it is
translation invariant iff `T` is: `τ + g ∈ T` for every `τ ∈ T` and `g ∈ 𝔽₂ⁿ` (translation is a
bijection of the finite set of 3-sets, so closure under it means invariance). -/
def IsTranslationInvariant {n : ℕ} (T : Finset (Finset (Vec n))) : Prop :=
  ∀ g : Vec n, ∀ τ ∈ T, τ.image (· + g) ∈ T

end AbelianCayleyHDX


