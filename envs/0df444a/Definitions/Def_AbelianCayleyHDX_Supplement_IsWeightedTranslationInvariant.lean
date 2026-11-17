-- Prove2me | Definitions.Def_AbelianCayleyHDX_Supplement_IsWeightedTranslationInvariant
-- name    : AbelianCayleyHDX_Supplement_IsWeightedTranslationInvariant
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:02:24.713388+00:00
-- url     : https://prove2.me/theorems/78725372-bdee-4613-be87-d48915877623
-- title:
--   Translation invariance of a weighted complex over $\mathbb F_2^n$
-- statement:
--   A weighted complex $(X,\mu)$ on $\mathbb F_2^n$ is **translation invariant** if its top-face distribution is invariant under translations: for every $g\in\mathbb F_2^n$ and every top face $\tau$, the translate $\tau+g$ is a top face and
--   $$\mu(\tau+g)=\mu(\tau).$$
--
--   Together with the Cayley-complex property this lets a complex be described by one representative per translation orbit, which is what an explicit construction outputs.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.3, p.9

import Mathlib
import Definitions.Def_ReplParity_Vec
open ReplParity (Vec)

namespace AbelianCayleyHDX.Supplement

/-- **Translation invariance of a weighted complex** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.3, p.9): "its top-face
distribution is invariant under translations by `𝔽₂ⁿ`": for every `g ∈ 𝔽₂ⁿ` and every top face
`τ`, the translate `τ + g` is a top face of the same weight.

**Formalization Note** Translation by `g` is a bijection of the finite set of `(d+1)`-sets, so
closure of `tops` under it together with `μ(τ + g) = μ(τ)` is exactly invariance of the top-face
distribution. -/
def IsWeightedTranslationInvariant {n : ℕ} (tops : Finset (Finset (Vec n)))
    (μ : Finset (Vec n) → ℚ) : Prop :=
  ∀ g : Vec n, ∀ τ ∈ tops, τ.image (· + g) ∈ tops ∧ μ (τ.image (· + g)) = μ τ

end AbelianCayleyHDX.Supplement


