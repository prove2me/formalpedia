-- Prove2me | Definitions.Def_AbelianCayleyHDX_Supplement_faceMass
-- name    : AbelianCayleyHDX_Supplement_faceMass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:01:32.861019+00:00
-- url     : https://prove2.me/theorems/0c187e36-331f-40b4-ba13-349082f2ae41
-- title:
--   Unnormalized induced weight of a face of a weighted complex over $\mathbb F_2^n$
-- statement:
--   Let $(X,\mu_d)$ be a weighted pure $d$-dimensional simplicial complex on the vertex set $\mathbb F_2^n$, given by its set $X(d)$ of top faces and a top-face weight $\mu_d$. For a set $\sigma$ of vertices put
--   $$m(\sigma)=\sum_{\tau\in X(d),\ \sigma\subseteq\tau}\mu_d(\tau).$$
--   The induced distribution on $i$-faces is $\mu_i(\sigma)=\binom{d+1}{i+1}^{-1}m(\sigma)$, so $m(\sigma)=\binom{d+1}{|\sigma|}\mu_{|\sigma|-1}(\sigma)$.
--
--   Comparing induced weights of faces of equal size, such as edge weights, amounts to comparing $m$.
--
--   **Formalization Note** Weights are rational; values of $\mu$ off $X(d)$ are never used.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.2, p.8 (induced distributions $\mu_i$)

import Mathlib
import Definitions.Def_ReplParity_Vec
open ReplParity (Vec)

namespace AbelianCayleyHDX.Supplement

/-- **Unnormalized induced weight of a face** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.2, p.8). A weighted pure
`d`-dimensional complex over `𝔽₂ⁿ` is given by its set `tops` of top faces (`d`-faces) and a top-face
weight `μ`; the induced distribution on `i`-faces is
`μ_i(σ) = binom(d+1, i+1)⁻¹ ∑_{τ ∈ X(d), σ ⊆ τ} μ_d(τ)`. This is the sum
`∑_{τ ∈ tops, σ ⊆ τ} μ(τ)`, i.e. `binom(d+1, |σ|) · μ_{|σ|-1}(σ)`.

**Formalization Note** The binomial normalization depends only on `|σ|`, so comparisons of the
induced weights of faces of the same size (edge weights, link weights) are comparisons of
`faceMass`. Values of `μ` off `tops` are never used. -/
def faceMass {n : ℕ} (tops : Finset (Finset (Vec n))) (μ : Finset (Vec n) → ℚ)
    (σ : Finset (Vec n)) : ℚ :=
  ∑ τ ∈ tops.filter (fun τ => σ ⊆ τ), μ τ

end AbelianCayleyHDX.Supplement


