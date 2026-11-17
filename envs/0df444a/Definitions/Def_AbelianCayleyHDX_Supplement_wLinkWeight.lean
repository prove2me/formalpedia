-- Prove2me | Definitions.Def_AbelianCayleyHDX_Supplement_wLinkWeight
-- name    : AbelianCayleyHDX_Supplement_wLinkWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:03:38.70761+00:00
-- url     : https://prove2.me/theorems/1c496e65-3e56-4262-8587-f9fa8a8887cf
-- title:
--   Edge weights of the weighted link graph of a face
-- statement:
--   Let $(X,\mu)$ be a weighted complex and $\sigma$ a face. The link $X_\sigma$ carries the top-face distribution obtained by conditioning $\mu$ on $\sigma\subseteq\tau$, and its weighted link graph is its one-skeleton with induced edge weights. For link vertices $u\neq v$ these weights are proportional to
--   $$w_\sigma(u,v)=\sum_{\tau\in X(d),\ \sigma\cup\{u,v\}\subseteq\tau}\mu(\tau),$$
--   and $w_\sigma(u,u)=0$.
--
--   **Formalization Note** The weight is unnormalized: the conditioning and the binomial normalization multiply all link edge weights by the same constant, which changes neither the random-walk operator nor its stationary measure. Rational weights are cast to $\mathbb R$.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.2, p.8 (links and their top-face distribution)

import Mathlib
import Definitions.Def_ReplParity_Vec
open ReplParity (Vec)

namespace AbelianCayleyHDX.Supplement

/-- **The edge weights of the weighted link graph of a face** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.2, p.8): the
link `X_σ` is "equipped with the top-face distribution obtained by conditioning `μ_d` on the event
`σ ⊆ τ`", and its weighted link graph is its one-skeleton with the induced edge weights. For link
vertices `u ≠ v` the induced weight of the link edge `{u, v}` is proportional to
`∑_{τ ∈ X(d), σ ∪ {u, v} ⊆ τ} μ_d(τ)`; the diagonal gets weight `0` (no loops).

**Formalization Note** The weight is unnormalized: the conditioned distribution divides by
`∑_{τ ⊇ σ} μ_d(τ)` and the induced measure on link edges by a binomial depending only on `d` and
`|σ|`; the random-walk operator and its stationary measure do not change under this common scaling.
The rational weights are cast to `ℝ`. For `|σ| = d - 1` the sum has the single term
`μ(σ ∪ {u, v})`. -/
noncomputable def wLinkWeight {n : ℕ} (tops : Finset (Finset (Vec n))) (μ : Finset (Vec n) → ℚ)
    (σ : Finset (Vec n)) (u v : Vec n) : ℝ :=
  if u = v then 0 else ∑ τ ∈ tops.filter (fun τ => insert u (insert v σ) ⊆ τ), (μ τ : ℝ)

end AbelianCayleyHDX.Supplement


