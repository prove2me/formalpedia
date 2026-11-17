-- Prove2me | Definitions.Def_AbelianCayleyHDX_Supplement_HasCodimTwoLocalSpectralNorm
-- name    : AbelianCayleyHDX_Supplement_HasCodimTwoLocalSpectralNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:04:39.781266+00:00
-- url     : https://prove2.me/theorems/be945d34-2b0e-49b0-aaf6-099fdaf07dd6
-- title:
--   Two-sided codimension-two local spectral norm at most $\lambda$
-- statement:
--   A weighted $d$-dimensional complex $(X,\mu)$ has **two-sided codimension-two local spectral norm at most $\lambda$** if for every $(d-2)$-face $\sigma$ (a face with $d-1$ vertices) the weighted link graph $(L(\sigma),w_\sigma)$ is connected and its random-walk operator $P_\sigma$ satisfies
--   $$\big\|P_\sigma|_{\mathbf 1^{\perp\pi_\sigma}}\big\|_{\pi_\sigma}\le\lambda,$$
--   where $\pi_\sigma$ is the stationary measure of $P_\sigma$, i.e. the link graph is a two-sided $\lambda$-spectral expander.
--
--   For $d=2$ the codimension-two faces are the vertices and this is the usual two-sided condition on vertex links.
--
--   **Formalization Note** The spectral condition is the base mission's `IsTwoSidedSpectralExpander`. Used with $d\ge 2$.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.2, p.8

import Mathlib
import Definitions.Def_ReplParity_Vec
import Definitions.Def_AbelianCayleyHDX_IsTwoSidedSpectralExpander
import Definitions.Def_AbelianCayleyHDX_Supplement_IsFace
import Definitions.Def_AbelianCayleyHDX_Supplement_wLinkVerts
import Definitions.Def_AbelianCayleyHDX_Supplement_wLinkWeight
open ReplParity (Vec)

namespace AbelianCayleyHDX.Supplement

/-- **Two-sided codimension-two local spectral norm at most `λ`** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.2, p.8):
"`(X, μ_d)` has two-sided codimension-two local spectral norm at most `λ` if, for every
`σ ∈ X(d − 2)`, the weighted link graph `X_σ` is connected and `‖P_σ|_{1^⊥π_σ}‖_{π_σ} ≤ λ`".

The `(d − 2)`-faces are the faces with `d − 1` vertices; for each, the weighted link graph
(`wLinkVerts`, `wLinkWeight`) is a two-sided `λ`-spectral expander in the sense of the base
mission's `IsTwoSidedSpectralExpander` (connected, and the random-walk operator has norm at most
`λ` on the mean-zero functions of its stationary measure).

**Formalization Note** Used with `d ≥ 2`, so `d - 1` is the true difference. The link weights are
unnormalized (see `wLinkWeight`), which changes neither the walk nor its stationary measure. -/
def HasCodimTwoLocalSpectralNorm {n : ℕ} (d : ℕ) (tops : Finset (Finset (Vec n)))
    (μ : Finset (Vec n) → ℚ) (lam : ℝ) : Prop :=
  ∀ σ : Finset (Vec n), IsFace tops σ → σ.card = d - 1 →
    AbelianCayleyHDX.IsTwoSidedSpectralExpander (wLinkVerts tops σ) (wLinkWeight tops μ σ) lam

end AbelianCayleyHDX.Supplement


