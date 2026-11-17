-- Prove2me | Definitions.Def_AbelianCayleyHDX_Supplement_wLinkVerts
-- name    : AbelianCayleyHDX_Supplement_wLinkVerts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:03:10.598432+00:00
-- url     : https://prove2.me/theorems/ec3dddec-d712-465c-9f42-86e0a8f54c19
-- title:
--   Vertex set of the link of a face
-- statement:
--   For a face $\sigma$ of $X$, the link is $X_\sigma=\{\tau\setminus\sigma:\tau\in X,\ \sigma\subseteq\tau\}$. Its vertex set is
--   $$L(\sigma)=\{u\notin\sigma:\ \sigma\cup\{u\}\text{ is a face of }X\}.$$
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.2, p.8 (links)

import Mathlib
import Definitions.Def_ReplParity_Vec
open ReplParity (Vec)

namespace AbelianCayleyHDX.Supplement

/-- **The vertex set of the link of a face** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.2, p.8: the link of `σ` is
`X_σ = {τ ∖ σ : τ ∈ X, σ ⊆ τ}`): the vertices `u ∉ σ` such that `σ ∪ {u}` is contained in a
top face. -/
def wLinkVerts {n : ℕ} (tops : Finset (Finset (Vec n))) (σ : Finset (Vec n)) : Finset (Vec n) :=
  Finset.univ.filter fun u => u ∉ σ ∧ ∃ τ ∈ tops, insert u σ ⊆ τ

end AbelianCayleyHDX.Supplement


