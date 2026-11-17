-- Prove2me | Definitions.Def_AbelianCayleyHDX_Supplement_LinkConnected
-- name    : AbelianCayleyHDX_Supplement_LinkConnected
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:04:08.353179+00:00
-- url     : https://prove2.me/theorems/b09d6db1-0cc1-4756-aed1-4f5936a7978a
-- title:
--   Connectivity of the link of a face
-- statement:
--   The link of a face $\sigma$ is **connected** if the graph on $L(\sigma)$ in which $u\sim v$ iff $u\neq v$ and $\sigma\cup\{u,v\}$ is a face is connected: every two link vertices are joined by a path of link edges.
--
--   Under full support of $\mu$ the link edges are exactly the pairs with $w_\sigma(u,v)>0$, so this is connectivity of the weighted link graph.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.2, p.8; Theorem 1.3, p.4 ("all positive-dimensional links are connected")

import Mathlib
import Definitions.Def_ReplParity_Vec
import Definitions.Def_AbelianCayleyHDX_Supplement_wLinkVerts
open ReplParity (Vec)

namespace AbelianCayleyHDX.Supplement

/-- **The link of a face is connected** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.2, p.8; Theorem 1.3, p.4: "all
positive-dimensional links are connected"): the one-skeleton of the link `X_σ` — vertex set
`wLinkVerts tops σ`, with `u ~ v` iff `u ≠ v` and `σ ∪ {u, v}` lies in a top face — is connected:
any two link vertices are joined by a path of link edges.

**Formalization Note** Under full support of `μ` the link edges are exactly the pairs of positive
link weight, so this is connectivity of the weighted link graph. -/
def LinkConnected {n : ℕ} (tops : Finset (Finset (Vec n))) (σ : Finset (Vec n)) : Prop :=
  ∀ u ∈ wLinkVerts tops σ, ∀ v ∈ wLinkVerts tops σ,
    Relation.ReflTransGen
      (fun a b => a ∈ wLinkVerts tops σ ∧ b ∈ wLinkVerts tops σ ∧ a ≠ b ∧
        ∃ τ ∈ tops, insert a (insert b σ) ⊆ τ) u v

end AbelianCayleyHDX.Supplement


