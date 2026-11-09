-- Prove2me | Definitions.Def_AbelianCayleyHDX_linkVerts
-- name    : AbelianCayleyHDX_linkVerts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:25:50.639188+00:00
-- url     : https://prove2.me/theorems/d761f731-c26b-4c90-875e-c9968232c40d
-- title:
--   Vertex set of the link of a vertex
-- statement:
--   For a triangle set $T$ and a vertex $v$, the **link** $X_v = \{\tau \setminus \{v\} : v \in \tau\}$ has as vertices the points $u \ne v$ that lie in a common triangle with $v$ (the neighbours of $v$ in the one-skeleton).
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.2, p.8; p.3

import Mathlib
import Definitions.Def_ReplParity_Vec
open ReplParity (Vec)

namespace AbelianCayleyHDX

/-- **The vertex set of the link of a vertex** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.2, p.8: `X_σ = {τ ∖ σ : σ ⊆ τ}`;
p.3: "the graph on its neighbors"): the vertices `u ≠ v` that lie in a triangle of `T` together
with `v`. -/
def linkVerts {n : ℕ} (T : Finset (Finset (Vec n))) (v : Vec n) : Finset (Vec n) :=
  Finset.univ.filter fun u => u ≠ v ∧ ∃ τ ∈ T, v ∈ τ ∧ u ∈ τ

end AbelianCayleyHDX


