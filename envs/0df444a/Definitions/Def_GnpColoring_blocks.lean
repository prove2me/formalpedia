-- Prove2me | Definitions.Def_GnpColoring_blocks
-- name    : GnpColoring_blocks
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:31:23.94167+00:00
-- url     : https://prove2.me/theorems/cd1f9921-5b93-473d-b36f-587474b45912
-- title:
--   The blocks $\mathcal B$ of a vertex set $S$
-- statement:
--   For a vertex set $S$, the **blocks** are the vertex sets of the connected components of $G$ after removing all vertices of $S$:
--
--   $$\mathcal B=\{\text{block of }v:\ v\notin S\}.$$
--
--   The vertices of $S$ are the *singletons*. With $S=\hat S$ this is the family $\hat{\mathcal B}$ of Section 4.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Definition 3.2, p.15; Section 4, p.35

import Mathlib
import Definitions.Def_GnpColoring_blockOf

open scoped Classical
open Finset

namespace GnpColoring

/-- **The blocks** `𝓑` of `S`: the vertex sets of the connected components of `G` after removing
all vertices of `S`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Definition 3.2, p.15 ("We refer to every component in 𝓑 as a block and to the vertices in
S as singletons"); with `S = Ŝ` this is `𝓑̂`, Section 4, p.35 ("Let 𝓑̂ be the collection of vertex
sets of the connected components of G[V ∖ Ŝ]"). -/
noncomputable def blocks {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (univ.filter fun v => v ∉ S).image (blockOf G S)

end GnpColoring


