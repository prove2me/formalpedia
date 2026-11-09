-- Prove2me | Definitions.Def_TermCycDich_HasRedGrid
-- name    : TermCycDich_HasRedGrid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:43:46.795574+00:00
-- url     : https://prove2.me/theorems/7b1ff51d-67d3-40b1-b606-64c452a09e31
-- title:
--   All-red grid red-minor $(\Gamma_k, V(\Gamma_k)) \preceq (G,R)$
-- statement:
--   $(G, R)$ **contains the all-red $(k\times k)$-grid** if $(\Gamma_k, V(\Gamma_k))$ is a red-minor of $(G,R)$, where $\Gamma_k$ is the $(k\times k)$-grid (vertices $(i,j)$, $1\le i,j\le k$, adjacent when $|i-i'|+|j-j'|=1$) and every vertex of $\Gamma_k$ is red. Thus every branch set of the model contains a vertex of $R$.
--
--   **Formalization Note** $\Gamma_k$ is the public `RobertsonSeymour1986.GM5.grid k`. $\Gamma_0$ is empty, so $k=0$ always qualifies.
-- source:
--   Bentert–Cavallaro–Wiederrecht, A Dichotomy for Terminal Cyclability, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Section 2.1, p.16 (PDF 18)

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_grid
import Definitions.Def_TermCycDich_IsRedMinor

namespace TermCycDich

/-- `(G, R)` contains the **all-red `(k × k)`-grid** `(Γ_k, V(Γ_k))` as a red-minor.

Bentert–Cavallaro–Wiederrecht, *A Dichotomy for Terminal Cyclability*, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Section 2.1, p.16 (PDF 18): "there exists (Γ_k, V(Γ_k)) as a red-minor in (G, R) where
Γ_k denotes the (k × k)-grid."

**Formalization Note** `Γ_k` is the public `RobertsonSeymour1986.GM5.grid k` on `Fin k × Fin k`
(adjacency `|i − i'| + |j − j'| = 1`), every vertex red (`Set.univ`). `Γ_0` is the empty graph,
so `HasRedGrid G R 0` always holds; `Γ_1` needs a red vertex. -/
def HasRedGrid {V : Type} (G : SimpleGraph V) (R : Set V) (k : ℕ) : Prop :=
  IsRedMinor (RobertsonSeymour1986.GM5.grid k) Set.univ G R

end TermCycDich


