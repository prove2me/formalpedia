-- Prove2me | Definitions.Def_PCNonBool_Var
-- name    : PCNonBool_Var
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:49.696453+00:00
-- url     : https://prove2.me/theorems/40a0b723-bcd8-4033-a1ae-2573324b0096
-- title:
--   Edge variables $x_{i,j}$, $(i,j)\in E$
-- statement:
--   The variables of the pigeonhole formulas on a bipartite graph $G=(U\sqcup V,E)$ are
--   $$\{\,x_{i,j} : i\in U,\ j\in N(i)\,\},$$
--   one variable for each edge $(i,j)\in E$. They are grouped by pigeon: $X_i=\{x_{i,j}:j\in N(i)\}$.
--
--   **Formalization Note** The variable type is the set of edges, so there is no variable for a non-edge.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §5.1 (variable groups $X_i$), p.27 (PDF p.30)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph

namespace PCNonBool

/-- The variables of FPHP(G): one variable `x_{i,j}` for each edge `(i, j)` of `G`
(Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §5.1, p.27 (PDF p.30): "the variables {x_{i,j} : i ∈ U, j ∈ N(U)}", grouped as
`X_i = {x_{i,j} : j ∈ N(i)}`).

**Formalization Note** Indexing by edges rather than by `U × V` means there is no variable for
a non-edge, exactly as in (33a)–(33d), where `x_{i,j}` occurs only for `j ∈ N(i)`. -/
abbrev Var {U V : Type*} (G : BipGraph U V) : Type _ := {e : U × V // G.Adj e.1 e.2}

end PCNonBool


