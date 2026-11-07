-- Prove2me | Definitions.Def_PCNonBool_nbrOn
-- name    : PCNonBool_nbrOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:41.903176+00:00
-- url     : https://prove2.me/theorems/87cd8ab0-8f3d-48ea-a380-d19f93ed55f8
-- title:
--   Neighbourhood $N_{V_a}(i)$ of a pigeon inside a set of holes
-- statement:
--   For a pigeon $i\in U$ and a set $V_a\subseteq V$ of holes, the **neighbourhood of $i$ in $V_a$** is
--   $$N_{V_a}(i)=\{\,j\in V_a : (i,j)\in E\,\}=N(i)\cap V_a .$$
--   For $V_a=V$ this is $N(i)$, the set of holes into which pigeon $i$ may fly.
--
--   The subscripted form is used for the subgraphs $G[U_a\sqcup V_a]$ that Algorithm 1 produces, where the degree of a pigeon is counted among the remaining holes only.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §3.2 (Graph Theory, Basics: $N(U)$ and $N_W(U)$), p.10 (PDF p.13)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph

namespace PCNonBool

/-- The holes in `Va` adjacent to the pigeon `i`, i.e. `N_{Va}(i) = N(i) ∩ Va`
(Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §3.2, p.10 (PDF p.13): "the neighborhood of U in W ⊆ V is N_W(U) = N(U) ∩ W").
With `Va = univ` this is `N(i)`, the set of holes of pigeon `i`. -/
def nbrOn {U V : Type*} (G : BipGraph U V) (Va : Finset V) (i : U) : Finset V :=
  Va.filter (G.Adj i)

end PCNonBool


