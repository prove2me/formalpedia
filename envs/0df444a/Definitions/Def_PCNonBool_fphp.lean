-- Prove2me | Definitions.Def_PCNonBool_fphp
-- name    : PCNonBool_fphp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:30:40.780213+00:00
-- url     : https://prove2.me/theorems/cc01bdab-e701-48c0-b7e2-a4efcd7dd81d
-- title:
--   Functional pigeonhole principle FPHP$(G)$ ($\pm1$ encoding)
-- statement:
--   For a bipartite graph $G=(U\sqcup V,E)$, **FPHP$(G)$** is the set of polynomials
--   $$x_{i,j}^2-1,\qquad \prod_{j\in N(i)}(x_{i,j}+1),\qquad (x_{i,j}-1)(x_{i',j}-1),\qquad (x_{i,j}-1)(x_{i,j'}-1)$$
--   for $i\in U$, $j\in N(i)$; $i\ne i'\in U$, $j\in N(i)\cap N(i')$; and $j\ne j'\in N(i)$ (displays (33a)–(33d)). In the $\pm1$ encoding $x_{i,j}=-1$ means that pigeon $i$ flies to hole $j$. When $|U|>|V|$ the axioms have no common root, and the paper's first main result bounds the size of polynomial calculus refutations of FPHP$(G)$ from below.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §5, (33a)–(33d), p.25 (PDF p.28)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_Var
import Definitions.Def_PCNonBool_fphpOn

namespace PCNonBool

/-- The graph functional pigeonhole principle FPHP(G), the axioms (33a)–(33d) on the whole graph
(Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §5, p.25 (PDF p.28)). -/
def fphp {F : Type*} [Field F] {U V : Type*} [Fintype U] [Fintype V] (G : BipGraph U V) :
    Set (MvPolynomial (Var G) F) :=
  fphpOn G Finset.univ Finset.univ

end PCNonBool


