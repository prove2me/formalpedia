-- Prove2me | Definitions.Def_PCNonBool_localAxioms
-- name    : PCNonBool_localAxioms
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:30:10.86062+00:00
-- url     : https://prove2.me/theorems/92b67ca5-3e12-4394-a589-833b0190b620
-- title:
--   Local axioms $A_i$ of a pigeon
-- statement:
--   For a pigeon $i\in U$, the set of axioms of FPHP$(G)$ that mention only pigeon $i$ is (display (35))
--   $$A_i=\{x_{i,j}^2-1 : j\in N(i)\}\ \cup\ \Bigl\{\prod_{j\in N(i)}(x_{i,j}+1)\Bigr\}\ \cup\ \{(x_{i,j}-1)(x_{i,j'}-1) : j\ne j'\in N(i)\}.$$
--   Its common roots are the $\pm1$ assignments to the variables of $i$ with exactly one $-1$.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §5.1, display (35), p.27 (PDF p.30)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_nbrOn
import Definitions.Def_PCNonBool_Var
import Definitions.Def_PCNonBool_xv

namespace PCNonBool

/-- The axioms of FPHP(G) that mention only pigeon `i`, display (35)
(Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §5.1, p.27 (PDF p.30)):
`A_i = {x_{i,j}² - 1 : j ∈ N(i)} ∪ {∏_{j ∈ N(i)} (x_{i,j} + 1)} ∪
{(x_{i,j} - 1)(x_{i,j'} - 1) : j ≠ j' ∈ N(i)}`. -/
def localAxioms {F : Type*} [Field F] {U V : Type*} [Fintype V] (G : BipGraph U V) (i : U) :
    Set (MvPolynomial (Var G) F) :=
  {p | (∃ j ∈ nbrOn G Finset.univ i, p = xv G i j ^ 2 - 1) ∨
       p = ∏ j ∈ nbrOn G Finset.univ i, (xv G i j + 1) ∨
       (∃ j ∈ nbrOn G Finset.univ i, ∃ j' ∈ nbrOn G Finset.univ i, j ≠ j' ∧
          p = (xv G i j - 1) * (xv G i j' - 1))}

end PCNonBool


