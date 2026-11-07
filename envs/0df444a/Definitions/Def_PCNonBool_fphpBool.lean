-- Prove2me | Definitions.Def_PCNonBool_fphpBool
-- name    : PCNonBool_fphpBool
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:29:49.088683+00:00
-- url     : https://prove2.me/theorems/c6aa0ca1-f2df-4178-85d5-15dd6158b595
-- title:
--   Functional pigeonhole principle FPHP$(G)_{\mathrm{bool}}$ ($0/1$ encoding)
-- statement:
--   For a bipartite graph $G=(U\sqcup V,E)$, the Boolean encoding **FPHP$(G)_{\mathrm{bool}}$** consists of
--   1. (34a) $x_{i,j}^2-x_{i,j}$ for $i\in U$, $j\in N(i)$;
--   2. (34b) $\sum_{j\in N(i)}x_{i,j}-1$ for $i\in U$;
--   3. (34c) $x_{i,j}x_{i',j}$ for $i\ne i'\in U$, $j\in N(i)\cap N(i')$;
--   4. (34d) $x_{i,j}x_{i,j'}$ for $i\in U$, $j\ne j'\in N(i)$,
--
--   with the same semantics as FPHP$(G)$ but $x_{i,j}=1$ meaning that pigeon $i$ flies to hole $j$. The known pigeon-degree lower bound of Mikša and Nordström is stated for this encoding.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §5, (34a)–(34d), p.26 (PDF p.29)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_nbrOn
import Definitions.Def_PCNonBool_Var
import Definitions.Def_PCNonBool_xv

namespace PCNonBool

/-- The Boolean encoding FPHP(G)_bool of the graph functional pigeonhole principle
(Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §5, (34a)–(34d), p.26 (PDF p.29)), where `x_{i,j} = 1` means "pigeon `i` flies to
hole `j`":

* (34a) `x_{i,j}² - x_{i,j}` for `(i, j) ∈ E`;
* (34b) `∑_{j ∈ N(i)} x_{i,j} - 1` for `i ∈ U`;
* (34c) `x_{i,j} x_{i',j}` for `i ≠ i'`, `j ∈ N(i) ∩ N(i')`;
* (34d) `x_{i,j} x_{i,j'}` for `j ≠ j' ∈ N(i)`.

**Formalization Note** The empty sum in (34b) is `0`, so an isolated pigeon contributes the
axiom `-1`. -/
def fphpBool {F : Type*} [Field F] {U V : Type*} [Fintype V] (G : BipGraph U V) :
    Set (MvPolynomial (Var G) F) :=
  {p | (∃ e : Var G, p = MvPolynomial.X e ^ 2 - MvPolynomial.X e) ∨
       (∃ i, p = (∑ j ∈ nbrOn G Finset.univ i, xv G i j) - 1) ∨
       (∃ i i', i ≠ i' ∧ ∃ j ∈ nbrOn G Finset.univ i, j ∈ nbrOn G Finset.univ i' ∧
          p = xv G i j * xv G i' j) ∨
       (∃ i, ∃ j ∈ nbrOn G Finset.univ i, ∃ j' ∈ nbrOn G Finset.univ i, j ≠ j' ∧
          p = xv G i j * xv G i j')}

end PCNonBool


