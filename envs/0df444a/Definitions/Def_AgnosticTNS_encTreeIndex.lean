-- Prove2me | Definitions.Def_AgnosticTNS_encTreeIndex
-- name    : AgnosticTNS_encTreeIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:35:46.99104+00:00
-- url     : https://prove2.me/theorems/b2566645-b85b-419e-89c1-8b1f7f9c2bb2
-- title:
--   Input string of an instance of Corollary 5.2
-- statement:
--   $n,d,\chi,k_\epsilon,k_\delta$ in unary and the adjacency matrix of $T$, so that time polynomial in its length is time polynomial in $n,d,\chi,1/\epsilon,\log(1/\delta)$.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Corollary 5.2, p.40

import Mathlib
import Definitions.Def_AgnosticTNS_TreeIndex
import Definitions.Def_AgnosticTNS_encGraph
open QAlgorithms.Complexity

namespace AgnosticTNS

/-- **The input string of an instance of Corollary 5.2**, p.40 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): `n, d, χ, k_ε, k_δ` in unary
and the adjacency matrix of `T`, so that "polynomial in `n, d, χ, 1/ε, log(1/δ)`" is polynomial in
its length. -/
noncomputable def encTreeIndex (i : TreeIndex) : QAlgorithms.Complexity.Str :=
  encNat i.n ++ encGraph i.T ++ encNat i.d ++ encNat i.χ ++ encNat i.kε ++ encNat i.kδ

end AgnosticTNS


