-- Prove2me | Definitions.Def_PCNonBool_splitSet
-- name    : PCNonBool_splitSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:30:47.121111+00:00
-- url     : https://prove2.me/theorems/780a2e98-b84a-49e9-b5eb-e1011c21a22c
-- title:
--   Pigeon split of a set of axioms
-- statement:
--   For a set $P$ of polynomials, $\mathrm{PigeonSplit}_{i,j,j'}(P)$ is the set consisting of both components of $\mathrm{PigeonSplit}_{i,j,j'}(a)$ for every $a\in P$.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Lemma 5.9 (PigeonSplit of an axiom set), p.28 (PDF p.31)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_Var
import Definitions.Def_PCNonBool_pigeonSplit

namespace PCNonBool

/-- `PigeonSplit_{i,j,j'}(P)` for a set `P` of axioms: the set of both components of
`PigeonSplit(a)` for every `a ∈ P` (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Lemma 5.9, p.28 (PDF p.31)). -/
noncomputable def splitSet {F : Type*} [Field F] {U V : Type*} [DecidableEq U] [DecidableEq V]
    (G : BipGraph U V) (i : U) (j j' : V) (P : Set (MvPolynomial (Var G) F)) :
    Set (MvPolynomial (Var G) F) :=
  ⋃ a ∈ P, {(pigeonSplit G i j j' a).1, (pigeonSplit G i j j' a).2}

end PCNonBool


