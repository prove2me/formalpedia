-- Prove2me | Definitions.Def_PCNonBool_splitSeq
-- name    : PCNonBool_splitSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:30:27.405814+00:00
-- url     : https://prove2.me/theorems/b88f0011-10c6-455b-ad14-c4ef7f484922
-- title:
--   Pigeon split of a sequence of polynomials
-- statement:
--   For a sequence $\pi=(p_1,\dots,p_\tau)$, $\mathrm{PigeonSplit}_{i,j,j'}(\pi)$ is the sequence of length $2\tau$ obtained by replacing each line $p_k$ with the two lines of $\mathrm{PigeonSplit}_{i,j,j'}(p_k)$. Its last two lines are $\mathrm{PigeonSplit}_{i,j,j'}(p_\tau)$.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Definition 5.8, p.28 (PDF p.31)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_Var
import Definitions.Def_PCNonBool_pigeonSplit

namespace PCNonBool

/-- `PigeonSplit_{i,j,j'}(π)` for a sequence `π = (p₁, …, p_τ)`: "the concatenation of
PigeonSplit_{i,j,j'} applied to each polynomial in π" (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Definition 5.8, p.28 (PDF
p.31)). Each line `p` becomes the two consecutive lines `PigeonSplit(p).1, PigeonSplit(p).2`. -/
noncomputable def splitSeq {F : Type*} [Field F] {U V : Type*} [DecidableEq U] [DecidableEq V]
    (G : BipGraph U V) (i : U) (j j' : V) (π : List (MvPolynomial (Var G) F)) :
    List (MvPolynomial (Var G) F) :=
  π.flatMap (fun p => [(pigeonSplit G i j j' p).1, (pigeonSplit G i j j' p).2])

end PCNonBool


