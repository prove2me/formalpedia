-- Prove2me | Definitions.Def_LawLocalComp_encPairs
-- name    : LawLocalComp_encPairs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:10:35.158195+00:00
-- url     : https://prove2.me/theorems/1f22a592-6155-4ce1-8a0b-ae3aaae2589d
-- title:
--   Binary encoding of a list of (atom, mass) pairs
-- statement:
--   A law handed to a Turing machine is a list of rational pairs $(x_1,m_1),\dots,(x_k,m_k)$ (atom, mass). It is written as $x_1,m_1,\dots,x_k,m_k$, each rational in lowest terms with numerator and denominator in binary, using the published encoding `RobustToDynamics.encListRat`.
--
--   **Formalization Note** The alphabet is `OnlineCRS.Combine.Sym` $=\{0,1,2,3\}$: bits, the numerator/denominator separator $2$ and the item separator $3$. The encoding length is the usual bit size.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Theorem 1.1, p.2; Lemma 3.1, p.5

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_RobustToDynamics_encListRat

namespace LawLocalComp

/-- **Machine encoding of a law given as a list of (atom, mass) pairs.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Theorem 1.1, p.2 ("polynomial in input bits"); Lemma 3.1, p.5 (rational cuts, splits and means).

A list `[(x₁, m₁), …, (x_k, m_k)]` of rationals is written as `x₁, m₁, …, x_k, m_k`, each in binary by
the published `RobustToDynamics.encListRat` (reduced numerator, separator `2`, denominator, item
separator `3`).

**Formalization Note.** Polynomial time is read in Mathlib's Turing-machine model
`Turing.TM2ComputableInPolyTime` over the alphabet `OnlineCRS.Combine.Sym = Fin 4`. Rationals are
binary and in lowest terms, so the encoding length is the usual bit size. -/
def encPairs (l : List (ℚ × ℚ)) : List OnlineCRS.Combine.Sym :=
  RobustToDynamics.encListRat (l.flatMap fun z => [z.1, z.2])

end LawLocalComp


