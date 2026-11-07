-- Prove2me | Definitions.Def_PCNonBool_touchSetOn
-- name    : PCNonBool_touchSetOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:33:56.994675+00:00
-- url     : https://prove2.me/theorems/21064aca-a187-49d8-af6b-928832f6ae57
-- title:
--   The pair set $\mathrm{Touch}_{i,j,j',D}(\pi)$
-- statement:
--   For a pigeon $i$, holes $j\ne j'\in N(i)$ and a sequence of polynomials $\pi$,
--   $$\mathrm{Touch}_{i,j,j',D}(\pi)=\{\,q\in\mathrm{PPHigh}_D(\pi) : q \text{ is touched by } (x_{i,j},x_{i,j'})\,\}.$$
--   These are the pairs of high pairwise pigeon degree that PigeonSplit on $(i,j,j')$ eliminates (Lemma 5.10).
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §5.1 (Touch), p.28 (PDF p.31)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_Var
import Definitions.Def_PCNonBool_ppHighOn
import Definitions.Def_PCNonBool_touches

namespace PCNonBool

/-- `Touch_{i,j,j',D}(π)`: the pairs of `PPHigh_D(π)` (in the instance `G[Ua ⊔ Va]`) touched by
`(x_{i,j}, x_{i,j'})` (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), p.28 (PDF p.31): "denote by Touch_{i,j,j',D}(p) the set of pairs
in PPHigh_D(p) that are touched by (x_{i,j}, x_{i,j'}) … Touch_{i,j,j',D}(S) = ⋃_{p ∈ S}
Touch_{i,j,j',D}(p)"). -/
noncomputable def touchSetOn {F : Type*} [Field F] {U V : Type*} [DecidableEq U] [DecidableEq V]
    (G : BipGraph U V) (Ua : Finset U) (Va : Finset V) (D : ℝ) (i : U) (j j' : V)
    (π : List (MvPolynomial (Var G) F)) : Finset (Sym2 (Var G →₀ ℕ)) := by
  classical
  exact (ppHighOn G Ua Va D π).filter (touches G i j j')

end PCNonBool


