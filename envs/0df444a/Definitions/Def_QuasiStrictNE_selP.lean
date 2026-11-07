-- Prove2me | Definitions.Def_QuasiStrictNE_selP
-- name    : QuasiStrictNE_selP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:10:00.365965+00:00
-- url     : https://prove2.me/theorems/a2d7ec57-5c4e-4010-b137-a35b9144dca4
-- title:
--   The selection $p_F$ computed by a Lemma 3 map
-- statement:
--   Given a map $g_P$ and a rational game, the selection assigns to a face $F$ the rational point whose code $g_P$ outputs on the labels of $F$, viewed in $\mathbb R^m$. For maps with the Lemma 3 property and faces of the complex, this is a point of $\mathrm{relint}\,F$.
--
--   **Formalization Note** The output code is decoded by choice; the vector code is self-delimiting, so the decoded point is the one computed. The value is $0$ when the output is not a code.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), §4, p.15; Lemma 3, p.14

import Mathlib
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_QuasiStrictNE_RatGame
import Definitions.Def_QuasiStrictNE_labelsP

namespace QuasiStrictNE

open Classical in
/-- **The selection `p` computed by a Lemma 3 map** (Hansen & Nie, *On Existence and Computational
Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, §4, p.15: "Choose the points pF and qG for
every F ∈ Cm and G ∈ Cn using Lemma 3"; Lemma 3, p.14: "pF ∈ relint F").

For a map `gP` and a rational game `G`, `selP gP G F` is the rational point whose code
`encRatVec m v` is `gP (labelsP G F)`, cast to `ℝ`; it is `0` if the output is not such a code.

**Formalization Note** `encRatVec` is self-delimiting, hence injective, so the decoded point is the
one output by `gP`. For a map with the Lemma 3 property (`IsLPSelection`) and a face of `Cm` the
output is always a code, of a point of the relative interior. -/
noncomputable def selP (gP : List Bool → List Bool) (G : RatGame) (F : Set (Fin G.m → ℝ)) :
    Fin G.m → ℝ :=
  if h : ∃ v : Fin G.m → ℚ, gP (labelsP G F) = CardinalMatching.encRatVec G.m v then
    fun i => (h.choose i : ℝ)
  else 0

end QuasiStrictNE


