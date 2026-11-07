-- Prove2me | Definitions.Def_QuasiStrictNE_selQ
-- name    : QuasiStrictNE_selQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:09:35.959731+00:00
-- url     : https://prove2.me/theorems/84c6d003-dc22-4622-859a-6ec2981e461a
-- title:
--   The selection $q_G$ computed by a Lemma 3 map
-- statement:
--   Given a map $g_Q$ and a rational game, the selection assigns to a face $G$ the rational point whose code $g_Q$ outputs on the labels of $G$, viewed in $\mathbb R^n$. For maps with the Lemma 3 property and faces of the complex, this is a point of $\mathrm{relint}\,G$.
--
--   **Formalization Note** The output code is decoded by choice; the vector code is self-delimiting, so the decoded point is the one computed. The value is $0$ when the output is not a code.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), §4, p.15; Lemma 3, p.14

import Mathlib
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_QuasiStrictNE_RatGame
import Definitions.Def_QuasiStrictNE_labelsQ

namespace QuasiStrictNE

open Classical in
/-- **The selection `q` computed by a Lemma 3 map** (Hansen & Nie, *On Existence and Computational
Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, §4, p.15: "Choose the points pF and qG for
every F ∈ Cm and G ∈ Cn using Lemma 3"; Lemma 3, p.14: "qG ∈ relint G").

For a map `gQ` and a rational game `G`, `selQ gQ G Q` is the rational point whose code
`encRatVec n v` is `gQ (labelsQ G Q)`, cast to `ℝ`; it is `0` if the output is not such a code.

**Formalization Note** `encRatVec` is self-delimiting, hence injective, so the decoded point is the
one output by `gQ`. For a map with the Lemma 3 property (`IsLPSelection`) and a face of `Cn` the
output is always a code, of a point of the relative interior. -/
noncomputable def selQ (gQ : List Bool → List Bool) (G : RatGame) (Q : Set (Fin G.n → ℝ)) :
    Fin G.n → ℝ :=
  if h : ∃ v : Fin G.n → ℚ, gQ (labelsQ G Q) = CardinalMatching.encRatVec G.n v then
    fun i => (h.choose i : ℝ)
  else 0

end QuasiStrictNE


