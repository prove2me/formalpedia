-- Prove2me | Definitions.Def_QuasiStrictNE_IsLPSelection
-- name    : QuasiStrictNE_IsLPSelection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:09:50.477301+00:00
-- url     : https://prove2.me/theorems/f27c7355-2a41-40e8-8328-97e211a2ce2d
-- title:
--   Polynomial-time relative-interior selection (Lemma 3 property)
-- statement:
--   A pair of maps $(g_P,g_Q)$ on bit strings has the **Lemma 3 property** when both are computable in polynomial time and, for every rational bimatrix game with $m,n\ge 1$,
--
--   1. for every face $F\in\mathcal C_m$, $g_P$ maps (game, $I_F$, $J_F$) to the code of a rational point $p_F\in\mathrm{relint}\,F$;
--   2. for every face $G\in\mathcal C_n$, $g_Q$ maps (game, $I_G$, $J_G$) to the code of a rational point $q_G\in\mathrm{relint}\,G$.
--
--   Since the output depends on the face only through its labels, the same point is selected whenever the same face occurs.
--
--   **Formalization Note** $\mathrm{relint}$ is Mathlib's `intrinsicInterior ℝ`.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Lemma 3, p.14

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_QuasiStrictNE_RatGame
import Definitions.Def_QuasiStrictNE_Cm
import Definitions.Def_QuasiStrictNE_Cn
import Definitions.Def_QuasiStrictNE_labelsP
import Definitions.Def_QuasiStrictNE_labelsQ

namespace QuasiStrictNE

/-- **Polynomial-time relative-interior selection, as in Lemma 3** (Hansen & Nie, *On Existence and
Computational Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, Lemma 3, p.14: "Given these
index sets, a rational point pF ∈ relint F can be computed in polynomial time. The same holds for
G ∈ Cn").

`IsLPSelection gP gQ` holds iff `gP` and `gQ` are computable in polynomial time and, for every
rational game with `m, n ≥ 1`:

1. for every face `F ∈ Cm`, `gP` maps the input `labelsP` (game, `I_F`, `J_F`) to the code
   `encRatVec m v` of a rational point `v ∈ relint F`;
2. for every face `G ∈ Cn`, `gQ` maps `labelsQ` (game, `I_G`, `J_G`) to the code of a rational point
   of `relint G`.

**Formalization Note** `relint` is Mathlib's `intrinsicInterior ℝ` (interior in the affine hull,
p.6). The output depends on the face only through its label sets, so the same point is selected
whenever the same face occurs (p.14, "selects the same point whenever the same face occurs"). -/
def IsLPSelection (gP gQ : List Bool → List Bool) : Prop :=
  CookPvsNP.PolyTimeComputable gP ∧ CookPvsNP.PolyTimeComputable gQ ∧
    ∀ G : RatGame, 1 ≤ G.m → 1 ≤ G.n →
      (∀ F ∈ Cm (G.B.map ((↑) : ℚ → ℝ)), ∃ v : Fin G.m → ℚ,
        gP (labelsP G F) = CardinalMatching.encRatVec G.m v ∧
        (fun i => (v i : ℝ)) ∈ intrinsicInterior ℝ F) ∧
      (∀ Q ∈ Cn (G.A.map ((↑) : ℚ → ℝ)), ∃ w : Fin G.n → ℚ,
        gQ (labelsQ G Q) = CardinalMatching.encRatVec G.n w ∧
        (fun j => (w j : ℝ)) ∈ intrinsicInterior ℝ Q)

end QuasiStrictNE


