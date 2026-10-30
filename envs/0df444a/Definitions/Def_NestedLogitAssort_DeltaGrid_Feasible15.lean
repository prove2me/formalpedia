-- Prove2me | Definitions.Def_NestedLogitAssort_DeltaGrid_Feasible15
-- name    : NestedLogitAssort_DeltaGrid_Feasible15
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:06:07.615217+00:00
-- url     : https://prove2.me/theorems/10137d00-2481-4604-9554-8afa4da0ea81
-- title:
--   Problem (15) is feasible at level $l$
-- statement:
--   Problem (15) at nest $i$ and level $l$,
--
--   $$
--   \hat G_{il}=\max_{S_i\subseteq N}\Bigl\{\sum_{j\in S_i}r_{ij}v_{ij}:\ \delta^{l-1}\le v_{i0}+\sum_{j\in S_i}v_{ij}\le\delta^l\Bigr\},
--   $$
--
--   is feasible when some assortment of nest $i$ lies in the window $[\delta^{l-1},\delta^l]$. This is the hypothesis of Proposition 15 ("Assuming that problem (32) has a feasible solution"), where (32) is (15) for one nest and level.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, Section 6.2, eq. (15), p. 28; Proposition 15, p. 51

import Mathlib
import Definitions.Def_NestedLogitAssort_DeltaGrid_Window

namespace NestedLogitAssort.DeltaGrid

/-- **Problem (15) has a feasible solution.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, Section 6.2, eq. (15), p. 28, and the hypothesis of Proposition 15, p. 51
("Assuming that problem (32) has a feasible solution"; (32) is (15) for one nest and level):
some assortment of nest `i` lies in the window `[δ^{l−1}, δ^l]` of level `l`. -/
def Feasible15 {M : Type*} {n : ℕ} (I : Instance M n) (δ : ℝ) (i : M) (l : ℤ) : Prop :=
  ∃ S : Finset (Fin n), Window I δ i l S

end NestedLogitAssort.DeltaGrid


