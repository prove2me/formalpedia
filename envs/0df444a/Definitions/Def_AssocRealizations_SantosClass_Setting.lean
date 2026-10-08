-- Prove2me | Definitions.Def_AssocRealizations_SantosClass_Setting
-- name    : AssocRealizations_SantosClass_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T10:17:40.90004+00:00
-- url     : https://prove2.me/theorems/1555e901-2d09-4b7e-ba26-66782f22352a
-- title:
--   Santos associahedron setting — polygon symmetries, flips, normal fans and seed vectors
-- statement:
--   Fix a cyclically ordered polygon with $N$ vertices. Its diagonals are unordered pairs of nonadjacent vertices. A triangulation $T$ is a maximal set of pairwise noncrossing diagonals. A *flip insertion* is a diagonal outside $T$ that replaces one member of $T$ and again gives a triangulation. Let $B_T$ be $T$ together with all such insertions.
--
--   For a seed triangulation $T_0$, use the real vector space with basis $\{\alpha_d:d\in T_0\}$. The normal vector attached to a diagonal $e$ is
--
--   $$
--   v_e(T_0)=\begin{cases}-\alpha_e,&e\in T_0,\\ \sum_{d\in T_0:\,e\text{ crosses }d}\alpha_d,&e\notin T_0.\end{cases}
--   $$
--
--   The Santos fan contains the nonnegative cone on $\{v_e(T_0):e\in D\}$ for every noncrossing diagonal set $D$. Two such fans are normally isomorphic when an invertible real linear map sends every cone of one fan to a cone of the other. Two nonzero vectors are opposite when one is a negative scalar multiple of the other. Polygon equivalence uses only rotations and reflections $i\mapsto r+i$ and $i\mapsto r-i$ modulo $N$.
--
--   These objects state the geometric and combinatorial setting of Corollary 5.7. The basis is indexed by the actual seed diagonals, so its numbering is irrelevant.
--
--   **Formalization Note** The polygon's vertices are zero-based positions in `Fin N`; diagonals are `Sym2 (Fin N)`. The fan uses the nonnegative real hull of the stated vectors.
-- source:
--   Ceballos, Santos and Ziegler, Many non-equivalent realizations of the associahedron, arXiv:1109.5544v2, pp. 5, 19, 23–24, Definition 2.1 and §5.3

import Mathlib
import Definitions.Def_ChvatalArtGallery_FanPartition_Triangulation
import Definitions.Def_AssocRealizations_TypesMeet_Setting

open ChvatalArtGallery.FanPartition

namespace AssocRealizations.SantosClass

/-- Two nonzero normal directions face opposite ways, up to positive scaling. -/
def Opposite {V : Type*} [AddCommGroup V] [Module ℝ V] (v w : V) : Prop :=
  v ≠ 0 ∧ ∃ c : ℝ, 0 < c ∧ v = -(c • w)

/-- The seed diagonals together with all diagonals inserted by one flip. -/
def bSet {N : ℕ} (T : Finset (Sym2 (Fin N))) : Finset (Sym2 (Fin N)) :=
  T ∪ AssocRealizations.TypesMeet.flipSet N T

end AssocRealizations.SantosClass


