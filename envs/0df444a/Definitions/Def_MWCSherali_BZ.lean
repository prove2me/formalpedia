-- Prove2me | Definitions.Def_MWCSherali_BZ
-- name    : MWCSherali_BZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:12:51.520054+00:00
-- url     : https://prove2.me/theorems/cafeff21-da7e-4ecd-aabd-2025facacf5b
-- title:
--   The central-region capacities $B^Z_i$
-- statement:
--   On each of the 72 tetrahedra $T$ of the central region, $dB^T_i=dF^T_{a,i}=Cc^T_i\,dt$ for all $i\neq a$, and
--
--   $$F^Z_{a,i}=\sum_TF^T_{a,i},\qquad B^Z_i=\sum_TB^T_i ,$$
--
--   with the density vectors of Lemma 4.6. The 72 tetrahedra and their vectors are the images of the six representatives of Table 5 under the 24 coordinate permutations.
--
--   **Formalization Note** The sum runs over pairs (representative $r$, permutation $\pi$), with tetrahedron $\{t\circ\pi^{-1}\mid t\in T_r\}$ and vector $c^{T_r}\circ\pi^{-1}$. Each tetrahedron arises from exactly two pairs (each representative is fixed by one transposition, the "Symmetry" column of Table 5) with the same vector, hence the factor $\tfrac12$. Shared faces are null.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), §4.4, pp.38–40

import Mathlib
import Definitions.Def_MWCSherali_volD4
import Definitions.Def_MWCSherali_cpt__6e2ea3
import Definitions.Def_MWCSherali_tetVerts
import Definitions.Def_MWCSherali_densVec

namespace MWCSherali

open MeasureTheory

/-- **The central-region capacities `B^Z_i` (= flows `F^Z_{a,i}`).** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), §4.4,
pp.38–40: on each tetrahedron `T` of the triangulation of `Z`,
"`dB^T_i = dF^T_{a,i} = C c^T_i dt`, `∀ i ≠ a`", and "`F^Z_{a,i} = ∑_T F^T_{a,i}`,
`B^Z_i = ∑_T B^T_i`" (p.40), with the density vectors of Lemma 4.6.

The 72 tetrahedra are the images `π · T_r = {t ∘ π⁻¹ | t ∈ T_r}` of the six representatives
`T_r` (Table 5) under the 24 coordinate permutations `π`, with density vector `c^{T_r} ∘ π⁻¹`
("the density vectors for other tetrahedra may be obtained by permuting the coordinates", p.38).
Each representative is fixed by one transposition (the "Symmetry" column of Table 5), so each
tetrahedron occurs exactly twice in the sum over `(r, π)`, with the same vector; hence the factor
`1/2`.

**Formalization Note.** `π · T_r` is the convex hull of the four permuted vertices
`cpt α β (tetVerts r m) ∘ π⁻¹`. The weight `C c_i` enters through `ENNReal.ofReal`; it is
nonnegative under Lemma 4.6's hypotheses and `C > 0`. Shared faces of tetrahedra are null, so the
sum of restrictions is `C c^T_i dt` on each tetrahedron. -/
noncomputable def BZ (α β C : ℝ) (i : Fin 4) : Measure (Fin 4 → ℝ) :=
  (1 / 2 : ENNReal) • ∑ r : Fin 6, ∑ π : Equiv.Perm (Fin 4),
    ENNReal.ofReal (C * densVec α β r (π.symm i)) •
      volD4.restrict (convexHull ℝ (Set.range fun m : Fin 4 => cpt α β (tetVerts r m) ∘ π.symm))

end MWCSherali


