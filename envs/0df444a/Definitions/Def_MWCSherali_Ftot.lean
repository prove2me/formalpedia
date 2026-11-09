-- Prove2me | Definitions.Def_MWCSherali_Ftot
-- name    : MWCSherali_Ftot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:16:08.180208+00:00
-- url     : https://prove2.me/theorems/b07f97d4-cdde-4202-bde4-7cab8dd34946
-- title:
--   The assembled flows $F_{a,i}$ (19)
-- statement:
--   $$F_{a,i}=\sum_RF^R_{a,i},\qquad i\neq a\in[4],\tag{19}$$
--
--   the sum over all corners, simplex edges, tubes and the central region, with $C$ given by (18). Commodity $a$ flows in direction $i$ in its own corner $K_a$, on the edge $E_{ai}$, in the tubes $T_{ab}$ with $b\notin\{a,i\}$, and in the central region.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), (19), p.41

import Mathlib
import Definitions.Def_MWCSherali_FK
import Definitions.Def_MWCSherali_FE
import Definitions.Def_MWCSherali_FT
import Definitions.Def_MWCSherali_BZ
import Definitions.Def_MWCSherali_Cnorm

namespace MWCSherali

open MeasureTheory

/-- **The assembled flows `F_{a,i}`.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), (19), p.41: "`F_{a,i} = ∑_R F^R_{a,i}`,
`∀ i ≠ a ∈ [4]`, where the summation variable `R` is taken over all corners, simplex edges,
tubes, and the central region", with `C` given by (18).

Commodity `a`'s flow in direction `i ≠ a`: the corner flow `F^{K_a}_{a,i}`, the edge flow
`F^{E_{ai}}_{a,i}`, the tube flows `F^{T_{ab}}_{a,i}` for `b ∉ {a, i}`, and the central flow
`F^Z_{a,i} = B^Z_i`; every other region carries no commodity-`a` flow in direction `i`.

**Formalization Note.** Only `a ≠ i` is used; `Ftot α β a a` is not a variable. -/
noncomputable def Ftot (α β : ℝ) (a i : Fin 4) : Measure (Fin 4 → ℝ) :=
  FK α β (Cnorm α β) a i + FE α β (Cnorm α β) a i +
    ∑ b ∈ Finset.univ.filter (fun b => b ≠ a ∧ b ≠ i), FT α β (Cnorm α β) a b i +
    BZ α β (Cnorm α β) i

end MWCSherali


