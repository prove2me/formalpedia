-- Prove2me | Definitions.Def_MWCSherali_Btot
-- name    : MWCSherali_Btot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:15:57.858203+00:00
-- url     : https://prove2.me/theorems/07e689b4-34f9-41b1-8d2b-d4496877339b
-- title:
--   The assembled capacities $B_i$ (19)
-- statement:
--   $$B_i=\sum_RB^R_i,\tag{19}$$
--
--   the sum over all corners, simplex edges, tubes and the central region, with $C$ given by (18): the corner capacities $B^{K_a}_i$ ($a\neq i$), the edge capacities $B^{E_{ai}}_i$ ($a\neq i$), the tube capacities $B^{T_{ab}}_i$ for the three tubes $\{a,b\}\not\ni i$, and $B^Z_i$.
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

/-- **The assembled capacities `B_i`.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), (19), p.41: "`B_i = ∑_R B^R_i`", the sum
over all corners, simplex edges, tubes and the central region, with `C` given by (18).

The capacity in direction `i`: `B^{K_a}_i = F^{K_a}_{a,i}` for every corner `a ≠ i` (p.33),
`B^{E_{ai}}_i = F^{E_{ai}}_{a,i}` for every edge `E_{ai}`, `a ≠ i` (p.34), `B^{T_{ab}}_i` for every
tube `T_{ab}` with `i ∉ {a, b}`, counted once per unordered pair `{a, b}` (p.35), and `B^Z_i`
(p.40). -/
noncomputable def Btot (α β : ℝ) (i : Fin 4) : Measure (Fin 4 → ℝ) :=
  ∑ a ∈ Finset.univ.filter (· ≠ i), FK α β (Cnorm α β) a i +
    ∑ a ∈ Finset.univ.filter (· ≠ i), FE α β (Cnorm α β) a i +
    ∑ a, ∑ b ∈ Finset.univ.filter (fun b => a < b ∧ a ≠ i ∧ b ≠ i), FT α β (Cnorm α β) a b i +
    BZ α β (Cnorm α β) i

end MWCSherali


