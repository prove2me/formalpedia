-- Prove2me | Definitions.Def_Timetabling_CT4_Instance_WellFormed
-- name    : Timetabling_CT4_Instance_WellFormed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:31:58.909046+00:00
-- url     : https://prove2.me/theorems/1ba0a2ea-fa2a-45d0-ac6c-d1d463852cca
-- title:
--   Well-formed CT4 instance
-- statement:
--   A CT4 instance is **well formed** when
--
--   1. every $\bar b_{ik}$ and every $\bar c_{jk}$ is $0$ or $1$;
--   2. for every teacher $t_j$, the list of available periods has no repetition and contains exactly the periods $k$ with $\bar c_{jk} = 1$;
--   3. for every teacher $t_j$ and class $c_i$, class $c_i$ occurs exactly $\bar r_{ij}$ times in the list of classes $t_j$ must meet.
--
--   Conditions 2 and 3 determine the lists up to order, so a well-formed instance is just CT4's data $(\bar r, \bar b, \bar c)$ with the per-teacher lists of Table 1 attached.
-- source:
--   de Werra (1985), Sec. 2.2, p. 154 (b̄_ik, c̄_jk are 1 or 0); Table 1, p. 155. D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib
import Definitions.Def_Timetabling_CT4_Instance

namespace Timetabling.CT4

/-- **Consistency of a CT4 instance.**
de Werra, *An introduction to timetabling*, EJOR 19 (1985), Sec. 2.2, p. 154 (`b̄_ik`, `c̄_jk`
are `1` or `0`) and Table 1, p. 155.

An instance is well formed when

1. every `b̄_ik` and every `c̄_jk` is `0` or `1`;
2. for every teacher `t_j`, the list `avail j` has no repetition and contains exactly the
   periods `k` with `c̄_jk = 1`;
3. for every teacher `t_j` and class `c_i`, class `c_i` occurs `r̄_ij` times in `lectures j`.

**Formalization Note.** Conditions 2 and 3 determine the lists up to order; they hold for the
lists of Table 1. -/
def Instance.WellFormed {m n p : ℕ} (I : Instance m n p) : Prop :=
  (∀ i k, I.bbar i k = 0 ∨ I.bbar i k = 1) ∧
  (∀ j k, I.cbar j k = 0 ∨ I.cbar j k = 1) ∧
  (∀ j, (I.avail j).Nodup ∧ ∀ k, k ∈ I.avail j ↔ I.cbar j k = 1) ∧
  (∀ j i, (I.lectures j).count i = I.rbar i j)

end Timetabling.CT4


