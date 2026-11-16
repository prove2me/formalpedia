-- Prove2me | Definitions.Def_SwitchingStable_Universal_Supplement_Tables
-- name    : SwitchingStable_Universal_Supplement_Tables
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T13:34:30.778879+00:00
-- url     : https://prove2.me/theorems/d55d6119-b782-4dda-8344-74d05b3c7898
-- title:
--   Tables 4–8 — five literal complete preference instances
-- statement:
--   The two sides of each market have labels $1,\ldots,n$. Tables 4–8 give every agent's complete preference list, in order from best to worst, for $n=7,9,11,13,15$. The named instances $I_7,I_9,I_{11},I_{13},I_{15}$ are exactly these arrays, without a choice of a market having a prescribed count.
--
--   $$I_n=(r_U,r_V),\qquad r_U(i,v)=\text{position of }v\text{ in row }u_i,$$
--
--   and similarly for $r_V$. A position is the inverse of the displayed list permutation. The checked inverse tables ensure that each row is a bijection, so each instance has strict complete preferences. These fixed inputs make the exact count assertion of Theorem 2 independently reproducible.
--
--   **Formalization Note** Agent labels and positions are shifted once to $\mathrm{Fin}\,n$; the two rank fields still represent different sides. The small inverse checks are structural proofs, not stable-count certificates.
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), pp. 31–34, PDF pp. 32–35, Appendix G, Tables 4–8

import Mathlib
import Definitions.Def_StableCount_Count

namespace SwitchingStable.Universal.Supplement

open StableMatching

/-- A literal best-to-worst row, with a checked inverse position table. -/
def listRank {n : ℕ} (row inv : Fin n → Fin n)
    (h₁ : ∀ k, inv (row k) = k) (h₂ : ∀ k, row (inv k) = k) : Fin n ≃ Fin n :=
  (⟨row, inv, h₁, h₂⟩ : Fin n ≃ Fin n).symm

/-- Appendix G, Table 4: entries shifted from labels 1,…,7 to Fin 7. -/
def table7 : Instance 7 where
  manRank
    | 0 => listRank ![0, 1, 5, 6, 3, 2, 4] ![0, 1, 5, 4, 6, 2, 3] (by decide) (by decide)
    | 1 => listRank ![1, 0, 3, 6, 4, 2, 5] ![1, 0, 5, 2, 4, 6, 3] (by decide) (by decide)
    | 2 => listRank ![2, 5, 1, 4, 6, 3, 0] ![6, 2, 0, 5, 3, 1, 4] (by decide) (by decide)
    | 3 => listRank ![3, 6, 4, 2, 5, 1, 0] ![6, 5, 3, 0, 2, 4, 1] (by decide) (by decide)
    | 4 => listRank ![4, 6, 5, 2, 3, 0, 1] ![5, 6, 3, 4, 0, 2, 1] (by decide) (by decide)
    | 5 => listRank ![5, 2, 4, 1, 0, 3, 6] ![4, 3, 1, 5, 2, 0, 6] (by decide) (by decide)
    | 6 => listRank ![6, 3, 0, 1, 5, 2, 4] ![2, 3, 5, 1, 6, 4, 0] (by decide) (by decide)
  womanRank
    | 0 => listRank ![3, 4, 5, 6, 1, 0, 2] ![5, 4, 6, 0, 1, 2, 3] (by decide) (by decide)
    | 1 => listRank ![4, 3, 6, 5, 2, 0, 1] ![5, 6, 4, 1, 0, 3, 2] (by decide) (by decide)
    | 2 => listRank ![6, 1, 0, 4, 3, 5, 2] ![2, 1, 6, 4, 3, 5, 0] (by decide) (by decide)
    | 3 => listRank ![2, 5, 4, 0, 1, 6, 3] ![3, 4, 0, 6, 2, 1, 5] (by decide) (by decide)
    | 4 => listRank ![0, 1, 2, 5, 3, 4, 6] ![0, 1, 2, 4, 5, 3, 6] (by decide) (by decide)
    | 5 => listRank ![1, 6, 3, 4, 0, 2, 5] ![4, 0, 5, 2, 3, 6, 1] (by decide) (by decide)
    | 6 => listRank ![5, 2, 1, 0, 4, 3, 6] ![3, 2, 1, 5, 4, 0, 6] (by decide) (by decide)
/-- Appendix G, Table 5: entries shifted from labels 1,…,9 to Fin 9. -/
def table9 : Instance 9 where
  manRank
    | 0 => listRank ![0, 5, 6, 8, 7, 3, 2, 1, 4] ![0, 7, 6, 5, 8, 1, 2, 4, 3] (by decide) (by decide)
    | 1 => listRank ![1, 7, 5, 2, 8, 4, 3, 0, 6] ![7, 0, 3, 6, 5, 2, 8, 1, 4] (by decide) (by decide)
    | 2 => listRank ![2, 3, 4, 1, 0, 5, 6, 8, 7] ![4, 3, 0, 1, 2, 5, 6, 8, 7] (by decide) (by decide)
    | 3 => listRank ![3, 2, 1, 4, 5, 0, 8, 6, 7] ![5, 2, 1, 0, 3, 4, 7, 8, 6] (by decide) (by decide)
    | 4 => listRank ![4, 8, 0, 3, 6, 1, 7, 5, 2] ![2, 5, 8, 3, 0, 7, 4, 6, 1] (by decide) (by decide)
    | 5 => listRank ![5, 0, 8, 6, 3, 7, 1, 2, 4] ![1, 6, 7, 4, 8, 0, 3, 5, 2] (by decide) (by decide)
    | 6 => listRank ![6, 5, 7, 8, 2, 3, 4, 1, 0] ![8, 7, 4, 5, 6, 1, 0, 2, 3] (by decide) (by decide)
    | 7 => listRank ![7, 1, 2, 5, 4, 8, 0, 3, 6] ![6, 1, 2, 7, 4, 3, 8, 0, 5] (by decide) (by decide)
    | 8 => listRank ![8, 4, 3, 0, 1, 6, 5, 7, 2] ![3, 4, 8, 2, 1, 6, 5, 7, 0] (by decide) (by decide)
  womanRank
    | 0 => listRank ![1, 7, 3, 2, 8, 4, 5, 0, 6] ![7, 0, 3, 2, 5, 6, 8, 1, 4] (by decide) (by decide)
    | 1 => listRank ![6, 0, 5, 4, 8, 2, 3, 7, 1] ![1, 8, 5, 6, 3, 2, 0, 7, 4] (by decide) (by decide)
    | 2 => listRank ![5, 0, 6, 1, 7, 3, 2, 4, 8] ![1, 3, 6, 5, 7, 0, 2, 4, 8] (by decide) (by decide)
    | 3 => listRank ![7, 1, 6, 0, 5, 4, 8, 2, 3] ![3, 1, 7, 8, 5, 4, 2, 0, 6] (by decide) (by decide)
    | 4 => listRank ![0, 6, 1, 7, 3, 2, 8, 4, 5] ![0, 2, 5, 4, 7, 8, 1, 3, 6] (by decide) (by decide)
    | 5 => listRank ![4, 8, 2, 3, 7, 1, 6, 0, 5] ![7, 5, 2, 3, 0, 8, 6, 4, 1] (by decide) (by decide)
    | 6 => listRank ![3, 2, 8, 4, 5, 0, 6, 1, 7] ![5, 7, 1, 0, 3, 4, 6, 8, 2] (by decide) (by decide)
    | 7 => listRank ![8, 4, 5, 0, 6, 1, 7, 2, 3] ![3, 5, 7, 8, 1, 2, 4, 6, 0] (by decide) (by decide)
    | 8 => listRank ![2, 3, 7, 1, 6, 0, 5, 4, 8] ![5, 3, 0, 1, 7, 6, 4, 2, 8] (by decide) (by decide)
/-- Appendix G, Table 6: entries shifted from labels 1,…,11 to Fin 11. -/
def table11 : Instance 11 where
  manRank
    | 0 => listRank ![0, 2, 5, 1, 9, 4, 6, 3, 8, 7, 10] ![0, 3, 1, 7, 5, 2, 6, 9, 8, 4, 10] (by decide) (by decide)
    | 1 => listRank ![1, 10, 4, 0, 3, 5, 7, 9, 2, 6, 8] ![3, 0, 8, 4, 2, 5, 9, 6, 10, 7, 1] (by decide) (by decide)
    | 2 => listRank ![2, 0, 1, 5, 4, 9, 3, 6, 7, 8, 10] ![1, 2, 0, 6, 4, 3, 7, 8, 9, 5, 10] (by decide) (by decide)
    | 3 => listRank ![3, 6, 7, 8, 2, 10, 1, 0, 4, 5, 9] ![7, 6, 4, 0, 8, 9, 1, 2, 3, 10, 5] (by decide) (by decide)
    | 4 => listRank ![4, 8, 3, 10, 7, 0, 2, 5, 1, 9, 6] ![5, 8, 6, 2, 0, 7, 10, 4, 1, 9, 3] (by decide) (by decide)
    | 5 => listRank ![5, 7, 9, 2, 6, 1, 8, 4, 10, 3, 0] ![10, 5, 3, 9, 7, 0, 4, 1, 6, 2, 8] (by decide) (by decide)
    | 6 => listRank ![6, 3, 8, 7, 10, 2, 0, 1, 5, 4, 9] ![6, 7, 5, 1, 9, 8, 0, 3, 2, 10, 4] (by decide) (by decide)
    | 7 => listRank ![7, 5, 2, 9, 1, 6, 4, 8, 3, 10, 0] ![10, 4, 2, 8, 6, 1, 5, 0, 7, 3, 9] (by decide) (by decide)
    | 8 => listRank ![8, 4, 10, 3, 0, 7, 5, 2, 9, 1, 6] ![4, 9, 7, 3, 1, 6, 10, 5, 0, 8, 2] (by decide) (by decide)
    | 9 => listRank ![9, 7, 6, 2, 8, 1, 10, 4, 0, 3, 5] ![8, 5, 3, 9, 7, 10, 2, 1, 4, 0, 6] (by decide) (by decide)
    | 10 => listRank ![10, 1, 0, 4, 5, 3, 9, 7, 6, 2, 8] ![2, 1, 9, 5, 3, 4, 8, 7, 10, 6, 0] (by decide) (by decide)
  womanRank
    | 0 => listRank ![5, 9, 3, 6, 4, 8, 1, 10, 2, 0, 7] ![9, 6, 8, 2, 4, 0, 3, 10, 5, 1, 7] (by decide) (by decide)
    | 1 => listRank ![8, 4, 6, 3, 9, 5, 7, 0, 2, 10, 1] ![7, 10, 8, 3, 1, 5, 2, 6, 0, 4, 9] (by decide) (by decide)
    | 2 => listRank ![10, 1, 8, 4, 6, 3, 9, 5, 7, 0, 2] ![9, 1, 10, 5, 3, 7, 4, 8, 2, 6, 0] (by decide) (by decide)
    | 3 => listRank ![9, 5, 7, 0, 2, 10, 1, 8, 4, 6, 3] ![3, 6, 4, 10, 8, 1, 9, 2, 7, 0, 5] (by decide) (by decide)
    | 4 => listRank ![6, 3, 9, 5, 7, 0, 2, 10, 1, 8, 4] ![5, 8, 6, 1, 10, 3, 0, 4, 9, 2, 7] (by decide) (by decide)
    | 5 => listRank ![3, 6, 4, 8, 1, 10, 2, 0, 7, 5, 9] ![7, 4, 6, 0, 2, 9, 1, 8, 3, 10, 5] (by decide) (by decide)
    | 6 => listRank ![1, 10, 2, 0, 7, 5, 9, 3, 6, 4, 8] ![3, 0, 2, 7, 9, 5, 8, 4, 10, 6, 1] (by decide) (by decide)
    | 7 => listRank ![0, 2, 10, 1, 8, 4, 6, 3, 9, 5, 7] ![0, 3, 1, 7, 5, 9, 6, 10, 4, 8, 2] (by decide) (by decide)
    | 8 => listRank ![2, 0, 7, 5, 9, 3, 6, 4, 8, 1, 10] ![1, 9, 0, 5, 7, 3, 6, 2, 8, 4, 10] (by decide) (by decide)
    | 9 => listRank ![4, 8, 1, 10, 2, 0, 7, 5, 9, 3, 6] ![5, 2, 4, 9, 0, 7, 10, 6, 1, 8, 3] (by decide) (by decide)
    | 10 => listRank ![7, 5, 9, 3, 6, 4, 8, 1, 10, 0, 2] ![9, 7, 10, 3, 5, 1, 4, 0, 6, 2, 8] (by decide) (by decide)
/-- Appendix G, Table 7: entries shifted from labels 1,…,13 to Fin 13. -/
def table13 : Instance 13 where
  manRank
    | 0 => listRank ![0, 3, 2, 1, 12, 5, 6, 8, 7, 10, 9, 4, 11] ![0, 3, 2, 1, 11, 5, 6, 8, 7, 10, 9, 12, 4] (by decide) (by decide)
    | 1 => listRank ![1, 11, 5, 0, 8, 2, 10, 12, 4, 6, 3, 7, 9] ![3, 0, 5, 10, 8, 2, 9, 11, 4, 12, 6, 1, 7] (by decide) (by decide)
    | 2 => listRank ![2, 4, 12, 3, 6, 1, 7, 5, 9, 8, 11, 10, 0] ![12, 5, 0, 3, 1, 7, 4, 6, 9, 8, 11, 10, 2] (by decide) (by decide)
    | 3 => listRank ![3, 0, 1, 2, 5, 12, 8, 6, 10, 7, 4, 9, 11] ![1, 2, 3, 0, 10, 4, 7, 9, 6, 11, 8, 12, 5] (by decide) (by decide)
    | 4 => listRank ![4, 2, 3, 12, 1, 6, 5, 7, 8, 9, 10, 11, 0] ![12, 4, 1, 2, 0, 6, 5, 7, 8, 9, 10, 11, 3] (by decide) (by decide)
    | 5 => listRank ![5, 9, 8, 11, 10, 0, 4, 2, 3, 12, 1, 6, 7] ![5, 10, 7, 8, 6, 0, 11, 12, 2, 1, 4, 3, 9] (by decide) (by decide)
    | 6 => listRank ![6, 8, 7, 10, 9, 4, 11, 3, 0, 1, 2, 5, 12] ![8, 9, 10, 7, 5, 11, 0, 2, 1, 4, 3, 6, 12] (by decide) (by decide)
    | 7 => listRank ![7, 8, 9, 10, 11, 4, 0, 3, 2, 1, 12, 5, 6] ![6, 9, 8, 7, 5, 11, 12, 0, 1, 2, 3, 4, 10] (by decide) (by decide)
    | 8 => listRank ![8, 6, 10, 7, 4, 9, 3, 11, 1, 0, 5, 2, 12] ![9, 8, 11, 6, 4, 10, 1, 3, 0, 5, 2, 7, 12] (by decide) (by decide)
    | 9 => listRank ![9, 5, 11, 8, 0, 10, 2, 4, 12, 3, 6, 1, 7] ![4, 11, 6, 9, 7, 1, 10, 12, 3, 0, 5, 2, 8] (by decide) (by decide)
    | 10 => listRank ![10, 12, 4, 6, 3, 7, 1, 9, 5, 11, 8, 0, 2] ![11, 6, 12, 4, 2, 8, 3, 5, 10, 7, 0, 9, 1] (by decide) (by decide)
    | 11 => listRank ![11, 1, 0, 5, 2, 8, 12, 10, 6, 4, 7, 3, 9] ![2, 1, 4, 11, 9, 3, 8, 10, 5, 12, 7, 0, 6] (by decide) (by decide)
    | 12 => listRank ![12, 10, 6, 4, 7, 3, 9, 1, 11, 5, 0, 8, 2] ![10, 7, 12, 5, 3, 9, 2, 4, 11, 6, 1, 8, 0] (by decide) (by decide)
  womanRank
    | 0 => listRank ![10, 12, 8, 6, 7, 5, 9, 1, 11, 3, 0, 2, 4] ![10, 7, 11, 9, 12, 5, 3, 4, 2, 6, 0, 8, 1] (by decide) (by decide)
    | 1 => listRank ![9, 5, 7, 6, 8, 12, 10, 2, 4, 0, 3, 11, 1] ![9, 12, 7, 10, 8, 1, 3, 2, 4, 0, 6, 11, 5] (by decide) (by decide)
    | 2 => listRank ![8, 6, 7, 5, 9, 1, 11, 3, 0, 4, 2, 10, 12] ![8, 5, 10, 7, 9, 3, 1, 2, 0, 4, 11, 6, 12] (by decide) (by decide)
    | 3 => listRank ![11, 1, 9, 5, 7, 6, 8, 12, 10, 2, 4, 0, 3] ![11, 1, 9, 12, 10, 3, 5, 4, 6, 2, 8, 0, 7] (by decide) (by decide)
    | 4 => listRank ![0, 3, 11, 1, 9, 5, 7, 6, 8, 12, 10, 2, 4] ![0, 3, 11, 1, 12, 5, 7, 6, 8, 4, 10, 2, 9] (by decide) (by decide)
    | 5 => listRank ![7, 6, 8, 12, 10, 2, 4, 0, 3, 11, 1, 9, 5] ![7, 10, 5, 8, 6, 12, 1, 0, 2, 11, 4, 9, 3] (by decide) (by decide)
    | 6 => listRank ![5, 9, 1, 11, 3, 0, 4, 2, 10, 12, 8, 6, 7] ![5, 2, 7, 4, 6, 0, 11, 12, 10, 1, 8, 3, 9] (by decide) (by decide)
    | 7 => listRank ![1, 11, 3, 0, 4, 2, 10, 12, 8, 6, 7, 5, 9] ![3, 0, 5, 2, 4, 11, 9, 10, 8, 12, 6, 1, 7] (by decide) (by decide)
    | 8 => listRank ![12, 10, 2, 4, 0, 3, 11, 1, 9, 5, 7, 6, 8] ![4, 7, 2, 5, 3, 9, 11, 10, 12, 8, 1, 6, 0] (by decide) (by decide)
    | 9 => listRank ![3, 0, 4, 2, 10, 12, 8, 6, 7, 5, 9, 1, 11] ![1, 11, 3, 0, 2, 9, 7, 8, 6, 10, 4, 12, 5] (by decide) (by decide)
    | 10 => listRank ![2, 4, 0, 3, 11, 1, 9, 5, 7, 6, 8, 12, 10] ![2, 5, 0, 3, 1, 7, 9, 8, 10, 6, 12, 4, 11] (by decide) (by decide)
    | 11 => listRank ![4, 2, 10, 12, 8, 6, 7, 5, 9, 1, 11, 0, 3] ![11, 9, 1, 12, 0, 7, 5, 6, 4, 8, 2, 10, 3] (by decide) (by decide)
    | 12 => listRank ![6, 7, 5, 9, 1, 11, 3, 0, 4, 2, 10, 12, 8] ![7, 4, 9, 6, 8, 2, 0, 1, 12, 3, 10, 5, 11] (by decide) (by decide)
/-- Appendix G, Table 8: entries shifted from labels 1,…,15 to Fin 15. -/
def table15 : Instance 15 where
  manRank
    | 0 => listRank ![0, 9, 13, 3, 11, 6, 14, 1, 2, 8, 5, 10, 7, 12, 4] ![0, 7, 8, 3, 14, 10, 5, 12, 9, 1, 11, 4, 13, 2, 6] (by decide) (by decide)
    | 1 => listRank ![1, 5, 8, 7, 10, 0, 12, 13, 4, 11, 9, 14, 3, 2, 6] ![5, 0, 13, 12, 8, 1, 14, 3, 2, 10, 4, 9, 6, 7, 11] (by decide) (by decide)
    | 2 => listRank ![2, 8, 5, 10, 7, 12, 0, 4, 13, 9, 11, 3, 14, 6, 1] ![6, 14, 0, 11, 7, 2, 13, 4, 1, 9, 3, 10, 5, 8, 12] (by decide) (by decide)
    | 3 => listRank ![3, 0, 6, 13, 1, 11, 8, 14, 10, 2, 12, 5, 4, 7, 9] ![1, 4, 9, 0, 12, 11, 2, 13, 6, 14, 8, 5, 10, 3, 7] (by decide) (by decide)
    | 4 => listRank ![4, 13, 9, 11, 3, 14, 6, 2, 1, 5, 8, 7, 10, 0, 12] ![13, 8, 7, 4, 0, 9, 6, 11, 10, 2, 12, 3, 14, 1, 5] (by decide) (by decide)
    | 5 => listRank ![5, 1, 7, 8, 0, 10, 13, 12, 11, 4, 14, 9, 2, 3, 6] ![4, 1, 12, 13, 9, 0, 14, 2, 3, 11, 5, 8, 7, 6, 10] (by decide) (by decide)
    | 6 => listRank ![6, 7, 1, 0, 8, 13, 10, 11, 12, 14, 4, 2, 9, 5, 3] ![3, 2, 11, 14, 10, 13, 0, 1, 4, 12, 6, 7, 8, 5, 9] (by decide) (by decide)
    | 7 => listRank ![7, 6, 0, 1, 13, 8, 11, 10, 14, 12, 2, 4, 5, 9, 3] ![2, 3, 10, 14, 11, 12, 1, 0, 5, 13, 7, 6, 9, 4, 8] (by decide) (by decide)
    | 8 => listRank ![8, 2, 10, 5, 12, 7, 4, 0, 9, 13, 3, 11, 6, 14, 1] ![7, 14, 1, 10, 6, 3, 12, 5, 0, 8, 2, 11, 4, 9, 13] (by decide) (by decide)
    | 9 => listRank ![9, 0, 3, 13, 6, 11, 1, 14, 8, 2, 10, 5, 12, 7, 4] ![1, 6, 9, 2, 14, 11, 4, 13, 8, 0, 10, 5, 12, 3, 7] (by decide) (by decide)
    | 10 => listRank ![10, 14, 12, 2, 4, 5, 9, 7, 3, 0, 6, 13, 1, 11, 8] ![9, 12, 3, 8, 4, 5, 10, 7, 14, 6, 0, 13, 2, 11, 1] (by decide) (by decide)
    | 11 => listRank ![11, 12, 14, 4, 2, 9, 5, 3, 7, 6, 0, 1, 13, 8, 10] ![10, 11, 4, 7, 3, 6, 9, 8, 13, 5, 14, 0, 1, 12, 2] (by decide) (by decide)
    | 12 => listRank ![12, 11, 4, 14, 9, 2, 3, 5, 6, 7, 1, 0, 8, 13, 10] ![11, 10, 5, 6, 2, 7, 8, 9, 12, 4, 14, 1, 0, 13, 3] (by decide) (by decide)
    | 13 => listRank ![13, 4, 11, 9, 14, 3, 2, 6, 5, 1, 7, 8, 0, 10, 12] ![12, 9, 6, 5, 1, 8, 7, 10, 11, 3, 13, 2, 14, 0, 4] (by decide) (by decide)
    | 14 => listRank ![14, 10, 2, 12, 5, 4, 7, 9, 0, 3, 13, 6, 11, 1, 8] ![8, 13, 2, 9, 5, 4, 11, 6, 14, 7, 1, 12, 3, 10, 0] (by decide) (by decide)
  womanRank
    | 0 => listRank ![4, 13, 12, 11, 10, 14, 8, 2, 1, 5, 6, 7, 3, 9, 0] ![14, 8, 7, 12, 0, 9, 10, 11, 6, 13, 4, 3, 2, 1, 5] (by decide) (by decide)
    | 1 => listRank ![14, 10, 11, 12, 13, 4, 0, 9, 3, 7, 6, 5, 1, 2, 8] ![6, 12, 13, 8, 5, 11, 10, 9, 14, 7, 1, 2, 3, 4, 0] (by decide) (by decide)
    | 2 => listRank ![1, 5, 6, 7, 3, 9, 0, 4, 13, 12, 11, 10, 14, 8, 2] ![6, 0, 14, 4, 7, 1, 2, 3, 13, 5, 11, 10, 9, 8, 12] (by decide) (by decide)
    | 3 => listRank ![5, 1, 2, 8, 14, 10, 11, 12, 13, 4, 0, 9, 3, 6, 7] ![10, 1, 2, 12, 9, 0, 13, 14, 3, 11, 5, 6, 7, 8, 4] (by decide) (by decide)
    | 4 => listRank ![9, 3, 7, 6, 5, 1, 2, 8, 14, 10, 11, 12, 13, 4, 0] ![14, 5, 6, 1, 13, 4, 3, 2, 7, 0, 9, 10, 11, 12, 8] (by decide) (by decide)
    | 5 => listRank ![6, 7, 3, 9, 0, 4, 13, 12, 11, 10, 14, 8, 2, 1, 5] ![4, 13, 12, 2, 5, 14, 0, 1, 11, 3, 9, 8, 7, 6, 10] (by decide) (by decide)
    | 6 => listRank ![2, 8, 14, 10, 11, 12, 13, 4, 0, 9, 3, 7, 6, 1, 5] ![8, 13, 0, 10, 7, 14, 12, 11, 1, 9, 3, 4, 5, 6, 2] (by decide) (by decide)
    | 7 => listRank ![3, 9, 0, 4, 13, 12, 11, 10, 14, 8, 2, 1, 5, 6, 7] ![2, 11, 10, 0, 3, 12, 13, 14, 9, 1, 7, 6, 5, 4, 8] (by decide) (by decide)
    | 8 => listRank ![11, 12, 13, 4, 0, 9, 3, 7, 6, 5, 1, 2, 8, 10, 14] ![4, 10, 11, 6, 3, 9, 8, 7, 12, 5, 13, 0, 1, 2, 14] (by decide) (by decide)
    | 9 => listRank ![7, 6, 5, 1, 2, 8, 14, 10, 11, 12, 13, 4, 0, 9, 3] ![12, 3, 4, 14, 11, 2, 1, 0, 5, 13, 7, 8, 9, 10, 6] (by decide) (by decide)
    | 10 => listRank ![13, 4, 0, 9, 3, 7, 6, 5, 1, 2, 8, 14, 10, 11, 12] ![2, 8, 9, 4, 1, 7, 6, 5, 10, 3, 12, 13, 14, 0, 11] (by decide) (by decide)
    | 11 => listRank ![10, 14, 8, 2, 1, 5, 6, 7, 3, 9, 0, 4, 13, 12, 11] ![10, 4, 3, 8, 11, 5, 6, 7, 2, 9, 0, 14, 13, 12, 1] (by decide) (by decide)
    | 12 => listRank ![0, 9, 3, 7, 6, 5, 1, 2, 8, 14, 10, 11, 12, 4, 13] ![0, 6, 7, 2, 13, 5, 4, 3, 8, 1, 10, 11, 12, 14, 9] (by decide) (by decide)
    | 13 => listRank ![12, 11, 10, 14, 8, 2, 1, 5, 6, 7, 3, 9, 0, 4, 13] ![12, 6, 5, 10, 13, 7, 8, 9, 4, 11, 2, 1, 0, 14, 3] (by decide) (by decide)
    | 14 => listRank ![8, 2, 1, 5, 6, 7, 3, 9, 0, 4, 13, 12, 11, 10, 14] ![8, 2, 1, 6, 9, 3, 4, 5, 0, 7, 13, 12, 11, 10, 14] (by decide) (by decide)

end SwitchingStable.Universal.Supplement


