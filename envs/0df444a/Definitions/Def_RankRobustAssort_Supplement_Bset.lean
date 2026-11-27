-- Prove2me | Definitions.Def_RankRobustAssort_Supplement_Bset
-- name    : RankRobustAssort_Supplement_Bset
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:33:01.51161+00:00
-- url     : https://prove2.me/theorems/6f99a667-49bd-4320-9a54-4df446a4d255
-- title:
--   Products first offered in past assortment $m$, $B_m$
-- statement:
--   For past assortments $S_1,\dots,S_M\subseteq\mathcal N_0$ and $m\in\mathcal M$, the products offered in $S_m$ and in no earlier past assortment are
--
--   $$
--   B_m=S_m\setminus\bigcup_{m'=1}^{m-1}S_{m'} .
--   $$
--
--   In particular $B_1=S_1$; when the past assortments are nested, $B_m=S_m\setminus S_{m-1}$ for $m\ge2$, and the sets $B_1,\dots,B_M$ are disjoint. Lemma 10 uses them to describe $\mathcal L$.
-- source:
--   Sturt, The value of robust assortment optimization under ranking-based choice models, arXiv:2112.05010v4, §5.3, equation (3), p.19

import Mathlib
import Definitions.Def_RankRobustAssort_Problem

namespace RankRobustAssort.Supplement

/-- The products first offered in past assortment `m`:
`B_m ≜ S_m \ ⋃_{m'=1}^{m−1} S_{m'}` (so `B₁ = S₁`).

Sturt, arXiv:2112.05010v4, §5.3, equation (3), p.19.

Formalization Note: past assortments are indexed by `Fin M` (paper index `m` = Lean index
`m − 1`); the union runs over the Lean indices `m' < m`. This is the defining (left-hand)
expression of (3); under Assumption 1 it equals `S_m \ S_{m−1}` for `m ≥ 2`. -/
def Bset {n M : ℕ} (P : Problem n M) (m : Fin M) : Finset (Fin (n + 1)) :=
  P.S m \ (Finset.univ.filter (fun m' : Fin M => m' < m)).biUnion P.S

end RankRobustAssort.Supplement


