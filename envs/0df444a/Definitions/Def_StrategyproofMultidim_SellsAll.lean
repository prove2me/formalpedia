-- Prove2me | Definitions.Def_StrategyproofMultidim_SellsAll
-- name    : StrategyproofMultidim_SellsAll
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:12:25.691839+00:00
-- url     : https://prove2.me/theorems/031b1981-87c4-46d8-80f8-6eb79c9798eb
-- title:
--   Sells all objects at all profiles
-- statement:
--   A mechanism **sells all objects at all profiles** ("no-wastage") if at every positive profile $v$ every object $k$ is sold to some buyer: for each $k$ there is $i$ with $d_i^k(v)=1$.
-- source:
--   Basu, Mukherjee, Strategyproof multidimensional mechanism design without unit demand, IIM Calcutta WPS No 875 (April 2022), Theorem 4 and footnote 13, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_StrategyproofMultidim_Mechanism
import Definitions.Def_StrategyproofMultidim_PosProfile

namespace StrategyproofMultidim

/-- **Sells all objects at all profiles** (Theorem 4, p.15; footnote 13: "KMS [14] refer to
such mechanisms as 'no-wastage' mechanisms").
Basu, Mukherjee, *Strategyproof multidimensional mechanism design without unit demand*,
IIM Calcutta WPS No 875 (April 2022), p.15.

At every positive profile every object is sold to some buyer. -/
def SellsAll {n m : ℕ} (μ : Mechanism n m) : Prop :=
  ∀ v, PosProfile v → ∀ k, ∃ i, μ.q v i k = true

end StrategyproofMultidim


