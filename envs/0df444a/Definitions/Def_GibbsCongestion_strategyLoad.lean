-- Prove2me | Definitions.Def_GibbsCongestion_strategyLoad
-- name    : GibbsCongestion_strategyLoad
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:00:23.672348+00:00
-- url     : https://prove2.me/theorems/fcfacaf9-d501-4020-b1a1-992e43cd1ef2
-- title:
--   Strategy load $z_p(s)$
-- statement:
--   For a symmetric congestion game with common strategy set $\mathcal P$, a profile $s\in\mathcal P^n$ and a strategy $p\in\mathcal P$,
--   $$z_p(s)=|\{i\in N: s_i=p\}|$$
--   is the number of players choosing $p$. The vector $z(s)=(z_p(s))_{p\in\mathcal P}$ is the **strategy load profile** of $s$, and $\mathcal S(\alpha)=\{s: z(s)=\alpha\}$.
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §2.1, p.7

import Mathlib

namespace GibbsCongestion

/-- The **strategy load** `z_p(s) = |{i ∈ N : s_i = p}|`, the number of players choosing
strategy `p` (Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §2.1, p.7). The vector `z(s) = (z_p(s))_{p ∈ P}` is the strategy load
profile of `s`. -/
noncomputable def strategyLoad {E : Type*} [DecidableEq E] {P : Finset (Finset E)} {n : ℕ} (s : Fin n → P)
    (p : P) : ℕ :=
  (Finset.univ.filter (fun i => s i = p)).card

end GibbsCongestion


