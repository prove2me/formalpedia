-- Prove2me | Definitions.Def_MultiAllocToAlloc_Subadditive_PickingGame
-- name    : MultiAllocToAlloc_Subadditive_PickingGame
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:09:27.465401+00:00
-- url     : https://prove2.me/theorems/0581580f-ec24-48d6-a4eb-a59403fe0adb
-- title:
--   ω(S_p, M, v) and ω(S_q, M, v): values of the alternating picking game (Definition 7)
-- statement:
--   Two players $p$ (`0 : Fin 2`) and $q$ (`1 : Fin 2`) pick the items of a finite set $M\subseteq$ `Fin m` one at a time, in the order of a picking sequence. $S_p$ (`seqP |M|`) alternates $p,q,p,\dots$ and $S_q$ (`seqQ |M|`) alternates $q,p,q,\dots$, each of length $|M|$, so every item of $M$ is picked. Player $p$ has valuation $v$ and payoff $v(T)$ for the set $T$ she picks; $q$'s payoff is $-v(T)$. $\omega(S_p,M,v)$ (`omegaP v M`) and $\omega(S_q,M,v)$ (`omegaQ v M`) are the maximin values of $p$ (Definition 7, p. 6), computed by backward induction with the published `FairShares.gameVal`: at $p$'s turn she takes the item maximizing the continuation value, at $q$'s turn the item minimizing it is removed, and the final value is $v$ of $p$'s holdings, starting from the empty holding.
-- source:
--   Feige, arXiv:2506.21493v1, §2.1 and Definition 7, p. 6

import Mathlib
import Definitions.Def_FairShares_gameVal

namespace MultiAllocToAlloc.Subadditive

/-- The alternating picking sequence `S_p = p, q, p, q, …` of length `len`
(Feige, arXiv:2506.21493v1, §2.1, p. 6). Player `p` is `0 : Fin 2`, player `q` is `1 : Fin 2`;
round `r` (counted from `0`) is a pick by `p` exactly when `r` is even. -/
def seqP (len : ℕ) : List (Fin 2) :=
  (List.range len).map (fun r => if r % 2 = 0 then 0 else 1)

/-- The alternating picking sequence `S_q = q, p, q, p, …` of length `len`
(Feige, arXiv:2506.21493v1, §2.1, p. 6). Player `p` is `0 : Fin 2`, player `q` is `1 : Fin 2`;
round `r` (counted from `0`) is a pick by `q` exactly when `r` is even. -/
def seqQ (len : ℕ) : List (Fin 2) :=
  (List.range len).map (fun r => if r % 2 = 0 then 1 else 0)

/-- `ω(S_p, M, v)` (Feige, arXiv:2506.21493v1, Definition 7, p. 6): the maximin value that
player `p`, with valuation `v` on the bundle `T` she picks, can guarantee in the two-player
picking game on the item set `M` with the alternating sequence `S_p` of length `|M|`
(`p` picks first; every item of `M` is picked). It is the backward-induction value
`FairShares.gameVal` with two players, `p = 0`, remaining items `M` and empty initial holding. -/
noncomputable def omegaP {m : ℕ} (v : Finset (Fin m) → ℝ) (M : Finset (Fin m)) : ℝ :=
  FairShares.gameVal v (0 : Fin 2) (seqP M.card) M ∅

/-- `ω(S_q, M, v)` (Feige, arXiv:2506.21493v1, Definition 7, p. 6): as `omegaP`, but with the
alternating sequence `S_q` of length `|M|`, in which `q` picks first. -/
noncomputable def omegaQ {m : ℕ} (v : Finset (Fin m) → ℝ) (M : Finset (Fin m)) : ℝ :=
  FairShares.gameVal v (0 : Fin 2) (seqQ M.card) M ∅

end MultiAllocToAlloc.Subadditive


