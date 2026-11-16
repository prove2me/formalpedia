-- Prove2me | Definitions.Def_TightClock_Supplement_levelDraw
-- name    : TightClock_Supplement_levelDraw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:09:34.520209+00:00
-- url     : https://prove2.me/theorems/5d7034cf-dfa7-49aa-9b49-aea00ccc127d
-- title:
--   Price level drawn with probability $p_{j,r}$, (4.3)–(4.5)
-- statement:
--   For the sampled bidders $T\cap G_j$ of a group, with revealed values $v_i$, let
--
--   $$W_j=\sum_{i\in T\cap G_j}q(v_i),\qquad c_{j,r}=|\{i\in T\cap G_j:q(v_i)=2^r\}|,\qquad p_{j,r}=\frac{c_{j,r}2^r}{W_j}\quad(r\in\mathbb Z).$$
--
--   When $W_j>0$ the probabilities $p_{j,r}$ sum to $1$. A level $r$ is drawn with probability $p_{j,r}$ from one uniform $u\in[0,1]$ by the inverse distribution function: the least level whose cumulative probability $\sum_{r'\le r}p_{j,r'}$ exceeds $u$.
--
--   **Formalization Note** Used only when $W_j>0$; the fallback level $0$ arises only at $u=1$, a null event.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §4.2, (4.3)–(4.5), p.17 (PDF p.20)

import Mathlib
import Definitions.Def_TightClock_Supplement_dyadicRound

set_option autoImplicit false

namespace TightClock.Supplement

/-- The price level `r` drawn in Auction 2 for an unsampled bidder of a group whose sampled
bidders are `S` with revealed values `val`: level `r ∈ ℤ` has probability
`p_r = c_r 2^r / W` (4.5), where `W = ∑_{i∈S} q(vᵢ)` (4.3) and `c_r = |{i ∈ S : q(vᵢ) = 2^r}|` (4.4).
It is realized from one uniform `u ∈ [0,1]` by the inverse distribution function: the least level
`r` (among those with `c_r > 0`) whose cumulative probability `∑_{r′ ≤ r} p_{r′}` exceeds `u`.
Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), §4.2, (4.3)–(4.5), p.17 (PDF 20).

**Formalization Note** Used only when `W > 0`. The fallback `0` arises only at `u = 1`, a null
event. -/
noncomputable def levelDraw {n : ℕ} (S : Finset (Fin n)) (val : Fin n → ℝ) (u : ℝ) : ℤ :=
  let W : ℝ := ∑ i ∈ S, dyadicRound (val i)
  let levels : Finset ℤ := (S.filter (fun i => 0 < val i)).image (fun i => Int.log 2 (val i))
  let p : ℤ → ℝ := fun r =>
    ((S.filter (fun i => dyadicRound (val i) = (2 : ℝ) ^ r)).card : ℝ) * (2 : ℝ) ^ r / W
  let cum : ℤ → ℝ := fun r => ∑ r' ∈ levels.filter (· ≤ r), p r'
  if h : (levels.filter (fun r => u < cum r)).Nonempty then
    (levels.filter (fun r => u < cum r)).min' h
  else 0

end TightClock.Supplement


