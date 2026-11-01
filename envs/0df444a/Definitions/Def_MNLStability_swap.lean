-- Prove2me | Definitions.Def_MNLStability_swap
-- name    : MNLStability_swap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:23.218912+00:00
-- url     : https://prove2.me/theorems/ad278e00-95ca-41e0-b840-d46f8093d008
-- title:
--   $I$-swapping $U\hookleftarrow_I V$
-- statement:
--   For a set of products $I$ and two inventory vectors $U,V$, the **$I$-swapping of $V$ into $U$** is
--
--   $$(U\hookleftarrow_I V)_i=\begin{cases}V_i,& i\in I,\\ U_i,& i\notin I.\end{cases}$$
--
--   Class swapping ($I=W_k$) builds the near-optimal vector $\tilde U$ of §3.2, and $I$-universal families (§4) are defined through it.
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), §3.2, p.16; §4.1, p.18

import Mathlib

namespace MNLStability

variable {n : ℕ}

/-- `U ↩_I V`, the `I`-swapping of `V` into `U` (SSRN:3498325, §3.2, p.16 and §4.1, p.18): the
inventory level of each product `i ∈ I` is set to `V i`; all other products keep `U i`. -/
def swap (I : Finset (Fin n)) (U V : Fin n → ℕ) : Fin n → ℕ :=
  fun i => if i ∈ I then V i else U i

end MNLStability


