-- Prove2me | Definitions.Def_FastCore_step
-- name    : FastCore_step
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:30:44.604904+00:00
-- url     : https://prove2.me/theorems/e8dbd1ae-6497-45d6-945c-00d8e70ef5a2
-- title:
--   One transition of Algorithm 1
-- statement:
--   One step of the algorithm, mirroring Algorithm 1 and Procedure 2 line by line, with precision $\epsilon$ and the oracle $q$ as its only access to the bids.
--
--   1. **After the return:** nothing changes.
--   2. **Outer loop.** If $S_t=\emptyset$, the loop exits. Otherwise query $q(\bar\pi^{(t)})$, obtaining $T_t$ (line 4), and set $S_{t+1}=S_t\cap T_t$ (line 5). The first answer also supplies $w(N)$. If $S_{t+1}=\emptyset$ the algorithm returns $\pi^{(t)}$. Otherwise Core-Search starts with $\Delta_l=0$, $\Delta_h=1$.
--   3. **Core-Search.** If $\Delta_h-\Delta_l\le\epsilon/|S|$, set $\pi^{(t+1)}=\pi^{(t)}+\Delta_l$ and $\bar\pi^{(t+1)}=\pi^{(t)}+\Delta_h$ on $S$, leaving the other coordinates of $\pi^{(t)}$ unchanged, and increase $t$ by one. Otherwise let $\Delta=(\Delta_l+\Delta_h)/2$ and $\tilde\pi=\pi^{(t)}+\Delta$ on $S$; if $w(N)-\sum_{i\in N}\tilde\pi_i$ is at least the oracle's value at $\tilde\pi$, set $\Delta_l=\Delta$, else $\Delta_h=\Delta$.
--
--   **Formalization Note** The `return` on line 11 is read as the else branch of line 6: returning after the first pass contradicts Figure 1 and p.19. The call counter increases at each oracle query. The additional time charges $n$ for each pass through lines 3–5, each bisection step and each exit from Core-Search.
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Algorithm 1 and Procedure 2, pp.15–16

import Mathlib
import Definitions.Def_FastCore_Phase
import Definitions.Def_FastCore_Cfg
import Definitions.Def_FastCore_bump
import Definitions.Def_FastCore_Oracle

namespace FastCore

/-- One transition of Algorithm 1 and Procedure 2 (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, pp.15–16), with the oracle `q` as the
only access to the bids.

* Phase `done`: nothing changes.
* Phase `outer` (lines 3–6): if `S = ∅` the loop exits. Otherwise line 4 queries `π̄`, giving `T`, and
  line 5 sets `S ← S ∩ T`. If the new `S` is empty the run returns `π`; otherwise Core-Search starts
  with `Δl = 0`, `Δh = 1`.
* Phase `search` (Procedure 2): if `Δh − Δl ≤ ε/|S|` the search exits, setting `π` and `π̄` from `Δl`
  and `Δh` and `t ← t + 1`. Otherwise it tests the midpoint `Δ` with one oracle call and moves `Δl`
  or `Δh` to it.

**Formalization Note.** The `return π^(t)` of line 11 is read as the else branch of line 6: a return
after the first pass would contradict the paper's Figure 1 and p.19. `calls` is incremented at each
oracle query. `ticks` charges `n` per pass of lines 3–5, per bisection step and per exit from
Core-Search. `log` is written and never read. -/
noncomputable def step {n : ℕ} (q : Oracle n) (ε : ℝ) (c : Cfg n) : Cfg n :=
  match c.phase with
  | Phase.done => c
  | Phase.outer =>
    if c.S = ∅ then
      { c with phase := Phase.done }
    else
      let r := q c.πbar
      let Snew := c.S ∩ r.2
      let c' : Cfg n :=
        { c with
          S := Snew
          log := c.log ++ [r.2]
          wN := if c.t = 0 then r.1 else c.wN
          calls := c.calls + 1
          ticks := c.ticks + n }
      if Snew = ∅ then
        { c' with phase := Phase.done }
      else
        { c' with phase := Phase.search, Δl := 0, Δh := 1 }
  | Phase.search =>
    if c.Δh - c.Δl ≤ ε / (c.S.card : ℝ) then
      { c with
        phase := Phase.outer
        π := bump c.π c.S c.Δl
        πbar := bump c.π c.S c.Δh
        t := c.t + 1
        ticks := c.ticks + n }
    else
      let Δ := (c.Δl + c.Δh) / 2
      let πtilde := bump c.π c.S Δ
      let c' : Cfg n := { c with calls := c.calls + 1, ticks := c.ticks + n }
      if c.wN - ∑ i, πtilde i ≥ (q πtilde).1 then
        { c' with Δl := Δ }
      else
        { c' with Δh := Δ }

end FastCore


