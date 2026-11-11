-- Prove2me | Definitions.Def_DecDynMatch_feedback
-- name    : DecDynMatch_feedback
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:57:05.389207+00:00
-- url     : https://prove2.me/theorems/9b4fcd0b-89d8-42d8-864a-cb8c4291d3fe
-- title:
--   Feedback step of SC-DA with replay rule $F$
-- statement:
--   After proposing to arm $x$ and observing the outcome $z\in\{A,R\}$, a player with replay rule $F$ updates its state in this order:
--
--   1. $\rho\leftarrow\min\{J,\rho+1\}$ if $x=$ BUS and $z=A$, and $\rho\leftarrow 0$ otherwise;
--   2. in **Seek**: on $R$ it sets $\textsf{seenR}$; on $A$ with $\textsf{seenR}$ set and $\rho\ge 2$ it schedules Work (AA handoff);
--   3. in **Sweep**: on a BUS rejection it schedules Seek; otherwise it records $b=\textsf{blockOK}\wedge(z=A)$ and, if $s<2K$, advances $s$ and stores $b$; at $s=2K$ it schedules Work if $b$ holds and otherwise restarts the block ($s\leftarrow1$, $\textsf{blockOK}\leftarrow$ true);
--   4. in **Work**: in the final round $h=J-1$ it **outputs**, whatever $z$: $y\leftarrow x$, $L\leftarrow F(a-\ell)$, $q\leftarrow a+L$, $\ell\leftarrow a$, and schedules Replay; otherwise it advances $k\leftarrow\min\{k+1,K\}$ if $h>4K$ and $z=R$, and sets $h\leftarrow h+1$;
--   5. in **Replay**: on $R$ it schedules Seek;
--   6. $a\leftarrow a+1$.
--
--   Scheduled mode changes take effect at the start of the next round. With $F(x)=H+2x$ the output update is Algorithm 1's $L=H+2(a-\ell)$.
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), Algorithm 1, lines 19–42 and SweepFeedback, p.6; eq. (13) and execution conventions, p.14

import Mathlib
import Definitions.Def_DecDynMatch_J
import Definitions.Def_DecDynMatch_LState

namespace DecDynMatch

variable {K : ℕ} {ι : Type*} [Fintype ι]

/-- **Feedback step of SC-DA with replay rule `F`.** J. Chen, M. Gao, Z. Zhang, *Decentralized
Dynamic Stable Matching*, arXiv:2610.41912 (held version, sha256 6a27277e…), Algorithm 1,
lines 21–42 and SweepFeedback, p.6, with the replay update (13), p.14
("L ← F(a − ℓ), q ← a + L, ℓ ← a"), in the order of p.14: "After proposing, each player updates
the BUS counter ρ, processes feedback in its current mode, and increments local time a, in that
order."

`feedback I F st x z` is the state after a round in which the player, in round-start state `st`,
proposed to arm `x` and got outcome `z` (`true` = A, `false` = R):
1. `ρ ← min{J, ρ + 1}` if `x = BUS` and `z = A`, else `0`;
2. Seek: on R set `seenR`; on A with `seenR` and (updated) `ρ ≥ 2`, `ν ← Work` (AA handoff);
3. Sweep (SweepFeedback): on a BUS rejection `ν ← Seek`; otherwise `b ← blockOK ∧ z = A` and, if
   `s < 2K`, `s ← s + 1, blockOK ← b`; if `s = 2K` and `b`, `ν ← Work`; else restart the block
   (`s ← 1, blockOK ← true`);
4. Work: at `h = J − 1` output: `y ← x`, `q ← a + F(a − ℓ)`, `ℓ ← a`, `ν ← Replay` (whatever `z`);
   otherwise `k ← min{k + 1, K}` if `h > 4K` and `z = R`, and `h ← h + 1`;
5. Replay: on R, `ν ← Seek`;
6. `a ← a + 1`.

**Formalization Note.** With `F = scdaRule K` the output update is Algorithm 1's line 31,
`L ← H + 2(a − ℓ)`. -/
def feedback (I : Instance K ι) (F : ℕ → ℕ) (st : LState K) (x : Fin K) (z : Bool) : LState K :=
  let st1 : LState K :=
    { st with ρ := if x = bus I ∧ z = true then min (J K) (st.ρ + 1) else 0 }
  let st2 : LState K :=
    match st1.m with
    | .seek =>
        if z = false then { st1 with seenR := true }
        else if st1.seenR = true ∧ 2 ≤ st1.ρ then { st1 with ν := some .work }
        else st1
    | .sweep =>
        if x = bus I ∧ z = false then { st1 with ν := some .seek }
        else
          let bb := st1.blockOK && z
          if st1.s < 2 * K then { st1 with s := st1.s + 1, blockOK := bb }
          else if bb = true then { st1 with blockOK := bb, ν := some .work }
          else { st1 with s := 1, blockOK := true }
    | .work =>
        if st1.h = J K - 1 then
          { st1 with y := x, q := st1.a + F (st1.a - st1.l), l := st1.a, ν := some .replay }
        else
          { st1 with
            k := if 4 * K < st1.h ∧ z = false then min (st1.k + 1) K else st1.k,
            h := st1.h + 1 }
    | .replay => if z = false then { st1 with ν := some .seek } else st1
  { st2 with a := st2.a + 1 }

end DecDynMatch


