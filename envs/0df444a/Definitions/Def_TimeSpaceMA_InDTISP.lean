-- Prove2me | Definitions.Def_TimeSpaceMA_InDTISP
-- name    : TimeSpaceMA_InDTISP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:56:52.207949+00:00
-- url     : https://prove2.me/theorems/a2dab8b8-638a-49e2-8513-bc2122ef45d7
-- title:
--   The class $\mathrm{DTISP}[t(n),s(n)]$
-- statement:
--   A language $L$ of bit strings is in $\mathrm{DTISP}[t(n),s(n)]$ if a single random-access Turing machine, on every input $x$ of length $n$, is in a halting state after $t(n)$ steps, has scanned at most $s(n)$ work cells during those steps, and is in the accepting state exactly when $x \in L$.
--
--   This is the class of the goal theorem. There is no restriction on $t$ and $s$ beyond those bounds.
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), §2, p.6

import Definitions.Def_TimeSpaceMA_RATM

namespace TimeSpaceMA

/-- `L ∈ DTISP[t(n), s(n)]` (Williams, Xi, STOC 2027 submission, manuscript sha256 184c2f95…, §2,
p.6): some random-access machine, on every input `x`, halts within `t |x|` steps, scans at most
`s |x|` work cells, and enters its accepting state exactly when `x ∈ L`.

**Formalization Note** Space counts distinct scanned (tape, position) cells; the address register is
not counted, since it holds `O(log n)` bits (`RATM.applyAddr`) and the page's `S = s + O(log nt)`
pays for it. -/
def InDTISP (L : Set (List Bool)) (t s : ℕ → ℕ) : Prop :=
  ∃ M : RATM, ∀ x : List Bool,
    let c := M.run x (t x.length)
    (c.state = M.qaccept ∨ c.state = M.qreject) ∧
      (M.scanned x (t x.length)).card ≤ s x.length ∧
      (c.state = M.qaccept ↔ x ∈ L)

end TimeSpaceMA


