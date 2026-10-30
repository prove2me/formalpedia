-- Prove2me | Definitions.Def_CoffmanMitrani_classOffset
-- name    : CoffmanMitrani_classOffset
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:13:24.379983+00:00
-- url     : https://prove2.me/theorems/e604aaf1-0c5f-4cb8-af85-6659d09517bc
-- title:
--   Number of class-$i$ jobs before a busy period
-- statement:
--   For a job $j_0$ opening a busy period and a class $i$, the offset is the number of class-$i$ jobs that arrived strictly before $a_{j_0}$. The class-$i$ job with index (offset $+\,r$) is the $r$-th class-$i$ arrival of that busy period; $r$ is its rank within the busy period. Ranks name jobs without revealing how many jobs came before the busy period.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 812, Assumption 2

import Mathlib
import Definitions.Def_CoffmanMitrani_arrival

namespace CoffmanMitrani

/-- **Number of class-`i` jobs that arrived before a busy period.**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 812, Assumption 2 (decisions in a busy period may not use information on prior busy
periods).

`classOffset ω j0 i` is the number of class-`i` jobs arriving strictly before `arrival ω j0`. Inside
the busy period opened by `j0`, the class-`i` job `(i, classOffset ω j0 i + r)` is the `r`-th
(0-based) class-`i` arrival of that busy period; `r` is its rank within the busy period.

**Formalization Note.** `Set.ncard` is `0` on an infinite set; almost surely only finitely many jobs
arrive before any finite time. -/
noncomputable def classOffset {M : ℕ} (ω : Omega M) (j0 : Job M) (i : Fin M) : ℕ :=
  {m : ℕ | arrival ω (i, m) < arrival ω j0}.ncard

end CoffmanMitrani


