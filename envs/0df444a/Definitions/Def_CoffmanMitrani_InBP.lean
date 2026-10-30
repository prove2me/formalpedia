-- Prove2me | Definitions.Def_CoffmanMitrani_InBP
-- name    : CoffmanMitrani_InBP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:12:21.404275+00:00
-- url     : https://prove2.me/theorems/ed220fe1-e0bd-46ea-8734-6b4ce1444be4
-- title:
--   Time inside the busy period opened by a job
-- statement:
--   A time $t$ lies in the busy period opened by job $j_0$ if $t \ge a_{j_0}$ and, at every time $s \in (a_{j_0}, t]$, the work that arrived in $[a_{j_0}, s)$ exceeds $s - a_{j_0}$, i.e. the work that entered since the busy period started has not yet been exhausted.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 812 (busy periods)

import Mathlib
import Definitions.Def_CoffmanMitrani_workIn

namespace CoffmanMitrani

/-- **Time inside the busy period opened by a job.**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 812 (busy periods).

`InBP ω j0 t` says that `t ≥ arrival ω j0` and that at every time `s ∈ (arrival ω j0, t]` the work
arrived in `[arrival ω j0, s)` exceeds the elapsed time `s − arrival ω j0`, i.e. the work that
entered since `arrival ω j0` has not been exhausted by time `s`. When `IsBPStart ω j0` holds, this
is exactly "`t` lies in the busy period that starts at the arrival of `j0`".

**Formalization Note.** Strategy-independent, like `IsBPStart`. A busy period ending exactly when a
new job arrives is followed by a new busy period opened by that job. -/
def InBP {M : ℕ} (ω : Omega M) (j0 : Job M) (t : ℝ) : Prop :=
  arrival ω j0 ≤ t ∧ ∀ s ∈ Set.Ioc (arrival ω j0) t, s - arrival ω j0 < workIn ω (arrival ω j0) s

end CoffmanMitrani


