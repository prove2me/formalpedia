-- Prove2me | Definitions.Def_AffDisp4n_State_W
-- name    : AffDisp4n_State_W
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T08:00:20.808197+00:00
-- url     : https://prove2.me/theorems/df235ac1-c165-4b6d-9cd5-b7c3392517d0
-- title:
--   The potential $W = s + 4q + \sum \mathrm{wt}(x)$
-- statement:
--   The weight of an unpaired parameter is $\mathrm{wt}(x) = 0$ if $\deg(x) = 0$ and $\mathrm{wt}(x) = 6$ if $\deg(x) \ge 1$. The **potential** of a state is
--   $$
--   W = s + 4q + \sum_{x \text{ unpaired}} \mathrm{wt}(x) = s + 4q + 6\cdot\#\{x \text{ unpaired} : \deg(x) \ge 1\}.
--   $$
--   Paired parameters contribute only through $4q$. Initially $W \le |C_0| + 6n$. Each iteration of gate elimination lowers $W$ by at least $10$ per unit decrease of $a$, which gives the $4n - 10d$ bound.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §2.6, p.18, displays (4)–(5)

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic
import Definitions.Def_AffDisp4n_Acyclic_Reads
import Definitions.Def_AffDisp4n_State
import Definitions.Def_AffDisp4n_State_s
import Definitions.Def_AffDisp4n_State_q
import Definitions.Def_AffDisp4n_State_IsPaired
import Definitions.Def_AffDisp4n_State_deg

namespace AffDisp4n

/-- The **potential** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), displays (4)–(5), p.18): `W = s + 4q + ∑_{x unpaired} wt(x)`, where the
weight of an unpaired parameter is `wt(x) = 0` if `deg(x) = 0` and `wt(x) = 6` if `deg(x) ≥ 1`. So
`W = s + 4q + 6 · #{unpaired parameters of degree ≥ 1}`. Paired parameters contribute only through `4q`. -/
noncomputable def State.W {n : ℕ} (σ : State n) : ℕ :=
  σ.s + 4 * σ.q + 6 * Nat.card {x : Fin σ.m // ¬ σ.IsPaired x ∧ 1 ≤ σ.deg x}

end AffDisp4n


