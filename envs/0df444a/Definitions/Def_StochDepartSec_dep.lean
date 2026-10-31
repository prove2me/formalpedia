-- Prove2me | Definitions.Def_StochDepartSec_dep
-- name    : StochDepartSec_dep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:55:58.480972+00:00
-- url     : https://prove2.me/theorems/85883737-7f79-4a11-aac0-6d358027b7b6
-- title:
--   Departure time $D_i=\min\{A_i+L_i,1\}$
-- statement:
--   The **departure time** of candidate $i$ in outcome $\omega$ is
--
--   $$
--   D_i=\min\{a_i+\ell_i,\,1\}.
--   $$
--
--   Every candidate still in the system at time $1$ leaves at time $1$, so several candidates can depart at the same instant.
-- source:
--   Kesselheim, Psomas, Vardi, How to Hire Secretaries with Stochastic Departures, arXiv:1909.08660v1, §2, p.5

import Mathlib
import Definitions.Def_StochDepartSec_Outcome

namespace StochDepartSec

/-- Departure time of candidate `i`: `D_i = min {A_i + L_i, 1}`.
Kesselheim, Psomas, Vardi, *How to Hire Secretaries with Stochastic Departures*, arXiv:1909.08660v1, §2, p.5: "The departure time D_i is min{A_i + L_i, 1}."

**Formalization Note** The cap at time 1 makes simultaneous departures at time 1 generic: every
candidate still present leaves at time 1. -/
noncomputable def dep {n : ℕ} (ω : Outcome n) (i : Fin n) : ℝ :=
  min (arrival ω i + waiting ω i) 1

end StochDepartSec


