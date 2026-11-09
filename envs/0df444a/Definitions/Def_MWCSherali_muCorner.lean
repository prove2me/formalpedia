-- Prove2me | Definitions.Def_MWCSherali_muCorner
-- name    : MWCSherali_muCorner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:13:03.573544+00:00
-- url     : https://prove2.me/theorems/200f71ab-e7ce-428c-bb41-7e45250a1fd0
-- title:
--   The exit measure $\mu_a$ of the corner $K_a$
-- statement:
--   $$\mu_a=\mu^Z_a+\sum_{b\neq a}\big(\mu^T_{ab}+\mu^E_{ab}\big),$$
--
--   the measure on the cross section $\{t\in\Delta_4\mid t_a=\alpha\}$ through which commodity $a$ leaves its corner: into the central region, the three tubes and the three simplex edges.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), §4.1, p.33

import Mathlib
import Definitions.Def_MWCSherali_muZ
import Definitions.Def_MWCSherali_muT
import Definitions.Def_MWCSherali_muE

namespace MWCSherali

open MeasureTheory

/-- **The exit measure `μ_a` of the corner `K_a`.** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), §4.1, p.33:
"`μ_a = μ^Z_a + ∑_{b ≠ a} (μ^T_{ab} + μ^E_{ab})`", the measure on the cross section
`{t ∈ Δ₄ | t_a = α}` through which commodity `a` leaves the corner. -/
noncomputable def muCorner (α β C : ℝ) (a : Fin 4) : Measure (Fin 4 → ℝ) :=
  muZ α β C a + ∑ b ∈ Finset.univ.filter (· ≠ a), (muT α β C a b + muE α β C a b)

end MWCSherali


