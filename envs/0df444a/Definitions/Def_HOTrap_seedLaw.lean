-- Prove2me | Definitions.Def_HOTrap_seedLaw
-- name    : HOTrap_seedLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:46:02.279326+00:00
-- url     : https://prove2.me/theorems/5db8974e-5306-4246-876a-4a9d4bcfb2d5
-- title:
--   Law of a fresh seed sequence
-- statement:
--   The law on $[0,1]^{\mathbb N}$ of a sequence of independent Uniform$[0,1]$ variables, the seeds of the randomized line-integration rule.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Appendix C.1, p.70

import Mathlib

namespace HOTrap

/-- **The law of a fresh seed sequence**: i.i.d. Uniform`[0,1]` coordinates. Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, Appendix C.1, p.70
("Let `Z₁,…,Zₙ` be independent uniform random variables on `[0,1]`"). -/
noncomputable def seedLaw : MeasureTheory.Measure (ℕ → unitInterval) :=
  MeasureTheory.Measure.infinitePi (fun _ => MeasureTheory.volume)

end HOTrap


