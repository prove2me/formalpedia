-- Prove2me | Definitions.Def_GaussDiffSVP_shell
-- name    : GaussDiffSVP_shell
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:59:09.631904+00:00
-- url     : https://prove2.me/theorems/e5244cd8-7711-438e-a7a2-aaf19cf6f17b
-- title:
--   Thin shell $S_r(a) = \{x : E_r(x)\in a(1\pm w)\}$
-- statement:
--   For a width $r$, a relative width $w$ and an energy $a$,
--   $$S_r(a) = \{x\in\mathbb R^n : E_r(x)\in [a(1-w),\,a(1+w)]\},$$
--   the closed thin shell of normalized energy $a$. The paper writes $a(1\pm w_n)$ for the closed interval.
--
--   **Formalization Note** The width $w$ is an explicit argument; every statement passes the $w_n$ of the schedule in force.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (7), §3.3, p.18

import Mathlib
import Definitions.Def_GaussDiffSVP_energy

namespace GaussDiffSVP

/-- The thin shell `S_r(a) = {x : E_r(x) ∈ a(1 ± w)}` (Gao–Han–Hu, *Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (7), p.18), where
"`a(1 ± w_n)` denotes the closed interval `[a(1 − w_n), a(1 + w_n)]`".

**Formalization Note.** The relative width `w` is an explicit argument; every use passes the
`w_n` of the schedule in force (`svpBudget.w n` or `singleBudget δ`). -/
def shell {n : ℕ} (r w a : ℝ) : Set (SuperlatSVP.E n) :=
  {x | energy r x ∈ Set.Icc (a * (1 - w)) (a * (1 + w))}

end GaussDiffSVP


