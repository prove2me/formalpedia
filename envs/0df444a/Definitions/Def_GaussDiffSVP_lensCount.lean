-- Prove2me | Definitions.Def_GaussDiffSVP_lensCount
-- name    : GaussDiffSVP_lensCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T22:00:57.49585+00:00
-- url     : https://prove2.me/theorems/1b3db774-48ba-4069-a1e9-cb2c5463886d
-- title:
--   Midpoint lens count $J_d(z)$
-- statement:
--   At parent offset $p$ and local shift $d$, with $C_+ = p/2+d+\Gamma$ and $C_- = -p/2+d+\Gamma$, $J_d(z)$ is the number of pairs $z = x-y$ with $x\in C_+\cap S_r(a)$ and $y\in C_-\cap S_r(a)$: the number of representations of $z$ as a difference of two child-shell points.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), §8.1, p.38

import Mathlib
import Definitions.Def_GaussDiffSVP_shell

namespace GaussDiffSVP

/-- The midpoint lens count `J_d(z)` (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), §8.1, p.38): at parent offset `p` and local shift `d`,
with `C₊ = p/2 + d + Γ` and `C₋ = −p/2 + d + Γ`, the number of pairs `z = x − y` with
`x ∈ C₊ ∩ S_r(a)` and `y ∈ C₋ ∩ S_r(a)`.

**Formalization Note.** `Γ` is any `ℤ`-submodule (a lattice in every use); the count is
`Set.encard` (never collapses on an infinite set). -/
noncomputable def lensCount {n : ℕ} (Γ : Submodule ℤ (SuperlatSVP.E n)) (r w a : ℝ)
    (p d z : SuperlatSVP.E n) : ℕ∞ :=
  {xy : SuperlatSVP.E n × SuperlatSVP.E n | z = xy.1 - xy.2 ∧
    xy.1 - ((1 / 2 : ℝ) • p + d) ∈ Γ ∧ xy.1 ∈ shell r w a ∧
    xy.2 - (-((1 / 2 : ℝ) • p) + d) ∈ Γ ∧ xy.2 ∈ shell r w a}.encard

end GaussDiffSVP


