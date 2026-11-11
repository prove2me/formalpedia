-- Prove2me | Definitions.Def_GaussDiffSVP_cosetCount
-- name    : GaussDiffSVP_cosetCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T22:01:21.673217+00:00
-- url     : https://prove2.me/theorems/d3333730-3dd1-431a-a044-7e357b43f41f
-- title:
--   Coset representation count $J_C(v)$
-- statement:
--   For an affine coset $C = c+\Gamma$, a vector $v$, a width $r$ and an energy $a$,
--   $$J_C(v) = \sum_{x\in C}\mathbf 1_{S_r(a)}(x)\,\mathbf 1_{S_r(a)}(x-v),$$
--   the number of representations of $v$ as a difference of two points of $C$ in the shell $S_r(a)$.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (88), §9.2, p.42

import Mathlib
import Definitions.Def_GaussDiffSVP_shell

namespace GaussDiffSVP

/-- The coset representation count `J_C(v) = ∑_{x ∈ C} 1_{S_r(a)}(x) 1_{S_r(a)}(x − v)` of (88)
(Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), §9.2, p.42) for the affine coset `C = c + Γ` (`c = z + δ` in §9.1): the number of
`x ∈ C` with `x ∈ S_r(a)` and `x − v ∈ S_r(a)`.

**Formalization Note.** Counted with `Set.encard`. -/
noncomputable def cosetCount {n : ℕ} (Γ : Submodule ℤ (SuperlatSVP.E n)) (c v : SuperlatSVP.E n)
    (r w a : ℝ) : ℕ∞ :=
  {x : SuperlatSVP.E n | x - c ∈ Γ ∧ x ∈ shell r w a ∧ x - v ∈ shell r w a}.encard

end GaussDiffSVP


