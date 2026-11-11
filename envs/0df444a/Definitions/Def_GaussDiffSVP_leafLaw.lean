-- Prove2me | Definitions.Def_GaussDiffSVP_leafLaw
-- name    : GaussDiffSVP_leafLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:10.04757+00:00
-- url     : https://prove2.me/theorems/f99e5d16-826d-44df-bf2d-22efb31354e9
-- title:
--   Leaf pool of $N$ independent trials
-- statement:
--   The record list of a leaf: run $N$ independent trials and append a record for every trial that does not fail, in trial order. Algorithm 1 uses $N = 2M_{\mathrm{leaf}}$ corrected trials.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Algorithm 1, lines 1–7, p.29

import Mathlib

namespace GaussDiffSVP

/-- The record list of a leaf pool (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Algorithm 1, lines 1–7, p.29): run `N` independent
trials with law `trial` and append a record for every trial that does not return the failure
symbol `†` (`none`), in trial order ("Store only nonfailure records", p.29). Algorithm 1 uses
`N = 2M_leaf`. -/
noncomputable def leafLaw {α : Type*} (trial : PMF (Option α)) : ℕ → PMF (List α)
  | 0 => PMF.pure []
  | N + 1 => trial.bind fun o => (leafLaw trial N).map fun l => o.toList ++ l

end GaussDiffSVP


