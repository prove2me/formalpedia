-- Prove2me | Definitions.Def_StochAutoreg_bernMass
-- name    : StochAutoreg_bernMass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:11:35.596194+00:00
-- url     : https://prove2.me/theorems/144005dc-c9aa-47d1-80fd-233bc18c0370
-- title:
--   Mass of a Bernoulli law at a token
-- statement:
--   For $p\in\mathbb R$ and a token $b$, the mass of $\mathrm{Bern}(p)$ at $b$ is $p$ when $b=1$ and $1-p$ when $b=0$. It is the building block of the trajectory law of a generator.
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, §1.1, p.2

import Mathlib

namespace StochAutoreg

/-- The mass of a Bernoulli law of mean `p` at a token: `p` at `1` (`true`), `1 - p` at `0` (`false`).
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, §1.1, p.2. -/
noncomputable def bernMass (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

end StochAutoreg


