-- Prove2me | Definitions.Def_StochAutoreg_clampI
-- name    : StochAutoreg_clampI
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:12:01.787529+00:00
-- url     : https://prove2.me/theorems/1a7522bc-6c74-4022-abf1-49b84f1ef4bb
-- title:
--   Projection of a real number into $[0,1]$
-- statement:
--   The projection of a real number onto $[0,1]$.
--
--   **Formalization Note** It only gives the probabilities of the families $G_N$ and $H_D$ the type of a probability. Under the data of (7.1) those values already lie in $[0,1]$, so it changes nothing where it is used.
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, §7, pp.15–16

import Mathlib

namespace StochAutoreg

/-- The real number `r` projected into `[0,1]`.

**Formalization Note.** Used only to give the probabilities of the families of Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, §7, pp.15–16, the type
`unitInterval`. Under `StochAutoreg.AmpData` every such value lies in `[0,1]` already (verification file),
so the projection changes nothing where it is used. -/
noncomputable def clampI (r : ℝ) : unitInterval := Set.projIcc (0 : ℝ) 1 zero_le_one r

end StochAutoreg


