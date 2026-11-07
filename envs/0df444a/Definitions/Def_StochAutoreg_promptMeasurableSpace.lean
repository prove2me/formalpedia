-- Prove2me | Definitions.Def_StochAutoreg_promptMeasurableSpace
-- name    : StochAutoreg_promptMeasurableSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:11:50.470973+00:00
-- url     : https://prove2.me/theorems/366f7261-05b6-4343-8641-9fbca025e5bb
-- title:
--   Discrete $\sigma$-algebra on the prompts
-- statement:
--   The discrete $\sigma$-algebra on the countable set $\Sigma^\star$ of prompts, so that the sample spaces carry measures.
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, §1.1, p.3

import Mathlib

namespace StochAutoreg

/-- The discrete σ-algebra on the countable set `Σ⋆` of prompts, so that the sample spaces of the paper
carry measures. Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, §1.1, p.3 ("A learner is a total measurable map on finite samples and random
seeds"). -/
instance promptMeasurableSpace : MeasurableSpace (List Bool) := ⊤

instance : DiscreteMeasurableSpace (List Bool) := ⟨fun _ => trivial⟩

end StochAutoreg


