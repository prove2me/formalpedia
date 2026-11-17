-- Prove2me | Definitions.Def_OmniMix_Supplement_alg1Reward
-- name    : OmniMix_Supplement_alg1Reward
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:33:57.109562+00:00
-- url     : https://prove2.me/theorems/260a2922-2156-4478-a1fb-daae557260fd
-- title:
--   Expert reward $z_{t,f,v}$ of Algorithm 1
-- statement:
--   In Algorithm 1 each expert is a pair $(f,v)$ of a benchmark $f\in F$ and a threshold $v\in[0,1]$. Its **reward** in round $t$ is
--   $$
--   z_{t,f,v}=\mathbb E_{P\sim D_t}\big[b_v(P,f(x_t))\,(y_t-P)\big],\qquad b_v(p,q)=\mathbb 1\{p<v\le q\}-\mathbb 1\{q<v\le p\},
--   $$
--   where $D_t$ is the round-$t$ forecast, a probability measure on $[0,1]$.
--
--   **Formalization Note** The expectation is an integral against an arbitrary probability measure; the integrand is bounded by $1$ and Borel in $P$.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, Algorithm 1, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_OmniMix_bV
import Definitions.Def_OmniMix_outVal

namespace OmniMix.Supplement

open OmniMix

/-- **Expert reward `z_{t,f,v}` of Algorithm 1.** Liu–Luo–Ratliff, *Omniprediction for All Mixable
Proper Losses and Beyond*, arXiv:2610.41023, Algorithm 1, p.11: "For every expert
`(f, v) ∈ F × [0, 1]`, define its reward as `z_{t,f,v} = E_{P∼D_t}[b_v(P, f(x_t))(y_t − P)]`".

**Formalization Note.** The forecasts `D_t` are arbitrary probability measures on `[0,1]` (the EVI
solver of Algorithm 1 returns "a distribution `D_t` over `[0, 1]`"), so the expectation is an
integral; the integrand is bounded by `1` and Borel in `P`. `b_v` is the base `OmniMix.bV`. -/
noncomputable def alg1Reward {X : Type*} {T : ℕ} (x : Fin T → X) (y : Fin T → Bool)
    (D : Fin T → MeasureTheory.ProbabilityMeasure unitInterval) (t : Fin T)
    (f : X → unitInterval) (v : ℝ) : ℝ :=
  ∫ P, bV v P (f (x t)) * (outVal (y t) - P) ∂(D t : MeasureTheory.Measure unitInterval)

end OmniMix.Supplement


