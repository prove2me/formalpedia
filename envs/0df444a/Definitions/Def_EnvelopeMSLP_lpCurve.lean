-- Prove2me | Definitions.Def_EnvelopeMSLP_lpCurve
-- name    : EnvelopeMSLP_lpCurve
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:26:50.491235+00:00
-- url     : https://prove2.me/theorems/80b1f612-2af0-4310-9217-676410727804
-- title:
--   The data curve $\theta\mapsto\mathcal D(\theta)$
-- statement:
--   For parametrized data, the curve $\mathcal D(\theta)=(A(\theta),b(\theta),c(\theta))$ in $\mathbb R^N$.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), proof of Theorem 2, p.10

import Mathlib
import Definitions.Def_EnvelopeMSLP_lpData
open Matrix

namespace EnvelopeMSLP

/-- **The data curve `θ ↦ D(θ)`.** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), proof of Theorem 2, p.10: `D(θ) = (A(θ), b(θ), c(θ))`. -/
def lpCurve {m n : ℕ} (A : ℝ → Matrix (Fin m) (Fin n) ℝ) (b : ℝ → Fin m → ℝ) (c : ℝ → Fin n → ℝ) :
    ℝ → LPIndex m n → ℝ :=
  fun θ => lpData (A θ) (b θ) (c θ)

end EnvelopeMSLP


