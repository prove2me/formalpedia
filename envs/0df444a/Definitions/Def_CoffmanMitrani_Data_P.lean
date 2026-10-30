-- Prove2me | Definitions.Def_CoffmanMitrani_Data_P
-- name    : CoffmanMitrani_Data_P
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:04:18.279711+00:00
-- url     : https://prove2.me/theorems/f55e69b8-c2af-4e89-9a52-eb5ddcc0b8e7
-- title:
--   Probability law of the multiclass M/M/1 model
-- statement:
--   Under the law $P$ all coordinates of the sample space are independent; the interarrival times of class $i$ are exponential with rate $\lambda_i$, so that class-$i$ jobs arrive in a Poisson stream of rate $\lambda_i$ started at time $0$; the service requirements of class $i$ are exponential with parameter $\mu_i$; and every seed is uniform on $[0,1]$. The system is empty at time $0$.
--
--   This is the paper's model: Poisson arrival streams and exponential service times, with "the arrival and service processes for all job classes … mutually independent".
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 811; p. 814 (systems start idle at t = 0)

import Mathlib
import Definitions.Def_CoffmanMitrani_Data
import Definitions.Def_CoffmanMitrani_Omega
open MeasureTheory ProbabilityTheory

namespace CoffmanMitrani

/-- **The probability law of the model.**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §1, p. 811: Poisson arrivals at rate `λi`, exponential service times with parameter `μi`,
"The arrival and service processes for all job classes are mutually independent."

`D.P` is the product measure on `Omega D.M` under which all coordinates are independent, the
interarrival times of class `i` are exponential with rate `λi` (so class-`i` arrivals form a Poisson
process of rate `λi` started at time `0`), the service requirements of class `i` are exponential
with rate `μi`, and all seeds are uniform on `[0, 1]`.

**Formalization Note.** Built from `Measure.infinitePi` and Mathlib's `expMeasure`. The system is
empty at time `0` (p. 814: "Assume that all these systems start in the idle state at t = 0"). -/
noncomputable def Data.P (D : Data) : Measure (Omega D.M) :=
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.lam j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.lam_pos j.1)
  haveI : ∀ j : Job D.M, IsProbabilityMeasure (expMeasure (D.mu j.1)) :=
    fun j => isProbabilityMeasure_expMeasure (D.mu_pos j.1)
  (Measure.infinitePi fun j : Job D.M => expMeasure (D.lam j.1)).prod
    ((Measure.infinitePi fun j : Job D.M => expMeasure (D.mu j.1)).prod
      (Measure.infinitePi fun _ : Job D.M =>
        Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval)))

end CoffmanMitrani


