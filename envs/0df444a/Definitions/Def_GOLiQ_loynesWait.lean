-- Prove2me | Definitions.Def_GOLiQ_loynesWait
-- name    : GOLiQ_loynesWait
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:50:21.615599+00:00
-- url     : https://prove2.me/theorems/f0e6d89e-17fd-4168-b5e8-5232a7207800
-- title:
--   Loynes' stationary waiting time $\sup_{n\ge0}\sum_{j\le n}(s_j-\tau_j)$
-- statement:
--   For service times $s_j$ and interarrival times $\tau_j$ read backwards from a customer at time $0$ ($s_j$ is the service time of customer $-j$, $\tau_j$ the time between the arrivals of customers $-j$ and $-j+1$), the waiting time of customer $0$ in a queue that has run forever is
--   $$W_\infty=\sup_{n\ge0}\sum_{j=1}^n (s_j-\tau_j).$$
--   For i.i.d. inputs with negative drift this supremum is finite almost surely and has the steady-state law of the waiting time (Loynes). It realizes the steady-state waiting time on the same primitives as the transient queue, which is the coupling from the past used in the proof of Lemma 4.
--
--   **Formalization Note** The supremum is taken in $[0,\infty]$ and returned as a real number; the value $+\infty$, which has probability $0$ for a stable queue, becomes the junk value $0$.
-- source:
--   Chen, Liu, Hong, An Online Learning Approach to Dynamic Pricing and Capacity Sizing in Service Systems, arXiv:2009.02911v3, proof of Lemma 4, p.58 (coupling from the past)

import Mathlib

namespace GOLiQ

/-- **Loynes' stationary waiting time** (coupling from the past; Chen, Liu, Hong,
arXiv:2009.02911v3, proof of Lemma 4, p.58: `Yₙ = Σ_{j=1}^n (Vⱼ/µ − Uⱼ/λ(p))`, "a random walk with
negative drift").

For service times `sⱼ` and interarrival times `τⱼ` read backwards from the customer at time `0`
(`sⱼ` is the service time of customer `−j`, `τⱼ` the time between the arrivals of customers `−j`
and `−j + 1`), the waiting time of customer `0` in the queue that has run forever is

`W∞ = sup_{n ≥ 0} Σ_{j=1}^n (sⱼ − τⱼ)`.

**Formalization Note.** The supremum is taken in `[0, ∞]` (the `n = 0` term is `0`) and returned
as a real number; the value `+∞` (which has probability `0` for a stable queue) is returned as the
junk value `0`. -/
noncomputable def loynesWait (s τ : ℕ → ℝ) : ℝ :=
  (⨆ n : ℕ, ENNReal.ofReal (∑ j ∈ Finset.Icc 1 n, (s j - τ j))).toReal

end GOLiQ


