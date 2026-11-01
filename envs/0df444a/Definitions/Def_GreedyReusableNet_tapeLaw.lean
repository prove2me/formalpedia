-- Prove2me | Definitions.Def_GreedyReusableNet_tapeLaw
-- name    : GreedyReusableNet_tapeLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:33:00.655059+00:00
-- url     : https://prove2.me/theorems/d1904fb8-6721-4649-b75a-62495e28debd
-- title:
--   Law of the random seeds (the tape)
-- statement:
--   All randomness of the process is generated from independent seeds uniform on $[0,1]$: in each period $t<T$, one seed $u$ for the policy's own randomization (including any oracle it calls), one seed for the activation draw, and one seed $U_{t,i}$ per arm for its blocking time. The **tape** is the collection of these seeds over the horizon; its law is the product of uniform laws.
--
--   Blocking times are realized as $F_i^{-1}(U_{t,i};n)$, as in the queue coupling of §3.2, so the same seeds serve both for the policy's own run and for the coupled run of the proof.
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, §2.1, Algorithm 1 steps 3 and 6, pp.8–9; §3.2, Queue Coupling, p.20

import Mathlib

open MeasureTheory

namespace GreedyReusableNet

/-- The uniform distribution on `[0, 1]`, the law of every random seed. -/
noncomputable def unif : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

/-- **The random seeds of one period**: a seed for the policy's own randomization (including any
oracle it calls), a seed for the activation draw, and one seed `U_{t,i}` per arm for the time
`b_{t,i}` it stays blocked (Simchi-Levi, Zheng & Zhu, SSRN 3981123, Algorithm 1 steps 3 and 6, pp.8–9; §3.2, "Queue
Coupling", p.20: "we generate an independent uniform sample `U_{t,i} ∼ U[0,1]` for any `i ∈ B`"). -/
abbrev Noise (N : ℕ) := ℝ × ℝ × (Fin N → ℝ)

/-- **A tape**: the seeds of the periods `0, …, T - 1`. -/
abbrev Tape (N T : ℕ) := Fin T → Noise N

/-- The law of one period's seeds: all `N + 2` seeds independent and uniform on `[0, 1]`. -/
noncomputable def noiseLaw (N : ℕ) : Measure (Noise N) :=
  unif.prod (unif.prod (Measure.pi fun _ : Fin N => unif))

/-- **The law of the tape** (SSRN 3981123, §2.1 and §3.2, pp.8–11, 20): the periods' seeds are
independent, each with law `noiseLaw N`; every random choice of the process is a fixed
measurable function of these seeds.

**Formalization Note** Periods are 0-based, `Fin T` = `{0, …, T-1}` for the paper's
`t = 1, …, T`. -/
noncomputable def tapeLaw (N T : ℕ) : Measure (Tape N T) :=
  Measure.pi fun _ : Fin T => noiseLaw N

end GreedyReusableNet


