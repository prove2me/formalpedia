-- Prove2me | Definitions.Def_OfflineToOnline_seedLaw
-- name    : OfflineToOnline_seedLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:33:29.44382+00:00
-- url     : https://prove2.me/theorems/388d4aca-d4f0-47e0-a989-8b53098b46e7
-- title:
--   Law of the seeds of $T$ runs of $N$ subproblems
-- statement:
--   Let $\nu$ be the law of the random seed that drives one call of $\textsc{Local-update}$. The seeds $(\omega_{t,i})_{t\le T,\,i\le N}$ of $T$ runs of $N$ subproblems are independent with law $\nu$ each, so their joint law is the product measure
--
--   $$
--   \nu^{\otimes(T\times N)}\quad\text{on}\quad\Omega^{T\times N}.
--   $$
--
--   Expectations $\mathbb E[f_t(z_t)]$ in Definition 6 and Theorem 2 are taken under this law.
-- source:
--   Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, Online Learning via Offline Greedy Algorithms: Applications in Market Design and Optimization, arXiv:2102.11050v4, Algorithm 1, p.14; Definition 6, p.16

import Mathlib

namespace OfflineToOnline

/-- The law of the seeds of `T` runs of `N` subproblems: independent seeds, each with law `ν`, so
the product measure `ν^{⊗ T × N}` on `Fin T → Fin N → Ω`. This is the randomness of Local-update
over which `E[f_t(z_t)]` is taken in Definition 6, p.16, and Theorem 2, p.20.

Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, arXiv:2102.11050v4, Algorithm 1, p.14 ("we allow Local-update : Θ × D → Δ(C) to incorporate randomness");
Definition 6, p.16. -/
noncomputable def seedLaw {Ω : Type*} [MeasurableSpace Ω] (ν : MeasureTheory.Measure Ω)
    [MeasureTheory.SigmaFinite ν] (T N : ℕ) : MeasureTheory.Measure (Fin T → Fin N → Ω) :=
  MeasureTheory.Measure.pi (fun _ : Fin T => MeasureTheory.Measure.pi (fun _ : Fin N => ν))

end OfflineToOnline


