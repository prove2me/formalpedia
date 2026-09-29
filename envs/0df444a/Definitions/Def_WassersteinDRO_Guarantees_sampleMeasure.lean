-- Prove2me | Definitions.Def_WassersteinDRO_Guarantees_sampleMeasure
-- name    : WassersteinDRO_Guarantees_sampleMeasure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:34:05.990708+00:00
-- url     : https://prove2.me/theorems/49db3a0a-276c-43b4-94c0-bd899c558083
-- title:
--   Law of $N$ iid training samples, $P^N$
-- statement:
--   $P^N$ is the law of $N$ independent, identically distributed training samples
--   $(\hat\xi_1,\dots,\hat\xi_N)$, each drawn from $P$: the product probability measure on
--   $(\mathbb{R}^m)^N$ with all $N$ marginals equal to $P$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, notation used throughout Section 3, e.g. Theorem 18, p. 22

import Mathlib

open MeasureTheory

namespace WassersteinDRO.Guarantees

/-- The law `P^N` of `N` iid training samples drawn from `P`, Kuhn et al. 2019, notation used
throughout Section 3 (e.g. Theorem 18, p. 22): the probability that an event holds for the
random sample sequence `(ξ̂_1,…,ξ̂_N)`, each `ξ̂_i` iid `~ P`, is computed under the product
measure on `Fin N → ℝ^m`. -/
noncomputable def sampleMeasure {m : ℕ} (P : Measure (EuclideanSpace ℝ (Fin m))) (N : ℕ) :
    Measure (Fin N → EuclideanSpace ℝ (Fin m)) :=
  Measure.pi (fun _ : Fin N => P)

end WassersteinDRO.Guarantees


