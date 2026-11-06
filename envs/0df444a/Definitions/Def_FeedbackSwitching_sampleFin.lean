-- Prove2me | Definitions.Def_FeedbackSwitching_sampleFin
-- name    : FeedbackSwitching_sampleFin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:38:19.526901+00:00
-- url     : https://prove2.me/theorems/c394dc5c-1ab9-4dfb-9225-3c98795a99df
-- title:
--   Inverse-CDF draws from a finite law, and i.i.d. uniform coins
-- statement:
--   Every random draw of the mission's algorithms is made from one fresh coin $u$ uniform on $[0,1]$: the draw from a probability vector $v$ on $\{0,\dots,n-1\}$ is the least $i$ with $u<\sum_{j\le i}v_j$. This equals $i$ exactly when $u\in[\sum_{j<i}v_j,\sum_{j\le i}v_j)$, an interval of length $v_i$, so the draw has law $v$.
--
--   The coin space of the algorithms is the space of sequences in $[0,1]$ with the product of Lebesgue measures (i.i.d. uniform coins).
--
--   **Formalization Note** If no index qualifies (only for $u\ge\sum_jv_j$, a null event) the draw is $0$.
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), conventions of Algorithms 1, 2, 4 ("draw", "with probability"), pp.18, 22, 35 (PDF pp.20, 24, 37)

import Mathlib

open MeasureTheory
open scoped Classical

namespace FeedbackSwitching

/-- Cesa-Bianchi et al., arXiv:2606.03851 (held version, sha256 ded8f8bc…).

**Inverse-CDF draw** from a finite law: `sampleFin v u` is the least `i` with
`u < ∑_{j ≤ i} v_j` (`0` if there is none). For a probability vector `v` and `u` uniform on
`[0, 1]`, `sampleFin v u = i` with probability `v i` (proved in
`Solutions/verification/FeedbackSwitching_sampleFin.lean`). Every random draw of the mission's
algorithms ("draw `X ∼ p`", "with probability …") is made this way from one fresh uniform coin. -/
noncomputable def sampleFin {n : ℕ} [NeZero n] (v : Fin n → ℝ) (u : ℝ) : Fin n :=
  if h : (Finset.univ.filter (fun i : Fin n => u < ∑ j ∈ Finset.Iic i, v j)).Nonempty then
    (Finset.univ.filter (fun i : Fin n => u < ∑ j ∈ Finset.Iic i, v j)).min' h
  else 0

/-- The coin space of the mission's algorithms: a sequence of coins in `[0, 1]`. -/
abbrev Coins : Type := ℕ → unitInterval

/-- The law of the coins: i.i.d. uniform on `[0, 1]` (the product of Lebesgue measure on the unit
interval). -/
noncomputable def coinLaw : Measure Coins :=
  Measure.infinitePi (fun _ : ℕ => (volume : Measure unitInterval))

instance : IsProbabilityMeasure coinLaw := by
  unfold coinLaw; infer_instance

end FeedbackSwitching


