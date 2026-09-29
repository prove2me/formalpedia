-- Prove2me | Definitions.Def_OpenGA_SurgeryVolumeProfile
-- name    : OpenGA_SurgeryVolumeProfile
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-10T18:31:24.355334+00:00
-- url     : https://prove2.me/theorems/35bfeea1-d648-484f-a169-c765a3de7342
-- title:
--   Volume bookkeeping across the surgeries of a Ricci flow with surgery
-- statement:
--   A Ricci flow with surgery on a compact time interval $[a,b]$ carries two volume functions: $V^-(t)=\mathrm{vol}(M_t^-)$, the volume of the backward (pre-surgery) time slice, and $V^+(t)=\mathrm{vol}(M_t^+)$, the volume of the forward (post-surgery) time slice. A *surgery volume profile* on $[a,b]$ records these two functions, a set $S\subseteq(a,b]$ of surgery times, a growth rate $C\ge 0$ and a surgery scale $h>0$, subject to two inequalities.
--
--   1. **Growth along the flow.** For all $a\le s<t\le b$,
--   $$V^-(t)\;\le\;V^+(s)\,e^{C\,(t-s)}.$$
--   This is the volume growth estimate: a lower bound $R\ge -C$ for the scalar curvature on the interval gives $\frac{d}{dt}\mathrm{vol}=-\int_M R\,dV\le C\,\mathrm{vol}$ between surgery times, while a surgery only removes volume.
--
--   2. **Loss at a surgery.** For every $t\in S$,
--   $$V^+(t)+h^3\;\le\;V^-(t).$$
--   This is Kleiner–Lott's Remark 73.5: for sufficiently small $\delta$ one has $\mathrm{vol}(M_t^+)<\mathrm{vol}(M_t^-)-h(t)^3$ at each surgery time, because each discarded component contains at least half of a $\delta$-neck, whose volume is at least $\mathrm{const.}\,\delta^{-1}h(t)^3$, while the cap added has volume $O(h(t)^3)$. Here $h$ is a positive lower bound for the surgery scale on $[a,b]$.
--
--   The record also fixes the discounted volume $U(t)=V^+(t)e^{-C(t-a)}$ and the quantity $q=h^3e^{-C(b-a)}$ by which each surgery decreases it. Together these are the "volume considerations" that Kleiner–Lott invoke on p. 147 to rule out an accumulation of surgery times.
--
--   **Formalization note.** No geometric meaning is imposed on the two volume functions: the record is bookkeeping data extracted from a flow, and is not itself a definition of Ricci flow with surgery. The hypotheses are consistent, and consistent with a nonempty set of surgery times.
-- source:
--   Kleiner-Lott, Notes on Perelman's papers, https://arxiv.org/abs/math/0605667, Remark 73.5 (p. 140) and Section 77, p. 147 ("volume considerations rule out an accumulation of surgery times")

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Set.Basic

/-!
# Volume bookkeeping across the surgeries of a Ricci flow with surgery

Kleiner-Lott, *Notes on Perelman's papers*, https://arxiv.org/abs/math/0605667:
Remark 73.5 (p. 140) and the sentence on p. 147 that "volume considerations rule out
an accumulation of surgery times".

A `SurgeryVolumeProfile a b` records, for a Ricci flow with surgery defined on the
compact time interval `[a, b]`, the two volume functions

* `volBefore t = vol (M_t^-)`, the volume of the backward (pre-surgery) time slice, and
* `volAfter t = vol (M_t^+)`, the volume of the forward (post-surgery) time slice,

together with the two inequalities that the surgery process provides:

* volume grows at most exponentially along the flow, `vol (M_t^-) ≤ vol (M_s^+) e^{C (t-s)}`
  for `s < t`, which follows from a lower bound `R ≥ -C` for the scalar curvature on the
  interval through `d/dt vol = - ∫ R`, together with the fact that surgeries only remove
  volume; and
* each surgery destroys at least `h ^ 3` of volume, `vol (M_t^+) + h ^ 3 ≤ vol (M_t^-)`,
  which is Remark 73.5, `h` being a lower bound for the surgery scale on `[a, b]`.

No geometric interpretation of the two volume functions is imposed here: this file
records the bookkeeping that the finiteness argument uses, not the metric surgery
construction that produces it.
-/

set_option autoImplicit false

open Set

namespace OpenGA

/-- **Math.** Volume bookkeeping for a Ricci flow with surgery on a compact time
interval `[a, b]`: the pre- and post-surgery volumes of the time slices, an exponential
bound on volume growth along the flow, and a definite volume loss at each surgery. -/
structure SurgeryVolumeProfile (a b : ℝ) where
  /-- The volume of the backward (pre-surgery) time slice. -/
  volBefore : ℝ → ℝ
  /-- The volume of the forward (post-surgery) time slice. -/
  volAfter : ℝ → ℝ
  /-- The set of surgery times. -/
  surgeryTimes : Set ℝ
  /-- Surgeries occur inside the interval. -/
  surgeryTimes_subset : surgeryTimes ⊆ Ioc a b
  /-- The exponential rate controlling volume growth along the flow. -/
  growthRate : ℝ
  growthRate_nonneg : 0 ≤ growthRate
  /-- A positive lower bound for the surgery scale `h` on `[a, b]`. -/
  surgeryScale : ℝ
  surgeryScale_pos : 0 < surgeryScale
  /-- Volumes of forward time slices are nonnegative. -/
  volAfter_nonneg : ∀ t ∈ Icc a b, 0 ≤ volAfter t
  /-- Volume grows at most exponentially along the flow. -/
  growth : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s < t →
      volBefore t ≤ volAfter s * Real.exp (growthRate * (t - s))
  /-- Each surgery destroys at least `surgeryScale ^ 3` of volume. -/
  drop : ∀ t ∈ surgeryTimes, volAfter t + surgeryScale ^ 3 ≤ volBefore t

namespace SurgeryVolumeProfile

variable {a b : ℝ} (P : SurgeryVolumeProfile a b)

/-- The volume of the forward time slice, discounted by the exponential growth factor. -/
noncomputable def discounted (t : ℝ) : ℝ :=
  P.volAfter t * Real.exp (-(P.growthRate * (t - a)))

/-- The amount by which each surgery decreases the discounted volume. -/
noncomputable def quantum : ℝ :=
  P.surgeryScale ^ 3 * Real.exp (-(P.growthRate * (b - a)))

lemma quantum_pos : 0 < P.quantum :=
  mul_pos (pow_pos P.surgeryScale_pos 3) (Real.exp_pos _)

end SurgeryVolumeProfile

end OpenGA


