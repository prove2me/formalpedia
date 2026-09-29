-- Prove2me | Definitions.Def_OpenGA_SurgeryContinuationData
-- name    : OpenGA_SurgeryContinuationData
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-10T18:31:25.067901+00:00
-- url     : https://prove2.me/theorems/801b0535-7bbc-44eb-a7ac-fa4118ff0e8b
-- title:
--   The continuation mechanism of a Ricci flow with surgery
-- statement:
--   Fix a normalized initial condition and positive nonincreasing parameters $r,\delta$. Kleiner–Lott describe the time domain of the resulting Ricci flow with $(r,\delta)$-cutoff through two continuation mechanisms (p. 147, and Lemma 73.7 on p. 140). A *surgery continuation datum* records that time domain abstractly: a predicate $\mathrm{Def}(T)$, read as "the flow with surgery is defined on all of $[0,T]$" (empty time slices being allowed), a set $S$ of surgery times, and the following properties.
--
--   1. $\mathrm{Def}(0)$ holds, and $\mathrm{Def}$ is downward closed: $0\le S\le T$ and $\mathrm{Def}(T)$ imply $\mathrm{Def}(S)$.
--
--   2. **Prolongation.** For every $T\ge 0$ with $\mathrm{Def}(T)$ there is $T'>T$ with $\mathrm{Def}(T')$. This is the mechanism of Lemma 73.7: the $r$-canonical neighbourhood assumption lets one run the flow forward to the next singular time and perform surgery there.
--
--   3. **No accumulation.** If $T>0$, if $\mathrm{Def}(S)$ holds for every $0\le S<T$, and if the set of surgery times $\le T$ is finite, then $\mathrm{Def}(T)$ holds.
--
--   This is the interface on which the all-time existence argument of Section 77 operates. Unlike the earlier record `OpenGA.CutoffSurgeryProcess`, no volume-loss budget is bundled here: the finiteness required by (3) is left to be supplied separately, for instance by a surgery volume profile on each finite horizon. Consequently a datum of this kind is allowed to have infinitely many surgery times, as long as they do not accumulate.
--
--   **Formalization note.** The metric surgery construction, and the derivation of such a record from a closed Riemannian three-manifold with normalized metric, are geometric inputs that this interface does not perform.
-- source:
--   Kleiner-Lott, Notes on Perelman's papers, https://arxiv.org/abs/math/0605667, Lemma 73.7 (p. 140) and Section 77, p. 147

import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Set.Basic

/-!
# The continuation mechanism of a Ricci flow with surgery

Kleiner-Lott, *Notes on Perelman's papers*, https://arxiv.org/abs/math/0605667:
Lemma 73.7 (prolongation of Ricci flows with cutoff, p. 140) and the description of
all-time existence on p. 147.

A `SurgeryContinuationData` records the time domain of a Ricci flow with surgery
started from a fixed initial condition, through the predicate `DefinedUpTo T`, read as
"the flow with surgery is defined on all of `[0, T]`" (empty time slices are allowed),
together with the two continuation mechanisms of p. 147:

* `extend_forward`: the `r`-canonical neighbourhood assumption lets one run the flow
  forward past any time already reached, performing surgery at the next singular time;
* `extend_limit`: a time reached only as a limit is itself attained, provided that only
  finitely many surgeries occur up to it.

Unlike `OpenGA.CutoffSurgeryProcess`, no volume-loss budget is bundled here: the
finiteness needed by `extend_limit` is left to be supplied, for instance by
`OpenGA.SurgeryVolumeProfile`. The metric surgery construction, and the derivation of
such a record from a normalized closed Riemannian three-manifold, are geometric tasks
that this interface does not perform.
-/

set_option autoImplicit false

open Set

namespace OpenGA

/-- **Math.** The time domain of a Ricci flow with surgery, recorded through its two
continuation mechanisms. -/
structure SurgeryContinuationData where
  /-- `DefinedUpTo T`: the flow with surgery is defined on all of `[0, T]`. -/
  DefinedUpTo : ℝ → Prop
  /-- The initial condition is a time slice of the flow. -/
  definedUpTo_zero : DefinedUpTo 0
  /-- A flow defined on `[0, T]` is defined on every `[0, S]` with `0 ≤ S ≤ T`. -/
  definedUpTo_mono : ∀ ⦃S T : ℝ⦄, 0 ≤ S → S ≤ T → DefinedUpTo T → DefinedUpTo S
  /-- The surgery times of the flow. -/
  surgeryTimes : Set ℝ
  /-- Prolongation: the flow runs forward past any time it reaches. -/
  extend_forward : ∀ T : ℝ, 0 ≤ T → DefinedUpTo T → ∃ T' : ℝ, T < T' ∧ DefinedUpTo T'
  /-- No accumulation: a time reached only as a limit is attained, provided only
  finitely many surgeries occur up to it. -/
  extend_limit : ∀ T : ℝ, 0 < T → (∀ S : ℝ, 0 ≤ S → S < T → DefinedUpTo S) →
    (surgeryTimes ∩ Iic T).Finite → DefinedUpTo T

end OpenGA


