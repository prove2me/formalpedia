-- Prove2me | Definitions.Def_GeoRobustLearn_DangerInterval
-- name    : GeoRobustLearn_DangerInterval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:08:18.130436+00:00
-- url     : https://prove2.me/theorems/984a51df-a6e9-4e0e-9436-3acb674a75ea
-- title:
--   Clipped prediction $\bar p$, danger interval $I_r(x)$, threshold rules and the six rounding events
-- statement:
--   Let $P:\mathbb R^{d+1}\to\mathbb R$ (in the paper, the smoothed polynomial returned by the learning step). Define
--
--   $$\bar p(x)=\max\{0,\min\{1,P(x,0)\}\},\qquad I_r(x)=[P(x,-r)-r,\ P(x,r)+r]\cap[0,1],$$
--
--   an interval with reversed endpoints being empty. For a threshold $\theta$, $g_\theta(x)=\mathbf 1\{\bar p(x)\ge\theta\}$ (Algorithm 3) and $g_i(x)=\mathbf 1\{P(x,0)\ge\theta_i\}$ (Algorithm 4). For thresholds $\theta_1,\theta_2,\theta_3$ the error and danger events are
--
--   $$E_i=\{(x,y):g_i(x)\ne y\},\qquad C_i=\{(x,y):\theta_i\in I_r(x)\},$$
--
--   and $(F_1,\dots,F_6)=(E_1,E_2,E_3,C_1,C_2,C_3)$.
--
--   These quantities connect the polynomial's certificates to the error and boundary volume of a rounded classifier.
--
--   **Formalization Note** $|I_r(x)|$ is the Lebesgue measure of $I_r(x)$; thresholds are indexed by `Fin 3`.
-- source:
--   Lange, Marcussen, Vasilyan, Geometrically Constrained Learning I: Agnostically Learning Adversarially Robust Classifiers, manuscript (Nov. 3, 2026; sha256 8cbf3f52…), §6, p.31; Algorithm 3, p.32; Algorithm 4, p.36

import Definitions.Def_GeoRobustLearn_OffsetLift

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GeoRobustLearn

open GeoLipLearn.Agnostic

/-!
# Clipped prediction, danger interval, threshold rules and the six rounding events

Lange, Marcussen, Vasilyan, *Geometrically Constrained Learning I*, manuscript of November 3, 2026
(sha256 8cbf3f52…): §6 (p.31), Algorithm 3 (p.32), Algorithm 4 (p.36).

**Formalization Note.** `P : Space (d+1) → ℝ` is any function (the paper's smoothed polynomial);
`P(x, a)` is `P (lift x a)`. The danger interval is a subset of `ℝ`; a closed interval with reversed
endpoints is empty, as Algorithm 3 prescribes, and its length is its Lebesgue measure.
-/

/-- `p̄(x) = max{0, min{1, P(x, 0)}}` (p.31, Algorithm 3 line 1). -/
noncomputable def pbar {d : ℕ} (P : Space (d+1) → ℝ) (x : Space d) : ℝ :=
  max 0 (min 1 (P (lift x 0)))

/-- The danger interval `I_r(x) = [P(x, −r) − r, P(x, r) + r] ∩ [0, 1]` (Lemma 6.2, p.31). -/
def dangerInterval {d : ℕ} (P : Space (d+1) → ℝ) (r : ℝ) (x : Space d) : Set ℝ :=
  Set.Icc (P (lift x (-r)) - r) (P (lift x r) + r) ∩ Set.Icc 0 1

/-- `g_θ(x) = 1{p̄(x) ≥ θ}` (Algorithm 3, line 2). -/
noncomputable def clipThreshold {d : ℕ} (P : Space (d+1) → ℝ) (θ : ℝ) (x : Space d) : ℝ :=
  if θ ≤ pbar P x then 1 else 0

/-- `g_i(x) = 1{P(x, 0) ≥ θ_i}` (Algorithm 4, line 1; Algorithm 2, line 6). -/
noncomputable def polyThreshold {d : ℕ} (P : Space (d+1) → ℝ) (θ : ℝ) (x : Space d) : ℝ :=
  if θ ≤ P (lift x 0) then 1 else 0

/-- The error event `E_i = {(x, y) : g_i(x) ≠ y}` (Algorithm 4, line 2). -/
def errEvent {d : ℕ} (P : Space (d+1) → ℝ) (θ : ℝ) : Set (Space d × ℝ) :=
  {z | polyThreshold P θ z.1 ≠ z.2}

/-- The danger event `C_i = {(x, y) : θ_i ∈ I_r(x)}` (Algorithm 4, line 2). -/
def dangerEvent {d : ℕ} (P : Space (d+1) → ℝ) (r θ : ℝ) : Set (Space d × ℝ) :=
  {z | θ ∈ dangerInterval P r z.1}

/-- `(F_1, …, F_6) = (E_1, E_2, E_3, C_1, C_2, C_3)` (Algorithm 4, line 2). -/
def sixEvents {d : ℕ} (P : Space (d+1) → ℝ) (r : ℝ) (θ : Fin 3 → ℝ) (j : Fin 6) :
    Set (Space d × ℝ) :=
  if h : j.val < 3 then errEvent P (θ ⟨j.val, h⟩)
  else dangerEvent P r (θ ⟨j.val - 3, by omega⟩)

end GeoRobustLearn


