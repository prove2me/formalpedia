-- Prove2me | Definitions.Def_RankingQueryCost_Joint_Correction
-- name    : RankingQueryCost_Joint_Correction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T13:26:59.677187+00:00
-- url     : https://prove2.me/theorems/bcb3cb6f-d0b7-4ec1-a78e-9e560a05a3c5
-- title:
--   Warm-order correction, projection, and its two error terms
-- statement:
--   Fix a warm rank permutation $\pi$, a transcript $T$ and an inclusion mask $I$. Orient each incidence vector $x_e$ from lower to higher warm rank. Let $a_e$ and $y_e$ be the true and observed inversion indicators, and put $w_e=I_e/p$. The correction and its two error terms are computed as
--
--   $$\widetilde q=\pi+\sum_ew_ey_ex_e,\quad q=\operatorname{Proj}_Q(\widetilde q),\quad Z=\sum_e(w_e-1)a_ex_e,\quad F_{\rm err}=\sum_ew_e(y_e-a_e)x_e.$$
--
--   Projection selects an actual minimum of squared distance on $Q$; it is not an arbitrary vector constrained by a desired error conclusion. For the source's admissible domain, compactness and nonemptiness of $Q$ ensure that its minimizer branch exists. This module supplies the objects in the adaptive correction decomposition.
--
--   **Formalization Note** A missing observed answer has inversion indicator zero, irrelevant to an unselected pair; actual acquisitions supply every selected answer. Projection has an explicit fallback for inputs without a minimizer, outside the valid compact setting.
-- source:
--   Chaoqiang Fu, Yifan Su, Daofeng Li, STOC 2027 submission #812 (October 2026), §6.2, equations (26)–(27), p. 29, PDF p. 30; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/812.pdf

import Definitions.Def_RankingQueryCost_Joint_Pivot
import Definitions.Def_RankingQueryCost_Joint_Flow

set_option autoImplicit false

noncomputable section

namespace RankingQueryCost.Joint

attribute [local instance] Classical.propDecidable

/-- A genuine nearest-point selection on Q; the alternative is only for degenerate inputs.
For the source domain n≥16, Q is nonempty compact, so the minimizer branch always applies. -/
def projectEstimate {n : ℕ} (z : Fin n → ℝ) : Fin n → ℝ :=
  if h : ∃ q ∈ estimateSet n, ∀ y ∈ estimateSet n, squaredError q z ≤ squaredError y z then
    Classical.choose h
  else fallback n

/-- The incidence orientation used by the warm rank permutation, from low to high. -/
def warmIncidence {n : ℕ} (π : Rank n) (e : Pair n) (i : Fin n) : ℝ :=
  if π e.1.1 < π e.1.2 then incidence e i else -incidence e i

def trueInversion {n : ℕ} (r π : Rank n) (e : Pair n) : ℝ :=
  if truthful r e = truthful π e then 0 else 1

def observedInversion {n : ℕ} (π : Rank n) (T : Transcript n) (e : Pair n) : ℝ :=
  match T e with
  | none => 0
  | some b => if b = truthful π e then 0 else 1

def inclusionWeight {n : ℕ} (p : ℝ) (mask : Pair n → Bool) (e : Pair n) : ℝ :=
  if mask e then 1 / p else 0

def correctedScore {n : ℕ} (π : Rank n) (T : Transcript n) (p : ℝ)
    (mask : Pair n → Bool) : Fin n → ℝ := fun i =>
  rankVector π i + ∑ e, inclusionWeight p mask e * observedInversion π T e * warmIncidence π e i

def correctedEstimate {n : ℕ} (π : Rank n) (T : Transcript n) (p : ℝ)
    (mask : Pair n → Bool) : Fin n → ℝ := projectEstimate (correctedScore π T p mask)

def samplingNoise {n : ℕ} (r π : Rank n) (p : ℝ) (mask : Pair n → Bool) : Fin n → ℝ :=
  fun i => ∑ e, (inclusionWeight p mask e - 1) * trueInversion r π e * warmIncidence π e i

def erroneousFlow {n : ℕ} (r π : Rank n) (T : Transcript n) (p : ℝ)
    (mask : Pair n → Bool) : Fin n → ℝ := fun i =>
  ∑ e, inclusionWeight p mask e * (observedInversion π T e - trueInversion r π e) * warmIncidence π e i

end RankingQueryCost.Joint


