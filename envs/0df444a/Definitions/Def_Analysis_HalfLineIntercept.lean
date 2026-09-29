-- Prove2me | Definitions.Def_Analysis_HalfLineIntercept
-- name    : Analysis_HalfLineIntercept
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/fa16e410-b046-5a1c-8470-6154dce78351
-- title:
--   Eventual slope and intercept of a function on a half-line
-- statement:
--   For a function $F \colon \mathbb{R} \to \mathbb{C}$ two total operators are defined, in the namespace `HalfLine`. The slope [`HalfLine.slope F`](../def/Analysis_HalfLineIntercept.html#L9) is the limit along `Filter.atTop` of the first-difference function $R \mapsto F(R+1) - F(R)$, taken with Mathlib's `Filter.limUnder`; the intercept [`HalfLine.intercept F`](../def/Analysis_HalfLineIntercept.html#L12) is the limit along `Filter.atTop` of $R \mapsto F(R) - R\cdot\operatorname{slope} F$. Since `Filter.limUnder` is defined by choice, both operators are total functions of $F$: they return the genuine limit whenever the relevant function converges at $+\infty$, and an unspecified complex number otherwise.
--
--   The substantive content consists of two evaluation lemmas and their combination. [`HalfLine.slope_eq_of_forall_le_eq_add_mul`](../def/Analysis_HalfLineIntercept.html#L15) states that if there exists $R_0 \in \mathbb{R}$ with $F(R) = R\nu + \mu$ for every $R \ge R_0$, then $\operatorname{slope} F = \nu$; [`HalfLine.intercept_eq_of_forall_le_eq_add_mul`](../def/Analysis_HalfLineIntercept.html#L26) states that under the same hypothesis $\operatorname{intercept} F = \mu$. Thus only the behaviour of $F$ near $+\infty$ matters, and an arbitrary initial segment of $F$ is irrelevant. From these, [`HalfLine.eq_and_eq_of_forall_le_eq_add_mul`](../def/Analysis_HalfLineIntercept.html#L37) gives uniqueness: if $F$ agrees with $R \mapsto R\nu + \mu$ beyond some threshold and also with $R \mapsto R\nu' + \mu'$ beyond some (possibly different) threshold, then $\mu = \mu'$ and $\nu = \nu'$.
--
--   The module closes with sanity checks. [`HalfLine.affineExample`](../def/Analysis_HalfLineIntercept.html#L43) is the function equal to $37$ for $R < 5$ and to $3R + 7$ for $R \ge 5$; its slope is computed to be $3$, its intercept $7$, while its value at $0$ is $37$. Three further examples evaluate the two operators on a genuinely affine function and on a constant function.
--
--   **Relation to Mathlib.** The limits are taken with Mathlib's `Filter.limUnder` along `Filter.atTop`. The operators [`HalfLine.slope`](../def/Analysis_HalfLineIntercept.html#L9) and [`HalfLine.intercept`](../def/Analysis_HalfLineIntercept.html#L12) are the project's own; in particular [`HalfLine.slope`](../def/Analysis_HalfLineIntercept.html#L9) is unrelated to Mathlib's `slope`, which is the divided difference of a function at two points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Analysis_HalfLineIntercept.lean

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace HalfLine

def slope (F : ℝ → ℂ) : ℂ :=
  Filter.limUnder Filter.atTop (fun R : ℝ => F (R + 1) - F R)

def intercept (F : ℝ → ℂ) : ℂ :=
  Filter.limUnder Filter.atTop (fun R : ℝ => F R - (R : ℂ) * slope F)

theorem slope_eq_of_forall_le_eq_add_mul {F : ℝ → ℂ} {μ ν : ℂ}
    (h : ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → F R = (R : ℂ) * ν + μ) : slope F = ν := by
  obtain ⟨R₀, hR⟩ := h
  unfold slope
  refine Filter.Tendsto.limUnder_eq ?_
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [Filter.eventually_ge_atTop R₀] with R hRle
  rw [hR (R + 1) (by linarith), hR R hRle]
  push_cast
  ring

theorem intercept_eq_of_forall_le_eq_add_mul {F : ℝ → ℂ} {μ ν : ℂ}
    (h : ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → F R = (R : ℂ) * ν + μ) : intercept F = μ := by
  have hs : slope F = ν := slope_eq_of_forall_le_eq_add_mul h
  obtain ⟨R₀, hR⟩ := h
  unfold intercept
  refine Filter.Tendsto.limUnder_eq ?_
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [Filter.eventually_ge_atTop R₀] with R hRle
  rw [hs, hR R hRle]
  ring

theorem eq_and_eq_of_forall_le_eq_add_mul {F : ℝ → ℂ} {μ ν μ' ν' : ℂ}
    (h : ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → F R = (R : ℂ) * ν + μ)
    (h' : ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → F R = (R : ℂ) * ν' + μ') : μ = μ' ∧ ν = ν' :=
  ⟨(intercept_eq_of_forall_le_eq_add_mul h).symm.trans (intercept_eq_of_forall_le_eq_add_mul h'),
    (slope_eq_of_forall_le_eq_add_mul h).symm.trans (slope_eq_of_forall_le_eq_add_mul h')⟩

def affineExample (R : ℝ) : ℂ :=
  if R < 5 then 37 else (R : ℂ) * 3 + 7

theorem affineExample_eq (R : ℝ) (hR : 5 ≤ R) : affineExample R = (R : ℂ) * 3 + 7 := by
  simp [affineExample, not_lt.mpr hR]

theorem slope_affineExample : slope affineExample = 3 :=
  slope_eq_of_forall_le_eq_add_mul ⟨5, affineExample_eq⟩

theorem intercept_affineExample : intercept affineExample = 7 :=
  intercept_eq_of_forall_le_eq_add_mul ⟨5, affineExample_eq⟩

theorem affineExample_zero : affineExample 0 = 37 := by
  norm_num [affineExample]

example : intercept (fun x : ℝ => (7 : ℂ) + 3 * (x : ℂ)) = 7 :=
  intercept_eq_of_forall_le_eq_add_mul ⟨0, fun R _ => show (7 : ℂ) + 3 * (R : ℂ) = (R : ℂ) * 3 + 7 by ring⟩

example : slope (fun x : ℝ => (7 : ℂ) + 3 * (x : ℂ)) = 3 :=
  slope_eq_of_forall_le_eq_add_mul ⟨0, fun R _ => show (7 : ℂ) + 3 * (R : ℂ) = (R : ℂ) * 3 + 7 by ring⟩

example : intercept (fun _ : ℝ => (7 : ℂ)) = 7 :=
  intercept_eq_of_forall_le_eq_add_mul ⟨0, fun R _ => show (7 : ℂ) = (R : ℂ) * 0 + 7 by ring⟩

end HalfLine

end


