-- Prove2me | Definitions.Def_SubpowerLE
-- name    : SubpowerLE
-- status  : Definition
-- author  : @sensei
-- created : 2026-09-30T16:27:32.471985+00:00
-- url     : https://prove2.me/theorems/f99fa753-97cf-4f7f-a591-65145eb556ac
-- title:
--   Subpower bound $\lesssim_\delta$
-- statement:
--   A scale-dependent quantity $x(\delta)$ is subpower-bounded by $y(\delta)$, written $x \lesssim y$, if for every $\varepsilon > 0$ there exists $C \geq 0$ (independent of $\delta$) with $x(\delta) \leq C\, \delta^{-\varepsilon}\, y(\delta)$ for all $\delta \in (0,1)$. Includes the reflexivity and right-transitivity lemmas.
-- source:
--   Cai, Filtered Descent for the Physical Kakeya Incidence, 2026, https://cchx0000.github.io/papers/filtered-descent-physical-kakeya/filtered-descent-physical-kakeya.pdf, §1 (the $\delta^{-o(1)}$ convention)

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic

namespace FilteredDescent

/-- Subpower-loss domination `x ≲ y` uniformly for `δ ∈ (0,1)` (paper's `≲ δ^{-o(1)}`).

  For every `ε > 0` there is a constant `C ≥ 0` — allowed to depend on `ε`
  and on the dimension, but *not* on `δ` — such that
  `x δ ≤ C * δ ^ (-ε) * y δ` for *all* `δ ∈ (0,1)`.
  The paper uses this pervasively to bookkeep subpower losses as `δ → 0`.
  Quantities compared here are functions of the scale `δ`; constant
  quantities are embedded via `fun _ => c`. -/
def SubpowerLE (x y : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ < 1 → x δ ≤ C * δ ^ (-ε) * y δ

/-- Subpower domination is reflexive on quantities nonnegative on `(0,1)`. -/
theorem SubpowerLE.refl {x : ℝ → ℝ} (hx : ∀ δ : ℝ, 0 < δ → δ < 1 → 0 ≤ x δ) :
    SubpowerLE x x := by
  unfold SubpowerLE
  intro ε hε
  refine ⟨1, zero_le_one, fun δ hδ0 hδ1 => ?_⟩
  have h : (1 : ℝ) ≤ δ ^ (-ε) := by
    rw [Real.rpow_neg (le_of_lt hδ0)]
    exact (one_le_inv_iff₀).mpr ⟨Real.rpow_pos_of_pos hδ0 ε,
      le_of_lt (Real.rpow_lt_one (le_of_lt hδ0) hδ1 hε)⟩
  calc x δ = 1 * x δ := by ring
    _ ≤ δ ^ (-ε) * x δ := mul_le_mul_of_nonneg_right h (hx δ hδ0 hδ1)
    _ = 1 * δ ^ (-ε) * x δ := by ring

/-- Chaining a subpower bound through a middle factor. -/
theorem SubpowerLE.trans_right {x y z : ℝ → ℝ}
    (hxy : SubpowerLE x y) (hyz : SubpowerLE y z) :
    SubpowerLE x z := by
  unfold SubpowerLE at *
  intro ε hε
  obtain ⟨C₁, hC₁, h₁⟩ := hxy (ε / 2) (by linarith)
  obtain ⟨C₂, hC₂, h₂⟩ := hyz (ε / 2) (by linarith)
  refine ⟨C₁ * C₂, mul_nonneg hC₁ hC₂, fun δ hδ0 hδ1 => ?_⟩
  have hpow : δ ^ (-ε) = δ ^ (-(ε / 2)) * δ ^ (-(ε / 2)) := by
    rw [← Real.rpow_add hδ0]
    ring_nf
  have hnn : 0 ≤ δ ^ (-(ε / 2)) := Real.rpow_nonneg (le_of_lt hδ0) _
  calc x δ ≤ C₁ * δ ^ (-(ε / 2)) * y δ := h₁ δ hδ0 hδ1
    _ ≤ C₁ * δ ^ (-(ε / 2)) * (C₂ * δ ^ (-(ε / 2)) * z δ) :=
        mul_le_mul_of_nonneg_left (h₂ δ hδ0 hδ1) (mul_nonneg hC₁ hnn)
    _ = (C₁ * C₂) * δ ^ (-ε) * z δ := by rw [hpow]; ring

end FilteredDescent


