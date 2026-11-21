-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpEndpointLeftLim_F000
-- name    : LevyStochCalc_Ito_JumpEndpointLeftLim_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:46:13.922958+00:00
-- url     : https://prove2.me/theorems/05a0420d-66c4-41e2-9ad2-342f048753db
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpEndpointLeftLim
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpEndpointLeftLim. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoStopped_F001
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The endpoint value of a piecewise translated path

A continuous path translated by a vector held fixed on an interval agrees there with a second
path. At the right endpoint of the interval the translated value is no longer the second path's
value but its left limit, because the translation is still the one carried on the interval while
the second path has already moved. Identifying the two is a limit along the interval: the
translated side converges by continuity, the other side converges to the left limit, and limits
in a Hausdorff space are unique.

The identity turns the jump term of Itô's formula along a chain of times into the increment of
the state function across the jump, evaluated at the left limit of the path.

## Main statements

* `LevyStochCalc.Brownian.Ito.exists_seq_lt_tendsto_of_lt_coe` — an interval of `WithTop ℝ` with
  a finite right endpoint contains a sequence converging to that endpoint.
* `LevyStochCalc.Brownian.Ito.tendsto_nhdsLT_of_shift` — the second function converges at the
  endpoint to the value of the continuous one.
* `LevyStochCalc.Brownian.Ito.leftLim_eq_of_shift` — the value of the continuous function at the
  endpoint is the left limit of the second one.
* `LevyStochCalc.Brownian.Ito.shift_endpoint_eq_leftLim` — the translated path at the endpoint is
  the left limit of the path it agrees with, and its coordinatewise form
  `LevyStochCalc.Brownian.Ito.shift_endpoint_eq_leftLim_apply`.
* `LevyStochCalc.Brownian.Ito.leftLim_pi_eq_leftLim_apply` — the left limit of a path in `ℝⁿ`
  with left limits in each coordinate is the vector of the coordinates' left limits.
* `LevyStochCalc.Brownian.Ito.jumpTerm_eq_zero_of_shift_eq`,
  `LevyStochCalc.Brownian.Ito.jumpTerm_of_horizon_le`,
  `LevyStochCalc.Brownian.Ito.jumpTerm_of_eq_top` — the jump term at an index where the
  translation does not move, and at an index whose time has passed the horizon.
* `LevyStochCalc.Brownian.Ito.jumpTerm_eq_leftLim_increment` — the jump term at a finite time
  inside the horizon is the increment of the state function across the jump at the left limit.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

universe u

section Sequence

/-- An interval of `WithTop ℝ` whose right endpoint is finite contains a sequence converging to
that endpoint. -/
theorem exists_seq_lt_tendsto_of_lt_coe {a : WithTop ℝ} {β : ℝ}
    (hab : a < ((β : ℝ) : WithTop ℝ)) :
    ∃ s : ℕ → ℝ, (∀ j, a < ((s j : ℝ) : WithTop ℝ)) ∧
      (∀ j, ((s j : ℝ) : WithTop ℝ) < ((β : ℝ) : WithTop ℝ)) ∧
      Tendsto s atTop (nhds β) := by
  obtain ⟨α, hα⟩ : ∃ α : ℝ, ((α : ℝ) : WithTop ℝ) = a :=
    WithTop.ne_top_iff_exists.mp (hab.trans_le le_top).ne
  have hαβ : α < β := by
    rw [← hα] at hab
    exact_mod_cast hab
  have hd : (0 : ℝ) < β - α := sub_pos.mpr hαβ
  have hm : ∀ j : ℕ, (1 : ℝ) < (j : ℝ) + 2 := by
    intro j
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  refine ⟨fun j => β - (β - α) / ((j : ℝ) + 2), fun j => ?_, fun j => ?_, ?_⟩
  · rw [← hα]
    have hlt : (β - α) / ((j : ℝ) + 2) < β - α := div_lt_self hd (hm j)
    exact_mod_cast (by linarith : α < β - (β - α) / ((j : ℝ) + 2))
  · have hpos : (0 : ℝ) < (β - α) / ((j : ℝ) + 2) :=
      div_pos hd (lt_trans zero_lt_one (hm j))
    exact_mod_cast (by linarith : β - (β - α) / ((j : ℝ) + 2) < β)
  · have hden : Tendsto (fun j : ℕ => (j : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    have h0 : Tendsto (fun j : ℕ => (β - α) / ((j : ℝ) + 2)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hden
    simpa using tendsto_const_nhds.sub h0
end Sequence

section Endpoint

/-- A continuous function that agrees with a second function on an interval with a finite right
endpoint forces the second function to converge from the left at that endpoint to the continuous
function's value there. -/
theorem tendsto_nhdsLT_of_shift {Y : Type*} [TopologicalSpace Y] {g h : ℝ → Y} {a : WithTop ℝ}
    {β : ℝ} (hg : Continuous g) (hab : a < ((β : ℝ) : WithTop ℝ))
    (hagree : ∀ s : ℝ, a < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < ((β : ℝ) : WithTop ℝ) → g s = h s) :
    Tendsto h (nhdsWithin β (Set.Iio β)) (nhds (g β)) := by
  obtain ⟨α, hα⟩ : ∃ α : ℝ, ((α : ℝ) : WithTop ℝ) = a :=
    WithTop.ne_top_iff_exists.mp (hab.trans_le le_top).ne
  have hαβ : α < β := by
    rw [← hα] at hab
    exact_mod_cast hab
  have hev : g =ᶠ[nhdsWithin β (Set.Iio β)] h := by
    filter_upwards [Ioo_mem_nhdsLT hαβ] with s hs
    refine hagree s ?_ ?_
    · rw [← hα]
      exact_mod_cast hs.1
    · exact_mod_cast hs.2
  exact Filter.Tendsto.congr' hev ((hg.tendsto β).mono_left nhdsWithin_le_nhds)
/-- The value at a finite right endpoint of a continuous function agreeing with a second function
on the interval below it is that second function's left limit there. -/
theorem leftLim_eq_of_shift {Y : Type*} [TopologicalSpace Y] [T2Space Y] {g h : ℝ → Y}
    {a : WithTop ℝ} {β : ℝ} (hg : Continuous g) (hab : a < ((β : ℝ) : WithTop ℝ))
    (hagree : ∀ s : ℝ, a < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < ((β : ℝ) : WithTop ℝ) → g s = h s) :
    g β = Function.leftLim h β :=
  (leftLim_eq_of_tendsto (tendsto_nhdsLT_of_shift hg hab hagree)).symm
variable {Ω : Type u} {n : ℕ}

/-- At the finite right endpoint of an interval on which a continuous path translated by a fixed
vector agrees with a second path, the translated value is that second path's left limit. -/
theorem shift_endpoint_eq_leftLim {V X : ℝ → Ω → Fin n → ℝ} {a : WithTop ℝ} {β : ℝ} {ω : Ω}
    {b : Fin n → ℝ} (hV : Continuous fun t => V t ω) (hab : a < ((β : ℝ) : WithTop ℝ))
    (hshift : ∀ s : ℝ, a < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < ((β : ℝ) : WithTop ℝ) → V s ω + b = X s ω) :
    V β ω + b = Function.leftLim (fun s => X s ω) β :=
  leftLim_eq_of_shift (g := fun s => V s ω + b) (hV.add continuous_const) hab hshift
/-- Coordinatewise form of the endpoint identity for a translated path. -/
theorem shift_endpoint_eq_leftLim_apply {V X : ℝ → Ω → Fin n → ℝ} {a : WithTop ℝ} {β : ℝ} {ω : Ω}
    {b : Fin n → ℝ} (hV : Continuous fun t => V t ω) (hab : a < ((β : ℝ) : WithTop ℝ))
    (hshift : ∀ s : ℝ, a < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < ((β : ℝ) : WithTop ℝ) → V s ω + b = X s ω) (i : Fin n) :
    V β ω i + b i = Function.leftLim (fun s => X s ω i) β :=
  leftLim_eq_of_shift (g := fun s => V s ω i + b i)
    (((continuous_apply i).comp hV).add continuous_const) hab
    fun s h₁ h₂ => congrFun (hshift s h₁ h₂) i
/-- The left limit of a path in `ℝⁿ` having a left limit in each coordinate is the vector of the
coordinates' left limits. -/
theorem leftLim_pi_eq_leftLim_apply {F : ℝ → Fin n → ℝ} {β : ℝ}
    (hleft : ∀ i : Fin n, ∃ L : ℝ,
      Tendsto (fun s => F s i) (nhdsWithin β (Set.Iio β)) (nhds L)) :
    Function.leftLim F β = fun i => Function.leftLim (fun s => F s i) β := by
  classical
  choose L hL using hleft
  rw [leftLim_eq_of_tendsto (tendsto_pi_nhds.mpr hL)]
  exact funext fun i => (leftLim_eq_of_tendsto (hL i)).symm
end Endpoint

section JumpTerm

variable {Ω : Type u} {n : ℕ}

/-- The jump term of the telescope vanishes at an index across which the translation does not
move. -/
theorem jumpTerm_eq_zero_of_shift_eq (f : (Fin n → ℝ) → ℝ) {c : ℕ → Ω → Fin n → ℝ} {k : ℕ}
    {ω : Ω} (y : Fin n → ℝ) (h : c k ω = c (k + 1) ω) :
    f (y + c (k + 1) ω) - f (y + c k ω) = 0 := by
  rw [h, sub_self]
/-- A translation read off the horizon clipped at a chain of times does not move across an index
at which the chain does not move. -/
theorem shift_eq_of_clipTime_eq {σ : ℕ → Ω → WithTop ℝ} {c : ℕ → Ω → Fin n → ℝ}
    {g : ℝ → Fin n → ℝ} {T : ℝ} {k : ℕ} {ω : Ω}
    (hc : ∀ j : ℕ, c j ω = g (clipTime (σ j) T ω)) (h : σ k ω = σ (k + 1) ω) :
    c k ω = c (k + 1) ω := by
  rw [hc k, hc (k + 1)]
  simp only [clipTime, h]
/-- Past the horizon the jump term of the telescope is evaluated at the horizon itself. -/
theorem jumpTerm_of_horizon_le (f : (Fin n → ℝ) → ℝ) {V : ℝ → Ω → Fin n → ℝ}
    {σ : ℕ → Ω → WithTop ℝ} {c : ℕ → Ω → Fin n → ℝ} {T : ℝ} {k : ℕ} {ω : Ω}
    (h : ((T : ℝ) : WithTop ℝ) ≤ σ (k + 1) ω) :
    f (V (clipTime (σ (k + 1)) T ω) ω + c (k + 1) ω)
        - f (V (clipTime (σ (k + 1)) T ω) ω + c k ω)
      = f (V T ω + c (k + 1) ω) - f (V T ω + c k ω) := by
  rw [clipTime_of_le h]
/-- At an index whose time is infinite the jump term of the telescope is evaluated at the
horizon. -/
theorem jumpTerm_of_eq_top (f : (Fin n → ℝ) → ℝ) {V : ℝ → Ω → Fin n → ℝ}
    {σ : ℕ → Ω → WithTop ℝ} {c : ℕ → Ω → Fin n → ℝ} {T : ℝ} {k : ℕ} {ω : Ω}
    (h : σ (k + 1) ω = ⊤) :
    f (V (clipTime (σ (k + 1)) T ω) ω + c (k + 1) ω)
        - f (V (clipTime (σ (k + 1)) T ω) ω + c k ω)
      = f (V T ω + c (k + 1) ω) - f (V T ω + c k ω) :=
  jumpTerm_of_horizon_le f (by rw [h]; exact le_top)
/-- At a finite time inside the horizon the jump term of the telescope is the increment of the
state function across the jump, evaluated at the left limit of the path the translated path
agrees with. -/
theorem jumpTerm_eq_leftLim_increment (f : (Fin n → ℝ) → ℝ) {V X : ℝ → Ω → Fin n → ℝ}
    {σ : ℕ → Ω → WithTop ℝ} {c : ℕ → Ω → Fin n → ℝ} {T β : ℝ} {k : ℕ} {ω : Ω}
    (hV : Continuous fun t => V t ω) (hβ : σ (k + 1) ω = ((β : ℝ) : WithTop ℝ)) (hβT : β ≤ T)
    (hlt : σ k ω < σ (k + 1) ω)
    (hshift : ∀ s : ℝ, σ k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < σ (k + 1) ω → V s ω + c k ω = X s ω) :
    f (V (clipTime (σ (k + 1)) T ω) ω + c (k + 1) ω)
        - f (V (clipTime (σ (k + 1)) T ω) ω + c k ω)
      = f (Function.leftLim (fun s => X s ω) β + (c (k + 1) ω - c k ω))
        - f (Function.leftLim (fun s => X s ω) β) := by
  have hclip : clipTime (σ (k + 1)) T ω = β := by
    rw [clipTime_eq_min hβ, min_eq_right hβT]
  have hab : σ k ω < ((β : ℝ) : WithTop ℝ) := by
    rw [← hβ]
    exact hlt
  have hend : V β ω + c k ω = Function.leftLim (fun s => X s ω) β :=
    shift_endpoint_eq_leftLim hV hab fun s h₁ h₂ => hshift s h₁ (by rw [hβ]; exact h₂)
  have harg : V β ω + c (k + 1) ω = V β ω + c k ω + (c (k + 1) ω - c k ω) := by
    abel
  rw [hclip, harg, hend]
end JumpTerm

end LevyStochCalc.Brownian.Ito


