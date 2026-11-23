-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_TorusAtExistsOfParts
-- name    : Development_AbelianVarietyTheory_Proofs_TorusSplitting_TorusAtExistsOfParts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:52.783634+00:00
-- url     : https://prove2.me/theorems/ba4a3229-5db3-424f-a29a-388e59b66be0
-- title:
--   Torus At Exists Of Parts
-- statement:
--   Definitions and structural lemmas for Torus At Exists Of Parts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/TorusAtExistsOfParts.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
namespace GlobalTheory
namespace TorusAtAssembly
section Form
variable {ι : Type} [Fintype ι]
open NumberField in
variable {ι : Type} [Fintype ι] in
theorem _root_.GlobalTheory.TorusAtAssembly.im_Hf_add_left (x y z : EuclideanSpace ℂ ι) :
    (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf (x + y) z).im = (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf x z).im + (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf y z).im := by
  simp [_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf, add_mul, Finset.sum_add_distrib]
open NumberField in
variable {ι : Type} [Fintype ι] in
theorem _root_.GlobalTheory.TorusAtAssembly.im_Hf_add_right (x y z : EuclideanSpace ℂ ι) :
    (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf x (y + z)).im = (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf x y).im + (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf x z).im := by
  simp [_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf, mul_add, Finset.sum_add_distrib]
open NumberField in
variable {ι : Type} [Fintype ι] in
theorem _root_.GlobalTheory.TorusAtAssembly.im_Hf_swap (x y : EuclideanSpace ℂ ι) :
    (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf y x).im = -(_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf x y).im := by
  have h : _root_.ReciprocityTheory.ChartRestriction.G.I2.Hf y x = (starRingEnd ℂ) (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf x y) := by
    simp [_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf, map_sum, mul_comm]
  rw [h, Complex.conj_im]
end Form
variable {E : Type} [Field E] [NumberField E]
open NumberField in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.TorusAtAssembly.act_add {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (x y : _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp dim) :
    _root_.ReciprocityTheory.ChartRestriction.G.I2.act α (x + y) = _root_.ReciprocityTheory.ChartRestriction.G.I2.act α x + _root_.ReciprocityTheory.ChartRestriction.G.I2.act α y := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.act
  ext i
  simp [mul_add]
open NumberField in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.TorusAtAssembly.Hf_act_conj [IsCMField E] {dim : (E →+* ℂ) → ℕ} (α β : 𝓞 E)
    (h : (β : E) = _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (α : E))
    (x y : _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp dim) : _root_.ReciprocityTheory.ChartRestriction.G.I2.Hf x (_root_.ReciprocityTheory.ChartRestriction.G.I2.act β y) = _root_.ReciprocityTheory.ChartRestriction.G.I2.Hf (_root_.ReciprocityTheory.ChartRestriction.G.I2.act α x) y := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.Hf _root_.ReciprocityTheory.ChartRestriction.G.I2.act
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc : (starRingEnd ℂ) (i.fst (β : E)) = i.fst (α : E) := by
    rw [h]
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
    rw [IsCMField.complexEmbedding_complexConj, Complex.conj_conj]
  simp only [map_mul, hc]
  ring
noncomputable def sgnFloor (t : ℝ) : ℤ := ((Int.negOnePow ⌊t⌋ : ℤˣ) : ℤ)
open NumberField in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.TorusAtAssembly.sgnFloor_pm (t : ℝ) :
    _root_.GlobalTheory.TorusAtAssembly.sgnFloor t = 1 ∨ _root_.GlobalTheory.TorusAtAssembly.sgnFloor t = -1 := by
  rcases Int.units_eq_one_or (Int.negOnePow ⌊t⌋) with h | h <;> simp [_root_.GlobalTheory.TorusAtAssembly.sgnFloor, h]
open NumberField in
variable {E : Type} [Field E] [NumberField E] in
theorem sgnFloor_intCast_eq_negOnePow (k : ℤ) :
    _root_.GlobalTheory.TorusAtAssembly.sgnFloor (k : ℝ) = ((Int.negOnePow k : ℤˣ) : ℤ) := by
  simp [_root_.GlobalTheory.TorusAtAssembly.sgnFloor]
open NumberField in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.TorusAtAssembly.sgnFloor_cos (k : ℤ) :
    (_root_.GlobalTheory.TorusAtAssembly.sgnFloor (k : ℝ) : ℝ) = Real.cos (Real.pi * k) := by
  rw [sgnFloor_intCast_eq_negOnePow, mul_comm, Real.cos_int_mul_pi, Int.cast_negOnePow]
open NumberField in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.TorusAtAssembly.sgnFloor_add (a b c k : ℤ) :
    (_root_.GlobalTheory.TorusAtAssembly.sgnFloor ((a : ℝ) + b + c + 2 * k) : ℝ) =
      _root_.GlobalTheory.TorusAtAssembly.sgnFloor (a : ℝ) * _root_.GlobalTheory.TorusAtAssembly.sgnFloor (b : ℝ) * Real.cos (Real.pi * c) := by
  rw [← _root_.GlobalTheory.TorusAtAssembly.sgnFloor_cos]
  have h : ((a : ℝ) + b + c + 2 * k) = ((a + b + c + 2 * k : ℤ) : ℝ) := by push_cast; ring
  rw [h, sgnFloor_intCast_eq_negOnePow, sgnFloor_intCast_eq_negOnePow, sgnFloor_intCast_eq_negOnePow,
    sgnFloor_intCast_eq_negOnePow, Int.negOnePow_add, Int.negOnePow_add, Int.negOnePow_add,
    Int.negOnePow_two_mul]
  push_cast
  ring
section Build
variable [IsCMField E] {dim : (E →+* ℂ) → ℕ}
  {b : Module.Basis (Fin (2 * Fintype.card (Idx dim))) ℝ (Vsp dim)} {w w' : 𝓞 E}
open NumberField in
variable {E : Type} [Field E] [NumberField E] in
variable [IsCMField E] {dim : (E →+* ℂ) → ℕ}
  {b : Module.Basis (Fin (2 * Fintype.card (_root_.ReciprocityTheory.ChartRestriction.G.I2.Idx dim))) ℝ (_root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp dim)} {w w' : 𝓞 E} in

theorem _root_.GlobalTheory.TorusAtAssembly.integral_of_parity (hw : (w' : E) = _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (w : E))
    (par : ∀ x ∈ _root_.ReciprocityTheory.ChartRestriction.G.I2.lat b, ∀ y ∈ _root_.ReciprocityTheory.ChartRestriction.G.I2.lat b, ∃ k : ℤ,
      (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf x (_root_.ReciprocityTheory.ChartRestriction.G.I2.act w y)).im - (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf x (_root_.ReciprocityTheory.ChartRestriction.G.I2.act w' y)).im - (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf x y).im = 2 * k) :
    ∀ x y : _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp dim, x ∈ _root_.ReciprocityTheory.ChartRestriction.G.I2.lat b → y ∈ _root_.ReciprocityTheory.ChartRestriction.G.I2.lat b → ∃ k : ℤ, (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf x y).im = k := by
  have hQ : ∀ x ∈ _root_.ReciprocityTheory.ChartRestriction.G.I2.lat b, ∃ k : ℤ, (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf x (_root_.ReciprocityTheory.ChartRestriction.G.I2.act w x)).im = k := by
    intro x hx
    obtain ⟨k, hk⟩ := par x hx x hx
    rw [_root_.GlobalTheory.TorusAtAssembly.Hf_act_conj w w' hw,
      _root_.GlobalTheory.TorusAtAssembly.im_Hf_swap x (_root_.ReciprocityTheory.ChartRestriction.G.I2.act w x)] at hk
    have h0 : (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf x x).im = 0 := by
      have := _root_.GlobalTheory.TorusAtAssembly.im_Hf_swap x x
      linarith
    exact ⟨k, by linarith⟩
  intro x y hx hy
  obtain ⟨k, hk⟩ := par x hx y hy
  rw [_root_.GlobalTheory.TorusAtAssembly.Hf_act_conj w w' hw,
    _root_.GlobalTheory.TorusAtAssembly.im_Hf_swap y (_root_.ReciprocityTheory.ChartRestriction.G.I2.act w x)] at hk
  obtain ⟨a, ha⟩ := hQ x hx
  obtain ⟨a', ha'⟩ := hQ y hy
  obtain ⟨s, hs⟩ := hQ (x + y) (Submodule.add_mem _ hx hy)
  rw [_root_.GlobalTheory.TorusAtAssembly.act_add, _root_.GlobalTheory.TorusAtAssembly.im_Hf_add_left, _root_.GlobalTheory.TorusAtAssembly.im_Hf_add_right,
    _root_.GlobalTheory.TorusAtAssembly.im_Hf_add_right] at hs
  refine ⟨s - a - a' - 2 * k, ?_⟩
  push_cast
  linarith
noncomputable def torus (r : ℕ)
    (hdim : ∀ τ, dim τ + dim (NumberField.ComplexEmbedding.conjugate τ) = r)
    (hw : (w' : E) = cc (w : E))
    (stable : ∀ (α : 𝓞 E) (x : Vsp dim), x ∈ lat b → act α x ∈ lat b)
    (par : ∀ x ∈ lat b, ∀ y ∈ lat b, ∃ k : ℤ,
      (Hf x (act w y)).im - (Hf x (act w' y)).im - (Hf x y).im = 2 * k)
    (perfect : ∀ φ : lat b →+ ℤ, ∃ x ∈ lat b, ∀ y : lat b, (φ y : ℝ) = (Hf x (y : Vsp dim)).im) :
    PT E where
  dim := dim
  r := r
  dim_conj := hdim
  b := b
  stable := stable
  integral := integral_of_parity hw par
  perfect := perfect
  eps y := sgnFloor (Hf y (act w y)).im
  eps_pm x _ := sgnFloor_pm _
  eps_add x hx y hy := by
    obtain ⟨a, ha⟩ := integral_of_parity hw par x (act w x) hx (stable w x hx)
    obtain ⟨a', ha'⟩ := integral_of_parity hw par y (act w y) hy (stable w y hy)
    obtain ⟨c, hc⟩ := integral_of_parity hw par x y hx hy
    obtain ⟨k, hk⟩ := par x hx y hy
    rw [Hf_act_conj w w' hw] at hk
    rw [ha, ha', hc, ← sgnFloor_add a a' c k]
    congr 2
    rw [act_add, im_Hf_add_left, im_Hf_add_right, im_Hf_add_right, im_Hf_swap (act w x) y]
    linarith
  eps_iso x _ h := by
    rw [im_Hf_swap, h w]
    simp [sgnFloor]
end Build
end TorusAtAssembly
end GlobalTheory


