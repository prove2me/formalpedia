-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_UnitriangularCharts
-- name    : Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_UnitriangularCharts
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T01:30:14.034878+00:00
-- url     : https://prove2.me/theorems/83893e02-aeaf-4efd-8c21-68725587aed1
-- title:
--   Unitriangular Charts
-- statement:
--   Definitions and structural lemmas for Unitriangular Charts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/UnitriangularCharts.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitriangularCharts
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
abbrev Below (r : ℕ) : Type := {p : Fin r × Fin r // p.2 < p.1}
theorem card_below (r : ℕ) : Fintype.card (Below r) = r * (r - 1) / 2 := by
  have h : Fintype.card (Below r) = ∑ i : Fin r, (i : ℕ) := by
    rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.card_filter]
    have : (Finset.univ.filter fun j : Fin r => j < i) = Finset.Iio i := by
      ext j; simp
    rw [this, Fin.card_Iio]
  rw [h, Fin.sum_univ_eq_sum_range (fun i => i) r, Finset.sum_range_id]
def flagDim (X : Data E r) : ℕ := X.Ψ.card * (r * (r - 1) / 2)
theorem card_index (X : Data E r) : Fintype.card (X.Ψ × Below r) = flagDim X := by
  rw [Fintype.card_prod, card_below, Fintype.card_coe, flagDim]
def numbering (X : Data E r) : X.Ψ × Below r ≃ Fin (flagDim X) :=
  Fintype.equivFinOfCardEq (card_index X)
def unitri (X : Data E r) (z : V (flagDim X)) : Frame X.Ψ r :=
  fun τ a b => if h : b < a then z (numbering X (τ, ⟨(a, b), h⟩)) else if a = b then 1 else 0
def IsUnitri {Ψ : Finset (E →+* ℂ)} (n : Frame Ψ r) : Prop :=
  ∀ τ, (∀ a, n τ a a = 1) ∧ ∀ a b, a < b → n τ a b = 0
def IsOrthonormalFrame (X : Data E r) (x0 : Frame X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x0 τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)
def chart (X : Data E r) (x0 : Frame X.Ψ r) (z : V (flagDim X)) : Frame X.Ψ r :=
  rmul x0 (unitri X z)
def chartDom (X : Data E r) (x0 : Frame X.Ψ r) : Set (V (flagDim X)) :=
  {z | chart X x0 z ∈ X.dom}
def offBlock (X : Data E r) (z : V (flagDim X)) : Frame X.Ψ r :=
  fun τ a b => if (b : ℕ) < X.p0 ∧ X.p0 ≤ (a : ℕ) then unitri X z τ a b else if a = b then 1 else 0
def inBlock (X : Data E r) (z : V (flagDim X)) : Frame X.Ψ r :=
  fun τ a b => if (b : ℕ) < X.p0 ∧ X.p0 ≤ (a : ℕ) then 0 else unitri X z τ a b
def blockChart (X : Data E r) (x0 : Frame X.Ψ r) (z : V (flagDim X)) : Frame X.Ψ r :=
  rmul x0 (rmul (offBlock X z) (inBlock X z))
def blockChartDom (X : Data E r) (x0 : Frame X.Ψ r) : Set (V (flagDim X)) :=
  {z | blockChart X x0 z ∈ X.dom}
def gap {Ψ : Finset (E →+* ℂ)} (la : Wt Ψ r) (τ : Ψ) (i : ℕ) (h : i + 1 < r) : ℤ :=
  la τ ⟨i, by omega⟩ - la τ ⟨i + 1, h⟩
def pairing {Ψ : Finset (E →+* ℂ)} (la : Wt Ψ r) (τ : Ψ) (h : 0 < r) : ℤ :=
  la τ ⟨r - 1, by omega⟩ - la τ ⟨0, h⟩
def canonicalWt (X : Data E r) : Wt X.Ψ r := fun _ i => 2 * ((i : ℕ) : ℤ) + 1 - (r : ℤ)
def IsStrictlyDominant (X : Data E r) (la : Wt X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, (∀ (i : ℕ) (h : i + 1 < r), i + 1 ≠ X.p0 → 0 < gap la τ i h) ∧
    ∀ (h0 : 0 < X.p0) (h1 : X.p0 < r), 0 < pairing la τ (h0.trans h1)
example (X : Data E r) : IsStrictlyDominant X
    (fun _ i => if (i : ℕ) < X.p0 then -((i : ℕ) : ℤ) else (r : ℤ) - ((i : ℕ) : ℤ)) := by
  intro τ
  refine ⟨fun i h hi => ?_, fun h0 h1 => ?_⟩
  · simp only [gap]; split_ifs <;> omega
  · simp only [pairing]; split_ifs <;> omega
end
end GlobalTheory.IndefiniteRowSideFullHecke.UnitriangularCharts


