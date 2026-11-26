-- Prove2me | Definitions.Def_BicausalOT_MultiPeriod
-- name    : BicausalOT_MultiPeriod
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:09:17.661828+00:00
-- url     : https://prove2.me/theorems/d57180d8-d9f4-4304-ab5f-51bdb10515e9
-- title:
--   Multi Period
-- statement:
--   Definitions and structural lemmas for Multi Period, from KT. Wu (MaxWellApexLab/BicausalOT-palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Bicausal optimal transport Bellman representation and measurable selection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/MultiPeriod.lean

import Definitions.Def_BicausalOT_Defs
import Definitions.Def_BicausalOT_UpperBound
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section
namespace MultiPeriod
variable (X Y : ℕ → Type*)
def PairHist : ℕ → Type _
  | 0 => X 0 × Y 0
  | t + 1 => PairHist t × (X (t + 1) × Y (t + 1))
def XHist : ℕ → Type _
  | 0 => X 0
  | t + 1 => XHist t × X (t + 1)
def YHist : ℕ → Type _
  | 0 => Y 0
  | t + 1 => YHist t × Y (t + 1)
variable {X Y}
def projX : (t : ℕ) → PairHist X Y t → XHist X t
  | 0, h => h.1
  | t + 1, hz => (projX t hz.1, hz.2.1)
def projY : (t : ℕ) → PairHist X Y t → YHist Y t
  | 0, h => h.2
  | t + 1, hz => (projY t hz.1, hz.2.2)
variable [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
variable (κμ : (t : ℕ) → XHist X t → Measure (X (t + 1)))
variable (κν : (t : ℕ) → YHist Y t → Measure (Y (t + 1)))
variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)
def Feas (t : ℕ) (h : PairHist X Y t) :
    Set (Measure (X (t + 1) × Y (t + 1))) :=
  {γ | γ.map Prod.fst = κμ t (projX t h) ∧ γ.map Prod.snd = κν t (projY t h)}
def Strat (X Y : ℕ → Type*)
    [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)] : Type _ :=
  (t : ℕ) → PairHist X Y t → Measure (X (t + 1) × Y (t + 1))
variable {κμ κν}
def costGo (γ : Strat X Y) : (k : ℕ) → (t : ℕ) → PairHist X Y t → ℝ≥0∞
  | 0, t, h => c t h
  | k + 1, t, h => c t h + ∫⁻ z, costGo γ k (t + 1) (h, z) ∂(γ t h)
def VGo (κμ : (t : ℕ) → XHist X t → Measure (X (t + 1)))
    (κν : (t : ℕ) → YHist Y t → Measure (Y (t + 1))) :
    (k : ℕ) → (t : ℕ) → PairHist X Y t → ℝ≥0∞
  | 0, t, h => c t h
  | k + 1, t, h => c t h +
      ⨅ (γm : Measure (X (t + 1) × Y (t + 1))) (_ : γm ∈ Feas κμ κν t h),
        ∫⁻ z, VGo κμ κν k (t + 1) (h, z) ∂γm
variable (κμ κν)
end MultiPeriod
end


