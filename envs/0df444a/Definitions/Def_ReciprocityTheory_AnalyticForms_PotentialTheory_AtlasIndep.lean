-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AtlasIndep
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_AtlasIndep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:29:39.505096+00:00
-- url     : https://prove2.me/theorems/d16ede9c-6c34-43a3-8cc3-1d2b2f332843
-- title:
--   Atlas Indep
-- statement:
--   Definitions and structural lemmas for Atlas Indep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/AtlasIndep.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
def unionAtlas (A B : FinHolAtlas e X) (h : A.Compatible B) : FinHolAtlas e X where
  n := A.n + B.n
  chart := Fin.append A.chart B.chart
  cover x := by
    obtain ⟨j, hj⟩ := A.cover x
    exact ⟨Fin.castAdd B.n j, by simpa using hj⟩
  holo j k := by
    induction j using Fin.addCases with
    | left j =>
      induction k using Fin.addCases with
      | left k => simpa [Fin.append_left] using A.holo j k
      | right k => simpa [Fin.append_left, Fin.append_right] using h.1 j k
    | right j =>
      induction k using Fin.addCases with
      | left k => simpa [Fin.append_left, Fin.append_right] using h.2 j k
      | right k => simpa [Fin.append_right] using B.holo j k
@[simp] theorem unionAtlas_chart_castAdd (A B : FinHolAtlas e X) (h : A.Compatible B)
    (j : Fin A.n) : (unionAtlas A B h).chart (Fin.castAdd B.n j) = A.chart j := by
  show Fin.append A.chart B.chart (Fin.castAdd B.n j) = A.chart j
  exact Fin.append_left _ _ _
@[simp] theorem unionAtlas_chart_natAdd (A B : FinHolAtlas e X) (h : A.Compatible B)
    (k : Fin B.n) : (unionAtlas A B h).chart (Fin.natAdd A.n k) = B.chart k := by
  show Fin.append A.chart B.chart (Fin.natAdd A.n k) = B.chart k
  exact Fin.append_right _ _ _
theorem compat_local {A B : FinHolAtlas e X} (h : A.Compatible B) (j : Fin B.n) {y : Fin e → ℂ}
    (hy : y ∈ (B.chart j).target) :
    ∃ k : Fin A.n, AnalyticAt ℂ (A.chart k ∘ (B.chart j).symm) y ∧
      (A.chart k ((B.chart j).symm y)) ∈ (A.chart k).target ∧
      (A.chart k).symm (A.chart k ((B.chart j).symm y)) = (B.chart j).symm y ∧
      ∀ {β : Type} (f : X → β), (f ∘ (B.chart j).symm) =ᶠ[𝓝 y]
        (f ∘ (A.chart k).symm) ∘ (A.chart k ∘ (B.chart j).symm) := by
  obtain ⟨k, hk⟩ := A.cover ((B.chart j).symm y)
  have hmem : y ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' (A.chart k).source := ⟨hy, hk⟩
  have hopen : IsOpen ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (A.chart k).source) :=
    (B.chart j).isOpen_inter_preimage_symm (A.chart k).open_source
  refine ⟨k, h.2 j k y hmem, (A.chart k).map_source hk, (A.chart k).left_inv hk, fun f => ?_⟩
  filter_upwards [hopen.mem_nhds hmem] with y' hy'
  simp only [Function.comp_apply, (A.chart k).left_inv hy'.2]
theorem smoothOn_of_compatible {A B : FinHolAtlas e X} (h : A.Compatible B) {U : Set X}
    (hU : IsOpen U) {f : X → ℝ} (hf : A.SmoothOn U f) : B.SmoothOn U f := by
  intro j y hy
  obtain ⟨k, hT, hTt, hTs, hev⟩ := compat_local h j hy.1
  have hTs' : (A.chart k).symm ((A.chart k) ((B.chart j).symm y)) ∈ U := by
    rw [hTs]
    exact hy.2
  have hopen : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' U) :=
    (A.chart k).isOpen_inter_preimage_symm hU
  have h1 : ContDiffAt ℝ ∞ (f ∘ (A.chart k).symm) ((A.chart k ∘ (B.chart j).symm) y) :=
    (hf k).contDiffAt (hopen.mem_nhds ⟨hTt, hTs'⟩)
  have h2 : ContDiffAt ℝ ∞ (A.chart k ∘ (B.chart j).symm) y :=
    (hT.contDiffAt (n := ∞)).restrict_scalars ℝ
  exact ((h1.comp y h2).congr_of_eventuallyEq (hev f)).contDiffWithinAt
theorem compatible_unionAtlas_left (A B : FinHolAtlas e X) (h : A.Compatible B) :
    A.Compatible (unionAtlas A B h) := by
  refine ⟨fun j k => ?_, fun j k => ?_⟩
  · induction k using Fin.addCases with
    | left k => simpa using A.holo j k
    | right k => simpa using h.1 j k
  · induction j using Fin.addCases with
    | left j => simpa using A.holo j k
    | right j => simpa using h.2 j k
theorem compatible_unionAtlas_right (A B : FinHolAtlas e X) (h : A.Compatible B) :
    B.Compatible (unionAtlas A B h) := by
  refine ⟨fun j k => ?_, fun j k => ?_⟩
  · induction k using Fin.addCases with
    | left k => simpa using h.2 j k
    | right k => simpa using B.holo j k
  · induction j using Fin.addCases with
    | left j => simpa using h.1 j k
    | right j => simpa using B.holo j k
def ChartPartition.extendLeft [CompactSpace X] [T2Space X] {A B : FinHolAtlas e X}
    (h : A.Compatible B) (P : ChartPartition A) : ChartPartition (unionAtlas A B h) where
  χ := Fin.append P.χ (fun _ _ => 0)
  smooth j := by
    induction j using Fin.addCases with
    | left j =>
      show (unionAtlas A B h).SmoothOn Set.univ _
      rw [Fin.append_left]
      exact smoothOn_of_compatible (compatible_unionAtlas_left A B h) isOpen_univ (P.smooth j)
    | right j =>
      intro k
      rw [Fin.append_right]
      exact contDiffOn_const
  nonneg j x := by
    induction j using Fin.addCases with
    | left j => simpa using P.nonneg j x
    | right j => simp
  tsupport_subset j := by
    induction j using Fin.addCases with
    | left j => simpa using P.tsupport_subset j
    | right j =>
      have : (fun _ : X => (0 : ℝ)) = 0 := rfl
      simp [this]
  sum_eq_one x := by
    change ∑ j : Fin (A.n + B.n), Fin.append P.χ (fun _ _ => 0) j x = 1
    rw [Fin.sum_univ_add]
    simpa using P.sum_eq_one x
def ChartPartition.extendRight [CompactSpace X] [T2Space X] {A B : FinHolAtlas e X}
    (h : A.Compatible B) (Q : ChartPartition B) : ChartPartition (unionAtlas A B h) where
  χ := Fin.append (fun _ _ => 0) Q.χ
  smooth j := by
    induction j using Fin.addCases with
    | left j =>
      intro k
      rw [Fin.append_left]
      exact contDiffOn_const
    | right j =>
      show (unionAtlas A B h).SmoothOn Set.univ _
      rw [Fin.append_right]
      exact smoothOn_of_compatible (compatible_unionAtlas_right A B h) isOpen_univ (Q.smooth j)
  nonneg j x := by
    induction j using Fin.addCases with
    | left j => simp
    | right j => simpa using Q.nonneg j x
  tsupport_subset j := by
    induction j using Fin.addCases with
    | left j =>
      have : (fun _ : X => (0 : ℝ)) = 0 := rfl
      simp [this]
    | right j => simpa using Q.tsupport_subset j
  sum_eq_one x := by
    change ∑ j : Fin (A.n + B.n), Fin.append (fun _ _ => 0) Q.χ j x = 1
    rw [Fin.sum_univ_add]
    simpa using Q.sum_eq_one x
end
end ReciprocityTheory.AnForm.M


