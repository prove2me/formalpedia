-- Prove2me | solution 1 for Auto.good_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:29:44.694682+00:00
-- url     : https://prove2.me/submissions/e55e70c7-526f-49c0-8a11-4a1e686356bb

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_phi_sq_mul_exp_le
public import Theorems.Thm_Auto_abs_Gm_le
public import Theorems.Thm_Auto_integrable_of_le_gdom
public import Theorems.Thm_Auto_integrable_prod_of_le_gdom
public import Theorems.Thm_Auto_continuousOn_Gm
public import Theorems.Thm_Auto_continuous_slice

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace Auto
theorem _root_.solution {Q : ℝ × (Fin 3 → ℝ) → ℝ} {sa sb σb β : ℝ} (hsa : 0 < sa) (hσb : 0 < σb)
    (hβ : 0 < β) (v : Fin 3) (hc : ContinuousOn Q (Set.Ioi 0 ×ˢ Set.univ))
    (hb : ∃ C, ∀ s ∈ Set.Icc sa sb, ∀ p, |Q (s, p)| ≤ C * HeatData.phi σb v p ^ 2) (m : ℕ) :
    (∀ s ∈ Set.Icc sa sb, Integrable (fun p => Gm β m s p * Q (s, p))) ∧ Integrable (fun z : ℝ ×
      (Fin 3 → ℝ) => Gm β m z.1 z.2 * Q z) ((volume.restrict (Set.Ioc sa sb)).prod volume) := by
  obtain ⟨CQ, hCQ⟩ := hb
  have hsb : 0 < sb ∨ sb < sa := by
    rcases lt_or_ge 0 sb with h | h
    · exact Or.inl h
    · right; linarith
  rcases hsb with hsb | hsb
  swap
  · refine ⟨fun s hs => absurd (hs.1.trans hs.2) (not_le.2 hsb), ?_⟩
    have : Set.Ioc sa sb = ∅ := Set.Ioc_eq_empty (not_lt.2 hsb.le)
    simp [this]
  obtain ⟨Cg, hCg0, hCg⟩ := abs_Gm_le m hβ hsa (sb := sb)
  set ε := min (1 / (8 * σb)) (1 / (4 * (β * sb))) / 4
  have hε : 0 < ε := by positivity
  have hτ : 0 < β * sb := by positivity
  have hbound : ∀ s ∈ Set.Icc sa sb, ∀ p, |Gm β m s p * Q (s, p)| ≤ (Cg * |CQ| * 4) * gdom ε p := by
    intro s hs p
    have h1 := hCg s hs p
    have h2 := hCQ s hs p
    have h3 := phi_sq_mul_exp_le hσb hτ v p
    rw [abs_mul]
    have hφ := sq_nonneg (HeatData.phi σb v p)
    have hE := (Real.exp_pos (-(p 0 + p 1 + p 2) ^ 2 / (4 * (β * sb)))).le
    calc |Gm β m s p| * |Q (s, p)|
        ≤ (Cg * Real.exp (-(p 0 + p 1 + p 2) ^ 2 / (4 * (β * sb)))) * (|CQ| * HeatData.phi σb v p ^
            2) := by
          refine mul_le_mul h1 (h2.trans ?_) (abs_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_right (le_abs_self _) hφ
      _ = Cg * |CQ| * (HeatData.phi σb v p ^ 2 *
            Real.exp (-(p 0 + p 1 + p 2) ^ 2 / (4 * (β * sb)))) := by ring
      _ ≤ Cg * |CQ| * (4 * gdom ε p) := by gcongr
      _ = _ := by ring
  have hGc := continuousOn_Gm β hβ m
  refine ⟨fun s hs => ?_, ?_⟩
  · have hs0 : 0 < s := hsa.trans_le hs.1
    exact integrable_of_le_gdom ((continuous_slice hGc hs0).mul (continuous_slice hc hs0)) hε
        (hbound s hs)
  · exact integrable_prod_of_le_gdom hsa (hGc.mul hc) hε fun s hs p =>
      hbound s (Set.Ioc_subset_Icc_self hs) p
end Auto
