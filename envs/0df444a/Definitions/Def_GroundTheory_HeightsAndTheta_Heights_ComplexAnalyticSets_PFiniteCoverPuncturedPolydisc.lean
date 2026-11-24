-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteCoverPuncturedPolydisc
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteCoverPuncturedPolydisc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:26.855863+00:00
-- url     : https://prove2.me/theorems/94c36397-c03c-4778-90ec-10edb8640e76
-- title:
--   PFinite Cover Punctured Polydisc
-- statement:
--   Definitions and structural lemmas for PFinite Cover Punctured Polydisc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PFiniteCoverPuncturedPolydisc.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteCoverPuncturedPolydisc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Filter Topology Complex
open scoped Real
noncomputable section
namespace FiniteCoverPuncturedPolydisc
variable {e : ℕ}
def strip (c : Fin (e + 1) → ℂ) (ρ : ℝ) : Set (Fin (e + 1) → ℂ) :=
  {u | (u 0).re < Real.log ρ ∧ ∀ i, i ≠ 0 → dist (u i) (c i) < ρ}
theorem convex_strip (c : Fin (e + 1) → ℂ) (ρ : ℝ) : Convex ℝ (strip c ρ) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, fun i hi => ?_⟩
  · have := convex_halfSpace_re_lt (r := Real.log ρ) hx.1 hy.1 ha hb hab
    simpa using this
  · have := convex_ball (c i) ρ (hx.2 i hi) (hy.2 i hi) ha hb hab
    simpa [Metric.mem_ball] using this
theorem isOpen_strip (c : Fin (e + 1) → ℂ) (ρ : ℝ) : IsOpen (strip c ρ) := by
  have h1 : IsOpen {u : Fin (e + 1) → ℂ | (u 0).re < Real.log ρ} :=
    isOpen_lt (continuous_re.comp (continuous_apply 0)) continuous_const
  have h2 : IsOpen {u : Fin (e + 1) → ℂ | ∀ i, i ≠ 0 → dist (u i) (c i) < ρ} := by
    have : {u : Fin (e + 1) → ℂ | ∀ i, i ≠ 0 → dist (u i) (c i) < ρ} =
        ⋂ i ∈ ({0}ᶜ : Finset (Fin (e + 1))), {u | dist (u i) (c i) < ρ} := by
      ext u; simp
    rw [this]
    exact isOpen_biInter_finset fun i _ =>
      isOpen_lt ((continuous_apply i).dist continuous_const) continuous_const
  exact h1.inter h2
theorem base_mem_strip (c : Fin (e + 1) → ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    Function.update c 0 ((Real.log ρ - 1 : ℝ) : ℂ) ∈ strip c ρ := by
  refine ⟨by simp, fun i hi => ?_⟩
  simp [Function.update_of_ne hi, hρ]
instance simplyConnected_strip (c : Fin (e + 1) → ℂ) (ρ : ℝ) [Fact (0 < ρ)] :
    SimplyConnectedSpace (strip c ρ) := by
  have := (convex_strip c ρ).contractibleSpace ⟨_, base_mem_strip c (Fact.out : 0 < ρ)⟩
  infer_instance
instance locPathConnected_strip (c : Fin (e + 1) → ℂ) (ρ : ℝ) :
    LocallyPathConnectedSpace (strip c ρ) :=
  (isOpen_strip c ρ).locallyPathConnectedSpace
def shift (c : Fin (e + 1) → ℂ) (ρ : ℝ) (k : ℤ) (u : strip c ρ) : strip c ρ :=
  ⟨Function.update u.1 0 (u.1 0 + k * (2 * π * I)), by
    refine ⟨by simpa using u.2.1, fun i hi => ?_⟩
    rw [Function.update_of_ne hi]
    exact u.2.2 i hi⟩
variable {c : Fin (e + 1) → ℂ} {r : ℝ}
theorem expMap_mem (hc : c 0 = 0) {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) (u : strip c ρ) :
    Function.update u.1 0 (exp (u.1 0)) ∈ Metric.ball c r ∩ {t : Fin (e + 1) → ℂ | t 0 ≠ 0} := by
  refine ⟨?_, by simp [exp_ne_zero]⟩
  rw [Metric.mem_ball, dist_pi_lt_iff (hρ.trans_le hρr)]
  intro i
  rcases eq_or_ne i 0 with rfl | hi
  · simp only [Function.update_self, hc, dist_zero_right, norm_exp]
    calc Real.exp (u.1 0).re < Real.exp (Real.log ρ) := Real.exp_lt_exp.2 u.2.1
      _ = ρ := Real.exp_log hρ
      _ ≤ r := hρr
  · rw [Function.update_of_ne hi]
    exact (u.2.2 i hi).trans_le hρr
def expMap (hc : c 0 = 0) {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) :
    C(strip c ρ, ↥(Metric.ball c r ∩ {t : Fin (e + 1) → ℂ | t 0 ≠ 0})) where
  toFun u := ⟨Function.update u.1 0 (exp (u.1 0)), expMap_mem hc hρ hρr u⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.update 0 (((continuous_apply 0).comp continuous_subtype_val).cexp)
end FiniteCoverPuncturedPolydisc
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


