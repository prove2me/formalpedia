-- Prove2me | Definitions.Def_SNumbers_Examples_IdentityL1Linfty
-- name    : SNumbers_Examples_IdentityL1Linfty
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T04:32:07.244269+00:00
-- url     : https://prove2.me/theorems/7a167710-c21b-4f50-ae47-5e746f50cfae
-- title:
--   Identity L1 Linfty
-- statement:
--   Definitions and structural lemmas for Identity L1 Linfty, from Mario Ullrich (mario-ullrich/Lean-SNumbers; see pinned Apache-2.0 LICENSE and source headers)'s pinned Pietsch axiomatic theory of s-numbers and maximal difference bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean

module
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_LittleGrothendieck
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_AddOns_Approximable
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Sequences
public import Theorems.Thm_SNumbers_norm_sq_eq_tsum_norm_sq
public import Theorems.Thm_SNumbers_sum_norm_apply_le_norm_l1

set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped ENNReal
namespace SNumbers.L1Linf
variable {𝕜 : Type*} [RCLike 𝕜]
abbrev L1 (𝕜 : Type*) [RCLike 𝕜] : Type _ := lp (fun _ : ℕ => 𝕜) 1
abbrev Linf (𝕜 : Type*) [RCLike 𝕜] : Type _ := lp (fun _ : ℕ => 𝕜) ∞
lemma norm_coe_linf_le_norm {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ 0)
    (f : lp (fun _ : ℕ => 𝕜) p) :
    ‖(lp.linearMapOfLE 𝕜 (fun _ : ℕ => 𝕜) le_top f : Linf 𝕜)‖ ≤ ‖f‖ := by
  refine lp.norm_le_of_forall_le (norm_nonneg f) (fun i => ?_)
  rw [lp.coe_linearMapOfLE_apply]
  exact lp.norm_apply_le_norm hp f i
noncomputable def incl : L1 𝕜 →L[𝕜] Linf 𝕜 :=
  LinearMap.mkContinuous (lp.linearMapOfLE 𝕜 (fun _ : ℕ => 𝕜) le_top) 1 (fun f => by
    rw [one_mul]; exact norm_coe_linf_le_norm (by norm_num) f)
noncomputable def e (i : ℕ) : L1 𝕜 := lp.single 1 i (1 : 𝕜)
noncomputable def emb1 (m : ℕ) : EuclideanSpace 𝕜 (Fin m) →L[𝕜] L1 𝕜 :=
  ∑ i : Fin m,
    (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => 𝕜) 1 (i : ℕ)).comp (EuclideanSpace.proj i)
noncomputable def projinf (m : ℕ) : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m) :=
  ∑ i : Fin m,
    (lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) ∞ (i : ℕ)).smulRight (EuclideanSpace.single i (1 : 𝕜))
noncomputable def proj1 (m : ℕ) : L1 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m) :=
  (projinf m).comp (incl : L1 𝕜 →L[𝕜] Linf 𝕜)
lemma norm_coe_l2_le_norm_l1 (f : L1 𝕜) :
    ‖(lp.linearMapOfLE 𝕜 (fun _ : ℕ => 𝕜) (by norm_num : (1 : ℝ≥0∞) ≤ 2) f : L2 𝕜)‖ ≤ ‖f‖ := by
  set g := (lp.linearMapOfLE 𝕜 (fun _ : ℕ => 𝕜) (by norm_num : (1 : ℝ≥0∞) ≤ 2) f : L2 𝕜)
    with hg
  have hcoord : ∀ i : ℕ, (g : ℕ → 𝕜) i = f i := by
    intro i
    rw [hg]
    exact congrFun (lp.coe_linearMapOfLE_apply _ _) i
  have hsq : ‖g‖ ^ 2 = ∑' i, ‖f i‖ ^ 2 := by
    rw [norm_sq_eq_tsum_norm_sq]
    exact tsum_congr fun i => by rw [hcoord]
  have hle : ∑' i, ‖f i‖ ^ 2 ≤ ‖f‖ ^ 2 :=
    Real.tsum_le_of_sum_range_le (fun _ => by positivity) fun n =>
      calc ∑ i ∈ Finset.range n, ‖f i‖ ^ 2
          ≤ (∑ i ∈ Finset.range n, ‖f i‖) ^ 2 :=
            Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => norm_nonneg _
        _ ≤ ‖f‖ ^ 2 :=
            pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => norm_nonneg _)
              (sum_norm_apply_le_norm_l1 f (Finset.range n)) 2
  nlinarith [norm_nonneg g, norm_nonneg f, hsq, hle]
noncomputable def inclL1L2 : L1 𝕜 →L[𝕜] L2 𝕜 :=
  LinearMap.mkContinuous (lp.linearMapOfLE 𝕜 (fun _ : ℕ => 𝕜)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)) 1 (fun f => by
    rw [one_mul]; exact norm_coe_l2_le_norm_l1 f)
noncomputable def inclL2Linf : L2 𝕜 →L[𝕜] Linf 𝕜 :=
  LinearMap.mkContinuous (lp.linearMapOfLE 𝕜 (fun _ : ℕ => 𝕜) le_top) 1 (fun f => by
    rw [one_mul]; exact norm_coe_linf_le_norm (by norm_num) f)
section Factors
variable (A : L2 𝕜 →L[𝕜] L1 𝕜) (B : Linf 𝕜 →L[𝕜] L2 𝕜)
noncomputable def T1 : L2 𝕜 →L[𝕜] L2 𝕜 := (inclL1L2 : L1 𝕜 →L[𝕜] L2 𝕜).comp A
noncomputable def T2 : L2 𝕜 →L[𝕜] L2 𝕜 := B.comp (inclL2Linf : L2 𝕜 →L[𝕜] Linf 𝕜)
noncomputable def row (j : ℕ) : L2 𝕜 :=
  ContinuousLinearMap.adjoint (T1 A) (lp.single 2 j (1 : 𝕜))
noncomputable def col (j : ℕ) : L2 𝕜 := B (lp.single ∞ j (1 : 𝕜))
noncomputable def trunc (m : ℕ) : L2 𝕜 →L[𝕜] L1 𝕜 :=
  (emb1 m).comp ((proj1 m).comp A)
end Factors
end SNumbers.L1Linf


