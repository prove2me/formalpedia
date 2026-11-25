-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ProdProofB
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_ProdProofB
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T12:41:38.826407+00:00
-- url     : https://prove2.me/theorems/a9bc97ca-d9a4-48c7-9af9-48ab84d0bbf6
-- title:
--   Prod Proof B
-- statement:
--   Definitions and structural lemmas for Prod Proof B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/ProdProofB.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ProdProofA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply


set_option autoImplicit false
namespace ReciprocityTheory.AnForm.M
open MeasureTheory Filter Topology FinHolAtlas
open scoped ContDiff
noncomputable section
variable {e e' : ℕ}
def appME (e e' : ℕ) : ((Fin e → ℂ) × (Fin e' → ℂ)) ≃ᵐ (Fin (e + e') → ℂ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin e ⊕ Fin e' => ℂ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ => ℂ) finSumFinEquiv)
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
theorem pp_source (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (j : Fin A.n) (k : Fin B.n) :
    (prodChart A B j k).source = (A.chart j).source ×ˢ (B.chart k).source := by
  simp [prodChart]
theorem pp_target (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (j : Fin A.n) (k : Fin B.n) :
    (prodChart A B j k).target =
      (appendCLE e e').symm ⁻¹' ((A.chart j).target ×ˢ (B.chart k).target) := by
  simp [prodChart]
theorem pp_mem_target (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (j : Fin A.n) (k : Fin B.n)
    (y : Fin (e + e') → ℂ) :
    y ∈ (prodChart A B j k).target ↔ pr1L y ∈ (A.chart j).target ∧ pr2L y ∈ (B.chart k).target := by
  rw [pp_target]; rfl
theorem contDiffOn_comp_pr1L {f : (Fin e → ℂ) → ℝ} {s : Set (Fin e → ℂ)} {t : Set (Fin (e + e') → ℂ)}
    (hf : ContDiffOn ℝ ∞ f s) (ht : ∀ y ∈ t, pr1L y ∈ s) : ContDiffOn ℝ ∞ (fun y => f (pr1L y)) t :=
  hf.comp ((pr1L (e := e) (e' := e')).contDiff.restrict_scalars ℝ).contDiffOn ht
theorem contDiffOn_comp_pr2L {f : (Fin e' → ℂ) → ℝ} {s : Set (Fin e' → ℂ)} {t : Set (Fin (e + e') → ℂ)}
    (hf : ContDiffOn ℝ ∞ f s) (ht : ∀ y ∈ t, pr2L y ∈ s) : ContDiffOn ℝ ∞ (fun y => f (pr2L y)) t :=
  hf.comp ((pr2L (e := e) (e' := e')).contDiff.restrict_scalars ℝ).contDiffOn ht
theorem tsupport_prod_mul_subset (a : X → ℝ) (b : Y → ℝ) :
    tsupport (fun p : X × Y => a p.1 * b p.2) ⊆ tsupport a ×ˢ tsupport b := by
  apply closure_minimal _ ((isClosed_tsupport a).prod (isClosed_tsupport b))
  intro p hp
  simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hp
  exact ⟨subset_tsupport _ hp.1, subset_tsupport _ hp.2⟩
def prodPartition (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (P : ChartPartition A)
    (Q : ChartPartition B) : ChartPartition (prodAtlas A B) where
  χ i p := P.χ (finProdFinEquiv.symm i).1 p.1 * Q.χ (finProdFinEquiv.symm i).2 p.2
  smooth i i' := by
    show ContDiffOn ℝ ∞ (fun y => P.χ (finProdFinEquiv.symm i).1
        ((A.chart (finProdFinEquiv.symm i').1).symm (pr1L y)) *
      Q.χ (finProdFinEquiv.symm i).2 ((B.chart (finProdFinEquiv.symm i').2).symm (pr2L y))) _
    refine (contDiffOn_comp_pr1L (P.smooth _ _) ?_).mul (contDiffOn_comp_pr2L (Q.smooth _ _) ?_)
    · exact fun y hy => ⟨((pp_mem_target A B (finProdFinEquiv.symm i').1
        (finProdFinEquiv.symm i').2 y).1 hy.1).1, trivial⟩
    · exact fun y hy => ⟨((pp_mem_target A B (finProdFinEquiv.symm i').1
        (finProdFinEquiv.symm i').2 y).1 hy.1).2, trivial⟩
  nonneg i p := mul_nonneg (P.nonneg _ _) (Q.nonneg _ _)
  tsupport_subset i := by
    refine (tsupport_prod_mul_subset _ _).trans ?_
    show _ ⊆ (prodChart A B _ _).source
    rw [pp_source]
    exact Set.prod_mono (P.tsupport_subset _) (Q.tsupport_subset _)
  sum_eq_one p := by
    show ∑ j : Fin (A.n * B.n), P.χ (finProdFinEquiv.symm j).1 p.1 * Q.χ (finProdFinEquiv.symm j).2 p.2 = 1
    rw [← finProdFinEquiv.sum_comp]
    simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]
    rw [← Finset.sum_mul_sum, P.sum_eq_one, Q.sum_eq_one, one_mul]
def onePartition {b : ℕ} (U : Set (Fin b → ℂ)) (hU : IsOpen U) (hne : U.Nonempty) :
    ChartPartition (openAtlas U hU hne) where
  χ _ _ := 1
  smooth _ _ := contDiffOn_const
  nonneg _ _ := zero_le_one
  tsupport_subset _ := fun x _ => Set.mem_univ x
  sum_eq_one _ := by
    show ∑ _j : Fin 1, (1 : ℝ) = 1
    simp
instance openAtlas_subsingleton {b : ℕ} (U : Set (Fin b → ℂ)) (hU : IsOpen U) (hne : U.Nonempty) :
    Subsingleton (Fin (openAtlas U hU hne).n) :=
  inferInstanceAs (Subsingleton (Fin 1))
end
end ReciprocityTheory.AnForm.M


