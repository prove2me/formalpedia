-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ExtensionSingularValues
-- name    : Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ExtensionSingularValues
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T22:10:51.094466+00:00
-- url     : https://prove2.me/theorems/b129ba92-5ad9-49f9-be02-f443ee491280
-- title:
--   Extension Singular Values
-- statement:
--   Definitions and structural lemmas for Extension Singular Values, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/ExtensionSingularValues.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylPoint
import Theorems.Thm_Formalism_GradedWeylDivisibility_isWH_algHom
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.L2.DIV
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.ExtensionSingularValues
abbrev V (r : ℕ) (μ : Fin r → ℕ) : Type := ↥(dualWeyl ℂ r r μ)
def nrm {r : ℕ} {μ : Fin r → ℕ} (F : V r μ) : ℝ :=
  √((fockS F.1 F.1).re / (fockS (hw ℂ (le_refl r) μ) (hw ℂ (le_refl r) μ)).re)
def subst {n₀ n₁ : ℕ} (h : n₀ ≤ n₁) (x : Matrix (Fin n₁) (Fin n₀) ℂ) :
    MvPolynomial (Fin n₀ × Fin n₀) ℂ →ₐ[ℂ] MvPolynomial (Fin n₁ × Fin n₁) ℂ :=
  aeval fun v => ∑ b : Fin n₁, C (x b v.1) * X (b, Fin.castLE h v.2)
def extZero (n₀ n₁ : ℕ) : (Fin n₀ → ℕ) →+ (Fin n₁ → ℕ) where
  toFun ν := rowNu (r := n₁) ν
  map_zero' := by funext a; simp [rowNu]
  map_add' ν μ := by
    funext a
    by_cases ha : a.val < n₀ <;> simp [rowNu, ha]
theorem extZero_single {n₀ n₁ : ℕ} (h : n₀ ≤ n₁) (s : Fin n₀) :
    extZero n₀ n₁ (Pi.single s 1) = Pi.single (Fin.castLE h s) 1 := by
  funext a
  change rowNu (r := n₁) (Pi.single s 1) a = _
  by_cases ha : a.val < n₀
  · simp only [rowNu, ha, dite_true, Pi.single_apply, Fin.ext_iff, Fin.val_castLE]
  · have : a ≠ Fin.castLE h s := by
      intro e
      apply ha
      rw [e]
      exact s.2
    simp [rowNu, ha, this]
theorem subst_mem {n₀ n₁ : ℕ} (h : n₀ ≤ n₁) (x : Matrix (Fin n₁) (Fin n₀) ℂ) (ν : Fin n₀ → ℕ)
    {F : MvPolynomial (Fin n₀ × Fin n₀) ℂ} (hF : F ∈ dualWeyl ℂ n₀ n₀ ν) :
    subst h x F ∈ dualWeyl ℂ n₁ n₁ (rowNu (r := n₁) ν) := by
  rw [dualWeylPoint] at hF ⊢
  constructor
  · refine isWH_algHom (subst h x) (fun v => extZero n₀ n₁ (colW n₀ n₀ v)) (colW n₁ n₁) ?_ ?_
    · intro v
      rw [subst, aeval_X, colW, extZero_single h]
      exact IsWeightedHomogeneous.sum _ _ _ fun b _ =>
        (isWeightedHomogeneous_X ℂ (colW n₁ n₁) (b, Fin.castLE h v.2)).C_mul _
    · intro m hm
      have h1 := hF.1 hm
      change _ = extZero n₀ n₁ ν
      rw [← h1, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, map_sum]
      simp only [map_nsmul]
  · intro l j hlj c
    by_cases hj : j.val < n₀
    · have hl : l.val < n₀ := lt_trans hlj hj
      have e : (colAdd ℂ l j c).comp (subst h x) =
          (subst h x).comp (colAdd ℂ (⟨l.val, hl⟩ : Fin n₀) ⟨j.val, hj⟩ c) := by
        apply MvPolynomial.algHom_ext
        intro v
        by_cases hv : v.2 = ⟨j.val, hj⟩
        · have h2 : Fin.castLE h v.2 = j := by rw [hv]; rfl
          have h3 : Fin.castLE h (⟨l.val, hl⟩ : Fin n₀) = l := rfl
          simp only [AlgHom.comp_apply, subst, colAdd, aeval_X, map_sum, map_mul, map_add, algHom_C,
            if_pos hv, h2, h3, if_true, algebraMap_eq, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
          refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun b _ => rfl) (Finset.sum_congr rfl fun b _ => ?_)
          ring
        · have h2 : Fin.castLE h v.2 ≠ j := by
            intro e
            have e' : v.2.val = j.val := congrArg (fun z : Fin n₁ => z.val) e
            exact hv (Fin.ext e')
          simp only [AlgHom.comp_apply, subst, colAdd, aeval_X, map_sum, map_mul, algHom_C,
            if_neg hv, if_neg h2, algebraMap_eq]
      have := DFunLike.congr_fun e F
      rw [AlgHom.comp_apply, AlgHom.comp_apply, hF.2 _ _ (by exact hlj) c] at this
      exact this
    · have e : (colAdd ℂ l j c).comp (subst h x) = subst h x := by
        apply MvPolynomial.algHom_ext
        intro v
        have h2 : Fin.castLE h v.2 ≠ j := by
          intro e
          apply hj
          rw [← e]
          exact v.2.2
        simp only [AlgHom.comp_apply, subst, colAdd, aeval_X, map_sum, map_mul, algHom_C,
          if_neg h2, algebraMap_eq]
      exact DFunLike.congr_fun e F
def rho {n₀ n₁ : ℕ} (h : n₀ ≤ n₁) (ν : Fin n₀ → ℕ) (x : Matrix (Fin n₁) (Fin n₀) ℂ) :
    V n₀ ν →ₗ[ℂ] V n₁ (rowNu (r := n₁) ν) :=
  (subst h x).toLinearMap.restrict fun _ hF => subst_mem h x ν hF
def IsOpNorm {r r' : ℕ} {μ : Fin r → ℕ} {μ' : Fin r' → ℕ} (T : V r μ →ₗ[ℂ] V r' μ') (c : ℝ) : Prop :=
  IsLeast {a : ℝ | 0 ≤ a ∧ ∀ F : V r μ, nrm (T F) ≤ a * nrm F} c
def sv {n₀ n₁ : ℕ} (x : Matrix (Fin n₁) (Fin n₀) ℂ) (i : Fin n₀) : ℝ :=
  (Matrix.toEuclideanLin x).singularValues i.val
def OpNormStatement : Prop :=
  ∀ (n₀ n₁ : ℕ) (h : n₀ ≤ n₁) (ν : Fin n₀ → ℕ), Antitone ν → ∀ x : Matrix (Fin n₁) (Fin n₀) ℂ,
    IsOpNorm (rho h ν x) (∏ i, sv x i ^ ν i) ∧
    IsOpNorm (rho h ν (x.map (starRingEnd ℂ))) (∏ i, sv x i ^ ν i)
end GlobalTheory.IndefiniteRowSideFullHecke.ExtensionSingularValues


