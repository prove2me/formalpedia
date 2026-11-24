-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFEqSumOfSubsetB
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_FockFEqSumOfSubsetB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:02.701467+00:00
-- url     : https://prove2.me/theorems/1efc0bac-b1d9-4ddc-af19-e58d34086748
-- title:
--   Fock FEq Sum Of Subset B
-- statement:
--   Definitions and structural lemmas for Fock FEq Sum Of Subset B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinBranching/FockFEqSumOfSubsetB.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinBranching_ExtremalFacts
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ClosedEqNabla
import Theorems.Thm_Formalism_GradedWeylDivisibility_fockHerm
import Theorems.Thm_Formalism_GradedWeylDivisibility_fockPos
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
noncomputable section
namespace PI.WGB
open Formalism.BasicNotions MvPolynomial
theorem fockF_eq_sum_lemma {σ : Type} (f g : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : f.support ⊆ S) :
    Formalism.REAL.fockF f g =
      ∑ m ∈ S, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold Formalism.REAL.fockF
  refine Finset.sum_subset hS fun m _ hm => ?_
  have h0 : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
  simp [h0]
theorem fockF_smul_right_B {σ : Type} (c : ℂ) (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF f (c • g) = star c * Formalism.REAL.fockF f g := by
  unfold Formalism.REAL.fockF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, star_mul']
  ring
theorem fockF_add_left_B {σ : Type} [DecidableEq σ] (f f' g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (f + f') g = Formalism.REAL.fockF f g + Formalism.REAL.fockF f' g := by
  rw [fockF_eq_sum_lemma (f + f') g (f.support ∪ f'.support) MvPolynomial.support_add,
    fockF_eq_sum_lemma f g (f.support ∪ f'.support) Finset.subset_union_left,
    fockF_eq_sum_lemma f' g (f.support ∪ f'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring
theorem fockF_self_re_nonneg_B {σ : Type} (f : MvPolynomial σ ℂ) : 0 ≤ (Formalism.REAL.fockF f f).re := by
  unfold Formalism.REAL.fockF
  rw [Complex.re_sum]
  refine Finset.sum_nonneg fun m _ => ?_
  rw [show star (f.coeff m) = (starRingEnd ℂ) (f.coeff m) from rfl, Complex.mul_conj,
    Complex.re_ofReal_mul, Complex.natCast_re]
  exact mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)
def coreB {N : ℕ} (lam : DomWeight N) : InnerProductSpace.Core ℂ (nablaSq ℂ N lam) where
  inner x y := Formalism.REAL.fockF (y : MvPolynomial (Fin N × Fin N) ℂ) x
  conj_inner_symm x y := by
    show starRingEnd ℂ (Formalism.REAL.fockF (x : MvPolynomial (Fin N × Fin N) ℂ) y) =
      Formalism.REAL.fockF (y : MvPolynomial (Fin N × Fin N) ℂ) x
    rw [starRingEnd_apply, ← Formalism.GradedWeylDivisibility.fockHerm]
  re_inner_nonneg x := fockF_self_re_nonneg_B (x : MvPolynomial (Fin N × Fin N) ℂ)
  add_left x y z := by
    show Formalism.REAL.fockF (z : MvPolynomial (Fin N × Fin N) ℂ)
      ((x + y : nablaSq ℂ N lam) : MvPolynomial (Fin N × Fin N) ℂ) = _
    rw [Submodule.coe_add, Formalism.GradedWeylDivisibility.fockHerm, fockF_add_left_B, star_add, ← Formalism.GradedWeylDivisibility.fockHerm,
      ← Formalism.GradedWeylDivisibility.fockHerm]
  smul_left x y r := by
    show Formalism.REAL.fockF (y : MvPolynomial (Fin N × Fin N) ℂ)
      ((r • x : nablaSq ℂ N lam) : MvPolynomial (Fin N × Fin N) ℂ) = _
    rw [Submodule.coe_smul, fockF_smul_right_B, starRingEnd_apply]
  definite x hx := by
    apply Subtype.ext
    by_contra hne
    have := (Formalism.GradedWeylDivisibility.fockPos _ (x : MvPolynomial (Fin N × Fin N) ℂ) hne).1
    have hx' : Formalism.REAL.fockF (x : MvPolynomial (Fin N × Fin N) ℂ) x = 0 := hx
    rw [hx'] at this; simp at this
def gStarB {N : ℕ} (g : GL (Fin N) ℂ) : GL (Fin N) ℂ where
  val := Matrix.conjTranspose (g : Matrix (Fin N) (Fin N) ℂ)
  inv := Matrix.conjTranspose ((g⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
  val_inv := by rw [← Matrix.conjTranspose_mul]; simp
  inv_val := by rw [← Matrix.conjTranspose_mul]; simp
end PI.WGB


