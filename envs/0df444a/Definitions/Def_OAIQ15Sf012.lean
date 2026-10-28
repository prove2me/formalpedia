-- Prove2me | Definitions.Def_OAIQ15Sf012
-- name    : OAIQ15Sf012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T15:32:21.524955+00:00
-- url     : https://prove2.me/theorems/ff6d6121-07cc-4098-888f-8e98e22fc8c0
-- title:
--   Definitions bundle OAIQ15Sf012 of the split of OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KaplanskyConsequences.stable_finiteness_bundle`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness*, OpenAI Math Release, September 23, 2026, result family 294, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 45 declarations of OpenAI's Lean: 14 definitions, 1 instance and 30 theorems. The definitions and types are `OAI.KaplanskyConsequences.QuasiValue.UltraQuotient`, `OAI.KaplanskyConsequences.QuasiValue.ofDimensionState`, `OAI.KaplanskyConsequences.QuasiValue.seqEvalHom`, `OAI.KaplanskyConsequences.QuasiValue.ultraHom`, `OAI.KaplanskyConsequences.QuasiValue.ultraQ`, `OAI.KaplanskyConsequences.SpectralKernel.FaithfulQuotient`, `OAI.KaplanskyConsequences.SpectralKernel.IsNull`, `OAI.KaplanskyConsequences.SpectralKernel.nullIdeal`, `OAI.KaplanskyConsequences.SpectralKernel.oneByOne`, `OAI.KaplanskyConsequences.SpectralKernel.quotientHom`, `OAI.KaplanskyConsequences.SpectralKernel.single`, `OAI.KaplanskyConsequences.actualFaithfulMap`, `OAI.KaplanskyConsequences.actualFaithfulRepresentation`, `OAI.KaplanskyConsequences.matrixMap`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Kaplansky, in whole or in part: [`Kaplansky_Quotient_MatrixKernel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/Quotient/MatrixKernel.lean), [`Kaplansky_Quotient_NullIdeal`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/Quotient/NullIdeal.lean), [`Kaplansky_Quotient_QuotientStable`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/Quotient/QuotientStable.lean), [`Kaplansky_StableFiniteness_FaithfulRepresentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/StableFiniteness/FaithfulRepresentation.lean), [`Kaplansky_Ultrapower_Construction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/Ultrapower/Construction.lean), [`Kaplansky_Ultrapower_Polar`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/Ultrapower/Polar.lean), [`Kaplansky_Ultrapower_QuasiValue`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/Ultrapower/QuasiValue.lean), [`Kaplansky_Ultrapower_UltraSaturation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/Ultrapower/UltraSaturation.lean), [`Kaplansky_Ultrapower_Unitary`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Kaplansky/Kaplansky/Ultrapower/Unitary.lean).
--
--   **Imports.** It imports the published bundle `Def_KaplanskyStableFiniteness`; the bundles `OAIQ15Sf010` and `OAIQ15Sf011` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.KaplanskyConsequences.QuasiValue.ultra_polar_corner`, `OAI.KaplanskyConsequences.QuasiValue.ultra_unitary_polar` and `OAI.KaplanskyConsequences.actualAlgebra_tensor_properlyInfinite`; the proofs of `OAI.KaplanskyConsequences.QuasiValue.ultra_polar_corner`, `OAI.KaplanskyConsequences.QuasiValue.ultra_unitary_polar`, `OAI.KaplanskyConsequences.actualAlgebra_tensor_properlyInfinite`, `OAI.KaplanskyConsequences.simple_stablyFinite_traceless_exists`, `OAI.KaplanskyConsequences.stable_finiteness_bundle` and `OAI.KaplanskyConsequences.trace_free_stably_finite_exists`.
-- source:
--   OpenAI, A counterexample to Kaplansky's quasitrace conjecture and failure of tensor-product stable finiteness, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 294; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Kaplanskys-quasitrace-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Kaplansky at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_KaplanskyStableFiniteness
import Definitions.Def_OAIQ15Sf010
import Definitions.Def_OAIQ15Sf011

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Quotient_NullIdeal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


namespace KaplanskyConsequences
open scoped Matrix CStarAlgebra ComplexOrder
open Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

namespace SpectralKernel
variable (d : CuntzDimensionState A)

@[simp] lemma val_one (n : ℕ) : val d (1 : Mat A n) = n := by
  rw [val_of_nonneg d zero_le_one]
  exact d.spectralValue_unit n

lemma val_smul {n : ℕ} (r : ℝ) (a : Mat A n) : val d (r • a) = r * val d a :=
  d.signedValue_smul a r

lemma val_square_swap {n : ℕ} (x : Mat A n) :
    val d (x*star x) = val d (star x*x) := by
  rw [val_of_nonneg d (mul_star_self_nonneg x), val_of_nonneg d (star_mul_self_nonneg x)]
  exact d.spectralValue_square_swap x

lemma abs_val_sub_le {n : ℕ} {a b : Mat A n} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |val d a - val d b| ≤ ‖a-b‖ * n := by
  rw [val_of_nonneg d ha, val_of_nonneg d hb]
  exact d.abs_spectralValue_sub_le ha hb

lemma gram_swap {n m : ℕ} (x : Matrix (Fin n) (Fin m) A) :
    val d (CStarMatrix.ofMatrix (x*x.conjTranspose)) =
      val d (CStarMatrix.ofMatrix (x.conjTranspose*x)) := by
  have hx := gram_nonneg x.conjTranspose
  rw [Matrix.conjTranspose_conjTranspose] at hx
  rw [val_of_nonneg d hx, val_of_nonneg d (gram_nonneg x)]
  exact d.spectralValue_rectangular_gram x hx (gram_nonneg x)

lemma weighted_gram_identity {n : ℕ} (a b S T : Mat A n) (r : ℝ)
    (hr : r ≠ 0) (hS : star S = S) (hT : star T = T) (hSS : S*S=a) (hTT : T*T=b) :
    let v := Matrix.fromCols (CStarMatrix.ofMatrix.symm S) (CStarMatrix.ofMatrix.symm T)
    let w := Matrix.fromCols (CStarMatrix.ofMatrix.symm (r • S))
      (CStarMatrix.ofMatrix.symm (-(r⁻¹ • T)))
    v.conjTranspose*v + w.conjTranspose*w =
      cuntzBlock (CStarMatrix.ofMatrix.symm ((1+r^2) • a))
        (CStarMatrix.ofMatrix.symm ((1+r⁻¹^2) • b)) := by
  let v := Matrix.fromCols (CStarMatrix.ofMatrix.symm S) (CStarMatrix.ofMatrix.symm T)
  let w := Matrix.fromCols (CStarMatrix.ofMatrix.symm (r • S))
    (CStarMatrix.ofMatrix.symm (-(r⁻¹ • T)))
  have hm : v.conjTranspose*v + w.conjTranspose*w =
      cuntzBlock (CStarMatrix.ofMatrix.symm ((1+r^2) • a))
        (CStarMatrix.ofMatrix.symm ((1+r⁻¹^2) • b)) := by
    dsimp [v,w]
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.fromRows_mul_fromCols, Matrix.fromRows_mul_fromCols]
    rw [Matrix.fromBlocks_add]
    congr 1
    · change star S*S + star (r • S)*(r • S) = (1+r^2) • a
      simp [hS,hSS,smul_smul,pow_two,add_smul]
    · change star S*T + star (r • S)*(-(r⁻¹ • T)) = 0
      simp [hS,smul_smul,hr]
    · change star T*S + star (-(r⁻¹ • T))*(r • S) = 0
      simp [hT,smul_smul,hr]
    · change star T*T + star (-(r⁻¹ • T))*(-(r⁻¹ • T)) = (1+r⁻¹^2) • b
      simp [hT,hTT,smul_smul,pow_two,add_smul]
  exact hm

attribute [local instance] OAI.KaplanskyConsequences.matRealCFC
attribute [local instance] OAI.KaplanskyConsequences.matNonnegSpectrum
lemma val_add_le {n : ℕ} {a b : Mat A n} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (r : ℝ) (hr : r ≠ 0) :
    val d (a+b) ≤ (1+r^2)*val d a + (1+r⁻¹^2)*val d b := by
  let S := CFC.sqrt a
  let T := CFC.sqrt b
  have hS : star S = S := (CFC.sqrt_nonneg a).isSelfAdjoint.star_eq
  have hT : star T = T := (CFC.sqrt_nonneg b).isSelfAdjoint.star_eq
  have hSS : S*S = a := CFC.sqrt_mul_sqrt_self a ha
  have hTT : T*T = b := CFC.sqrt_mul_sqrt_self b hb
  let v := Matrix.fromCols (CStarMatrix.ofMatrix.symm S) (CStarMatrix.ofMatrix.symm T)
  let w := Matrix.fromCols (CStarMatrix.ofMatrix.symm (r • S))
    (CStarMatrix.ofMatrix.symm (-(r⁻¹ • T)))
  have hv : v*v.conjTranspose = CStarMatrix.ofMatrix.symm (a+b) := by
    dsimp [v]
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromCols_mul_fromRows]
    change S*star S + T*star T = a+b
    rw [hS,hT,hSS,hTT]
  have hm := weighted_gram_identity a b S T r hr hS hT hSS hTT
  let v' := v.submatrix (Equiv.refl _) finSumFinEquiv.symm
  let w' := w.submatrix (Equiv.refl _) finSumFinEquiv.symm
  let p : CuntzPositiveMatrix A := ⟨n, CStarMatrix.ofMatrix.symm ((1+r^2) • a),
    smul_nonneg (show (0:ℝ) ≤ 1+r^2 by positivity) ha⟩
  let q : CuntzPositiveMatrix A := ⟨n, CStarMatrix.ofMatrix.symm ((1+r⁻¹^2) • b),
    smul_nonneg (show (0:ℝ) ≤ 1+r⁻¹^2 by positivity) hb⟩
  have hv' : CStarMatrix.ofMatrix (v'*v'.conjTranspose) = a+b := by
    dsimp [v']
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hv]
    rfl
  have hm' : CStarMatrix.ofMatrix (v'.conjTranspose*v') +
      CStarMatrix.ofMatrix (w'.conjTranspose*w') = CStarMatrix.ofMatrix (p.add q).matrix := by
    dsimp [v',w',p,q,CuntzPositiveMatrix.add]
    simp only [Matrix.conjTranspose_submatrix]
    change CStarMatrix.ofMatrix ((v.conjTranspose*v + w.conjTranspose*w).submatrix _ _) = _
    rw [hm]
    rfl
  have hle : CStarMatrix.ofMatrix (v'.conjTranspose*v') ≤
      CStarMatrix.ofMatrix (p.add q).matrix := by
    rw [← hm']
    exact le_add_of_nonneg_right (gram_nonneg w')
  have h := val_mono d (gram_nonneg v') hle
  rw [← gram_swap d v', hv'] at h
  have h := h.trans_eq (val_of_nonneg d (p.add q).nonneg)
  change val d (a+b) ≤ d.spectralValue (p.add q) at h
  rw [d.spectralValue_add p q] at h
  have hp := val_of_nonneg d (smul_nonneg (show (0:ℝ) ≤ 1+r^2 by positivity) ha)
  have hq := val_of_nonneg d (smul_nonneg (show (0:ℝ) ≤ 1+r⁻¹^2 by positivity) hb)
  change val d ((1+r^2) • a) = d.spectralValue p at hp
  change val d ((1+r⁻¹^2) • b) = d.spectralValue q at hq
  rw [← hp, ← hq, val_smul, val_smul] at h
  exact h

lemma val_add_of_zero {n : ℕ} {a b : Mat A n} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hzero : val d b = 0) : val d (a+b) = val d a := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hpos : 0 < val d a+1 := by linarith [val_nonneg d ha]
    let r := Real.sqrt (ε/(val d a+1))
    have hr : 0 < r := Real.sqrt_pos.2 (div_pos hε hpos)
    have hrsq : r^2 = ε/(val d a+1) := Real.sq_sqrt (le_of_lt (div_pos hε hpos))
    have hmul : r^2*(val d a+1)=ε := by rw [hrsq]; exact div_mul_cancel₀ ε hpos.ne'
    have h := val_add_le d ha hb r hr.ne'
    rw [hzero,mul_zero,add_zero] at h
    nlinarith [sq_nonneg r]
  · exact val_mono d ha (le_add_of_nonneg_right hb)

abbrev IsNull {n : ℕ} (x : Mat A n) : Prop := val d (star x*x) = 0

lemma null_zero (n : ℕ) : IsNull d (0 : Mat A n) := by simp [IsNull]

lemma null_star {n : ℕ} {x : Mat A n} (hx : IsNull d x) : IsNull d (star x) := by
  simpa only [IsNull,star_star,val_square_swap] using hx

lemma null_add {n : ℕ} {x y : Mat A n} (hx : IsNull d x) (hy : IsNull d y) :
    IsNull d (x+y) := by
  have hab : val d (star x*x + star y*y) = 0 := by
    rw [val_add_of_zero d (star_mul_self_nonneg x) (star_mul_self_nonneg y) hy]
    exact hx
  have hle : star (x+y)*(x+y) ≤ (2 : ℝ) • (star x*x + star y*y) := by
    rw [← sub_nonneg]
    convert star_mul_self_nonneg (x-y) using 1
    all_goals try with_reducible_and_instances rfl
    simp only [two_smul,star_sub,star_add]
    noncomm_ring
  apply le_antisymm _ (val_nonneg d (star_mul_self_nonneg _))
  calc val d (star (x+y)*(x+y)) ≤ val d ((2:ℝ) • (star x*x + star y*y)) :=
        val_mono d (star_mul_self_nonneg _) hle
    _ = 0 := by rw [val_smul,hab,mul_zero]

lemma null_smul {n : ℕ} {x : Mat A n} (hx : IsNull d x) (r : ℂ) :
    IsNull d (r • x) := by
  have h : star (r • x)*(r • x) = Complex.normSq r • (star x*x) := by
    rw [star_smul,smul_mul_assoc,mul_smul_comm,smul_smul]
    change ((starRingEnd ℂ) r * r) • (star x*x) = Complex.normSq r • (star x*x)
    rw [← Complex.normSq_eq_conj_mul_self]
    exact Complex.coe_smul _ _
  dsimp [IsNull]
  rw [h,val_smul,hx,mul_zero]

lemma null_mul_left {n : ℕ} {x : Mat A n} (hx : IsNull d x) (a : Mat A n) :
    IsNull d (a*x) := by
  have hle : star (a*x)*(a*x) ≤ ‖a‖^2 • (star x*x) := by
    have h := star_left_conjugate_le_conjugate
      (CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := a)) x
    simp only [mul_assoc,Algebra.algebraMap_eq_smul_one,mul_smul_comm,
      smul_mul_assoc,one_mul] at h
    simp only [star_mul, mul_assoc]
    exact h
  apply le_antisymm _ (val_nonneg d (star_mul_self_nonneg _))
  calc val d (star (a*x)*(a*x)) ≤ val d (‖a‖^2 • (star x*x)) :=
        val_mono d (star_mul_self_nonneg _) hle
    _ = 0 := by rw [val_smul,hx,mul_zero]

lemma null_mul_right {n : ℕ} {x : Mat A n} (hx : IsNull d x) (a : Mat A n) :
    IsNull d (x*a) := by
  simpa only [star_mul,star_star] using null_star d (null_mul_left d (null_star d hx) (star a))

lemma continuous_squareVal (n : ℕ) : Continuous (fun x : Mat A n => val d (star x*x)) := by
  have hc : Continuous (fun x : Mat A n =>
      (⟨star x*x,star_mul_self_nonneg x⟩ : {a : Mat A n // 0 ≤ a})) :=
    (continuous_star.mul continuous_id).subtype_mk _
  simpa only [Function.comp_def,val_of_nonneg d (star_mul_self_nonneg _)] using
    (d.spectralValue_continuous n).comp hc

def nullIdeal (n : ℕ) : ClosedStarIdeal (Mat A n) where
  carrier := {x | IsNull d x}
  zero_mem' := null_zero d n
  add_mem' := null_add d
  smul_mem' := fun r _ hx => null_smul d hx r
  mul_mem' := fun _ hy => null_mul_left d hy _
  star_mem' := null_star d
  mul_mem_left := fun a _ hx => null_mul_left d hx a
  mul_mem_right := fun _ a hx => null_mul_right d hx a
  closed := isClosed_eq (continuous_squareVal d n) continuous_const

end SpectralKernel
end KaplanskyConsequences

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Quotient_MatrixKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


namespace KaplanskyConsequences
open scoped Matrix CStarAlgebra ComplexOrder
open Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]
namespace SpectralKernel
variable (d : CuntzDimensionState A)

def single {n : ℕ} (i j : Fin n) (a : A) : Mat A n :=
  CStarMatrix.ofMatrix fun k l => if k=i ∧ l=j then a else 0

def oneByOne (a : A) : Mat A 1 := CStarMatrix.toOneByOne (Fin 1) ℂ A a

@[simp] lemma oneByOne_apply (a : A) (i j : Fin 1) : oneByOne a i j = a := rfl

@[simp] lemma single_apply {n : ℕ} (i j k l : Fin n) (a : A) :
    single i j a k l = if k=i ∧ l=j then a else 0 := rfl

end SpectralKernel
end KaplanskyConsequences

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Quotient_QuotientStable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


namespace KaplanskyConsequences
open scoped Matrix CStarAlgebra ComplexOrder
open Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def matrixMap (f : A →⋆ₐ[ℂ] B) (n : ℕ) : Mat A n →⋆ₐ[ℂ] Mat B n where
  toFun x := x.map f
  map_zero' := by ext; simp [CStarMatrix.zero_apply]
  map_one' := by
    ext i j
    by_cases h : i=j <;> simp [CStarMatrix.one_apply,h]
  map_add' x y := by ext; simp [CStarMatrix.add_apply,map_add]
  map_mul' x y := by ext; simp [CStarMatrix.mul_apply,map_sum,map_mul]
  commutes' r := by
    ext i j
    by_cases h : i=j
    · simp only [CStarMatrix.map_apply,CStarMatrix.algebraMap_apply,ite_eq_left h]
      exact AlgHomClass.commutes f r
    · simp [CStarMatrix.algebraMap_apply,h]
  map_star' x := by ext; simp [CStarMatrix.star_apply,map_star]

@[simp] lemma matrixMap_apply (f : A →⋆ₐ[ℂ] B) (n : ℕ) (x : Mat A n) (i j : Fin n) :
    matrixMap f n x i j = f (x i j) := rfl

namespace SpectralKernel
variable (d : CuntzDimensionState A)
abbrev FaithfulQuotient := (nullIdeal d 1).Quotient

def quotientHom : A →⋆ₐ[ℂ] FaithfulQuotient d :=
  (nullIdeal d 1).mkStarAlgHom.comp (CStarMatrix.toOneByOne (Fin 1) ℂ A).toStarAlgHom

end SpectralKernel
end KaplanskyConsequences

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_StableFiniteness_FaithfulRepresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences

open scoped InnerProductSpace ENNReal
open Kaplansky

def actualFaithfulMap (a : ActualAlgebra) : ActualRepresentationHilbert →L[ℂ] ActualRepresentationHilbert :=
  lp.mapCLM 2 (fun z => actualRepresentation z a) (norm_nonneg a) (fun z => actualRepresentation_norm z a)

@[simp] lemma actualFaithfulMap_apply (a : ActualAlgebra) (x : ActualRepresentationHilbert) (z : ActualTestIndex) :
    actualFaithfulMap a x z = actualRepresentation z a (x z) := rfl

lemma actualFaithfulMap_star (a : ActualAlgebra) : actualFaithfulMap (star a) = star (actualFaithfulMap a) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro x y
  rw [lp.inner_eq_tsum,lp.inner_eq_tsum]
  apply tsum_congr; intro z
  simp only [actualFaithfulMap_apply,map_star]
  exact (actualRepresentation z a).adjoint_inner_left _ _

def actualFaithfulRepresentation : ActualAlgebra →⋆ₐ[ℂ] (ActualRepresentationHilbert →L[ℂ] ActualRepresentationHilbert) where
  toFun := actualFaithfulMap
  map_zero' := by ext; rfl
  map_one' := by ext; rfl
  map_add' _ _ := by ext; rfl
  map_mul' _ _ := by ext; rfl
  commutes' _ := by ext; rfl
  map_star' := actualFaithfulMap_star


end KaplanskyConsequences

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_QuasiValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences
open scoped ComplexOrder
open Kaplansky SpectralKernel
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

namespace QuasiValue
variable {A : Type*} [CStarAlgebra A]

lemma spectral_commuting_add (d : CuntzDimensionState A) {n : ℕ}
    {a b : Mat A n} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hc : Commute a b) :
    d.signedValue (a+b)=d.signedValue a+d.signedValue b := by
  let τ : OneQuasitrace (Mat A n) :=
    { toFun := d.complexValue
      square_nonneg := d.complexValue_square_nonneg
      square_swap := d.complexValue_square_swap
      real_imag := d.complexValue_real_imag
      abelian_linear := d.complexValue_abelian_linear n }
  have h := τ.map_add ha hb hc
  change d.complexValue (a+b)=d.complexValue a+d.complexValue b at h
  rw [d.complexValue_selfAdjoint (ha.add hb),d.complexValue_selfAdjoint ha,
    d.complexValue_selfAdjoint hb] at h
  exact_mod_cast h

def ofDimensionState (d : CuntzDimensionState A) : QuasiValue A := by
  let e := (CStarMatrix.toOneByOne (Fin 1) ℂ A).toStarAlgHom
  have hn (a : A) : ‖e a‖=‖a‖ :=
    NonUnitalStarAlgHom.norm_map e (CStarMatrix.toOneByOne (Fin 1) ℂ A).injective a
  exact
    { val := fun a => d.signedValue (e a)
      zero := by rw [map_zero]; exact d.signedValue_zero 1
      one := by rw [map_one]; exact_mod_cast val_one d 1
      nonneg := by intro a ha; exact val_nonneg d (map_nonneg e ha)
      mono := by
        intro a b ha hab
        exact val_mono d (map_nonneg e ha) (OrderHomClass.mono e hab)
      smul := by
        intro r a
        change d.signedValue (r • e a)=r*d.signedValue (e a)
        exact d.signedValue_smul _ _
      bound := by
        intro a
        simpa only [Nat.cast_one,mul_one,hn] using d.abs_signedValue_le (e a)
      lipschitz_positive := by
        intro a b ha hb
        have h := abs_val_sub_le d (map_nonneg e ha) (map_nonneg e hb)
        simpa only [← map_sub,Nat.cast_one,mul_one,hn] using h
      square_swap := by
        intro x
        simpa only [map_mul,map_star] using val_square_swap d (e x)
      weighted_add := by
        intro a b ha hb r hr
        simpa only [map_add] using val_add_le d (map_nonneg e ha) (map_nonneg e hb) r hr
      add_commute := by
        intro a b ha hb hc
        simpa only [map_add] using spectral_commuting_add d (ha.map e) (hb.map e) (hc.map e) }

end QuasiValue
end KaplanskyConsequences

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_Construction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open scoped ComplexOrder ENNReal
open Filter Topology
open Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
variable (V : QuasiValue A) {ι : Type*} (u : Ultrafilter ι)

@[simp] lemma ultra_const (a : A) : (V.ultra u).val (constHom (A:=A) (ι:=ι) a)=V.val a := by
  exact tendsto_nhds_unique (V.ultra_val_tendsto u (constHom (A:=A) (ι:=ι) a)) tendsto_const_nhds


end KaplanskyConsequences.QuasiValue

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_UltraSaturation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue
open Filter Topology
open scoped ComplexOrder ENNReal

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
instance seq_nontrivial : Nontrivial (Sequences (A:=A) (ι:=ℕ)) := Kaplansky.boundedProduct_nontrivial

variable (V : QuasiValue A) (u : Ultrafilter ℕ) (hu : (u : Filter ℕ) ≤ atTop)
abbrev UltraQuotient := (V.ultra u).FaithfulQuotient
abbrev ultraHom : Sequences (A:=A) (ι:=ℕ) →⋆ₐ[ℂ] V.UltraQuotient u := (V.ultra u).quotientHom
abbrev ultraQ : V.UltraQuotient u → ℝ := (V.ultra u).quotQ

def seqEvalHom (i : ℕ) : Sequences (A:=A) (ι:=ℕ) →⋆ₐ[ℂ] A where
  toFun a := a i
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl
  commutes' _ := rfl

end KaplanskyConsequences.QuasiValue

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_Polar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open Filter Topology
open scoped ComplexOrder ENNReal
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
variable (V : QuasiValue A) (u : Ultrafilter ℕ) (hu : (u : Filter ℕ) ≤ atTop)

local instance ultraRealSMulComm_p0 :
    SMulCommClass ℝ (V.UltraQuotient u) (V.UltraQuotient u) := Algebra.to_smulCommClass

local instance ultraRealTower_p0 :
    IsScalarTower ℝ (V.UltraQuotient u) (V.UltraQuotient u) := IsScalarTower.right

local instance ultraRealCFC_p0 :
    NonUnitalContinuousFunctionalCalculus ℝ (V.UltraQuotient u) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

local instance ultraNonnegSpectrum_p0 : NonnegSpectrumClass ℝ (V.UltraQuotient u) :=
  CStarAlgebra.instNonnegSpectrumClass


end KaplanskyConsequences.QuasiValue

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_Unitary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open Filter Topology
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
variable (V : QuasiValue A) (u : Ultrafilter ℕ) (hu : (u : Filter ℕ) ≤ atTop)

local instance ultraRealSMulComm_p1 :
    SMulCommClass ℝ (V.UltraQuotient u) (V.UltraQuotient u) := Algebra.to_smulCommClass

local instance ultraRealTower_p1 :
    IsScalarTower ℝ (V.UltraQuotient u) (V.UltraQuotient u) := IsScalarTower.right

local instance ultraRealCFC_p1 :
    NonUnitalContinuousFunctionalCalculus ℝ (V.UltraQuotient u) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

local instance ultraNonnegSpectrum_p1 : NonnegSpectrumClass ℝ (V.UltraQuotient u) :=
  CStarAlgebra.instNonnegSpectrumClass


end KaplanskyConsequences.QuasiValue

end

end OAI
end


