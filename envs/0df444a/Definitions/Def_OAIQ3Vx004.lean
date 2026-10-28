-- Prove2me | Definitions.Def_OAIQ3Vx004
-- name    : OAIQ3Vx004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T06:31:21.604766+00:00
-- url     : https://prove2.me/theorems/72f5663f-4d2f-46f5-ad29-5bd86406b4b1
-- title:
--   Definitions bundle OAIQ3Vx004 of the split of OpenAI, Strongly rational unitary vertex operator algebras and conformal nets
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinimalVertex.main`, carved from OpenAI's openai/math development (OpenAI, *Strongly rational unitary vertex operator algebras and conformal nets*, OpenAI Math Release, September 25, 2026, result family 280, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 219 declarations of OpenAI's Lean: 21 definitions and 198 theorems. The definitions and types are `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.mobiusLocalIsometry`, `OAI.StronglyRationalVOA.CFTTypeVOA.lowerVirasoroSpace`, `OAI.StronglyRationalVOA.CFTTypeVOA.mobiusGenerator`, `OAI.StronglyRationalVOA.CFTTypeVOA.normalLeft`, `OAI.StronglyRationalVOA.CFTTypeVOA.normalRightHigh`, `OAI.StronglyRationalVOA.CFTTypeVOA.normalRightLow`, `OAI.StronglyRationalVOA.CFTTypeVOA.positiveColumnNorm`, `OAI.StronglyRationalVOA.CFTTypeVOA.primarySpace`, `OAI.StronglyRationalVOA.CFTTypeVOA.rawSharpMajorant`, `OAI.StronglyRationalVOA.CFTTypeVOA.sharpColumnQuantity`, `OAI.StronglyRationalVOA.CFTTypeVOA.sharpDegreeGrowthSubmodule`, `OAI.StronglyRationalVOA.CFTTypeVOA.sharpGrowthSubmodule`, `OAI.StronglyRationalVOA.CFTTypeVOA.sharpMajorant`, `OAI.StronglyRationalVOA.CFTTypeVOA.sharpZeroQuantity`, `OAI.StronglyRationalVOA.CFTTypeVOA.zeroGrowthSubmodule`, `OAI.StronglyRationalVOA.CFTTypeVOA.zeroModeCutoffNorm`, `OAI.StronglyRationalVOA.CFTTypeVOA.zeroModeOnCutoff`, `OAI.StronglyRationalVOA.ClosedGraphData.diagonalAction`, `OAI.StronglyRationalVOA.ClosedGraphData.doubleUnitary`, `OAI.StronglyRationalVOA.HilbertScale.regularized`, `OAI.StronglyRationalVOA.PositiveCircleGeometry.Field.flattening`.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory/VertexAlgebra, in whole or in part: `VertexAlgebra_AdjointMass`, `VertexAlgebra_ApproximatingFlowDerivative`, `VertexAlgebra_BlockGrowth`, `VertexAlgebra_BoundedMultiplierSingle`, `VertexAlgebra_CoefficientDifferentiated`, `VertexAlgebra_CoefficientSummableBound`, `VertexAlgebra_ColumnControl`, `VertexAlgebra_ConstrainedSquareBound`, `VertexAlgebra_CutoffPowerControl`, `VertexAlgebra_EnergyCutoff`, `VertexAlgebra_EnergyShiftPow`, `VertexAlgebra_FiniteSums`, `VertexAlgebra_GeneratorSharpGrowth`, `VertexAlgebra_GeometryContinuation`, `VertexAlgebra_GradeComponentC`, `VertexAlgebra_GraphCommutants`, `VertexAlgebra_GraphInvariantOf`, `VertexAlgebra_HighFieldGraph`, `VertexAlgebra_HilbertCore`, `VertexAlgebra_HilbertRegularization`, `VertexAlgebra_InverseEnergySelf`, `VertexAlgebra_LocalNormalMap`, `VertexAlgebra_Locality`, `VertexAlgebra_LoweringNormSq`, `VertexAlgebra_PrimaryStressWeak`, `VertexAlgebra_RegularizerFactorAdd`, `VertexAlgebra_SmoothSmearShift`, `VertexAlgebra_SmoothTopology`, `VertexAlgebra_StressCutoffNormalized2`, `VertexAlgebra_StressPropagatorDerivative`, `VertexAlgebra_StressSmoothness`, `VertexAlgebra_VirasoroLinearEnergy`.
--
--   **Imports.** It imports the published bundle `Def_VertexAlgebraNet`; the bundles `OAIQ3Vx000`, `OAIQ3Vx001` and `OAIQ3Vx002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ3Vx006` and `OAIQ3Vx007`.
-- source:
--   OpenAI, Strongly rational unitary vertex operator algebras and conformal nets, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 280; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strongly-rational-unitary-vertex-operator-algebras-and-conformal-nets-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory/VertexAlgebra at commit adc7f12

import Mathlib
import Definitions.Def_VertexAlgebraNet
import Definitions.Def_OAIQ3Vx000
import Definitions.Def_OAIQ3Vx001
import Definitions.Def_OAIQ3Vx002

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_FiniteSums
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section



 

namespace StronglyRationalVOA

universe u v



section Algebraic

variable {V : Type u} [AddCommGroup V] [Module ℂ V]



namespace VertexAlgebra

variable (A : VertexAlgebra V)



theorem mode_normal_product_hasFiniteSupport (a b c : V) (k : ℤ) :
    (Function.support fun j : ℕ =>
        mode A.fields a (-1 - j) (mode A.fields b (k + j) c) +
        mode A.fields b (k - 1 - j) (mode A.fields a j c)).Finite := by
  have h₁ := mode_shift_hasFiniteSupport A.fields b c k
  have h₂ := mode_shift_hasFiniteSupport A.fields a c 0
  apply (h₁.union h₂).subset
  intro j hj
  by_contra h
  have he₁ : mode A.fields b (k + j) c = 0 := by
    by_contra hn
    exact h (Or.inl hn)
  have he₂ : mode A.fields a j c = 0 := by
    by_contra hn
    apply h
    right
    change mode A.fields a (0 + j) c ≠ 0
    simpa only [zero_add] using hn
  exact hj (by simp only [he₁, he₂, map_zero, add_zero])



end VertexAlgebra
end Algebraic
end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_GradeComponentC
attribute [-instance] _root_.OAI.StronglyRationalVOA.CFTTypeVOA.energyCutoff_finite _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
section Algebraic
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
namespace CFTTypeVOA
variable (A : CFTTypeVOA V)



def lowerVirasoroSpace (d : ℕ) : Submodule ℂ V :=
  ⨆ n : Fin d, (A.grade (d - (n.val + 1))).map (A.virasoroMode (-(n.val + 1 : ℤ)))

theorem lowerVirasoroSpace_le_grade (d : ℕ) : A.lowerVirasoroSpace d ≤ A.grade d := by
  apply iSup_le
  intro n x hx
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx
  exact A.virasoro_mem_grade ha (-(n.val + 1 : ℤ)) (by have := n.isLt; omega)

theorem virasoro_mem_lowerVirasoroSpace {d n : ℕ} (hn : 0 < n) (hnd : n ≤ d)
    {a : V} (ha : a ∈ A.grade (d - n)) :
    A.virasoroMode (-(n : ℤ)) a ∈ A.lowerVirasoroSpace d := by
  let i : Fin d := ⟨n - 1, by omega⟩
  have hi : i.val + 1 = n := by dsimp [i]; omega
  have hei : (i.val + 1 : ℤ) = n := by omega
  apply Submodule.mem_iSup_of_mem i
  rw [hi, hei]
  exact Submodule.mem_map.mpr ⟨a, ha, rfl⟩



theorem normalProduct_mem_grade {d : ℕ} {a : V} (ha : a ∈ A.grade d) :
    mode A.fields a (-1) a ∈ A.grade (2 * d) :=
  A.mode_mem_grade ha ha (-1) (by omega)


end CFTTypeVOA

end Algebraic



end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_BlockGrowth
attribute [-instance] _root_.OAI.StronglyRationalVOA.CFTTypeVOA.energyCutoff_finite _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)



theorem selfCommutator_eq_sum_reduced {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hd : 1 ≤ d) (m : ℕ) (v : V) :
    A.selfCommutator a d m v =
      ∑ j ∈ Finset.range (2 * d - 1),
        (((m + d - 1).choose (j + 1) : ℂ) - ((d - 1).choose (j + 1) : ℂ)) •
          A.physicalMode (mode A.fields a (j + 1) a) (2 * d - j - 2) 0 v := by
  have hzero := A.selfCommutator_eq_sum ha hd 0 v
  simp only [selfCommutator_apply, Nat.cast_zero, neg_zero, sub_self, zero_add] at hzero
  have he : 2 * d = (2 * d - 1) + 1 := by omega
  calc
    _ = (∑ j ∈ Finset.range (2 * d), ((m + d - 1).choose j : ℂ) •
          A.physicalMode (mode A.fields a j a) (2 * d - j - 1) 0 v) -
        ∑ j ∈ Finset.range (2 * d), ((d - 1).choose j : ℂ) •
          A.physicalMode (mode A.fields a j a) (2 * d - j - 1) 0 v := by
      rw [A.selfCommutator_eq_sum ha hd, ← hzero, sub_zero]
    _ = ∑ j ∈ Finset.range (2 * d),
        (((m + d - 1).choose j : ℂ) - ((d - 1).choose j : ℂ)) •
          A.physicalMode (mode A.fields a j a) (2 * d - j - 1) 0 v := by
      rw [← Finset.sum_sub_distrib]
      simp only [sub_smul]
    _ = _ := by
      rw [he, Finset.sum_range_succ']
      simp only [Nat.choose_zero_right, Nat.cast_one, sub_self, zero_smul, add_zero]
      apply Finset.sum_congr rfl
      intro j _
      congr 3



end CFTTypeVOA
end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_LoweringNormSq
attribute [-instance] _root_.OAI.StronglyRationalVOA.CFTTypeVOA.energyCutoff_finite _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U


theorem norm_sq_eq_sum_grades (a : V) :
    ‖a‖ ^ 2 = ∑ d ∈ A.gradeSupport a, ‖A.gradeComponent d a‖ ^ 2 := by
  have h := U.grade_orthogonalFamily.norm_sum (fun d => A.gradingEquiv a d)
    (A.gradeSupport a)
  change ‖∑ d ∈ A.gradeSupport a, A.gradeComponent d a‖ ^ 2 =
    ∑ d ∈ A.gradeSupport a, ‖A.gradeComponent d a‖ ^ 2 at h
  rwa [A.sum_gradeComponents] at h


end UnitaryStructure
end CFTTypeVOA
end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_VirasoroLinearEnergy
attribute [-instance] _root_.OAI.StronglyRationalVOA.CFTTypeVOA.energyCutoff_finite _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U



theorem normal_product_quadratic {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a) (b : V) :
    (inner ℂ (mode A.fields (mode A.fields a (-1) a) (2 * (d : ℤ) - 1) b) b).re =
      ∑ᶠ j : ℕ,
        (‖A.physicalMode a d (d + j) b‖ ^ 2 +
         ‖A.physicalMode a d (j + 1 - d) b‖ ^ 2) := by
  let Q : V →+ ℝ :=
    { toFun := fun x => (inner ℂ x b).re
      map_zero' := by simp
      map_add' := by intro x y; simp }
  change Q _ = _
  rw [A.mode_normal_product,
    Q.map_finsum (A.mode_normal_product_hasFiniteSupport a a b (2 * (d : ℤ) - 1))]
  apply finsum_congr
  intro j
  have h₁ : mode A.fields a (-1 - j) = A.physicalMode a d (-(d + (j : ℤ))) := by
    dsimp [physicalMode]
    congr 1
    omega
  have h₂ : mode A.fields a (2 * (d : ℤ) - 1 + j) = A.physicalMode a d (d + j) := by
    dsimp [physicalMode]
    congr 1
    omega
  have h₃ : mode A.fields a (2 * (d : ℤ) - 1 - 1 - j) =
      A.physicalMode a d (-(j + 1 - d)) := by
    dsimp [physicalMode]
    congr 1
    omega
  have h₄ : mode A.fields a j = A.physicalMode a d (j + 1 - d) := by
    dsimp [physicalMode]
    congr 1
    omega
  dsimp [Q]
  rw [inner_add_left, Complex.add_re, h₁, h₂, h₃, h₄,
    U.physicalMode_adjoint ha hq hh (-(d + j)),
    U.physicalMode_adjoint ha hq hh (-(j + 1 - d))]
  simp only [neg_neg]
  exact congrArg₂ (· + ·) (inner_self_eq_norm_sq (𝕜 := ℂ) _) (inner_self_eq_norm_sq (𝕜 := ℂ) _)

omit U in
 

theorem normal_product_norms_hasFiniteSupport (a b : V) (d : ℕ) :
    Function.HasFiniteSupport (fun j : ℕ =>
        ‖A.physicalMode a d (d + j) b‖ ^ 2 +
        ‖A.physicalMode a d (j + 1 - d) b‖ ^ 2) := by
  have h₁ := mode_shift_hasFiniteSupport A.fields a b (2 * (d : ℤ) - 1)
  have h₂ := mode_shift_hasFiniteSupport A.fields a b 0
  apply (h₁.union h₂).subset
  intro j hj
  by_contra h
  have he₁ : mode A.fields a (2 * (d : ℤ) - 1 + j) b = 0 := by
    by_contra hn
    exact h (Or.inl hn)
  have he₂ : mode A.fields a (0 + j) b = 0 := by
    by_contra hn
    exact h (Or.inr hn)
  apply hj
  change ‖mode A.fields a (d + j + d - 1) b‖ ^ 2 +
        ‖mode A.fields a (j + 1 - d + d - 1) b‖ ^ 2 = 0
  rw [show (d : ℤ) + j + d - 1 = 2 * d - 1 + j by omega,
    show (j : ℤ) + 1 - d + d - 1 = 0 + j by omega, he₁, he₂]
  simp

 

theorem positive_column {a : V} {d : ℕ} (hd : 1 ≤ d) (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a) (b : V) :
    (∑ᶠ m : ℕ, ‖A.physicalMode a d m b‖ ^ 2) ≤
      (inner ℂ (mode A.fields (mode A.fields a (-1) a) (2 * (d : ℤ) - 1) b) b).re := by
  rw [U.normal_product_quadratic ha hq hh]
  have hf : Function.HasFiniteSupport (fun m : ℕ => ‖A.physicalMode a d m b‖ ^ 2) := by
    have h := mode_shift_hasFiniteSupport A.fields a b ((d : ℤ) - 1)
    have h' := Function.HasFiniteSupport.comp h (g := fun x : V => ‖x‖ ^ 2) (by simp)
    have he (m : ℕ) : (m : ℤ) + d - 1 = d - 1 + m := by omega
    simpa only [Function.comp_def, physicalMode, he] using h' 
  have hg := normal_product_norms_hasFiniteSupport (A := A) a b d
  rw [← tsum_eq_finsum (L := SummationFilter.unconditional ℕ) hf,
    ← tsum_eq_finsum (L := SummationFilter.unconditional ℕ) hg]
  apply Summable.tsum_le_tsum_of_inj (fun m => m + (d - 1))
    (by intro x y h; dsimp at h; omega) (by intro i hi; positivity) _
    (summable_of_hasFiniteSupport hf) (summable_of_hasFiniteSupport hg)
  intro m
  have he : ((m + (d - 1) : ℕ) : ℤ) + 1 - d = m := by omega
  rw [he]
  exact le_add_of_nonneg_left (sq_nonneg _)



end UnitaryStructure
end CFTTypeVOA
end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_EnergyShiftPow
attribute [-instance] _root_.OAI.StronglyRationalVOA.CFTTypeVOA.energyCutoff_finite _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U



theorem primary_decomposition {d : ℕ} {a : V} (ha : a ∈ A.grade d) :
    ∃ q ∈ A.grade d, A.IsPrimary q ∧ ∃ y ∈ A.lowerVirasoroSpace d, a = q + y := by
  let K := A.lowerVirasoroSpace d
  let := A.grade_finite d
  have : FiniteDimensional ℂ K :=
    Submodule.finiteDimensional_of_le (A.lowerVirasoroSpace_le_grade d)
  obtain ⟨y, hy, q, hq, hayq⟩ := K.exists_add_mem_mem_orthogonal a
  have hygrade := A.lowerVirasoroSpace_le_grade d hy
  have hqgrade : q ∈ A.grade d := by
    have he : q = a - y := by rw [hayq]; abel
    rw [he]
    exact (A.grade d).sub_mem ha hygrade
  have hp : A.IsPrimary q := by
    intro n hn
    by_cases hnd : n ≤ d
    · have hLq : A.virasoroMode n q ∈ A.grade (d - n) :=
        A.virasoro_mem_grade hqgrade n (by omega)
      have hmem : A.virasoroMode (-(n : ℤ)) (A.virasoroMode n q) ∈ K :=
        A.virasoro_mem_lowerVirasoroSpace hn hnd hLq
      apply (inner_self_eq_zero (𝕜 := ℂ)).mp
      have h := (K.mem_orthogonal q).mp hq _ hmem
      simpa only [U.virasoro_adjoint, neg_neg] using h
    · exact A.virasoro_eq_zero_of_lt hqgrade n (by omega)
  exact ⟨q, hqgrade, hp, y, hy, hayq.trans (add_comm _ _)⟩



end UnitaryStructure

end CFTTypeVOA

end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_EnergyCutoff
attribute [-instance] _root_.OAI.StronglyRationalVOA.CFTTypeVOA.energyCutoff_finite _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

theorem grade_le_energyCutoff {d N : ℕ} (h : d ≤ N) : A.grade d ≤ A.energyCutoff N := by
  intro v hv e he
  exact A.gradeComponent_of_mem_ne (by omega) hv

theorem exists_energyCutoff (v : V) : ∃ N, v ∈ A.energyCutoff N := by
  classical
  refine ⟨(A.gradeSupport v).sup id, ?_⟩
  intro d hd
  have hn : d ∉ A.gradeSupport v := fun h => (not_le.mpr hd) (Finset.le_sup (f := id) h)
  have hz : A.gradingEquiv v d = 0 := DFinsupp.notMem_support_iff.mp hn
  exact congrArg Subtype.val hz


namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U

 
theorem energyShift_pow_norm_on_cutoff {N : ℕ} {v : V}
    (hv : v ∈ A.energyCutoff N) (r : ℕ) :
    ‖(A.energyShift ^ r) v‖ ≤ (1 + (N : ℝ))^r * ‖v‖ := by
  classical
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [U.energy_norm_sq_eq_sum_grades, mul_pow, U.norm_sq_eq_sum_grades, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  have hdN : d ≤ N := by
    by_contra h
    have hz := hv d (by omega)
    have hne : A.gradingEquiv v d ≠ 0 := DFinsupp.mem_support_iff.mp hd
    apply hne
    exact Subtype.ext hz
  have hdR : (d : ℝ) ≤ N := by exact_mod_cast hdN
  rw [mul_pow]
  gcongr

end UnitaryStructure

 

def mobiusGenerator : Module.End ℂ V :=
  (2 : ℂ)⁻¹ • (A.virasoroMode 1 - A.virasoroMode (-1))

theorem mobiusGenerator_mem_energyCutoff {N : ℕ} {v : V}
    (hv : v ∈ A.energyCutoff N) :
    A.mobiusGenerator v ∈ A.energyCutoff (N + 1) := by
  classical
  rw [← A.sum_gradeComponents v, map_sum]
  apply Submodule.sum_mem
  intro e he
  have heN : e ≤ N := by
    by_contra h
    have hz := hv e (by omega)
    exact (DFinsupp.mem_support_iff.mp he) (Subtype.ext hz)
  apply Submodule.smul_mem
  apply Submodule.sub_mem
  · by_cases he0 : e = 0
    · rw [A.virasoro_eq_zero_of_lt (A.gradeComponent_mem e v) 1 (by omega)]
      exact Submodule.zero_mem _
    · apply A.grade_le_energyCutoff (d := e - 1) (by omega)
      exact A.virasoro_mem_grade (A.gradeComponent_mem e v) 1 (by omega)
  · apply A.grade_le_energyCutoff (d := e + 1) (by omega)
    exact A.virasoro_mem_grade (A.gradeComponent_mem e v) (-1) (by omega)

theorem mobiusGenerator_pow_mem_energyCutoff {N : ℕ} {v : V}
    (hv : v ∈ A.energyCutoff N) (n : ℕ) :
    (A.mobiusGenerator ^ n) v ∈ A.energyCutoff (N + n) := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    simpa only [pow_succ', Module.End.mul_apply, Nat.add_assoc] using
      A.mobiusGenerator_mem_energyCutoff ih

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U

 
theorem mobiusGenerator_skew (v w : V) :
    inner ℂ (A.mobiusGenerator v) w = - inner ℂ v (A.mobiusGenerator w) := by
  simp only [mobiusGenerator, LinearMap.smul_apply, LinearMap.sub_apply,
    inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
    U.virasoro_adjoint, neg_neg, map_inv₀, map_ofNat]
  ring

 
theorem mobiusGenerator_norm_cutoff {N : ℕ} {v : V}
    (hv : v ∈ A.energyCutoff N) :
    ‖A.mobiusGenerator v‖ ≤
      (8 * (1 + A.centralCharge.re)) * (1 + (N : ℝ)) * ‖v‖ := by
  have hc := U.centralCharge_nonneg.2
  have hpos := U.virasoro_linear_energy 1 v
  have hneg := U.virasoro_linear_energy (-1) v
  norm_num only [Int.cast_one, Int.cast_neg, abs_one, abs_neg, one_add_one_eq_two,
    Nat.reducePow] at hpos hneg
  have hE := U.energyShift_pow_norm_on_cutoff hv 1
  simp only [pow_one] at hE
  calc
    _ = (1 / 2 : ℝ) * ‖A.virasoroMode 1 v - A.virasoroMode (-1) v‖ := by
      simp [mobiusGenerator, norm_smul]
    _ ≤ 1 * (‖A.virasoroMode 1 v‖ + ‖A.virasoroMode (-1) v‖) :=
      mul_le_mul (by norm_num) (norm_sub_le _ _) (norm_nonneg _) (by norm_num)
    _ ≤ 8 * (1 + A.centralCharge.re) * ‖A.energyShift v‖ := by linarith
    _ ≤ _ := by
      calc
        _ ≤ 8 * (1 + A.centralCharge.re) * ((1 + (N : ℝ)) * ‖v‖) := by gcongr
        _ = _ := by ring

 
theorem mobiusGenerator_pow_norm {N : ℕ} {v : V} (hv : v ∈ A.energyCutoff N) (n : ℕ) :
    ‖(A.mobiusGenerator ^ n) v‖ ≤
      (8 * (1 + A.centralCharge.re))^n * ((N + 1).ascFactorial n : ℝ) * ‖v‖ := by
  have hc := U.centralCharge_nonneg.2
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    calc
      _ ≤ (8 * (1 + A.centralCharge.re)) * (1 + ((N + n : ℕ) : ℝ)) *
          ‖(A.mobiusGenerator ^ n) v‖ :=
        U.mobiusGenerator_norm_cutoff (A.mobiusGenerator_pow_mem_energyCutoff hv n)
      _ ≤ (8 * (1 + A.centralCharge.re)) * (1 + ((N + n : ℕ) : ℝ)) *
          ((8 * (1 + A.centralCharge.re))^n * ((N + 1).ascFactorial n : ℝ) * ‖v‖) := by
        gcongr
      _ = _ := by rw [Nat.ascFactorial_succ, pow_succ]; push_cast; ring

 

theorem summable_norm_mobiusEvolutionTerm {t : ℝ}
    (ht : 2 * |t| * (8 * (1 + A.centralCharge.re)) < 1) (v : V) :
    Summable (fun n => ‖LocalSkewFlow.skewExpTerm A.mobiusGenerator t n v‖) := by
  obtain ⟨N, hN⟩ := A.exists_energyCutoff v
  exact LocalSkewFlow.summable_norm_skewExpTerm _
    (by have hc := U.centralCharge_nonneg.2; positivity)
    (U.mobiusGenerator_pow_norm hN) ht



def mobiusLocalIsometry (t : ℝ)
    (ht : 2 * |t| * (8 * (1 + A.centralCharge.re)) < 1) :
    V →ₗᵢ[ℂ] UniformSpace.Completion V where
  toFun := LocalSkewFlow.skewExp A.mobiusGenerator t
  map_add' v w := LocalSkewFlow.skewExp_add _ t v w
    (U.summable_norm_mobiusEvolutionTerm ht v) (U.summable_norm_mobiusEvolutionTerm ht w)
  map_smul' z v := LocalSkewFlow.skewExp_smul _ t z v
  norm_map' v := LocalSkewFlow.norm_skewExp _ U.mobiusGenerator_skew t v
    (U.summable_norm_mobiusEvolutionTerm ht v)

end UnitaryStructure

 
theorem virasoro_one_physical_commutator {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (m : ℤ) :
    A.virasoroMode 1 * A.physicalMode a d m - A.physicalMode a d m * A.virasoroMode 1 =
      ((d : ℂ) - 1 - m) • A.physicalMode a d (m + 1) := by
  ext v
  have h := A.mode_commutator_nat A.conformalVector a v 2 (m + (d : ℤ) - 1)
  have h0 : mode A.fields A.conformalVector 0 a = A.toVertexAlgebra.translation a :=
    by rw [A.conformal_translation]
  have h1 : mode A.fields A.conformalVector 1 a = (d : ℂ) • a :=
    A.virasoro_zero_on_grade ha
  have h2 : mode A.fields A.conformalVector 2 a = 0 := hq
  have ht := congrArg (fun f : Module.End ℂ V => f v)
    (A.translation_covariance a (m + d + 1))
  simp only [LinearMap.smul_apply] at ht
  norm_num [Finset.sum_range_succ, h0, h1, h2, mode_zero, mode_smul] at h
  rw [show (2 : ℤ) + (m + d - 1) = m + d + 1 by omega] at h
  rw [ht] at h
  simp only [show m + (d : ℤ) + 1 - 1 = m + d by omega] at h
  change A.virasoroMode 1 (A.physicalMode a d m v) -
    A.physicalMode a d m (A.virasoroMode 1 v) =
      ((d : ℂ) - 1 - m) • A.physicalMode a d (m + 1) v
  change mode A.fields A.conformalVector 2 (mode A.fields a (m + d - 1) v) -
    mode A.fields a (m + d - 1) (mode A.fields A.conformalVector 2 v) =
      ((d : ℂ) - 1 - m) • mode A.fields a (m + 1 + d - 1) v
  rw [show m + 1 + (d : ℤ) - 1 = m + d by omega, h]
  push_cast
  module

 
theorem virasoro_neg_one_physical_commutator (a : V) (d : ℕ) (m : ℤ) :
    A.virasoroMode (-1) * A.physicalMode a d m -
      A.physicalMode a d m * A.virasoroMode (-1) =
        (-((d : ℂ) - 1 + m)) • A.physicalMode a d (m - 1) := by
  ext v
  have h := A.mode_commutator_nat A.conformalVector a v 0 (m + (d : ℤ) - 1)
  have h0 : mode A.fields A.conformalVector 0 a = A.toVertexAlgebra.translation a :=
    by rw [A.conformal_translation]
  norm_num [Finset.sum_range_succ, h0] at h
  have ht := congrArg (fun f : Module.End ℂ V => f v)
    (A.translation_covariance a (m + d - 1))
  simp only [LinearMap.smul_apply] at ht
  change mode A.fields A.conformalVector 0 (mode A.fields a (m + d - 1) v) -
    mode A.fields a (m + d - 1) (mode A.fields A.conformalVector 0 v) =
      (-((d : ℂ) - 1 + m)) • mode A.fields a (m - 1 + d - 1) v
  rw [h, ht, show m + (d : ℤ) - 1 - 1 = m - 1 + d - 1 by omega]
  push_cast
  congr 1
  ring

 

theorem mobius_physical_commutator {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (m : ℤ) :
    A.mobiusGenerator * A.physicalMode a d m - A.physicalMode a d m * A.mobiusGenerator =
      (((d : ℂ) - 1 - m) / 2) • A.physicalMode a d (m + 1) +
      (((d : ℂ) - 1 + m) / 2) • A.physicalMode a d (m - 1) := by
  calc
    _ = (2 : ℂ)⁻¹ •
        ((A.virasoroMode 1 * A.physicalMode a d m - A.physicalMode a d m * A.virasoroMode 1) -
         (A.virasoroMode (-1) * A.physicalMode a d m - A.physicalMode a d m * A.virasoroMode (-1))) := by
      simp only [mobiusGenerator, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, smul_sub]
      abel
    _ = _ := by
      rw [A.virasoro_one_physical_commutator ha hq, A.virasoro_neg_one_physical_commutator]
      module

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U

 

theorem physicalMode_polynomial_cutoff {a : V} (h : A.PolynomialEnergyBound a)
    (d : ℕ) (m : ℤ) : ∃ D : ℝ, 0 < D ∧ ∃ r : ℕ, ∀ {N : ℕ} {v : V},
    v ∈ A.energyCutoff N → ‖A.physicalMode a d m v‖ ≤ D * (1 + (N : ℝ))^r * ‖v‖ := by
  obtain ⟨C, hC, p, r, he⟩ := h
  refine ⟨C * (1 + |((m + (d : ℤ) - 1 : ℤ) : ℝ)|)^p, by positivity, r, ?_⟩
  intro N v hv
  apply (he (m + d - 1) v).trans
  have hg := U.energyShift_pow_norm_on_cutoff hv r
  calc
    _ ≤ C * (1 + |((m + (d : ℤ) - 1 : ℤ) : ℝ)|)^p * ((1 + (N : ℝ))^r * ‖v‖) := by
      gcongr
    _ = _ := by ring

 
theorem physicalMode_diagonal_zero {a v w : V} {d h : ℕ}
    (ha : a ∈ A.grade d) (hv : v ∈ A.grade h) (hw : w ∈ A.grade h)
    (m : ℤ) (hm : m ≠ 0) : inner ℂ v (A.physicalMode a d m w) = 0 := by
  by_cases hh : m ≤ (h : ℤ)
  · have hnat : 0 ≤ (h : ℤ) - m := by omega
    have hgrade : A.physicalMode a d m w ∈ A.grade ((h : ℤ) - m).toNat :=
      A.mode_mem_grade ha hw (m + d - 1) (by omega)
    exact U.grades_orthogonal (by omega) hv hgrade
  · change inner ℂ v (mode A.fields a (m + d - 1) w) = 0
    rw [A.mode_eq_zero_of_negative_energy ha hw (m + d - 1) (by omega), inner_zero_right]

end UnitaryStructure

 

theorem mobius_commutator_power {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (n : ℕ) :
    ((LocalSkewFlow.commutatorOperator (R := ℂ) A.mobiusGenerator)^n)
      (A.physicalMode a d 1) =
        MobiusCoefficients.representation (A.physicalMode a d) (MobiusCoefficients.coeff d n) := by
  let L := (LocalSkewFlow.commutatorOperator (R := ℂ) A.mobiusGenerator).restrictScalars ℝ
  have hL (m : ℤ) : L (A.physicalMode a d m) =
      (((d : ℝ) - 1 - m) / 2) • A.physicalMode a d (m + 1) +
      (((d : ℝ) - 1 + m) / 2) • A.physicalMode a d (m - 1) := by
    have he := A.mobius_physical_commutator ha hq m
    change LocalSkewFlow.commutatorOperator (R := ℂ) A.mobiusGenerator (A.physicalMode a d m) = _
    rw [LocalSkewFlow.commutatorOperator_apply, he]
    simp only [← Complex.coe_smul, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_add,
      Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_intCast, Complex.ofReal_ofNat]
  have h := MobiusCoefficients.representation_coeff (A.physicalMode a d) L d hL n
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  clear h
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [pow_succ', Module.End.mul_apply]
      exact congrArg (LocalSkewFlow.commutatorOperator (R := ℂ) A.mobiusGenerator) ih

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U

 
theorem mobius_commutator_diagonal {a v w : V} {d h : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a)
    (hv : v ∈ A.grade h) (hw : w ∈ A.grade h) (n : ℕ) :
    inner ℂ v ((((LocalSkewFlow.commutatorOperator (R := ℂ) A.mobiusGenerator)^n)
      (A.physicalMode a d 1)) w) =
       (MobiusCoefficients.coeff d n 0 : ℂ) * inner ℂ v (A.physicalMode a d 0 w) := by
  rw [A.mobius_commutator_power ha hq]
  let l : Module.End ℂ V →ₗ[ℝ] ℂ :=
    ((innerSL ℂ v).toLinearMap.comp (LinearMap.applyₗ w)).restrictScalars ℝ
  have hl (m : ℤ) (hm : m ≠ 0) : l (A.physicalMode a d m) = 0 :=
    U.physicalMode_diagonal_zero ha hv hw m hm
  have he := MobiusCoefficients.diagonal_representation (A.physicalMode a d) l hl
    (MobiusCoefficients.coeff d n)
  change inner ℂ v (((MobiusCoefficients.representation (A.physicalMode a d))
    (MobiusCoefficients.coeff d n)) w) =
      (MobiusCoefficients.coeff d n 0) • inner ℂ v (A.physicalMode a d 0 w) at he
  simpa only [Complex.real_smul] using he

end UnitaryStructure

theorem energyCutoff_mono : Monotone A.energyCutoff := by
  intro N M hNM v hv d hd
  exact hv d (by omega)

 
theorem mobiusTaylor_mem_energyCutoff {h : ℕ} {v : V}
    (hv : v ∈ A.energyCutoff h) (t : ℝ) (N : ℕ) :
    LocalSkewFlow.skewTaylor A.mobiusGenerator t N v ∈ A.energyCutoff (h + N) := by
  apply Submodule.sum_mem
  intro n hn
  apply Submodule.smul_mem
  exact A.energyCutoff_mono (by have h := Finset.mem_range.mp hn; omega)
    (A.mobiusGenerator_pow_mem_energyCutoff hv n)

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U

 

theorem summable_norm_mobiusInserted {a : V} (hp : A.PolynomialEnergyBound a)
    (d : ℕ) (m : ℤ) {t : ℝ}
    (ht : 2 * |t| * (8 * (1 + A.centralCharge.re)) < 1) (v : V) :
    Summable (fun n => ‖LocalSkewFlow.insertedExpTerm A.mobiusGenerator
      (A.physicalMode a d m) t n v‖) := by
  obtain ⟨D, hD, r, hT⟩ := U.physicalMode_polynomial_cutoff hp d m
  obtain ⟨N, hN⟩ := A.exists_energyCutoff v
  apply LocalSkewFlow.summable_norm_insertedExpTerm _ _
    (by have hc := U.centralCharge_nonneg.2; positivity) hD.le
    (U.mobiusGenerator_pow_norm hN) (N := N) (r := r) _ ht
  intro n
  simpa only [Nat.cast_add, add_assoc] using
    hT (A.mobiusGenerator_pow_mem_energyCutoff hN n)

 

theorem mobius_diagonal_compression {a v w : V} {d h : ℕ}
    (hp : A.PolynomialEnergyBound a) (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a)
    (hv : v ∈ A.grade h) (hw : w ∈ A.grade h) {t : ℝ}
    (ht : 2 * |t| * (8 * (1 + A.centralCharge.re)) < 1) :
    inner ℂ (LocalSkewFlow.skewExp A.mobiusGenerator (-t) v)
      (LocalSkewFlow.insertedExp A.mobiusGenerator (A.physicalMode a d 1) (-t) w) =
        (MobiusCoefficients.mean d t : ℂ) * inner ℂ v (A.physicalMode a d 0 w) := by
  have ht' : 2 * |-t| * (8 * (1 + A.centralCharge.re)) < 1 := by simpa using ht
  rw [LocalSkewFlow.inner_skewExp_inserted _ _ U.mobiusGenerator_skew t v w
    (U.summable_norm_mobiusEvolutionTerm ht' v)
    (U.summable_norm_mobiusInserted hp d 1 ht' w)]
  simp_rw [U.mobius_commutator_diagonal ha hq hv hw]
  calc
    _ = ∑' n, ((t^n / (n.factorial : ℝ) * MobiusCoefficients.coeff d n 0 : ℝ) : ℂ) *
        inner ℂ v (A.physicalMode a d 0 w) := by
      apply tsum_congr
      intro n
      push_cast
      ring
    _ = _ := by rw [tsum_mul_right, ← Complex.ofReal_tsum]; rfl

 

theorem mobiusInserted_bound {a : V} (hp : A.PolynomialEnergyBound a) (d : ℕ) (m : ℤ)
    {t : ℝ} (ht : 4 * |t| * (8 * (1 + A.centralCharge.re)) < 1) :
    ∃ B E : ℝ, 0 ≤ B ∧ 0 ≤ E ∧ ∀ (F : ℕ → ℝ),
      (∀ N, ∀ v ∈ A.energyCutoff N, ‖A.physicalMode a d m v‖ ≤ F N * ‖v‖) →
      ∀ N, ∀ v ∈ A.energyCutoff N,
        ‖LocalSkewFlow.insertedExp A.mobiusGenerator (A.physicalMode a d m) t v‖ ≤
          (F (2 * N) * B + E) * ‖v‖ := by
  let C := 8 * (1 + A.centralCharge.re)
  have hC : 0 ≤ C := by dsimp [C]; have hc := U.centralCharge_nonneg.2; positivity
  obtain ⟨D, hD, r, hT⟩ := U.physicalMode_polynomial_cutoff hp d m
  let B := 1 + (1 - 4 * |t| * C)⁻¹
  let E := D * (2 : ℝ)^r * ∑' n : ℕ, (1 + (n : ℝ))^r * (4 * |t| * C)^n
  have hB : 0 ≤ B := by
    dsimp [B]
    have hh : 0 < 1 - 4 * |t| * C := by linarith
    positivity
  have hE : 0 ≤ E := by
    dsimp [E]
    exact mul_nonneg (mul_nonneg hD.le (by positivity)) (tsum_nonneg (fun _ => by positivity))
  refine ⟨B, E, hB, hE, ?_⟩
  intro F hF N v hv
  have hF0 : 0 ≤ F (2 * N) := by
    have h := hF (2 * N) A.vacuum (A.grade_le_energyCutoff (d := 0) (by omega)
      (by rw [A.grade_zero]; exact Submodule.mem_span_singleton_self _))
    rw [U.vacuum_norm, mul_one] at h
    exact (norm_nonneg _).trans h
  have hq : 2 * |t| * C < 1 := by nlinarith [mul_nonneg (abs_nonneg t) hC]
  have hiter := U.mobiusGenerator_pow_norm hv
  have hTv (n : ℕ) : ‖A.physicalMode a d m ((A.mobiusGenerator^n) v)‖ ≤
      D * (1 + (N : ℝ) + n)^r * ‖(A.mobiusGenerator^n) v‖ := by
    simpa only [Nat.cast_add, add_assoc] using hT (A.mobiusGenerator_pow_mem_energyCutoff hv n)
  have hs := U.summable_norm_mobiusInserted hp d m hq v
  have he := LocalSkewFlow.apply_skewTaylor_add_tail A.mobiusGenerator (A.physicalMode a d m)
    (N := N) hs
  have hbnd := LocalSkewFlow.skewTaylor_norm_bound A.mobiusGenerator U.mobiusGenerator_skew hC hiter ht
  have htail := LocalSkewFlow.insertedExp_tail_norm_bound A.mobiusGenerator (A.physicalMode a d m)
    hC hD.le hiter hTv ht
  rw [← he]
  calc
    _ ≤ ‖(A.physicalMode a d m (LocalSkewFlow.skewTaylor A.mobiusGenerator t N v) : V)‖ +
        ‖∑' n, LocalSkewFlow.insertedExpTerm A.mobiusGenerator (A.physicalMode a d m) t (n + N) v‖ := by
      simpa only [UniformSpace.Completion.norm_coe] using norm_add_le
        ((A.physicalMode a d m (LocalSkewFlow.skewTaylor A.mobiusGenerator t N v) : V) : UniformSpace.Completion V)
        (∑' n, LocalSkewFlow.insertedExpTerm A.mobiusGenerator (A.physicalMode a d m) t (n + N) v)
    _ ≤ F (2 * N) * (B * ‖v‖) + E * ‖v‖ := by
      apply add_le_add _ htail
      apply (hF (2 * N) _ ?_).trans
      · exact mul_le_mul_of_nonneg_left hbnd hF0
      · simpa only [two_mul] using A.mobiusTaylor_mem_energyCutoff hv t N
    _ = _ := by ring

 

theorem zeroMode_transfer {a : V} {d : ℕ}
    (hp : A.PolynomialEnergyBound a) (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℕ → ℝ), (∀ N, 1 ≤ F N) →
      (∀ N, ∀ v ∈ A.energyCutoff N, ‖A.physicalMode a d 1 v‖ ≤ F N * ‖v‖) →
      ∀ h, ∀ w ∈ A.grade h, ‖A.physicalMode a d 0 w‖ ≤ C * F (2 * h) * ‖w‖ := by
  let L : ℝ := 8 * (1 + A.centralCharge.re)
  have hL : 0 < L := by dsimp [L]; have hc := U.centralCharge_nonneg.2; positivity
  let t : ℝ := (16 * L)⁻¹
  have ht : 0 < t := by dsimp [t]; positivity
  have h4 : 4 * |t| * L < 1 := by
    rw [abs_of_pos ht]
    dsimp [t]
    field_simp
    nlinarith
  have h4' : 4 * |-t| * L < 1 := by simpa using h4
  have h2 : 2 * |t| * L < 1 := by nlinarith [mul_nonneg (abs_nonneg t) hL.le]
  obtain ⟨B, E, hB, hE, hBE⟩ := U.mobiusInserted_bound hp d 1 h4'
  let c := MobiusCoefficients.mean d t
  have hc : 0 < c := MobiusCoefficients.mean_pos hd ht
  refine ⟨(1 + B + E) / c, div_pos (by positivity) hc, ?_⟩
  intro F hF hbound h w hw
  let v := A.physicalMode a d 0 w
  have hv : v ∈ A.grade h := A.mode_mem_grade ha hw ((0 : ℤ) + d - 1) (by omega)
  have hn := hBE F hbound h w (A.grade_le_energyCutoff le_rfl hw)
  have hi := U.mobius_diagonal_compression hp ha hq hv hw h2
  have he : ‖LocalSkewFlow.skewExp A.mobiusGenerator (-t) v‖ = ‖v‖ :=
    (U.mobiusLocalIsometry (-t) (by simpa using h2)).norm_map v
  have hh : c * ‖v‖^2 ≤ ‖v‖ * ((F (2 * h) * B + E) * ‖w‖) := by
    calc
      _ = ‖(c : ℂ) * inner ℂ v v‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc,
          inner_self_eq_norm_sq_to_K]
        simp
      _ = ‖inner ℂ (LocalSkewFlow.skewExp A.mobiusGenerator (-t) v)
        (LocalSkewFlow.insertedExp A.mobiusGenerator (A.physicalMode a d 1) (-t) w)‖ :=
          congrArg norm hi.symm
      _ ≤ ‖LocalSkewFlow.skewExp A.mobiusGenerator (-t) v‖ *
          ‖LocalSkewFlow.insertedExp A.mobiusGenerator (A.physicalMode a d 1) (-t) w‖ :=
            norm_inner_le_norm _ _
      _ ≤ _ := by rw [he]; exact mul_le_mul_of_nonneg_left hn (norm_nonneg _)
  by_cases hv0 : ‖v‖ = 0
  · change ‖v‖ ≤ _
    rw [hv0]
    have hFpos := (hF (2 * h)).trans_lt' (by norm_num : (0 : ℝ) < 1)
    positivity
  have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv0)
  have hvb : c * ‖v‖ ≤ (F (2 * h) * B + E) * ‖w‖ := by
    apply (mul_le_mul_iff_of_pos_left hvpos).mp
    nlinarith [hh]
  change ‖v‖ ≤ _
  apply (mul_le_mul_iff_of_pos_right hc).mp
  calc
    ‖v‖ * c ≤ (F (2 * h) * B + E) * ‖w‖ := by nlinarith [hvb]
    _ ≤ ((1 + B + E) * F (2 * h)) * ‖w‖ := by
      gcongr
      nlinarith [hF (2 * h)]
    _ = (((1 + B + E) / c * F (2 * h) * ‖w‖) * c) := by field_simp

end UnitaryStructure

end CFTTypeVOA

end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_ConstrainedSquareBound
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)



def positiveColumnNorm (a : V) (d N : ℕ) : ℝ := ‖A.positiveColumn a d N‖

theorem positiveColumnNorm_nonneg (a : V) (d N : ℕ) :
    0 ≤ A.positiveColumnNorm a d N := norm_nonneg (A.positiveColumn a d N)

theorem positiveColumn_norm_sq (a : V) (d N : ℕ) (v : A.energyCutoff N) :
    ‖A.positiveColumn a d N v‖^2 =
      ∑ m ∈ Finset.range (N + 1), ‖A.physicalMode a d m v‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [positiveColumn_apply]
  exact Fin.sum_univ_eq_sum_range (fun m => ‖A.physicalMode a d m v‖^2) (N + 1)

theorem sum_positive_modes_sq_le (a : V) (d : ℕ) {N : ℕ} {v : V}
    (hv : v ∈ A.energyCutoff N) :
    (∑ m ∈ Finset.range (N + 1), ‖A.physicalMode a d m v‖^2) ≤
      A.positiveColumnNorm a d N ^ 2 * ‖v‖^2 := by
  rw [← A.positiveColumn_norm_sq a d N ⟨v, hv⟩, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) ((A.positiveColumn a d N).le_opNorm ⟨v, hv⟩) 2

theorem physicalMode_zero_above_cutoff {a : V} {d N : ℕ} (ha : a ∈ A.grade d)
    {v : V} (hv : v ∈ A.energyCutoff N) (m : ℤ) (hm : (N : ℤ) < m) :
    A.physicalMode a d m v = 0 := by
  rw [← A.cutoffProjection_of_mem hv, cutoffProjection_apply, map_sum]
  apply Finset.sum_eq_zero
  intro e he
  apply A.mode_eq_zero_of_negative_energy ha (A.gradeComponent_mem e v)
  have he := Finset.mem_range.mp he
  omega

theorem physicalMode_mem_cutoff {a : V} {d N M : ℕ} (ha : a ∈ A.grade d)
    {v : V} (hv : v ∈ A.energyCutoff N) (m : ℤ) (hm : (N : ℤ) - m ≤ M) :
    A.physicalMode a d m v ∈ A.energyCutoff M := by
  rw [← A.cutoffProjection_of_mem hv, cutoffProjection_apply, map_sum]
  apply Submodule.sum_mem
  intro e he
  by_cases hem : (e : ℤ) < m
  · rw [show A.physicalMode a d m (A.gradeComponent e v) = 0 from
      A.mode_eq_zero_of_negative_energy ha (A.gradeComponent_mem e v) _ (by omega)]
    exact Submodule.zero_mem _
  · have hek : (e : ℤ) - m = ((e : ℤ) - m).toNat := by omega
    apply A.grade_le_energyCutoff (d := ((e : ℤ) - m).toNat)
      (by have he := Finset.mem_range.mp he; omega)
    exact A.mode_mem_grade ha (A.gradeComponent_mem e v) _ (by omega)

end CFTTypeVOA

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

theorem positive_mode_norm_le_column {a : V} {d N : ℕ} (ha : a ∈ A.grade d)
    {v : V} (hv : v ∈ A.energyCutoff N) (m : ℕ) :
    ‖A.physicalMode a d m v‖ ≤ A.positiveColumnNorm a d N * ‖v‖ := by
  have hR := A.positiveColumnNorm_nonneg a d N
  by_cases hm : N < m
  · rw [A.physicalMode_zero_above_cutoff ha hv m (by exact_mod_cast hm), norm_zero]
    positivity
  · apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow]
    apply le_trans _ (A.sum_positive_modes_sq_le a d hv)
    exact Finset.single_le_sum (f := fun i : ℕ => ‖A.physicalMode a d i v‖^2)
      (fun i _ => sq_nonneg _) (Finset.mem_range.mpr (show m < N + 1 by omega))

theorem finsum_positive_modes_sq_eq {a : V} {d N : ℕ} (ha : a ∈ A.grade d)
    {v : V} (hv : v ∈ A.energyCutoff N) :
    (∑ᶠ m : ℕ, ‖A.physicalMode a d m v‖^2) =
      ∑ m ∈ Finset.range (N + 1), ‖A.physicalMode a d m v‖^2 := by
  classical
  apply finsum_eq_sum_of_support_subset
  intro m hm
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra h
  apply hm
  change ‖A.physicalMode a d m v‖^2 = 0
  rw [A.physicalMode_zero_above_cutoff ha hv m (by omega)]
  simp

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U

theorem negative_mode_norm_le_column {a : V} {d N : ℕ} (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    {v : V} (hv : v ∈ A.energyCutoff N) (m : ℕ) :
    ‖A.physicalMode a d (-(m : ℤ)) v‖ ≤ A.positiveColumnNorm a d (N + m) * ‖v‖ := by
  have hR := A.positiveColumnNorm_nonneg a d (N + m)
  have hmem := A.physicalMode_mem_cutoff ha hv (-(m : ℤ)) (M := N + m) (by omega)
  have hb := A.positive_mode_norm_le_column ha hmem m
  have hs := U.mode_norm_sq_le_adjoint ha hq hh (-(m : ℤ)) v
  simp only [neg_neg] at hs
  have h := hs.trans (mul_le_mul_of_nonneg_left hb (norm_nonneg v))
  by_cases hx : ‖A.physicalMode a d (-(m : ℤ)) v‖ = 0
  · rw [hx]; positivity
  · have hxpos : 0 < ‖A.physicalMode a d (-(m : ℤ)) v‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
    apply (mul_le_mul_iff_of_pos_right hxpos).mp
    nlinarith [h]



end UnitaryStructure
end CFTTypeVOA

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

theorem virasoro_one_pow_mem_grade {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (j : ℕ) (hj : j ≤ d) : (A.virasoroMode 1 ^ j) a ∈ A.grade (d - j) := by
  induction j with
  | zero => simpa using ha
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact A.virasoro_mem_grade (ih (by omega)) 1 (by omega)

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)



theorem adjointPhysicalMode_zero_above_cutoff {a : V} {d N : ℕ} (ha : a ∈ A.grade d)
    {v : V} (hv : v ∈ A.energyCutoff N) (m : ℤ) (hm : (N : ℤ) < m) :
    U.adjointPhysicalMode a d (-m) v = 0 := by
  simp only [adjointPhysicalMode, LinearMap.smul_apply, LinearMap.sum_apply, neg_neg]
  have hs : (∑ j ∈ Finset.range (d + 1), ((j.factorial : ℂ)⁻¹) •
      A.physicalMode ((A.virasoroMode 1 ^ j) (U.pct a)) (d - j) m v) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [A.physicalMode_zero_above_cutoff
      (A.virasoro_one_pow_mem_grade (U.pct_mem_grade ha) j (by have := Finset.mem_range.mp hj; omega))
      hv m hm, smul_zero]
  rw [hs, smul_zero]

end UnitaryStructure
end CFTTypeVOA

end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_ColumnControl
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

theorem columnControl_subset {a : V} {d N : ℕ} {K : ℝ} (ha : a ∈ A.grade d)
    (H : A.ColumnControl a d N K) {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : Set.InjOn f s) {v : V} (hv : v ∈ A.energyCutoff N) :
    (∑ i ∈ s, ‖A.physicalMode a d (f i) v‖^2) ≤ K * ‖v‖^2 := by
  apply (SharpColumns.sum_injective_le s f hf (fun m => ‖A.physicalMode a d m v‖^2)
    (fun _ => sq_nonneg _) N ?_).trans (H v hv)
  intro m hm
  rw [A.physicalMode_zero_above_cutoff ha hv m (by exact_mod_cast hm)]
  simp

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)


theorem adjointColumnControl_subset {a : V} {d N : ℕ} {K : ℝ} (ha : a ∈ A.grade d)
    (H : U.AdjointColumnControl a d N K) {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : Set.InjOn f s) {v : V} (hv : v ∈ A.energyCutoff N) :
    (∑ i ∈ s, ‖U.adjointPhysicalMode a d (-(f i : ℤ)) v‖^2) ≤ K * ‖v‖^2 := by
  apply (SharpColumns.sum_injective_le s f hf
    (fun m => ‖U.adjointPhysicalMode a d (-(m : ℤ)) v‖^2)
    (fun _ => sq_nonneg _) N ?_).trans (H v hv)
  intro m hm
  rw [U.adjointPhysicalMode_zero_above_cutoff ha hv m (by exact_mod_cast hm)]
  simp

end UnitaryStructure

 
def normalLeft (a b v : V) (d e N m : ℕ) : V :=
  ∑ j ∈ Finset.range (N + 1), A.physicalMode a d (-1 - j)
    (A.physicalMode b e (m + 1 + j) v)

def normalRightHigh (a b v : V) (d e N m : ℕ) : V :=
  ∑ j ∈ Finset.range (N + 1) with m ≤ j, A.physicalMode b e ((m : ℤ) - j)
    (A.physicalMode a d j v)

def normalRightLow (a b v : V) (d e N m : ℕ) : V :=
  ∑ j ∈ Finset.range (N + 1) with j < m, A.physicalMode b e ((m : ℤ) - j)
    (A.physicalMode a d j v)

theorem normalLeft_mem_cutoff {a b v : V} {d e N m : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hv : v ∈ A.energyCutoff N) :
    A.normalLeft a b v d e N m ∈ A.energyCutoff N := by
  apply Submodule.sum_mem
  intro j _
  by_cases hj : N < m + 1 + j
  · rw [A.physicalMode_zero_above_cutoff hb hv (m + 1 + j) (by exact_mod_cast hj), map_zero]
    exact Submodule.zero_mem _
  · have hinner := A.physicalMode_mem_cutoff hb hv (m + 1 + j) (M := N - (m + 1 + j)) (by omega)
    exact A.physicalMode_mem_cutoff ha hinner (-1 - j) (by omega)

theorem normalRightHigh_mem_cutoff {a b v : V} {d e N m : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hv : v ∈ A.energyCutoff N) :
    A.normalRightHigh a b v d e N m ∈ A.energyCutoff N := by
  apply Submodule.sum_mem
  intro j hj
  have hjN := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  have hinner := A.physicalMode_mem_cutoff ha hv j (M := N - j) (by omega)
  exact A.physicalMode_mem_cutoff hb hinner ((m : ℤ) - j) (by omega)

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)

theorem normalLeft_sq_le {a b v : V} {d e N m : ℕ} {K L : ℝ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hv : v ∈ A.energyCutoff N)
    (hK : 0 ≤ K) (Ha : U.AdjointColumnControl a d N K) (Hb : A.ColumnControl b e N L) :
    ‖A.normalLeft a b v d e N m‖^2 ≤ K * L * ‖v‖^2 := by
  have H := SharpColumns.row_sq_le (Finset.range (N + 1))
    (fun j => A.physicalMode a d (-1 - j))
    (fun j => U.adjointPhysicalMode a d (-1 - j))
    (A.energyCutoff N) K hK (fun j _ x y => U.adjointPhysicalMode_inner ha _ x y)
    (fun w hw => by
      have HH := U.adjointColumnControl_subset ha Ha (Finset.range (N + 1))
        (fun j => j + 1) (by intro i _ j _ he; dsimp only at he; omega) hw
      simpa only [Nat.cast_add, Nat.cast_one, neg_add_rev, sub_eq_add_neg] using HH)
    (fun j => A.physicalMode b e (m + 1 + j) v) (fun _ => 1) 1 (by norm_num)
    (by intro j _; simp) (by simpa only [one_smul, normalLeft] using A.normalLeft_mem_cutoff ha hb hv (m := m))
  simp only [one_pow, one_mul, one_smul] at H
  apply H.trans
  have HH := A.columnControl_subset hb Hb (Finset.range (N + 1))
    (fun j => m + 1 + j) (by intro i _ j _ he; dsimp only at he; omega) hv
  push_cast at HH
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left HH hK

theorem normalRightHigh_sq_le {a b v : V} {d e N m : ℕ} {K L : ℝ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hv : v ∈ A.energyCutoff N)
    (hL : 0 ≤ L) (Ha : A.ColumnControl a d N K) (Hb : U.AdjointColumnControl b e N L) :
    ‖A.normalRightHigh a b v d e N m‖^2 ≤ K * L * ‖v‖^2 := by
  let s := (Finset.range (N + 1)).filter (fun j => m ≤ j)
  have H := SharpColumns.row_sq_le s
    (fun j => A.physicalMode b e ((m : ℤ) - j))
    (fun j => U.adjointPhysicalMode b e ((m : ℤ) - j))
    (A.energyCutoff N) L hL (fun j _ x y => U.adjointPhysicalMode_inner hb _ x y)
    (fun w hw => by
      have HH := U.adjointColumnControl_subset hb Hb s
        (fun j => j - m) (by
          intro i hi j hj he
          dsimp only at he
          have hi := (Finset.mem_filter.mp hi).2
          have hj := (Finset.mem_filter.mp hj).2
          omega) hw
      calc
        _ = ∑ j ∈ s, ‖U.adjointPhysicalMode b e (-((j - m : ℕ) : ℤ)) w‖^2 := by
          apply Finset.sum_congr rfl
          intro j hj
          have hj := (Finset.mem_filter.mp hj).2
          rw [show (m : ℤ) - j = -((j - m : ℕ) : ℤ) by omega]
        _ ≤ _ := HH)
    (fun j => A.physicalMode a d j v) (fun _ => 1) 1 (by norm_num)
    (by intro j _; simp) (by simpa only [one_smul, normalRightHigh, s] using A.normalRightHigh_mem_cutoff ha hb hv (m := m))
  simp only [one_pow, one_mul, one_smul] at H
  apply H.trans
  have HH := A.columnControl_subset ha Ha s id (by intro i _ j _ h; exact h) hv
  calc
    _ ≤ L * (K * ‖v‖^2) := mul_le_mul_of_nonneg_left HH hL
    _ = _ := by ring

end UnitaryStructure
end CFTTypeVOA

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

theorem normalRightLow_column_sq_le {a b v : V} {d e N : ℕ} {K L : ℝ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hv : v ∈ A.energyCutoff N)
    (hL : 0 ≤ L) (Ha : A.ColumnControl a d N K) (Hb : A.ColumnControl b e N L) :
    (∑ m ∈ Finset.range (N + 1), ‖A.normalRightLow a b v d e N m‖^2) ≤
      (N + 1 : ℝ) * K * L * ‖v‖^2 := by
  classical
  have H := SharpColumns.triangular_column_sq_le (Finset.range (N + 1)) (Finset.range (N + 1))
    (fun j => A.physicalMode a d j v) (fun m j => A.physicalMode b e ((m : ℤ) - j))
    (fun m j => j < m) (fun _ _ => 1) 1 L
    (by intro m _ j _ _; simp)
    (by
      intro j hj
      have hmem := A.physicalMode_mem_cutoff ha hv j (M := N) (by omega)
      have HH := A.columnControl_subset hb Hb ((Finset.range (N + 1)).filter (fun m => j < m))
        (fun m => m - j) (by
          intro r hr s hs he
          dsimp only at he
          have hr := (Finset.mem_filter.mp hr).2
          have hs := (Finset.mem_filter.mp hs).2
          omega) hmem
      calc
        _ = ∑ m ∈ Finset.range (N + 1) with j < m,
            ‖A.physicalMode b e ((m - j : ℕ) : ℤ) (A.physicalMode a d j v)‖^2 := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [Nat.cast_sub (Nat.le_of_lt (Finset.mem_filter.mp hm).2)]
        _ ≤ _ := HH)
  simp only [one_smul, one_pow, mul_one, Finset.card_range, Nat.cast_add, Nat.cast_one] at H
  apply H.trans
  have HH := mul_le_mul_of_nonneg_left (Ha v hv)
    (mul_nonneg (by positivity : 0 ≤ (N + 1 : ℝ)) hL)
  simpa only [normalRightLow, mul_assoc, mul_comm K L, mul_left_comm L K] using HH

 

theorem normal_product_cutoff_split {a b v : V} {d e N : ℕ}
    (hb : b ∈ A.grade e) (ha : a ∈ A.grade d) (hv : v ∈ A.energyCutoff N)
    (hd : 1 ≤ d) (m : ℕ) :
    A.physicalMode (mode A.fields a (-1) b) (d + e) m v =
      A.normalLeft a b v d e N m + A.normalRightHigh a b v d e N m +
      A.normalRightLow a b v d e N m -
      ∑ i ∈ Finset.range (d - 1), ∑ j ∈ Finset.range (i + 1),
        (i.choose j : ℂ) • mode A.fields (mode A.fields a j b)
          (m + d + e - 2 - j) v := by
  classical
  rw [A.physical_normal_product_resplit a b v d e hd m]
  have hL : Function.support (fun j : ℕ => A.physicalMode a d (-1 - j)
      (A.physicalMode b e (m + 1 + j) v)) ⊆ (Finset.range (N + 1) : Set ℕ) := by
    intro j hj
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hj
    change A.physicalMode a d (-1 - j) (A.physicalMode b e (m + 1 + j) v) = 0
    rw [A.physicalMode_zero_above_cutoff hb hv (m + 1 + j) (by omega), map_zero]
  have hR : Function.support (fun j : ℕ => A.physicalMode b e ((m : ℤ) - j)
      (A.physicalMode a d j v)) ⊆ (Finset.range (N + 1) : Set ℕ) := by
    intro j hj
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hj
    change A.physicalMode b e ((m : ℤ) - j) (A.physicalMode a d j v) = 0
    rw [A.physicalMode_zero_above_cutoff ha hv j (by omega), map_zero]
  rw [finsum_eq_sum_of_support_subset _ hL, finsum_eq_sum_of_support_subset _ hR]
  have hs := Finset.sum_filter_add_sum_filter_not (Finset.range (N + 1))
    (fun j => m ≤ j) (fun j => A.physicalMode b e ((m : ℤ) - j) (A.physicalMode a d j v))
  simp only [not_le] at hs
  dsimp only [normalLeft, normalRightHigh, normalRightLow]
  rw [← hs]
  simp only [add_assoc]


theorem singular_correction_column_sq_le {a b v : V} {d e N : ℕ} {R : ℝ}
    (hd : 1 ≤ d) (Hsing : ∀ j < d - 1,
      A.ColumnControl (mode A.fields a j b) (d + e - j - 1) N R)
    (hv : v ∈ A.energyCutoff N) :
    (∑ m ∈ Finset.range (N + 1), ‖∑ i ∈ Finset.range (d - 1), ∑ j ∈ Finset.range (i + 1),
      (i.choose j : ℂ) • mode A.fields (mode A.fields a j b) (m + d + e - 2 - j) v‖^2) ≤
      sharpCorrectionMass d * R * ‖v‖^2 := by
  classical
  let T := fun (i j m : ℕ) => (i.choose j : ℂ) •
    mode A.fields (mode A.fields a j b) (m + d + e - 2 - j) v
  have hinner (i : ℕ) (hi : i ∈ Finset.range (d - 1)) (j : ℕ)
      (hj : j ∈ Finset.range (i + 1)) :
      (∑ m ∈ Finset.range (N + 1), ‖T i j m‖^2) ≤ (i.choose j : ℝ)^2 * R * ‖v‖^2 := by
    have hjd : j < d - 1 := by have := Finset.mem_range.mp hi; have := Finset.mem_range.mp hj; omega
    have he : ∀ m : ℕ, (m : ℤ) + d + e - 2 - j = m + (d + e - j - 1 : ℕ) - 1 := by
      intro m
      omega
    simp only [T, norm_smul, Complex.norm_natCast, mul_pow, he,
      ← Finset.mul_sum]
    simpa only [mul_assoc, physicalMode] using mul_le_mul_of_nonneg_left (Hsing j hjd v hv) (sq_nonneg (i.choose j : ℝ))
  have hi (i : ℕ) (hi : i ∈ Finset.range (d - 1)) :
      (∑ m ∈ Finset.range (N + 1), ‖∑ j ∈ Finset.range (i + 1), T i j m‖^2) ≤
        (i + 1 : ℝ) * ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ)^2 * R * ‖v‖^2 := by
    simpa only [Finset.card_range, Nat.cast_add, Nat.cast_one] using
      SharpColumns.sum_columns_sq_le (Finset.range (i + 1)) (Finset.range (N + 1))
        (T i) (fun j => (i.choose j : ℝ)^2 * R * ‖v‖^2) (hinner i hi)
  have H := SharpColumns.sum_columns_sq_le (Finset.range (d - 1)) (Finset.range (N + 1))
    (fun i m => ∑ j ∈ Finset.range (i + 1), T i j m)
    (fun i => (i + 1 : ℝ) * ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ)^2 * R * ‖v‖^2) hi
  simpa only [Finset.card_range, sharpCorrectionMass, Finset.sum_mul, mul_assoc, T] using H

end CFTTypeVOA

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

theorem columnControl_mono {a : V} {d N : ℕ} {K L : ℝ}
    (H : A.ColumnControl a d N K) (hKL : K ≤ L) : A.ColumnControl a d N L := by
  intro v hv
  exact (H v hv).trans (mul_le_mul_of_nonneg_right hKL (sq_nonneg _))

theorem columnControl_mode_sq_le {a v : V} {d N m : ℕ} {K : ℝ}
    (ha : a ∈ A.grade d) (H : A.ColumnControl a d N K) (hv : v ∈ A.energyCutoff N) :
    ‖A.physicalMode a d m v‖^2 ≤ K * ‖v‖^2 := by
  simpa using A.columnControl_subset ha H {m} id (by intro i _ j _ h; exact h) hv

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)

theorem normalProduct_columnControl {a b : V} {d e N : ℕ} {K L R : ℝ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hd : 1 ≤ d)
    (hK : 0 ≤ K) (hL : 0 ≤ L)
    (Ha : A.ColumnControl a d N K) (Ha' : U.AdjointColumnControl a d N K)
    (Hb : A.ColumnControl b e N L) (Hb' : U.AdjointColumnControl b e N L)
    (Hsing : ∀ j < d - 1,
      A.ColumnControl (mode A.fields a j b) (d + e - j - 1) N R) :
    A.ColumnControl (mode A.fields a (-1) b) (d + e) N
      (12 * (N + 1 : ℝ) * K * L + 4 * sharpCorrectionMass d * R) := by
  intro v hv
  let T := fun m : ℕ => ∑ i ∈ Finset.range (d - 1), ∑ j ∈ Finset.range (i + 1),
    (i.choose j : ℂ) • mode A.fields (mode A.fields a j b) (m + d + e - 2 - j) v
  have hleft : (∑ m ∈ Finset.range (N + 1), ‖A.normalLeft a b v d e N m‖^2) ≤
      (N + 1 : ℝ) * K * L * ‖v‖^2 := by
    calc
      _ ≤ ∑ _m ∈ Finset.range (N + 1), K * L * ‖v‖^2 :=
        Finset.sum_le_sum fun _ _ => U.normalLeft_sq_le ha hb hv hK Ha' Hb
      _ = _ := by simp [mul_assoc]
  have hhigh : (∑ m ∈ Finset.range (N + 1), ‖A.normalRightHigh a b v d e N m‖^2) ≤
      (N + 1 : ℝ) * K * L * ‖v‖^2 := by
    calc
      _ ≤ ∑ _m ∈ Finset.range (N + 1), K * L * ‖v‖^2 :=
        Finset.sum_le_sum fun _ _ => U.normalRightHigh_sq_le ha hb hv hL Ha Hb'
      _ = _ := by simp [mul_assoc]
  have hlow := A.normalRightLow_column_sq_le ha hb hv hL Ha Hb
  have hsing := A.singular_correction_column_sq_le hd Hsing hv
  calc
    _ ≤ ∑ m ∈ Finset.range (N + 1), 4 * (‖A.normalLeft a b v d e N m‖^2 +
      ‖A.normalRightHigh a b v d e N m‖^2 + ‖A.normalRightLow a b v d e N m‖^2 + ‖T m‖^2) := by
      apply Finset.sum_le_sum
      intro m _
      rw [A.normal_product_cutoff_split hb ha hv hd]
      exact SharpColumns.norm_add_add_sub_sq_le _ _ _ _
    _ = 4 * ((∑ m ∈ Finset.range (N + 1), ‖A.normalLeft a b v d e N m‖^2) +
      (∑ m ∈ Finset.range (N + 1), ‖A.normalRightHigh a b v d e N m‖^2) +
      (∑ m ∈ Finset.range (N + 1), ‖A.normalRightLow a b v d e N m‖^2) +
      (∑ m ∈ Finset.range (N + 1), ‖T m‖^2)) := by rw [← Finset.mul_sum]; simp only [Finset.sum_add_distrib]
    _ ≤ _ := by dsimp only [T] at *; nlinarith

theorem normalProduct_zero_sq_le {a b v : V} {d e N : ℕ} {K L R : ℝ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hd : 1 ≤ d)
    (hv : v ∈ A.energyCutoff N) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (Ha : A.ColumnControl a d N K) (Ha' : U.AdjointColumnControl a d N K)
    (Hb : A.ColumnControl b e N L) (Hb' : U.AdjointColumnControl b e N L)
    (Hsing : ∀ j < d - 1,
      A.ColumnControl (mode A.fields a j b) (d + e - j - 1) N R) :
    ‖A.physicalMode (mode A.fields a (-1) b) (d + e) 0 v‖^2 ≤
      (8 * K * L + 4 * sharpCorrectionMass d * R) * ‖v‖^2 := by
  let T := fun m : ℕ => ∑ i ∈ Finset.range (d - 1), ∑ j ∈ Finset.range (i + 1),
    (i.choose j : ℂ) • mode A.fields (mode A.fields a j b) (m + d + e - 2 - j) v
  have hleft := U.normalLeft_sq_le (m := 0) ha hb hv hK Ha' Hb
  have hhigh := U.normalRightHigh_sq_le (m := 0) ha hb hv hL Ha Hb'
  have hlow : A.normalRightLow a b v d e N 0 = 0 := by simp [normalRightLow]
  have hsing : ‖T 0‖^2 ≤ sharpCorrectionMass d * R * ‖v‖^2 := by
    apply (Finset.single_le_sum (f := fun m => ‖T m‖^2) (fun _ _ => sq_nonneg _) (by simp : 0 ∈ Finset.range (N + 1))).trans
    exact A.singular_correction_column_sq_le hd Hsing hv
  calc
    _ ≤ 4 * (‖A.normalLeft a b v d e N 0‖^2 + ‖A.normalRightHigh a b v d e N 0‖^2 +
      ‖A.normalRightLow a b v d e N 0‖^2 + ‖T 0‖^2) := by
      rw [show (0 : ℤ) = (0 : ℕ) by rfl, A.normal_product_cutoff_split hb ha hv hd]
      exact SharpColumns.norm_add_add_sub_sq_le _ _ _ _
    _ ≤ _ := by rw [hlow, norm_zero, zero_pow (by decide : 2 ≠ 0)]; nlinarith

end UnitaryStructure
end CFTTypeVOA

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)



theorem columnGrowth_zero (X : ℕ → ℝ) (d p q : ℕ) : A.ColumnGrowth X 0 d p q := by
  refine ⟨0, le_rfl, ?_⟩
  intro N v hv
  simp [physicalMode, mode_zero]

theorem zeroGrowth_zero (X : ℕ → ℝ) (d p q : ℕ) : A.ZeroGrowth X 0 d p q := by
  refine ⟨0, le_rfl, ?_⟩
  intro N v hv
  simp [physicalMode, mode_zero]

theorem columnGrowth_add {X : ℕ → ℝ} {a b : V} {d p q : ℕ}
    (Ha : A.ColumnGrowth X a d p q) (Hb : A.ColumnGrowth X b d p q) :
    A.ColumnGrowth X (a + b) d p q := by
  obtain ⟨C, hC, HC⟩ := Ha
  obtain ⟨D, hD, HD⟩ := Hb
  refine ⟨2 * (C + D), by positivity, ?_⟩
  intro N v hv
  calc
    _ ≤ ∑ m ∈ Finset.range (N + 1), 2 * (‖A.physicalMode a d m v‖^2 + ‖A.physicalMode b d m v‖^2) := by
      apply Finset.sum_le_sum
      intro m _
      simp only [physicalMode, mode_add, LinearMap.add_apply]
      exact SharpColumns.norm_add_sq_le_two _ _
    _ = 2 * ((∑ m ∈ Finset.range (N + 1), ‖A.physicalMode a d m v‖^2) +
        ∑ m ∈ Finset.range (N + 1), ‖A.physicalMode b d m v‖^2) := by rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ _ := by nlinarith [HC N v hv, HD N v hv]

theorem zeroGrowth_add {X : ℕ → ℝ} {a b : V} {d p q : ℕ}
    (Ha : A.ZeroGrowth X a d p q) (Hb : A.ZeroGrowth X b d p q) :
    A.ZeroGrowth X (a + b) d p q := by
  obtain ⟨C, hC, HC⟩ := Ha
  obtain ⟨D, hD, HD⟩ := Hb
  refine ⟨2 * (C + D), by positivity, ?_⟩
  intro N v hv
  have h := SharpColumns.norm_add_sq_le_two (A.physicalMode a d 0 v) (A.physicalMode b d 0 v)
  simp only [physicalMode, mode_add, LinearMap.add_apply]
  dsimp only [physicalMode] at h HC HD
  nlinarith [HC N v hv, HD N v hv]

theorem columnGrowth_smul {X : ℕ → ℝ} {a : V} {d p q : ℕ}
    (Ha : A.ColumnGrowth X a d p q) (z : ℂ) : A.ColumnGrowth X (z • a) d p q := by
  obtain ⟨C, hC, HC⟩ := Ha
  refine ⟨‖z‖^2 * C, by positivity, ?_⟩
  intro N v hv
  simpa only [physicalMode, mode_smul, LinearMap.smul_apply, norm_smul, mul_pow,
    ← Finset.mul_sum, mul_assoc] using mul_le_mul_of_nonneg_left (HC N v hv) (sq_nonneg ‖z‖)

theorem zeroGrowth_smul {X : ℕ → ℝ} {a : V} {d p q : ℕ}
    (Ha : A.ZeroGrowth X a d p q) (z : ℂ) : A.ZeroGrowth X (z • a) d p q := by
  obtain ⟨C, hC, HC⟩ := Ha
  refine ⟨‖z‖^2 * C, by positivity, ?_⟩
  intro N v hv
  simpa only [physicalMode, mode_smul, LinearMap.smul_apply, norm_smul, mul_pow,
    mul_assoc] using mul_le_mul_of_nonneg_left (HC N v hv) (sq_nonneg ‖z‖)

theorem columnGrowth_mono {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N) {a : V} {d p q p' q' : ℕ}
    (H : A.ColumnGrowth X a d p q) (hp : p ≤ p') (hq : q ≤ q') :
    A.ColumnGrowth X a d p' q' := by
  obtain ⟨C, hC, HC⟩ := H
  refine ⟨C, hC, fun N => A.columnControl_mono (HC N) ?_⟩
  have hXN := zero_le_one.trans (hX N)
  gcongr
  · linarith [Nat.cast_nonneg (α := ℝ) N]
  · exact hX N

theorem zeroGrowth_mono {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N) {a : V} {d p q p' q' : ℕ}
    (H : A.ZeroGrowth X a d p q) (hp : p ≤ p') (hq : q ≤ q') :
    A.ZeroGrowth X a d p' q' := by
  obtain ⟨C, hC, HC⟩ := H
  refine ⟨C, hC, ?_⟩
  intro N v hv
  apply (HC N v hv).trans
  have hXN := zero_le_one.trans (hX N)
  gcongr
  · linarith [Nat.cast_nonneg (α := ℝ) N]
  · exact hX N

theorem zeroGrowth_of_columnGrowth {X : ℕ → ℝ} {a : V} {d p q : ℕ}
    (ha : a ∈ A.grade d) (H : A.ColumnGrowth X a d p q) : A.ZeroGrowth X a d p q := by
  obtain ⟨C, hC, HC⟩ := H
  exact ⟨C, hC, fun N v hv => A.columnControl_mode_sq_le ha (HC N) hv (m := 0)⟩



def sharpGrowthSubmodule (X : ℕ → ℝ) (d : ℕ) : Submodule ℂ V where
  carrier := {a | A.SharpGrowth X a d}
  zero_mem' := ⟨A.columnGrowth_zero X d _ _, A.zeroGrowth_zero X d _ _⟩
  add_mem' h k := ⟨A.columnGrowth_add h.1 k.1, A.zeroGrowth_add h.2 k.2⟩
  smul_mem' z _ h := ⟨A.columnGrowth_smul h.1 z, A.zeroGrowth_smul h.2 z⟩

theorem finite_columnGrowth_uniform {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N)
    {ι : Type*} (s : Finset ι) (a : ι → V) (d : ι → ℕ) (p q : ℕ)
    (H : ∀ i ∈ s, A.ColumnGrowth X (a i) (d i) p q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ∈ s, ∀ N,
      A.ColumnControl (a i) (d i) N (C * (N + 1 : ℝ)^p * X N^q) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨C, hC, HC⟩ := H i (Finset.mem_insert_self _ _)
    obtain ⟨D, hD, HD⟩ := ih (fun j hj => H j (Finset.mem_insert_of_mem hj))
    refine ⟨C + D, add_nonneg hC hD, ?_⟩
    intro j hj N
    have hXN := zero_le_one.trans (hX N)
    rcases Finset.mem_insert.mp hj with rfl | hj
    · apply A.columnControl_mono (HC N)
      gcongr
      exact le_add_of_nonneg_right hD
    · apply A.columnControl_mono (HD j hj N)
      gcongr
      exact le_add_of_nonneg_left hC

end CFTTypeVOA

end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_AdjointMass
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)

theorem adjointColumnControl_of_columns {a : V} {d N : ℕ} {R : ℝ}
    (H : ∀ j ≤ d, A.ColumnControl ((A.virasoroMode 1^j) (U.pct a)) (d-j) N R) :
    U.AdjointColumnControl a d N (adjointMass d * R) := by
  intro v hv
  let T := fun j m : ℕ => (j.factorial : ℂ)⁻¹ •
    A.physicalMode ((A.virasoroMode 1^j) (U.pct a)) (d-j) m v
  have hT (j : ℕ) (hj : j ∈ Finset.range (d + 1)) :
      (∑ m ∈ Finset.range (N + 1), ‖T j m‖^2) ≤ ‖(j.factorial : ℂ)⁻¹‖^2 * R * ‖v‖^2 := by
    have H' := H j (by have := Finset.mem_range.mp hj; omega) v hv
    simpa only [T, norm_smul, mul_pow, ← Finset.mul_sum, mul_assoc] using
      mul_le_mul_of_nonneg_left H' (sq_nonneg ‖(j.factorial : ℂ)⁻¹‖)
  have h := SharpColumns.sum_columns_sq_le (Finset.range (d + 1)) (Finset.range (N + 1))
    T (fun j => ‖(j.factorial : ℂ)⁻¹‖^2 * R * ‖v‖^2) hT
  simpa only [adjointPhysicalMode, LinearMap.smul_apply, LinearMap.sum_apply,
    neg_neg, norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    adjointMass, Finset.card_range, Nat.cast_add, Nat.cast_one, Finset.sum_mul, mul_assoc, T] using h

 

theorem bothColumnGrowth {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N) {a : V} {d p q : ℕ}
    (Ha : A.ColumnGrowth X a d p q)
    (H : ∀ j ≤ d, A.ColumnGrowth X ((A.virasoroMode 1^j) (U.pct a)) (d-j) p q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N,
      A.ColumnControl a d N (C * (N + 1 : ℝ)^p * X N^q) ∧
      U.AdjointColumnControl a d N (C * (N + 1 : ℝ)^p * X N^q) := by
  obtain ⟨C, hC, HC⟩ := Ha
  obtain ⟨R, hR, HR⟩ := A.finite_columnGrowth_uniform hX (Finset.range (d + 1))
    (fun j => (A.virasoroMode 1^j) (U.pct a)) (fun j => d-j) p q
    (fun j hj => H j (by have := Finset.mem_range.mp hj; omega))
  refine ⟨C + adjointMass d * R, add_nonneg hC (mul_nonneg (adjointMass_nonneg d) hR), ?_⟩
  intro N
  have hXN := zero_le_one.trans (hX N)
  have hM := adjointMass_nonneg d
  constructor
  · apply A.columnControl_mono (HC N)
    gcongr
    exact le_add_of_nonneg_right (mul_nonneg hM hR)
  · intro v hv
    have H' := U.adjointColumnControl_of_columns
      (fun j hj => HR j (Finset.mem_range.mpr (by omega)) N) v hv
    apply H'.trans
    calc
      _ = (adjointMass d * R) * (N + 1 : ℝ)^p * X N^q * ‖v‖^2 := by ring
      _ ≤ _ := by gcongr; exact le_add_of_nonneg_left hC

theorem bothSharpColumnGrowth {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d)
    (H : ∀ e ≤ d, ∀ b ∈ A.grade e, A.ColumnGrowth X b e (2*e-1) (2*e)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N,
      A.ColumnControl a d N (C * (N + 1 : ℝ)^(2*d-1) * X N^(2*d)) ∧
      U.AdjointColumnControl a d N (C * (N + 1 : ℝ)^(2*d-1) * X N^(2*d)) := by
  apply U.bothColumnGrowth hX (H d le_rfl a ha)
  intro j hj
  apply A.columnGrowth_mono hX
    (H (d-j) (by omega) _ (A.virasoro_one_pow_mem_grade (U.pct_mem_grade ha) j hj)) <;> omega

end UnitaryStructure

 

theorem vacuum_columnGrowth (X : ℕ → ℝ) : A.ColumnGrowth X A.vacuum 0 0 0 := by
  refine ⟨1, zero_le_one, ?_⟩
  intro N v hv
  simp only [physicalMode, Nat.cast_zero, add_zero, A.vacuum_mode, pow_zero, one_mul, mul_one]
  have he (m : ℕ) : (m : ℤ) - 1 = -1 ↔ m = 0 := by omega
  simp only [he]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro m hm hm0; simp [hm0]
  · simp

theorem vacuum_sharpGrowth (X : ℕ → ℝ) (hX : ∀ N, 1 ≤ X N) : A.SharpGrowth X A.vacuum 0 := by
  constructor
  · simpa only [Nat.mul_zero, Nat.zero_sub] using A.vacuum_columnGrowth X
  · apply A.zeroGrowth_mono hX (A.zeroGrowth_of_columnGrowth (by rw [A.grade_zero]; exact Submodule.mem_span_singleton_self _) (A.vacuum_columnGrowth X)) <;> norm_num

 
theorem translation_physicalMode (a : V) (d : ℕ) (m : ℤ) :
    A.physicalMode (A.toVertexAlgebra.translation a) (d+1) m =
      (-((m : ℂ) + d)) • A.physicalMode a d m := by
  simp only [physicalMode, Nat.cast_add, Nat.cast_one]
  rw [show m + ((d : ℤ) + 1) - 1 = m + d by omega, A.translation_covariance]
  push_cast
  rfl

theorem translation_columnGrowth {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N) {a : V} {d p q : ℕ}
    (H : A.ColumnGrowth X a d p q) :
    A.ColumnGrowth X (A.toVertexAlgebra.translation a) (d+1) (p+2) q := by
  obtain ⟨C, hC, HC⟩ := H
  refine ⟨(d + 1 : ℝ)^2 * C, by positivity, ?_⟩
  intro N v hv
  have hcoef (m : ℕ) (hm : m ∈ Finset.range (N + 1)) :
      ‖(-((m : ℂ) + d))‖^2 ≤ (d + 1 : ℝ)^2 * (N + 1 : ℝ)^2 := by
    have hmR : (m : ℝ) ≤ N := by exact_mod_cast (show m ≤ N by have := Finset.mem_range.mp hm; omega)
    have he : ‖(-((m : ℂ) + d))‖ = (m + d : ℝ) := by
      rw [norm_neg, ← Nat.cast_add, Complex.norm_natCast, Nat.cast_add]
    rw [he, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Nat.cast_nonneg (α := ℝ) d, Nat.cast_nonneg (α := ℝ) N]
  have hXN := zero_le_one.trans (hX N)
  calc
    _ = ∑ m ∈ Finset.range (N + 1), ‖(-((m : ℂ) + d))‖^2 * ‖A.physicalMode a d m v‖^2 := by
      apply Finset.sum_congr rfl
      intro m _
      rw [A.translation_physicalMode, LinearMap.smul_apply, norm_smul, mul_pow, Int.cast_natCast]
    _ ≤ ∑ m ∈ Finset.range (N + 1), ((d + 1 : ℝ)^2 * (N + 1 : ℝ)^2) * ‖A.physicalMode a d m v‖^2 :=
      Finset.sum_le_sum fun m hm => mul_le_mul_of_nonneg_right (hcoef m hm) (sq_nonneg _)
    _ = ((d + 1 : ℝ)^2 * (N + 1 : ℝ)^2) * ∑ m ∈ Finset.range (N + 1), ‖A.physicalMode a d m v‖^2 := by rw [Finset.mul_sum]
    _ ≤ ((d + 1 : ℝ)^2 * (N + 1 : ℝ)^2) * (C * (N + 1 : ℝ)^p * X N^q * ‖v‖^2) :=
      mul_le_mul_of_nonneg_left (HC N v hv) (by positivity)
    _ = _ := by rw [pow_add]; ring

theorem translation_zeroGrowth {X : ℕ → ℝ} {a : V} {d p q : ℕ}
    (H : A.ZeroGrowth X a d p q) :
    A.ZeroGrowth X (A.toVertexAlgebra.translation a) (d+1) p q := by
  obtain ⟨C, hC, HC⟩ := H
  refine ⟨(d : ℝ)^2 * C, by positivity, ?_⟩
  intro N v hv
  rw [A.translation_physicalMode, LinearMap.smul_apply, norm_smul, mul_pow]
  simp only [Int.cast_zero, zero_add, norm_neg, Complex.norm_natCast]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (HC N v hv) (sq_nonneg (d : ℝ))

end CFTTypeVOA

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

theorem translation_sharpGrowth {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (H : A.SharpGrowth X a d) :
    A.SharpGrowth X (A.toVertexAlgebra.translation a) (d+1) := by
  by_cases hd : d = 0
  · subst d
    rw [A.grade_zero] at ha
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp ha
    have he : A.toVertexAlgebra.translation A.vacuum = 0 := by
      change mode A.fields A.vacuum (-2) A.vacuum = 0
      rw [A.vacuum_mode]
      norm_num
    rw [map_smul, he, smul_zero]
    exact ⟨A.columnGrowth_zero X _ _ _, A.zeroGrowth_zero X _ _ _⟩
  · constructor
    · exact A.columnGrowth_mono hX (A.translation_columnGrowth hX H.1) (by omega) (by omega)
    · exact A.zeroGrowth_mono hX (A.translation_zeroGrowth H.2) (by omega) (by omega)

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)

theorem normalProduct_degreeGrowth {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N)
    {a b : V} {d e u t : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hd : 1 ≤ d) (he : 1 ≤ e)
    (Ha : ∃ C : ℝ, 0 ≤ C ∧ ∀ N,
      A.ColumnControl a d N (C * (N + 1 : ℝ)^(2*d-1) * X N^(2*u)) ∧
      U.AdjointColumnControl a d N (C * (N + 1 : ℝ)^(2*d-1) * X N^(2*u)))
    (Hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ N,
      A.ColumnControl b e N (C * (N + 1 : ℝ)^(2*e-1) * X N^(2*t)) ∧
      U.AdjointColumnControl b e N (C * (N + 1 : ℝ)^(2*e-1) * X N^(2*t)))
    (Hsing : ∀ j < d - 1,
      A.ColumnGrowth X (mode A.fields a j b) (d+e-j-1) (2*(d+e)-2) (2*(u+t))) :
    A.SharpDegreeGrowth X (mode A.fields a (-1) b) (d+e) (u+t) := by
  obtain ⟨C, hC, HC⟩ := Ha
  obtain ⟨D, hD, HD⟩ := Hb
  obtain ⟨R, hR, HR⟩ := A.finite_columnGrowth_uniform hX (Finset.range (d-1))
    (fun j => mode A.fields a j b) (fun j => d+e-j-1) (2*(d+e)-2) (2*(u+t)) (fun j hj => Hsing j (Finset.mem_range.mp hj))
  have hM := sharpCorrectionMass_nonneg d
  have hconst : 0 ≤ 12 * C * D + 4 * sharpCorrectionMass d * R := by positivity
  have hp : (2*d-1)+(2*e-1) = 2*(d+e)-2 := by omega
  have hp' : (2*d-1)+(2*e-1)+1 = 2*(d+e)-1 := by omega
  have hq : 2*u+2*t = 2*(u+t) := by omega
  constructor
  · refine ⟨12 * C * D + 4 * sharpCorrectionMass d * R, hconst, ?_⟩
    intro N
    have hXN := zero_le_one.trans (hX N)
    apply A.columnControl_mono (U.normalProduct_columnControl ha hb hd
      (by positivity) (by positivity) (HC N).1 (HC N).2 (HD N).1 (HD N).2
      (fun j hj => HR j (Finset.mem_range.mpr hj) N))
    have hpow : (N + 1 : ℝ)^(2*(d+e)-2) ≤ (N + 1 : ℝ)^(2*(d+e)-1) :=
      pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) N]) (by omega)
    calc
      _ = 12*C*D*(N + 1 : ℝ)^((2*d-1)+(2*e-1)+1)*X N^(2*u+2*t) +
        4*sharpCorrectionMass d*R*(N + 1 : ℝ)^(2*(d+e)-2)*X N^(2*(u+t)) := by
        simp only [pow_add, pow_one]; ring
      _ ≤ 12*C*D*(N + 1 : ℝ)^(2*(d+e)-1)*X N^(2*(u+t)) +
        4*sharpCorrectionMass d*R*(N + 1 : ℝ)^(2*(d+e)-1)*X N^(2*(u+t)) := by
        rw [hp', hq]
        gcongr
      _ = _ := by ring
  · refine ⟨12 * C * D + 4 * sharpCorrectionMass d * R, hconst, ?_⟩
    intro N v hv
    have hXN := zero_le_one.trans (hX N)
    apply (U.normalProduct_zero_sq_le ha hb hd hv
      (by positivity) (by positivity) (HC N).1 (HC N).2 (HD N).1 (HD N).2
      (fun j hj => HR j (Finset.mem_range.mpr hj) N)).trans
    have hmax : max 1 (2*(d+e)-2) = 2*(d+e)-2 := by omega
    rw [hmax]
    calc
      _ = (8*C*D*(N + 1 : ℝ)^((2*d-1)+(2*e-1))*X N^(2*u+2*t) +
        4*sharpCorrectionMass d*R*(N + 1 : ℝ)^(2*(d+e)-2)*X N^(2*(u+t))) * ‖v‖^2 := by
        simp only [pow_add]; ring
      _ ≤ (12*C*D*(N + 1 : ℝ)^(2*(d+e)-2)*X N^(2*(u+t)) +
        4*sharpCorrectionMass d*R*(N + 1 : ℝ)^(2*(d+e)-2)*X N^(2*(u+t))) * ‖v‖^2 := by
        rw [hp, hq]
        gcongr
        norm_num
      _ = _ := by ring

end UnitaryStructure
end CFTTypeVOA

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

def sharpDegreeGrowthSubmodule (X : ℕ → ℝ) (d w : ℕ) : Submodule ℂ V where
  carrier := {a | A.SharpDegreeGrowth X a d w}
  zero_mem' := ⟨A.columnGrowth_zero X d _ _, A.zeroGrowth_zero X d _ _⟩
  add_mem' h k := ⟨A.columnGrowth_add h.1 k.1, A.zeroGrowth_add h.2 k.2⟩
  smul_mem' z _ h := ⟨A.columnGrowth_smul h.1 z, A.zeroGrowth_smul h.2 z⟩

theorem sharpDegreeGrowth_mono {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N) {a : V} {d w w' : ℕ}
    (H : A.SharpDegreeGrowth X a d w) (hw : w ≤ w') : A.SharpDegreeGrowth X a d w' :=
  ⟨A.columnGrowth_mono hX H.1 le_rfl (by omega), A.zeroGrowth_mono hX H.2 le_rfl (by omega)⟩

theorem translation_sharpDegreeGrowth {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N) {a : V} {d w : ℕ}
    (ha : a ∈ A.grade d) (H : A.SharpDegreeGrowth X a d w) :
    A.SharpDegreeGrowth X (A.toVertexAlgebra.translation a) (d+1) w := by
  by_cases hd : d = 0
  · subst d
    rw [A.grade_zero] at ha
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp ha
    have he : A.toVertexAlgebra.translation A.vacuum = 0 := by
      change mode A.fields A.vacuum (-2) A.vacuum = 0
      rw [A.vacuum_mode]
      norm_num
    rw [map_smul, he, smul_zero]
    exact ⟨A.columnGrowth_zero X _ _ _, A.zeroGrowth_zero X _ _ _⟩
  · constructor
    · exact A.columnGrowth_mono hX (A.translation_columnGrowth hX H.1) (by omega) le_rfl
    · exact A.zeroGrowth_mono hX (A.translation_zeroGrowth H.2) (by omega) le_rfl

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)

theorem adjointPhysicalMode_translation {a : V} {d : ℕ} (ha : a ∈ A.grade d) (m : ℤ) :
    U.adjointPhysicalMode (A.toVertexAlgebra.translation a) (d+1) m =
      (-((m : ℂ) + d)) • U.adjointPhysicalMode a d m := by
  have hT : A.toVertexAlgebra.translation a ∈ A.grade (d+1) := by
    rw [← A.virasoro_neg_one_eq_translation]
    exact A.virasoro_mem_grade ha (-1) (by omega)
  ext v
  apply ext_inner_left ℂ
  intro w
  rw [← U.adjointPhysicalMode_inner hT, A.translation_physicalMode, LinearMap.smul_apply,
    inner_smul_left, U.adjointPhysicalMode_inner ha, LinearMap.smul_apply, inner_smul_right]
  simp

theorem translation_bothColumnGrowth {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N) {a : V} {d p q : ℕ}
    (ha : a ∈ A.grade d)
    (H : ∃ C : ℝ, 0 ≤ C ∧ ∀ N,
      A.ColumnControl a d N (C * (N + 1 : ℝ)^p * X N^q) ∧
      U.AdjointColumnControl a d N (C * (N + 1 : ℝ)^p * X N^q)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N,
      A.ColumnControl (A.toVertexAlgebra.translation a) (d+1) N (C * (N + 1 : ℝ)^(p+2) * X N^q) ∧
      U.AdjointColumnControl (A.toVertexAlgebra.translation a) (d+1) N (C * (N + 1 : ℝ)^(p+2) * X N^q) := by
  obtain ⟨C, hC, HC⟩ := H
  refine ⟨(d + 1 : ℝ)^2 * C, by positivity, ?_⟩
  intro N
  have hXN := zero_le_one.trans (hX N)
  have hcoef (m : ℕ) (hm : m ∈ Finset.range (N+1)) (ε : ℤ) (hε : |(ε : ℝ)| ≤ 1) :
      ‖-(((ε * m : ℤ) : ℂ) + d)‖^2 ≤ (d + 1 : ℝ)^2 * (N + 1 : ℝ)^2 := by
    have hmR : (m : ℝ) ≤ N := by exact_mod_cast (show m ≤ N by have := Finset.mem_range.mp hm; omega)
    have hn : ‖-(((ε * m : ℤ) : ℂ) + d)‖ ≤ (d + 1 : ℝ) * (N + 1 : ℝ) := by
      rw [norm_neg]
      calc
        _ ≤ ‖(((ε * m : ℤ) : ℂ))‖ + ‖(d : ℂ)‖ := norm_add_le _ _
        _ = |(ε : ℝ)| * m + d := by simp only [Int.cast_mul, Int.cast_natCast,
          norm_mul, Complex.norm_intCast, Complex.norm_natCast]
        _ ≤ (m : ℝ) + d := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
        _ ≤ _ := by nlinarith [Nat.cast_nonneg (α := ℝ) d, Nat.cast_nonneg (α := ℝ) N]
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hn 2
  have step (F G : ℕ → Module.End ℂ V)
      (hf : ∀ m, ∃ z : ℂ, G m = z • F m ∧
        (m ∈ Finset.range (N+1) → ‖z‖^2 ≤ (d + 1 : ℝ)^2 * (N + 1 : ℝ)^2))
      (hF : ∀ v ∈ A.energyCutoff N, (∑ m ∈ Finset.range (N+1), ‖F m v‖^2) ≤ C*(N+1 : ℝ)^p*X N^q*‖v‖^2) :
      ∀ v ∈ A.energyCutoff N, (∑ m ∈ Finset.range (N+1), ‖G m v‖^2) ≤
        ((d+1 : ℝ)^2*C)*(N+1 : ℝ)^(p+2)*X N^q*‖v‖^2 := by
    intro v hv
    calc
      _ ≤ ∑ m ∈ Finset.range (N+1), ((d+1 : ℝ)^2*(N+1 : ℝ)^2)*‖F m v‖^2 := by
        apply Finset.sum_le_sum
        intro m hm
        obtain ⟨z, hz, hzn⟩ := hf m
        rw [hz, LinearMap.smul_apply, norm_smul, mul_pow]
        exact mul_le_mul_of_nonneg_right (hzn hm) (sq_nonneg _)
      _ = ((d+1 : ℝ)^2*(N+1 : ℝ)^2) * ∑ m ∈ Finset.range (N+1), ‖F m v‖^2 := by rw [Finset.mul_sum]
      _ ≤ ((d+1 : ℝ)^2*(N+1 : ℝ)^2) * (C*(N+1 : ℝ)^p*X N^q*‖v‖^2) :=
        mul_le_mul_of_nonneg_left (hF v hv) (by positivity)
      _ = _ := by rw [pow_add]; ring
  constructor
  · apply step (fun m => A.physicalMode a d m) _ _ (HC N).1
    intro m
    refine ⟨-((m : ℂ)+d), ?_, ?_⟩
    · simpa only [Int.cast_natCast] using A.translation_physicalMode a d m
    · intro hm
      simpa using hcoef m hm 1 (by norm_num)
  · apply step (fun m => U.adjointPhysicalMode a d (-(m : ℤ))) _ _ (HC N).2
    intro m
    refine ⟨-((-(m : ℤ) : ℤ) + d : ℂ), ?_, ?_⟩
    · simpa only [Int.cast_add, Int.cast_natCast] using U.adjointPhysicalMode_translation ha (-(m : ℤ))
    · intro hm
      simpa using hcoef m hm (-1) (by norm_num)

end UnitaryStructure
end CFTTypeVOA

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)

include U

 

theorem homogeneousC2_le_sharpDegreeGrowth {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N) (w : ℕ)
    (hprev : ∀ d < w, ∀ a ∈ A.grade d, A.SharpGrowth X a d) :
    A.homogeneousC2 w ≤ A.sharpDegreeGrowthSubmodule X w (w-1) := by
  apply Submodule.span_le.mpr
  rintro x ⟨d, e, a, b, ha, hb, hweight, rfl⟩
  change A.SharpDegreeGrowth X (mode A.fields a (-2) b) w (w-1)
  by_cases he : e = 0
  · subst e
    have hweight' : w = d + 1 := by omega
    rw [A.grade_zero] at hb
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp hb
    rw [map_smul]
    have H := A.translation_sharpDegreeGrowth hX ha (hprev d (by omega) a ha)
    rw [hweight']
    change A.SharpDegreeGrowth X (z • A.toVertexAlgebra.translation a) (d+1) (d+1-1)
    simpa only [Nat.add_sub_cancel] using
      (show A.SharpDegreeGrowth X (z • A.toVertexAlgebra.translation a) (d+1) d from
        ⟨A.columnGrowth_smul H.1 z, A.zeroGrowth_smul H.2 z⟩)
  by_cases hd : d = 0
  · subst d
    rw [A.grade_zero] at ha
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp ha
    rw [mode_smul, LinearMap.smul_apply, A.vacuum_mode]
    norm_num
    exact ⟨A.columnGrowth_zero X _ _ _, A.zeroGrowth_zero X _ _ _⟩
  have hTa : A.toVertexAlgebra.translation a ∈ A.grade (d+1) := by
    rw [← A.virasoro_neg_one_eq_translation]
    exact A.virasoro_mem_grade ha (-1) (by omega)
  have Ha := U.bothSharpColumnGrowth hX ha
    (fun f hf c hc => (hprev f (by omega) c hc).1)
  have HT := U.translation_bothColumnGrowth hX ha Ha
  have hpexp : (2*d-1)+2 = 2*(d+1)-1 := by omega
  rw [hpexp] at HT
  have HB := U.bothSharpColumnGrowth hX hb
    (fun f hf c hc => (hprev f (by omega) c hc).1)
  have HS : ∀ j < (d+1)-1,
      A.ColumnGrowth X (mode A.fields (A.toVertexAlgebra.translation a) j b)
        (d+1+e-j-1) (2*(d+1+e)-2) (2*(d+e)) := by
    intro j hj
    have hgrade := A.mode_mem_grade hTa hb (j : ℤ)
      (k := d+1+e-j-1) (by omega)
    exact A.columnGrowth_mono hX (hprev _ (by omega) _ hgrade).1 (by omega) (by omega)
  have H := U.normalProduct_degreeGrowth hX hTa hb (by omega) (by omega) HT HB HS
  have heq : mode A.fields (A.toVertexAlgebra.translation a) (-1) b = mode A.fields a (-2) b := by
    rw [A.translation_covariance]
    norm_num
  rw [heq] at H
  convert H using 1 <;> omega

 

theorem grade_sharpGrowth {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N) (D : ℕ)
    (hsmall : ∀ d, 1 ≤ d → d ≤ D → ∀ a ∈ A.grade d, A.IsQuasiPrimary a →
      A.SharpGrowth X a d)
    (hcut : ∀ d, D < d → A.grade d ≤ A.toVertexAlgebra.c2) :
    ∀ d, ∀ a ∈ A.grade d, A.SharpGrowth X a d := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro a ha
    by_cases hd0 : d = 0
    · subst d
      rw [A.grade_zero] at ha
      obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp ha
      exact ⟨A.columnGrowth_smul (A.vacuum_sharpGrowth X hX).1 z,
        A.zeroGrowth_smul (A.vacuum_sharpGrowth X hX).2 z⟩
    by_cases hdD : d ≤ D
    · obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd0
      obtain ⟨q, hq, hqq, b, hb, hab⟩ := U.quasiPrimary_decomposition ha
      rw [hab, A.virasoro_neg_one_eq_translation]
      have H := A.translation_sharpGrowth hX hb (ih e (by omega) b hb)
      have Q := hsmall _ (by omega) hdD q hq hqq
      exact ⟨A.columnGrowth_add Q.1 H.1, A.zeroGrowth_add Q.2 H.2⟩
    · have hc : a ∈ A.homogeneousC2 d := by
        rw [A.homogeneousC2_eq]
        exact ⟨hcut d (by omega) ha, ha⟩
      exact A.sharpDegreeGrowth_mono hX
        (U.homogeneousC2_le_sharpDegreeGrowth hX d ih hc) (by omega)

end UnitaryStructure
end CFTTypeVOA

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

 
def zeroModeOnCutoff (a : V) (d N : ℕ) : A.energyCutoff N →L[ℂ] V :=
  LinearMap.toContinuousLinearMap ((A.physicalMode a d 0).comp (A.energyCutoff N).subtype)

def zeroModeCutoffNorm (a : V) (d N : ℕ) : ℝ := ‖A.zeroModeOnCutoff a d N‖

theorem zeroMode_norm_le (a : V) (d : ℕ) {N : ℕ} {v : V} (hv : v ∈ A.energyCutoff N) :
    ‖A.physicalMode a d 0 v‖ ≤ A.zeroModeCutoffNorm a d N * ‖v‖ :=
  (A.zeroModeOnCutoff a d N).le_opNorm ⟨v, hv⟩



def sharpColumnQuantity (a : V) (d N : ℕ) : ℝ :=
  A.positiveColumnNorm a d N ^ 2 / (N+1 : ℝ)^(2*d-1)

def sharpZeroQuantity (a : V) (d N : ℕ) : ℝ :=
  A.zeroModeCutoffNorm a d N ^ 2 / (N+1 : ℝ)^(max 1 (2*d-2))

def rawSharpMajorant (D : ℕ) (S : ℕ → Finset V) (N : ℕ) : ℝ :=
  1 + ∑ d ∈ Finset.range (D+1), ∑ a ∈ S d,
    ((A.sharpColumnQuantity a d N)^((2*d : ℕ) : ℝ)⁻¹ +
     (A.sharpZeroQuantity a d N)^((2*d : ℕ) : ℝ)⁻¹)

 

def sharpMajorant (D : ℕ) (S : ℕ → Finset V) (N : ℕ) : ℝ :=
  (Finset.range (N+1)).sup' (by simp) (A.rawSharpMajorant D S)

theorem sharpColumnQuantity_nonneg (a : V) (d N : ℕ) : 0 ≤ A.sharpColumnQuantity a d N := by
  unfold sharpColumnQuantity
  positivity

theorem sharpZeroQuantity_nonneg (a : V) (d N : ℕ) : 0 ≤ A.sharpZeroQuantity a d N := by
  unfold sharpZeroQuantity
  positivity

theorem one_le_rawSharpMajorant (D : ℕ) (S : ℕ → Finset V) (N : ℕ) :
    1 ≤ A.rawSharpMajorant D S N := by
  unfold rawSharpMajorant
  have H : 0 ≤ ∑ d ∈ Finset.range (D+1), ∑ a ∈ S d,
    ((A.sharpColumnQuantity a d N)^((2*d : ℕ) : ℝ)⁻¹ +
     (A.sharpZeroQuantity a d N)^((2*d : ℕ) : ℝ)⁻¹) := by
    apply Finset.sum_nonneg
    intro d _
    apply Finset.sum_nonneg
    intro a _
    exact add_nonneg (Real.rpow_nonneg (A.sharpColumnQuantity_nonneg a d N) _)
      (Real.rpow_nonneg (A.sharpZeroQuantity_nonneg a d N) _)
  linarith

theorem rawSharpMajorant_le (D : ℕ) (S : ℕ → Finset V) {N M : ℕ} (hNM : N ≤ M) :
    A.rawSharpMajorant D S N ≤ A.sharpMajorant D S M := by
  exact Finset.le_sup' _ (Finset.mem_range.mpr (by omega))

theorem one_le_sharpMajorant (D : ℕ) (S : ℕ → Finset V) (N : ℕ) :
    1 ≤ A.sharpMajorant D S N :=
  (A.one_le_rawSharpMajorant D S N).trans (A.rawSharpMajorant_le D S le_rfl)

theorem sharpMajorant_mono (D : ℕ) (S : ℕ → Finset V) : Monotone (A.sharpMajorant D S) := by
  intro N M hNM
  apply Finset.sup'_le
  intro k hk
  exact A.rawSharpMajorant_le D S (by have := Finset.mem_range.mp hk; omega)

theorem root_sharpQuantity_le (D : ℕ) (S : ℕ → Finset V) {N d : ℕ} {a : V}
    (hd : d ≤ D) (ha : a ∈ S d) :
    (A.sharpColumnQuantity a d N)^((2*d : ℕ) : ℝ)⁻¹ ≤ A.sharpMajorant D S N ∧
    (A.sharpZeroQuantity a d N)^((2*d : ℕ) : ℝ)⁻¹ ≤ A.sharpMajorant D S N := by
  let F (e : ℕ) (b : V) := (A.sharpColumnQuantity b e N)^((2*e : ℕ) : ℝ)⁻¹ +
     (A.sharpZeroQuantity b e N)^((2*e : ℕ) : ℝ)⁻¹
  have hF (e : ℕ) (b : V) : 0 ≤ F e b :=
    add_nonneg (Real.rpow_nonneg (A.sharpColumnQuantity_nonneg b e N) _)
      (Real.rpow_nonneg (A.sharpZeroQuantity_nonneg b e N) _)
  have H₁ := Finset.single_le_sum (fun b _ => hF d b) ha
  have H₂ := Finset.single_le_sum (s := Finset.range (D+1)) (a := d) (f := fun e => ∑ b ∈ S e, F e b)
    (fun e _ => Finset.sum_nonneg (fun b _ => hF e b)) (Finset.mem_range.mpr (by omega))
  have H₃ : F d a ≤ A.sharpMajorant D S N := by
    apply (H₁.trans H₂).trans
    exact (le_add_of_nonneg_left zero_le_one).trans (A.rawSharpMajorant_le D S le_rfl)
  constructor
  · exact (le_add_of_nonneg_right (Real.rpow_nonneg (A.sharpZeroQuantity_nonneg a d N) _)).trans H₃
  · exact (le_add_of_nonneg_left (Real.rpow_nonneg (A.sharpColumnQuantity_nonneg a d N) _)).trans H₃
end CFTTypeVOA
end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_HilbertCore
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
open Filter

open scoped ContDiff



section GraphData
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace ClosedGraphData

theorem projection_selfAdjoint (T : H →ₗ.[ℂ] H) (hT : T.IsClosed) :
    IsSelfAdjoint (projection T hT) := by
  let : IsClosed (graph T : Set (Double H)) := graph_closed hT
  exact isSelfAdjoint_starProjection (graph T)

theorem coordinate_eq_adjoint (i : Bool) :
    coordinate (H := H) i = (inclusion i).adjoint := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  cases i <;> simp [coordinate, inclusion, WithLp.prod_inner_apply]

theorem adjoint_inclusion (i : Bool) : (inclusion (H := H) i).adjoint = coordinate i :=
  (coordinate_eq_adjoint i).symm

theorem adjoint_coordinate (i : Bool) : (coordinate (H := H) i).adjoint = inclusion i := by
  rw [coordinate_eq_adjoint, ContinuousLinearMap.adjoint_adjoint]

 
theorem star_entry (T : H →ₗ.[ℂ] H) (hT : T.IsClosed) (i j : Bool) :
    star (entry T hT i j) = entry T hT j i := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  simp only [entry, ContinuousLinearMap.adjoint_comp, adjoint_inclusion,
    adjoint_coordinate, (projection_selfAdjoint T hT).adjoint_eq,
    ContinuousLinearMap.comp_assoc]

 
def diagonalAction (Q : H →L[ℂ] H) : Double H →L[ℂ] Double H :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H H).symm.toContinuousLinearMap.comp
    ((Q.prodMap Q).comp (WithLp.prodContinuousLinearEquiv 2 ℂ H H).toContinuousLinearMap)

theorem diagonalAction_adj (Q : H →L[ℂ] H) :
    (diagonalAction Q).adjoint = diagonalAction Q.adjoint := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  change inner ℂ (WithLp.toLp 2 (Q.adjoint x.ofLp.1, Q.adjoint x.ofLp.2)) y =
    inner ℂ x (WithLp.toLp 2 (Q y.ofLp.1, Q y.ofLp.2))
  simp only [WithLp.prod_inner_apply,
    ContinuousLinearMap.adjoint_inner_left]

omit [CompleteSpace H] in
theorem coordinate_diagonalAction (Q : H →L[ℂ] H) (i : Bool) :
    (coordinate i).comp (diagonalAction Q) = Q.comp (coordinate i) := by
  ext x
  cases i <;> simp [coordinate, diagonalAction]

omit [CompleteSpace H] in
theorem diagonalAction_inclusion (Q : H →L[ℂ] H) (i : Bool) :
    (diagonalAction Q).comp (inclusion i) = (inclusion i).comp Q := by
  ext x
  cases i <;> simp [inclusion, diagonalAction]



end ClosedGraphData
end GraphData
end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_GraphCommutants
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
open Filter
open scoped ContDiff
section GraphData
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace ClosedGraphData

theorem entry_commutes_of_graph_invariant
    (T : H →ₗ.[ℂ] H) (hT : T.IsClosed) (Q : H →L[ℂ] H)
    (hQ : ∀ x y : H, (x,y) ∈ T.graph → (Q x,Q y) ∈ T.graph)
    (hQa : ∀ x y : H, (x,y) ∈ T.graph → (Q.adjoint x,Q.adjoint y) ∈ T.graph)
    (i j : Bool) : Q * entry T hT i j = entry T hT i j * Q := by
  have hinv : ∀ z ∈ graph T, diagonalAction Q z ∈ graph T := by
    intro z hz
    exact hQ _ _ hz
  have hinva : ∀ z ∈ graph T, (diagonalAction Q).adjoint z ∈ graph T := by
    rw [diagonalAction_adj]
    intro z hz
    exact hQa _ _ hz
  let : IsClosed (graph T : Set (Double H)) := graph_closed hT
  have hP : (diagonalAction Q).comp (projection T hT) =
      (projection T hT).comp (diagonalAction Q) :=
    commutes_projection_of_reduces (graph T) (diagonalAction Q) hinv hinva
  change Q.comp (entry T hT i j) = (entry T hT i j).comp Q
  have hc : Q.comp (coordinate i) = (coordinate i).comp (diagonalAction Q) :=
    (coordinate_diagonalAction Q i).symm
  calc
    Q.comp (entry T hT i j) =
        ((coordinate i).comp (diagonalAction Q)).comp ((projection T hT).comp (inclusion j)) := by
      rw [← hc]; rfl
    _ = (coordinate i).comp (((projection T hT).comp (diagonalAction Q)).comp (inclusion j)) := by
      simpa only [ContinuousLinearMap.comp_assoc] using
        congrArg (fun R => (coordinate i).comp (R.comp (inclusion j))) hP
    _ = (entry T hT i j).comp Q := by
      simp only [ContinuousLinearMap.comp_assoc, diagonalAction_inclusion, entry]

end ClosedGraphData

namespace LocalOperatorAlgebra
open scoped Pointwise


theorem subset_generated (s : Set (H →L[ℂ] H)) : s ⊆ generated s := by
  intro x hx
  exact StarAlgebra.adjoin_le_centralizer_centralizer ℂ s
    (StarAlgebra.subset_adjoin ℂ s hx)

theorem generated_mono {s t : Set (H →L[ℂ] H)} (hst : s ⊆ t) :
    generated s ≤ generated t :=
  StarSubalgebra.centralizer_le _ _ _ (StarSubalgebra.centralizer_le _ _ _ hst)

theorem generated_le {s : Set (H →L[ℂ] H)} {M : VonNeumannAlgebra H}
    (h : s ⊆ M) : generated s ≤ M := by
  have hle := StarSubalgebra.centralizer_le ℂ _ _ (StarSubalgebra.centralizer_le ℂ _ _ h)
  change (StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ s : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) ⊆ _
  change (StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ s : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) ⊆
    (StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ (M : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)) at hle
  simpa only [StarSubalgebra.coe_centralizer_centralizer,
    StarMemClass.star_coe_eq, Set.union_self, M.centralizer_centralizer] using hle



theorem generated_le_commutant_iff (s t : Set (H →L[ℂ] H)) :
    generated s ≤ (generated t).commutant ↔
      ∀ x ∈ s, ∀ y ∈ t, y*x = x*y ∧ star y*x = x*star y := by
  constructor
  · intro h x hx y hy
    have hmem := h (subset_generated s hx)
    rw [← SetLike.mem_coe, coe_generated_commutant] at hmem
    exact ⟨hmem y (Set.mem_union_left _ hy),
      hmem (star y) (Set.mem_union_right _ (by simpa using hy))⟩
  · intro h
    apply generated_le
    intro x hx
    rw [coe_generated_commutant]
    rintro y (hy | hy)
    · exact (h x hx y hy).1
    · have hy' : star y ∈ t := hy
      simpa using (h x hx (star y) hy').2

end LocalOperatorAlgebra

end GraphData

namespace CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {A : CFTTypeVOA V} (U : A.UnitaryStructure)



theorem closedSmoothField_graphData_mem (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (f : SmoothCircleFunction)
    {O : Set (AddCircle (2*Real.pi))} (hf : tsupport f.onCircle ⊆ O) (i j : Bool) :
    ClosedGraphData.entry (U.closedSmoothField hc a d f)
      (U.closedSmoothField_isClosed hc ha f) i j ∈ U.localAlgebra hc O :=
  LocalOperatorAlgebra.subset_generated _ ⟨a,d,ha,f,hf,i,j,rfl⟩



end CFTTypeVOA.UnitaryStructure

namespace CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {A : CFTTypeVOA V} (U : A.UnitaryStructure)



theorem energyCoordinates_coe (a : V) (d : ℕ) :
    (U.energyCoordinates (a : Completion V) d).val = A.gradeComponent d a := by
  apply A.homogeneous_induction (P := fun a =>
    (U.energyCoordinates (a : Completion V) d).val = A.gradeComponent d a)
  · change (U.energyCoordinates ((Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V) 0) d).val = _
    rw [map_zero, map_zero]
    simp only [map_zero, lp.coeFn_zero, Pi.zero_apply, Submodule.coe_zero]
  · intro e b hb
    rw [energyCoordinates_grade U ⟨b,hb⟩]
    by_cases hed : e = d
    · subst e
      simp [A.gradeComponent_of_mem hb]
    · simp [lp.single_apply, Ne.symm hed, A.gradeComponent_of_mem_ne hed hb]
  · intro b c hb hc
    change (U.energyCoordinates ((Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V) (b+c)) d).val = _
    simp only [map_add, lp.coeFn_add, Pi.add_apply, Submodule.coe_add]
    change (U.energyCoordinates (b : Completion V) d).val +
      (U.energyCoordinates (c : Completion V) d).val = _
    rw [hb,hc]

end CFTTypeVOA.UnitaryStructure

open scoped ENNReal
end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_BoundedMultiplierSingle
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
universe u
open scoped Topology
open Filter
namespace StronglyRationalVOA

namespace HilbertScale
open scoped ENNReal
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [DecidableEq ι] [∀ i, CompleteSpace (G i)]

omit [DecidableEq ι] in
theorem real_boundedMultiplier_selfAdjoint (w : ι → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hw : ∀ i, ‖(w i : ℂ)‖ ≤ C) :
    IsSelfAdjoint (boundedMultiplier (G := G) (fun i => (w i : ℂ)) hC hw) := by
  change (boundedMultiplier (G := G) (fun i => (w i : ℂ)) hC hw).adjoint =
    boundedMultiplier (G := G) (fun i => (w i : ℂ)) hC hw
  rw [boundedMultiplier_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  simp only [boundedMultiplier_apply,Complex.star_def,Complex.conj_ofReal]

end HilbertScale

end StronglyRationalVOA

namespace StronglyRationalVOA.HilbertScale
open Filter
open scoped Topology
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [instDec : DecidableEq ι]

variable [∀ i, CompleteSpace (G i)]

omit [DecidableEq ι]

theorem resolventWeight_add_complementWeight (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (n : ℕ) (i : ι) : resolventWeight h n i + complementWeight h n i = 1 := by
  unfold resolventWeight complementWeight
  have := hh i
  rw [← add_div,div_self (by positivity)]

theorem complementWeight_tendsto_zero (h : ι → ℝ) (i : ι) :
    Tendsto (fun n => complementWeight h n i) atTop (𝓝 0) := by
  apply Tendsto.const_div_atTop
  exact tendsto_atTop_add_const_right atTop (h i)
    (tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ)))

theorem resolvent_add_complement (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (n : ℕ) (x : Space G) :
    resolvent h hh n x + complement h hh n x = x := by
  apply lp.ext
  funext i
  change (resolventWeight h n i : ℂ) • x i + (complementWeight h n i : ℂ) • x i = x i
  rw [← add_smul,← Complex.ofReal_add,resolventWeight_add_complementWeight h hh,Complex.ofReal_one,one_smul]

theorem resolvent_selfAdjoint (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (n : ℕ) :
    IsSelfAdjoint (resolvent (G := G) h hh n) :=
  real_boundedMultiplier_selfAdjoint _ _ _

theorem resolvent_norm (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (n : ℕ) :
    ‖resolvent (G := G) h hh n‖ ≤ 1 := boundedMultiplier_norm _ _ _

end StronglyRationalVOA.HilbertScale

namespace StronglyRationalVOA

namespace RapidCoefficients

theorem int_mul {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    RapidCoefficients (fun n => (n : ℂ)*f n) := by
  intro p
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ (hf (p+1))
  intro n
  have hn : ‖(n : ℂ)‖ = |(n : ℝ)| := by
    rw [← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs]
  rw [norm_mul,hn,pow_succ]
  have h := mul_nonneg (norm_nonneg (f n)) (pow_nonneg (by positivity : 0 ≤ 1+|(n : ℝ)|) p)
  nlinarith

end RapidCoefficients

namespace CFTTypeVOA
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (A : CFTTypeVOA V)



namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)



theorem smearedMap_energy_commutator {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a) (he : A.PolynomialEnergyBound a)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (hreal : ∀ n, star (f n) = f (-n))
    (x y : V) :
    inner ℂ (A.smearedMap a d he f hf x) (A.energyShift y : Completion V)-
      inner ℂ (A.energyShift x : Completion V) (A.smearedMap a d he f hf y) =
    inner ℂ (A.smearedMap a d he (fun n => -(n : ℂ)*f n)
      (by simpa only [neg_mul,one_mul] using hf.int_mul.smul (-1)) x) (y : Completion V) := by
  have hf' : RapidCoefficients (fun n => -(n : ℂ)*f n) := by
    simpa only [neg_mul,one_mul] using hf.int_mul.smul (-1)
  rw [← U.smearedMap_symmetric ha hq hh he hf hreal (A.energyShift x) y]
  simp only [smearedMap_apply]
  rw [inner_tsum_left (A.summable_norm_physicalSmear he d hf x).of_norm,
      inner_tsum_left (A.summable_norm_physicalSmear he d hf (A.energyShift x)).of_norm,
      inner_tsum_left (A.summable_norm_physicalSmear he d hf' x).of_norm]
  rw [← (summable_inner_left (A.summable_norm_physicalSmear he d hf x).of_norm
    (A.energyShift y : Completion V)).tsum_sub
      (summable_inner_left (A.summable_norm_physicalSmear he d hf (A.energyShift x)).of_norm
        (y : Completion V))]
  apply tsum_congr
  intro n
  simp only [inner_smul_left,Completion.inner_coe]
  rw [← U.energyShift_adjoint,← mul_sub,← inner_sub_left,A.energyShift_physical_commutator ha,
    inner_smul_left]
  simp only [map_mul]
  ring

end UnitaryStructure
end CFTTypeVOA
end StronglyRationalVOA

namespace StronglyRationalVOA.HilbertScale
open Filter
open scoped Topology
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [DecidableEq ι] [∀ i, CompleteSpace (G i)]

theorem weighted_resolvent_core (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (n : ℕ)
    (x : finiteCore (G := G)) :
    coreDiagonal (fun i => (h i : ℂ))
      (coreMultiplier (fun i => (resolventWeight h n i : ℂ)) x) =
    ((n : ℂ)+1) • complement h hh n x := by
  apply lp.ext
  funext i
  simp only [coreDiagonal_apply,coreMultiplier_apply,lp.coeFn_smul,Pi.smul_apply,
    complement_apply,smul_smul]
  congr 1
  unfold resolventWeight complementWeight
  push_cast
  ring
end StronglyRationalVOA.HilbertScale

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_GeneratorSharpGrowth
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
theorem generator_sharpGrowth (D : ℕ) (S : ℕ → Finset V) {d : ℕ} {a : V}
    (hd : 0 < d) (hD : d ≤ D) (ha : a ∈ S d) :
    A.SharpGrowth (A.sharpMajorant D S) a d := by
  have hquant (N : ℕ) : A.sharpColumnQuantity a d N ≤ A.sharpMajorant D S N^(2*d) ∧
      A.sharpZeroQuantity a d N ≤ A.sharpMajorant D S N^(2*d) := by
    obtain ⟨H, K⟩ := A.root_sharpQuantity_le D S hD ha (N := N)
    have H' := pow_le_pow_left₀ (Real.rpow_nonneg (A.sharpColumnQuantity_nonneg a d N) _) H (2*d)
    have K' := pow_le_pow_left₀ (Real.rpow_nonneg (A.sharpZeroQuantity_nonneg a d N) _) K (2*d)
    rw [Real.rpow_inv_natCast_pow (A.sharpColumnQuantity_nonneg a d N) (by omega)] at H'
    rw [Real.rpow_inv_natCast_pow (A.sharpZeroQuantity_nonneg a d N) (by omega)] at K'
    exact ⟨H', K'⟩
  constructor
  · refine ⟨1, zero_le_one, ?_⟩
    intro N v hv
    have H := (div_le_iff₀ (by positivity : 0 < (N+1 : ℝ)^(2*d-1))).mp (hquant N).1
    apply (A.sum_positive_modes_sq_le a d hv).trans
    simpa only [one_mul, mul_comm (A.sharpMajorant D S N^(2*d))] using
      mul_le_mul_of_nonneg_right H (sq_nonneg ‖v‖)
  · refine ⟨1, zero_le_one, ?_⟩
    intro N v hv
    have H := (div_le_iff₀ (by positivity : 0 < (N+1 : ℝ)^(max 1 (2*d-2)))).mp (hquant N).2
    have Z := pow_le_pow_left₀ (norm_nonneg _) (A.zeroMode_norm_le a d hv) 2
    rw [mul_pow] at Z
    apply Z.trans
    simpa only [one_mul, mul_comm (A.sharpMajorant D S N^(2*d))] using
      mul_le_mul_of_nonneg_right H (sq_nonneg ‖v‖)

end CFTTypeVOA

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U

 

theorem exists_sharpMajorant (hc : A.toVertexAlgebra.C2Cofinite) :
    ∃ D : ℕ, 2 ≤ D ∧ ∃ S : ℕ → Finset V,
      (∀ d, d = 0 ∨ D < d → S d = ∅) ∧
      (∀ d, ∀ a ∈ S d, 1 ≤ d ∧ d ≤ D ∧ a ∈ A.grade d ∧
        A.IsQuasiPrimary a ∧ U.IsHermitian d a) ∧
      (∀ d, 1 ≤ d → d ≤ D → ∀ a ∈ A.grade d, A.IsQuasiPrimary a →
        a ∈ Submodule.span ℂ (S d : Set V)) ∧
      (∀ d, D < d → A.grade d ≤ A.toVertexAlgebra.c2) ∧
      (∀ w, ∀ a ∈ A.grade w, A.SharpGrowth (A.sharpMajorant D S) a w) := by
  classical
  obtain ⟨D, hD, hcut⟩ := A.exists_c2_weight_cutoff hc
  choose R hR hspan using U.exists_hermitian_quasiPrimary_spanning
  let S : ℕ → Finset V := fun d => if 1 ≤ d ∧ d ≤ D then R d else ∅
  have hS (d : ℕ) (a : V) (ha : a ∈ S d) :
      1 ≤ d ∧ d ≤ D ∧ a ∈ A.grade d ∧ A.IsQuasiPrimary a ∧ U.IsHermitian d a := by
    dsimp only [S] at ha
    split_ifs at ha with hd
    · exact ⟨hd.1, hd.2, hR d a ha⟩
    · simp at ha
  have hspanS (d : ℕ) (hd : 1 ≤ d) (hdD : d ≤ D) (a : V) (ha : a ∈ A.grade d)
      (hq : A.IsQuasiPrimary a) : a ∈ Submodule.span ℂ (S d : Set V) := by
    have he : S d = R d := by dsimp [S]; rw [ite_eq_left ⟨hd, hdD⟩]
    rw [he]
    exact hspan d a ha hq
  refine ⟨D, hD, S, ?_, hS, hspanS, hcut, ?_⟩
  · intro d hd
    dsimp [S]
    rw [ite_eq_right]
    omega
  · apply U.grade_sharpGrowth (A.one_le_sharpMajorant D S) D _ hcut
    intro d hd hdD a ha hq
    have hle : Submodule.span ℂ (S d : Set V) ≤
        A.sharpGrowthSubmodule (A.sharpMajorant D S) d := by
      apply Submodule.span_le.mpr
      intro b hb
      exact A.generator_sharpGrowth D S (by omega) hdD hb
    exact hle (hspanS d hd hdD a ha hq)

 

theorem physicalMode_cutoff_sq_of_grades {a : V} {d N : ℕ} (ha : a ∈ A.grade d)
    (m : ℤ) (K : ℝ)
    (H : ∀ h ≤ N, ∀ v ∈ A.grade h, ‖A.physicalMode a d m v‖^2 ≤ K*‖v‖^2)
    {v : V} (hv : v ∈ A.energyCutoff N) : ‖A.physicalMode a d m v‖^2 ≤ K*‖v‖^2 := by
  classical
  rw [physicalMode, U.mode_norm_sq_eq_sum_grades ha, U.norm_sq_eq_sum_grades v, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h hh
  have hhN : h ≤ N := by
    by_contra hnot
    have hz := hv h (by omega)
    have hne : A.gradingEquiv v h ≠ 0 := DFinsupp.mem_support_iff.mp hh
    exact hne (Subtype.ext hz)
  exact H h hhN _ (A.gradeComponent_mem h v)

end UnitaryStructure
end CFTTypeVOA

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

theorem finite_zeroGrowth_uniform {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N) {ι : Type*}
    (s : Finset ι) (a : ι → V) (d : ι → ℕ) (p q : ℕ)
    (H : ∀ i ∈ s, A.ZeroGrowth X (a i) (d i) p q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ∈ s, ∀ N v, v ∈ A.energyCutoff N →
      ‖A.physicalMode (a i) (d i) 0 v‖^2 ≤ C*(N+1 : ℝ)^p*X N^q*‖v‖^2 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨C, hC, HC⟩ := H i (Finset.mem_insert_self _ _)
    obtain ⟨D, hD, HD⟩ := ih (fun j hj => H j (Finset.mem_insert_of_mem hj))
    refine ⟨C + D, add_nonneg hC hD, ?_⟩
    intro j hj N v hv
    have hXN := zero_le_one.trans (hX N)
    rcases Finset.mem_insert.mp hj with rfl | hj
    · apply (HC N v hv).trans
      gcongr
      exact le_add_of_nonneg_right hD
    · apply (HD j hj N v hv).trans
      gcongr
      exact le_add_of_nonneg_left hC



theorem selfCommutator_sharp_bound {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hd : 2 ≤ d)
    (H : ∀ e ≤ 2*d-2, ∀ b ∈ A.grade e, A.SharpGrowth X b e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N m : ℕ) (v : V), v ∈ A.energyCutoff N →
      ‖A.selfCommutator a d m v‖ ≤
        C*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(2*d-3)*X N^(2*d-2)*‖v‖ := by
  have HS (j : ℕ) (hj : j ∈ Finset.range (2*d-1)) :
      A.ZeroGrowth X (mode A.fields a (j+1) a) (2*d-j-2) (2*(2*d-3)) (2*(2*d-2)) := by
    have hgrade := A.mode_mem_grade ha ha ((j+1 : ℕ) : ℤ)
      (k := 2*d-j-2) (by have := Finset.mem_range.mp hj; omega)
    have h := (H (2*d-j-2) (by omega) _ hgrade).2
    apply A.zeroGrowth_mono hX h <;> omega
  obtain ⟨C, hC, HC⟩ := A.finite_zeroGrowth_uniform hX (Finset.range (2*d-1))
    (fun j => mode A.fields a (j+1) a) (fun j => 2*d-j-2) (2*(2*d-3)) (2*(2*d-2)) HS
  refine ⟨(2*d-1 : ℕ)* (2*(d+1 : ℝ)^(2*d))*(C+1), by positivity, ?_⟩
  intro N m v hv
  have hXN := zero_le_one.trans (hX N)
  rw [A.selfCommutator_eq_sum_reduced ha (by omega)]
  calc
    _ ≤ ∑ j ∈ Finset.range (2*d-1),
      ‖((m+d-1).choose (j+1) : ℂ) - ((d-1).choose (j+1) : ℂ)‖ *
        ‖A.physicalMode (mode A.fields a (j+1) a) (2*d-j-2) 0 v‖ := by
      simpa only [norm_smul] using norm_sum_le (Finset.range (2*d-1))
        (fun j => (((m+d-1).choose (j+1) : ℂ) - ((d-1).choose (j+1) : ℂ)) •
          A.physicalMode (mode A.fields a (j+1) a) (2*d-j-2) 0 v)
    _ ≤ ∑ _j ∈ Finset.range (2*d-1),
      (2*(d+1 : ℝ)^(2*d)*(m+1 : ℝ)^(2*d)) *
        ((C+1)*(N+1 : ℝ)^(2*d-3)*X N^(2*d-2)*‖v‖) := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul (reduced_commutator_coefficient_bound (by omega) m j (Finset.mem_range.mp hj))
        (norm_of_sharp_square hXN hC N (2*d-3) (2*d-2) v _ (HC j hj N v hv))
        (norm_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end CFTTypeVOA

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U

 

theorem nonzeroModes_sharp_bound {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a)
    (hh : U.IsHermitian d a) (hd : 2 ≤ d)
    (H : ∀ e ≤ 2*d-2, ∀ b ∈ A.grade e, A.SharpGrowth X b e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N m : ℕ), 0 < m → ∀ v ∈ A.energyCutoff N,
      ‖A.physicalMode a d m v‖ ≤ C*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(d-1)*X N^(d-1)*‖v‖ ∧
      ‖A.physicalMode a d (-(m : ℤ)) v‖ ≤ C*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(d-1)*X N^(d-1)*‖v‖ := by
  obtain ⟨C, hC, HC⟩ := A.selfCommutator_sharp_bound hX ha hd H
  refine ⟨C+1, by positivity, ?_⟩
  intro N m hm v hv
  have hXN := zero_le_one.trans (hX N)
  let R := C*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(2*d-3)*X N^(2*d-2)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have HR (h : ℕ) (hhN : h ≤ N) (w : V) (hw : w ∈ A.grade h) :
      ‖A.selfCommutator a d m w‖ ≤ R*‖w‖ := HC N m w (A.grade_le_energyCutoff hhN hw)
  have HE : (N+1 : ℝ)*R = C*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(2*(d-1))*X N^(2*(d-1)) := by
    have hp : 2*(d-1) = (2*d-3)+1 := by omega
    have hq : 2*(d-1) = 2*d-2 := by omega
    dsimp [R]
    conv_rhs => arg 1; arg 2; rw [hp, pow_succ]
    rw [hq]
    ring
  have step (n : ℤ)
      (HN : ∀ h ≤ N, ∀ w ∈ A.grade h, ‖A.physicalMode a d n w‖^2 ≤ (h+1 : ℝ)*R*‖w‖^2) :
      ‖A.physicalMode a d n v‖ ≤ (C+1)*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(d-1)*X N^(d-1)*‖v‖ := by
    have Hsq : ‖A.physicalMode a d n v‖^2 ≤ ((N+1 : ℝ)*R)*‖v‖^2 := by
      apply U.physicalMode_cutoff_sq_of_grades ha n _ _ hv
      intro h hhN w hw
      apply (HN h hhN w hw).trans
      have hhR : (h : ℝ) ≤ N := by exact_mod_cast hhN
      gcongr
    rw [HE] at Hsq
    have Hnorm := norm_of_sharp_square hXN (show 0 ≤ C*(m+1 : ℝ)^(2*d) by positivity)
      N (d-1) (d-1) v _ Hsq
    apply Hnorm.trans
    have hM : 1 ≤ (m+1 : ℝ)^(2*d) := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) m])
    have hcoef : C*(m+1 : ℝ)^(2*d)+1 ≤ (C+1)*(m+1 : ℝ)^(2*d) := by nlinarith
    gcongr
  constructor
  · apply step m
    intro h hhN w hw
    have Hlower := U.lowering_norm_sq_of_commutator ha hq hh hm hR HR h hhN w hw
    apply Hlower.trans
    gcongr
    linarith
  · apply step (-(m : ℤ))
    intro h hhN w hw
    exact U.raising_norm_sq_of_commutator ha hq hh hm hR HR hhN hw

end UnitaryStructure
end CFTTypeVOA

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U

 

theorem zeroMode_sharpGrowth {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N) (hmono : Monotone X)
    {a : V} {d : ℕ} (hp : A.PolynomialEnergyBound a) (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a) (hd : 2 ≤ d)
    (H : ∀ e ≤ 2*d-2, ∀ b ∈ A.grade e, A.SharpGrowth X b e) :
    A.ZeroGrowth (fun N => X (2*N)) a d (2*(d-1)) (2*(d-1)) := by
  obtain ⟨C, hC, HC⟩ := U.nonzeroModes_sharp_bound hX ha hq hh hd H
  let F : ℕ → ℝ := fun N => (C+1)*2^(2*d)*(N+1 : ℝ)^(d-1)*X N^(d-1)
  have hF (N : ℕ) : 1 ≤ F N := by
    dsimp [F]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (by norm_num)))
      (one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) N]))) (one_le_pow₀ (hX N))
  have HF (N : ℕ) (v : V) (hv : v ∈ A.energyCutoff N) :
      ‖A.physicalMode a d 1 v‖ ≤ F N * ‖v‖ := by
    have H' := (HC N 1 (by decide) v hv).1
    apply H'.trans
    dsimp [F]
    have hXN := zero_le_one.trans (hX N)
    norm_num only [Nat.cast_one, show (1 : ℝ)+1 = 2 by norm_num]
    gcongr
    linarith
  obtain ⟨B, hB, HB⟩ := U.zeroMode_transfer hp ha hq hd
  let K := B*(C+1)*2^(2*d)*2^(d-1)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have HR (N h : ℕ) (hhN : h ≤ N) :
      B * F (2*h) ≤ K * (N+1 : ℝ)^(d-1)*X (2*N)^(d-1) := by
    have hx := zero_le_one.trans (hX (2*h))
    have hx' := zero_le_one.trans (hX (2*N))
    have hnR : (2*h+1 : ℝ) ≤ 2*(N+1 : ℝ) := by
      have hn : (h : ℝ) ≤ N := by exact_mod_cast hhN
      linarith
    have hXm : X (2*h) ≤ X (2*N) := hmono (by omega)
    calc
      _ ≤ B * ((C+1)*2^(2*d)*(2*(N+1 : ℝ))^(d-1)*X (2*N)^(d-1)) := by
        dsimp [F]
        push_cast
        gcongr
      _ = _ := by dsimp [K]; rw [mul_pow]; ring
  refine ⟨K^2, sq_nonneg _, ?_⟩
  intro N v hv
  have hXN := zero_le_one.trans (hX (2*N))
  have HK : ‖A.physicalMode a d 0 v‖^2 ≤
      (K*(N+1 : ℝ)^(d-1)*X (2*N)^(d-1))^2 * ‖v‖^2 := by
    apply U.physicalMode_cutoff_sq_of_grades ha 0 _ _ hv
    intro h hhN w hw
    have Hnorm : ‖A.physicalMode a d 0 w‖ ≤
        (K*(N+1 : ℝ)^(d-1)*X (2*N)^(d-1))*‖w‖ :=
      (HB F hF HF h w hw).trans (mul_le_mul_of_nonneg_right (HR N h hhN) (norm_nonneg _))
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) Hnorm 2
  simpa only [mul_pow, ← pow_mul, Nat.mul_comm (d-1) 2] using HK

end UnitaryStructure
end CFTTypeVOA

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

def zeroGrowthSubmodule (X : ℕ → ℝ) (d p q : ℕ) : Submodule ℂ V where
  carrier := {a | A.ZeroGrowth X a d p q}
  zero_mem' := A.zeroGrowth_zero X d p q
  add_mem' := A.zeroGrowth_add
  smul_mem' z _ H := A.zeroGrowth_smul H z

theorem zeroGrowth_changeControl {X Y : ℕ → ℝ} (hX : ∀ N, 0 ≤ X N)
    (hXY : ∀ N, X N ≤ Y N) {a : V} {d p q : ℕ} (H : A.ZeroGrowth X a d p q) :
    A.ZeroGrowth Y a d p q := by
  obtain ⟨C, hC, HC⟩ := H
  refine ⟨C, hC, ?_⟩
  intro N v hv
  apply (HC N v hv).trans
  gcongr
  · exact hX N
  · exact hXY N

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U

 

theorem grade_improved_zeroGrowth {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N)
    (hmono : Monotone X) (hp : A.PolynomialEnergyBounds)
    (H : ∀ e, ∀ b ∈ A.grade e, A.SharpGrowth X b e)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hd : 2 ≤ d) :
    A.ZeroGrowth (fun N => X (2*N)) a d (2*(d-1)) (2*(d-1)) := by
  classical
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 by omega)
  obtain ⟨q, hq, hqq, b, hb, hab⟩ := U.quasiPrimary_decomposition ha
  obtain ⟨S, hS, hspan⟩ := U.exists_hermitian_quasiPrimary_spanning (e+1)
  have Hq : A.ZeroGrowth (fun N => X (2*N)) q (e+1) (2*e) (2*e) := by
    have hle : Submodule.span ℂ (S : Set V) ≤
        A.zeroGrowthSubmodule (fun N => X (2*N)) (e+1) (2*e) (2*e) := by
      apply Submodule.span_le.mpr
      intro c hc
      obtain ⟨hcg, hcq, hch⟩ := hS c hc
      change A.ZeroGrowth (fun N => X (2*N)) c (e+1) (2*e) (2*e)
      simpa only [Nat.add_sub_cancel] using
        U.zeroMode_sharpGrowth hX hmono (hp c) hcg hcq hch hd
          (fun f _ c hcf => H f c hcf)
    exact hle (hspan q hq hqq)
  have Hb := A.translation_zeroGrowth (H e b hb).2
  have Hb' := A.zeroGrowth_changeControl (fun N => zero_le_one.trans (hX N))
    (fun N => hmono (by omega : N ≤ 2*N)) Hb
  have Hb'' := A.zeroGrowth_mono (fun N => hX (2*N)) Hb' (p' := 2*e) (q' := 2*e)
    (by omega) le_rfl
  rw [hab, A.virasoro_neg_one_eq_translation]
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using A.zeroGrowth_add Hq Hb''

omit U in
 

theorem positiveColumnNorm_sq_le {a : V} {d N : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (H : ∀ v ∈ A.energyCutoff N,
      (∑ m ∈ Finset.range (N+1), ‖A.physicalMode a d m v‖^2) ≤ K*‖v‖^2) :
    A.positiveColumnNorm a d N^2 ≤ K := by
  have HB : A.positiveColumnNorm a d N ≤ Real.sqrt K := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro v
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hK, A.positiveColumn_norm_sq]
    exact H v v.property
  exact (pow_le_pow_left₀ (A.positiveColumnNorm_nonneg a d N) HB 2).trans_eq (Real.sq_sqrt hK)

 

theorem generator_column_contraction {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N)
    (hmono : Monotone X) (hp : A.PolynomialEnergyBounds)
    (H : ∀ e, ∀ b ∈ A.grade e, A.SharpGrowth X b e)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hd : 1 ≤ d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N,
      A.positiveColumnNorm a d N^2 ≤ C*(N+1 : ℝ)^(2*d-1)*X (2*N)^(2*d-1) := by
  have hs : mode A.fields a (-1) a ∈ A.grade (2*d) := A.normalProduct_mem_grade ha
  obtain ⟨C, hC, HC⟩ := U.grade_improved_zeroGrowth hX hmono hp H hs (by omega)
  refine ⟨C+1, by linarith, ?_⟩
  intro N
  have hXN := zero_le_one.trans (hX (2*N))
  apply positiveColumnNorm_sq_le (by positivity)
  intro v hv
  have Hs := norm_of_sharp_square hXN hC N (2*d-1) (2*d-1) v _ (HC N v hv)
  have Hpos := U.positive_column hd ha hq hh v
  have Hfin : (∑ m ∈ Finset.range (N+1), ‖A.physicalMode a d m v‖^2) ≤
      ∑ᶠ m : ℕ, ‖A.physicalMode a d m v‖^2 :=
    (A.finsum_positive_modes_sq_eq ha hv).symm.le
  have HE : A.physicalMode (mode A.fields a (-1) a) (2*d) 0 v =
      mode A.fields (mode A.fields a (-1) a) (2*(d : ℤ)-1) v := by
    simp only [physicalMode, zero_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [HE] at Hs
  calc
    _ ≤ _ := Hfin.trans Hpos
    _ ≤ ‖mode A.fields (mode A.fields a (-1) a) (2*(d : ℤ)-1) v‖*‖v‖ := re_inner_le_norm (𝕜 := ℂ) _ _
    _ ≤ ((C+1)*(N+1 : ℝ)^(2*d-1)*X (2*N)^(2*d-1)*‖v‖)*‖v‖ :=
      mul_le_mul_of_nonneg_right Hs (norm_nonneg _)
    _ = _ := by ring

end UnitaryStructure
end CFTTypeVOA

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

theorem zeroModeCutoffNorm_le_column (a : V) (d N : ℕ) :
    A.zeroModeCutoffNorm a d N ≤ A.positiveColumnNorm a d N := by
  have hR := A.positiveColumnNorm_nonneg a d N
  apply ContinuousLinearMap.opNorm_le_bound _ hR
  intro v
  change ‖A.physicalMode a d 0 v‖ ≤ A.positiveColumnNorm a d N * ‖v‖
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow]
  apply le_trans _ (A.sum_positive_modes_sq_le a d v.property)
  exact Finset.single_le_sum (s := Finset.range (N+1)) (a := 0)
    (f := fun m : ℕ => ‖A.physicalMode a d m v‖^2) (fun m _ => sq_nonneg _)
    (Finset.mem_range.mpr (show 0 < N+1 by omega))

theorem zeroModeCutoffNorm_sq_le {a : V} {d N : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (H : ∀ v ∈ A.energyCutoff N, ‖A.physicalMode a d 0 v‖^2 ≤ K*‖v‖^2) :
    A.zeroModeCutoffNorm a d N^2 ≤ K := by
  have HB : A.zeroModeCutoffNorm a d N ≤ Real.sqrt K := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro v
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hK]
    exact H v v.property
  exact (pow_le_pow_left₀ (norm_nonneg (A.zeroModeOnCutoff a d N)) HB 2).trans_eq (Real.sq_sqrt hK)

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U

theorem generator_quantities_contraction {X : ℕ → ℝ} (hX : ∀ N, 1 ≤ X N)
    (hmono : Monotone X) (hp : A.PolynomialEnergyBounds)
    (H : ∀ e, ∀ b ∈ A.grade e, A.SharpGrowth X b e)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hd : 1 ≤ d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N,
      A.sharpColumnQuantity a d N ≤ C*X (2*N)^(2*d-1) ∧
      A.sharpZeroQuantity a d N ≤ C*X (2*N)^(2*d-1) := by
  obtain ⟨C, hC, HC⟩ := U.generator_column_contraction hX hmono hp H ha hd hq hh
  have HC' (N : ℕ) : A.sharpColumnQuantity a d N ≤ C*X (2*N)^(2*d-1) := by
    apply (div_le_iff₀ (by positivity : 0 < (N+1 : ℝ)^(2*d-1))).mpr
    simpa only [mul_assoc, mul_comm ((N+1 : ℝ)^(2*d-1)), mul_left_comm] using HC N
  by_cases hd1 : d = 1
  · subst d
    refine ⟨C, hC, fun N => ⟨HC' N, ?_⟩⟩
    apply le_trans _ (HC' N)
    unfold sharpZeroQuantity sharpColumnQuantity
    norm_num only
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact pow_le_pow_left₀ (norm_nonneg (A.zeroModeOnCutoff a 1 N))
      (A.zeroModeCutoffNorm_le_column a 1 N) 2
  · obtain ⟨B, hB, HB⟩ := U.zeroMode_sharpGrowth hX hmono (hp a) ha hq hh
      (by omega) (fun e _ b hb => H e b hb)
    have HB' (N : ℕ) : A.sharpZeroQuantity a d N ≤ B*X (2*N)^(2*d-1) := by
      have hXN := zero_le_one.trans (hX (2*N))
      have HB'' := A.zeroModeCutoffNorm_sq_le (a := a) (d := d) (N := N)
        (K := B*(N+1 : ℝ)^(2*(d-1))*X (2*N)^(2*(d-1))) (by positivity) (HB N)
      have he : max 1 (2*d-2) = 2*(d-1) := by omega
      unfold sharpZeroQuantity
      rw [he]
      apply (div_le_iff₀ (by positivity : 0 < (N+1 : ℝ)^(2*(d-1)))).mpr
      apply HB''.trans
      calc
        _ ≤ B*(N+1 : ℝ)^(2*(d-1))*X (2*N)^(2*d-1) := by
          gcongr
          · exact hX (2*N)
          · omega
        _ = _ := by ring
    refine ⟨C+B, add_nonneg hC hB, fun N => ⟨?_, ?_⟩⟩
    · apply (HC' N).trans
      gcongr
      · exact pow_nonneg (zero_le_one.trans (hX (2*N))) _
      · exact le_add_of_nonneg_right hB
    · apply (HB' N).trans
      gcongr
      · exact pow_nonneg (zero_le_one.trans (hX (2*N))) _
      · exact le_add_of_nonneg_left hC

end UnitaryStructure
end CFTTypeVOA
end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_CutoffPowerControl
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U

 

theorem sharpMajorant_power_contraction (D : ℕ) (hD : 2 ≤ D) (S : ℕ → Finset V)
    (hS : ∀ d, ∀ a ∈ S d, 1 ≤ d ∧ d ≤ D ∧ a ∈ A.grade d ∧
      A.IsQuasiPrimary a ∧ U.IsHermitian d a)
    (hp : A.PolynomialEnergyBounds)
    (H : ∀ e, ∀ b ∈ A.grade e, A.SharpGrowth (A.sharpMajorant D S) b e) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N,
      A.sharpMajorant D S N^(2*D) ≤ C*A.sharpMajorant D S (2*N)^(2*D-1) := by
  classical
  let X := A.sharpMajorant D S
  let Y : ℕ → ℝ := fun N => X (2*N)^(2*D-1)
  have hX := A.one_le_sharpMajorant D S
  have hm := A.sharpMajorant_mono D S
  have hpositive (d : ℕ) (a : V) (N : ℕ) :
      0 ≤ (A.sharpColumnQuantity a d N)^((2*d : ℕ) : ℝ)⁻¹ +
        (A.sharpZeroQuantity a d N)^((2*d : ℕ) : ℝ)⁻¹ :=
    add_nonneg (Real.rpow_nonneg (A.sharpColumnQuantity_nonneg a d N) _)
      (Real.rpow_nonneg (A.sharpZeroQuantity_nonneg a d N) _)
  have Hsum : CutoffPowerControl Y (2*D) (fun N =>
      ∑ d ∈ Finset.range (D+1), ∑ a ∈ S d,
        ((A.sharpColumnQuantity a d N)^((2*d : ℕ) : ℝ)⁻¹ +
         (A.sharpZeroQuantity a d N)^((2*d : ℕ) : ℝ)⁻¹)) := by
    apply cutoffPowerControl_sum (by omega)
      (hf := fun d _ N => Finset.sum_nonneg (fun a _ => hpositive d a N))
    intro d hd
    apply cutoffPowerControl_sum (by omega) (hf := fun a _ N => hpositive d a N)
    intro a haS
    obtain ⟨hdpos, hdD, ha, hq, hh⟩ := hS d a haS
    obtain ⟨C, hC, HC⟩ := U.generator_quantities_contraction hX hm hp H ha hdpos hq hh
    apply cutoffPowerControl_add
      (fun N => Real.rpow_nonneg (A.sharpColumnQuantity_nonneg a d N) _)
      (fun N => Real.rpow_nonneg (A.sharpZeroQuantity_nonneg a d N) _)
    · refine ⟨C, hC, ?_⟩
      intro N
      exact root_lift_power_bound (A.sharpColumnQuantity_nonneg a d N)
        (zero_le_one.trans (hX (2*N))) hC (by omega) (by omega)
        (((A.root_sharpQuantity_le D S hdD haS).1).trans (hm (by omega : N ≤ 2*N))) (HC N).1
    · refine ⟨C, hC, ?_⟩
      intro N
      exact root_lift_power_bound (A.sharpZeroQuantity_nonneg a d N)
        (zero_le_one.trans (hX (2*N))) hC (by omega) (by omega)
        (((A.root_sharpQuantity_le D S hdD haS).2).trans (hm (by omega : N ≤ 2*N))) (HC N).2
  have Hraw : CutoffPowerControl Y (2*D) (A.rawSharpMajorant D S) :=
    cutoffPowerControl_add (fun _ => zero_le_one)
      (fun N => Finset.sum_nonneg (fun d _ => Finset.sum_nonneg (fun a _ => hpositive d a N)))
      (cutoffPowerControl_one (fun N => one_le_pow₀ (hX (2*N))) (2*D)) Hsum
  obtain ⟨C, hC, HC⟩ := Hraw
  refine ⟨C+1, by linarith, ?_⟩
  intro N
  obtain ⟨n, hn, he⟩ := Finset.exists_mem_eq_sup' (s := Finset.range (N+1))
    (by simp) (A.rawSharpMajorant D S)
  change ((Finset.range (N+1)).sup' (by simp) (A.rawSharpMajorant D S))^(2*D) ≤ _
  rw [he]
  apply (HC n).trans
  have hXn := zero_le_one.trans (hX (2*n))
  have hnN : n ≤ N := by have := Finset.mem_range.mp hn; omega
  change C*X (2*n)^(2*D-1) ≤ (C+1)*X (2*N)^(2*D-1)
  gcongr
  · exact le_add_of_nonneg_right zero_le_one
  · exact hm (by omega)

end UnitaryStructure
end CFTTypeVOA

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U

 

theorem positiveColumnNorm_sq_polynomial {a : V} (hp : A.PolynomialEnergyBound a)
    (d : ℕ) (hd : 1 ≤ d) : PolynomialCutoffControl (fun N => A.positiveColumnNorm a d N^2) := by
  obtain ⟨C, hC, p, k, HC⟩ := hp
  let B := C*(d+2 : ℝ)^p
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have Hmode (N m : ℕ) (hm : m ≤ N) (v : V) (hv : v ∈ A.energyCutoff N) :
      ‖A.physicalMode a d m v‖ ≤ B*(N+1 : ℝ)^(p+k)*‖v‖ := by
    have hmR : (m : ℝ) ≤ N := by exact_mod_cast hm
    have hdR : 1 ≤ (d : ℝ) := by exact_mod_cast hd
    have hcoef : 1+|(((m : ℤ)+d-1 : ℤ) : ℝ)| ≤ (d+2 : ℝ)*(N+1 : ℝ) := by
      push_cast
      rw [abs_of_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) m])]
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    have HK := U.energyShift_pow_norm_on_cutoff hv k
    change ‖mode A.fields a ((m : ℤ)+d-1) v‖ ≤ _
    calc
      _ ≤ C*(1+|(((m : ℤ)+d-1 : ℤ) : ℝ)|)^p*‖(A.energyShift^k) v‖ := HC _ _
      _ ≤ C*((d+2 : ℝ)*(N+1 : ℝ))^p*((N+1 : ℝ)^k*‖v‖) := by
        have HK' : ‖(A.energyShift^k) v‖ ≤ (N+1 : ℝ)^k*‖v‖ := by simpa only [add_comm] using HK
        gcongr
      _ = _ := by dsimp [B]; rw [mul_pow, pow_add]; ring
  refine ⟨B^2, sq_nonneg _, 2*(p+k)+1, ?_⟩
  intro N
  apply positiveColumnNorm_sq_le (by positivity)
  intro v hv
  calc
    _ ≤ ∑ m ∈ Finset.range (N+1), (B*(N+1 : ℝ)^(p+k)*‖v‖)^2 := by
      apply Finset.sum_le_sum
      intro m hm
      exact pow_le_pow_left₀ (norm_nonneg _) (Hmode N m (by have := Finset.mem_range.mp hm; omega) v hv) 2
    _ = (N+1 : ℝ)*(B*(N+1 : ℝ)^(p+k)*‖v‖)^2 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    _ = (B^2*(N+1 : ℝ)^(2*(p+k)+1))*‖v‖^2 := by rw [pow_succ]; ring

theorem sharpQuantities_polynomial {a : V} (hp : A.PolynomialEnergyBound a)
    (d : ℕ) (hd : 1 ≤ d) :
    PolynomialCutoffControl (A.sharpColumnQuantity a d) ∧
      PolynomialCutoffControl (A.sharpZeroQuantity a d) := by
  obtain ⟨C, hC, p, HC⟩ := U.positiveColumnNorm_sq_polynomial hp d hd
  constructor
  · refine ⟨C, hC, p, ?_⟩
    intro N
    apply le_trans _ (HC N)
    exact div_le_self (sq_nonneg _) (one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) N]))
  · refine ⟨C, hC, p, ?_⟩
    intro N
    apply le_trans _ (HC N)
    apply le_trans (div_le_self (sq_nonneg _) (one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) N])))
    exact pow_le_pow_left₀ (norm_nonneg (A.zeroModeOnCutoff a d N))
      (A.zeroModeCutoffNorm_le_column a d N) 2

 

theorem sharpMajorant_polynomial (D : ℕ) (S : ℕ → Finset V)
    (hS : ∀ d, ∀ a ∈ S d, 1 ≤ d) (hp : A.PolynomialEnergyBounds) :
    PolynomialCutoffControl (A.sharpMajorant D S) := by
  classical
  have Hraw : PolynomialCutoffControl (A.rawSharpMajorant D S) := by
    apply polynomialCutoffControl_add polynomialCutoffControl_one
    apply polynomialCutoffControl_sum
    intro d hd
    apply polynomialCutoffControl_sum
    intro a ha
    have HQ := U.sharpQuantities_polynomial (hp a) d (hS d a ha)
    exact polynomialCutoffControl_add
      (polynomialCutoffControl_root (A.sharpColumnQuantity_nonneg a d) HQ.1 (by have := hS d a ha; omega))
      (polynomialCutoffControl_root (A.sharpZeroQuantity_nonneg a d) HQ.2 (by have := hS d a ha; omega))
  obtain ⟨C, hC, p, HC⟩ := Hraw
  refine ⟨C, hC, p, ?_⟩
  intro N
  apply Finset.sup'_le
  intro n hn
  apply (HC n).trans
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast (show n ≤ N by have := Finset.mem_range.mp hn; omega)
  gcongr

end UnitaryStructure
end CFTTypeVOA

open Filter


namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
include U

 

theorem exists_bounded_sharpGrowth (hc : A.toVertexAlgebra.C2Cofinite) :
    ∃ X : ℕ → ℝ, (∀ N, 1 ≤ X N) ∧ Monotone X ∧
      (∃ B : ℝ, 1 ≤ B ∧ ∀ N, X N ≤ B) ∧
      (∀ e, ∀ b ∈ A.grade e, A.SharpGrowth X b e) := by
  obtain ⟨D, hD, S, _hSzero, hS, _hspan, _hcut, H⟩ := U.exists_sharpMajorant hc
  have hp := U.polynomialEnergyBounds hc
  obtain ⟨C, hC, HC⟩ := U.sharpMajorant_power_contraction D hD S hS hp H
  have HB := polynomial_power_contraction_bounded (A.sharpMajorant D S)
    (A.one_le_sharpMajorant D S) (A.sharpMajorant_mono D S)
    (U.sharpMajorant_polynomial D S (fun d a ha => (hS d a ha).1) hp)
    2 (2*D) (by decide) (by omega) C hC HC
  exact ⟨A.sharpMajorant D S, A.one_le_sharpMajorant D S, A.sharpMajorant_mono D S, HB, H⟩

 

theorem optimal_quasiPrimary_cutoff (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a)
    (hh : U.IsHermitian d a) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ N (m : ℤ) v, v ∈ A.energyCutoff N →
      ‖A.physicalMode a d m v‖ ≤ C*(1+|(m : ℝ)|)^(2*d)*(N+1 : ℝ)^(d-1)*‖v‖ := by
  obtain ⟨X, hX, hm, ⟨B, hB, HB⟩, H⟩ := U.exists_bounded_sharpGrowth hc
  obtain ⟨C, hC, HC⟩ := U.nonzeroModes_sharp_bound hX ha hq hh hd (fun e _ b hb => H e b hb)
  obtain ⟨D, hD, HD⟩ := U.zeroMode_sharpGrowth hX hm (U.polynomialEnergyBounds hc a)
    ha hq hh hd (fun e _ b hb => H e b hb)
  let K := (C+D+2)*B^(d-1)
  have hK : 0 < K := by dsimp [K]; positivity
  have Hzero (N : ℕ) (v : V) (hv : v ∈ A.energyCutoff N) :
      ‖A.physicalMode a d 0 v‖ ≤ K*(N+1 : ℝ)^(d-1)*‖v‖ := by
    have Hn := norm_of_sharp_square (zero_le_one.trans (hX (2*N))) hD N (d-1) (d-1) v _ (HD N v hv)
    apply Hn.trans
    calc
      _ ≤ (C+D+2)*(N+1 : ℝ)^(d-1)*B^(d-1)*‖v‖ := by
        have hhX := zero_le_one.trans (hX (2*N))
        gcongr <;> linarith [HB (2*N)]
      _ = _ := by dsimp [K]; ring
  have Hpos (N m : ℕ) (hm : 0 < m) (v : V) (hv : v ∈ A.energyCutoff N) :
      ‖A.physicalMode a d m v‖ ≤ K*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(d-1)*‖v‖ ∧
      ‖A.physicalMode a d (-(m : ℤ)) v‖ ≤ K*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(d-1)*‖v‖ := by
    have Hn := HC N m hm v hv
    have hbound : C*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(d-1)*X N^(d-1)*‖v‖ ≤
        K*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(d-1)*‖v‖ := by
      have hhX := zero_le_one.trans (hX N)
      calc
        _ ≤ (C+D+2)*(m+1 : ℝ)^(2*d)*(N+1 : ℝ)^(d-1)*B^(d-1)*‖v‖ := by
          gcongr
          · linarith
          · exact HB N
        _ = _ := by dsimp [K]; ring
    exact ⟨Hn.1.trans hbound, Hn.2.trans hbound⟩
  refine ⟨K, hK, ?_⟩
  intro N m v hv
  rcases m with m | m
  · by_cases hm0 : m = 0
    · subst m
      simpa using Hzero N v hv
    · simpa only [Int.ofNat_eq_natCast, Int.cast_natCast,
        abs_of_nonneg (show (0 : ℝ) ≤ (m : ℝ) from Nat.cast_nonneg m), add_comm 1 (m : ℝ)] using
        (Hpos N m (by omega) v hv).1
  · have he : Int.negSucc m = -((m+1 : ℕ) : ℤ) := by omega
    rw [he]
    simpa only [Int.cast_neg, abs_neg, Int.cast_natCast,
      abs_of_nonneg (show (0 : ℝ) ≤ ((m+1 : ℕ) : ℝ) from Nat.cast_nonneg (m+1)),
      add_comm 1 ((m+1 : ℕ) : ℝ)] using (Hpos N (m+1) (by omega) v hv).2

 

theorem physical_energyBound_of_cutoffs {a : V} {d p k : ℕ} {C : ℝ}
    (ha : a ∈ A.grade d) (hC : 0 ≤ C)
    (H : ∀ N (m : ℤ) v, v ∈ A.energyCutoff N →
      ‖A.physicalMode a d m v‖ ≤ C*(1+|(m : ℝ)|)^p*(N+1 : ℝ)^k*‖v‖) :
    ∀ (m : ℤ) v, ‖A.physicalMode a d m v‖ ≤
      C*(1+|(m : ℝ)|)^p*‖(A.energyShift^k) v‖ := by
  classical
  intro m v
  let L := C*(1+|(m : ℝ)|)^p
  have hL : 0 ≤ L := by dsimp [L]; positivity
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mp
  change ‖A.physicalMode a d m v‖^2 ≤ (L*‖(A.energyShift^k) v‖)^2
  rw [physicalMode, U.mode_norm_sq_eq_sum_grades ha]
  calc
    _ ≤ ∑ h ∈ A.gradeSupport v, (L*(1+(h : ℝ))^k*‖A.gradeComponent h v‖)^2 := by
      apply Finset.sum_le_sum
      intro h _
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
      simpa only [L, physicalMode, add_comm (h : ℝ) 1] using H h m (A.gradeComponent h v)
        (A.grade_le_energyCutoff le_rfl (A.gradeComponent_mem h v))
    _ = L^2 * ∑ h ∈ A.gradeSupport v, ((1+(h : ℝ))^k*‖A.gradeComponent h v‖)^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      ring
    _ = _ := by rw [← U.energy_norm_sq_eq_sum_grades]; ring

 

theorem optimal_quasiPrimary_energyBound (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a)
    (hh : U.IsHermitian d a) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℤ) v, ‖A.physicalMode a d m v‖ ≤
      C*(1+|(m : ℝ)|)^(2*d)*‖(A.energyShift^(d-1)) v‖ := by
  obtain ⟨C, hC, H⟩ := U.optimal_quasiPrimary_cutoff hc ha hq hh hd
  exact ⟨C, hC, U.physical_energyBound_of_cutoffs ha hC.le H⟩

 

theorem current_linear_energyBound (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} (ha : a ∈ A.grade 1) (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian 1 a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℤ) v, ‖A.physicalMode a 1 m v‖ ≤
      C*(1+|(m : ℝ)|)*‖A.energyShift v‖ := by
  obtain ⟨X, hX, _hm, ⟨B, hB, HB⟩, H⟩ := U.exists_bounded_sharpGrowth hc
  obtain ⟨C, hC, HC⟩ := (H 1 a ha).1
  have HR (N : ℕ) : A.positiveColumnNorm a 1 N ≤ (C+1)*B*(N+1 : ℝ) := by
    have Hsq := positiveColumnNorm_sq_le (by positivity : 0 ≤ C*(N+1 : ℝ)*X N^2)
      (by simpa only [ColumnControl, show 2*1-1=1 by decide, show 2*1=2 by decide, pow_one] using HC N)
    have hXN := zero_le_one.trans (hX N)
    have hCX : C*(N+1 : ℝ)*X N^2 ≤ C*(N+1 : ℝ)*B^2 := by gcongr; exact HB N
    apply (sq_le_sq₀ (A.positiveColumnNorm_nonneg a 1 N) (by positivity)).mp
    apply Hsq.trans (hCX.trans _)
    have hN : 1 ≤ (N+1 : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) N]
    have hcc : C ≤ (C+1)^2 := by nlinarith
    calc
      _ ≤ (C+1)^2*(N+1 : ℝ)^2*B^2 := by gcongr; nlinarith
      _ = _ := by ring
  let K := (C+1)*B
  have hK : 0 < K := by dsimp [K]; positivity
  have Hcut (N : ℕ) (m : ℤ) v (hv : v ∈ A.energyCutoff N) :
      ‖A.physicalMode a 1 m v‖ ≤ K*(1+|(m : ℝ)|)^1*(N+1 : ℝ)^1*‖v‖ := by
    have HR' (n : ℕ) : A.positiveColumnNorm a 1 n ≤ K*(n+1 : ℝ) := HR n
    rcases m with m | m
    · apply (A.positive_mode_norm_le_column ha hv m).trans
      simp only [Int.ofNat_eq_natCast, Int.cast_natCast,
        abs_of_nonneg (show (0 : ℝ) ≤ m from Nat.cast_nonneg m), pow_one]
      calc
        _ ≤ K*(N+1 : ℝ)*‖v‖ := mul_le_mul_of_nonneg_right (HR' N) (norm_nonneg _)
        _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hK.le (by positivity : 0 ≤ (N+1 : ℝ))) (norm_nonneg v),
          mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (mul_nonneg (mul_nonneg hK.le (by positivity : 0 ≤ (N+1 : ℝ))) (norm_nonneg v))]
    · have he : Int.negSucc m = -((m+1 : ℕ) : ℤ) := by omega
      rw [he]
      apply (U.negative_mode_norm_le_column ha hq hh hv (m+1)).trans
      simp only [Int.cast_neg, abs_neg, Int.cast_natCast,
        abs_of_nonneg (show (0 : ℝ) ≤ ((m+1 : ℕ) : ℝ) from Nat.cast_nonneg (m+1)), pow_one]
      calc
        _ ≤ K*((N+(m+1) : ℕ)+1 : ℝ)*‖v‖ := mul_le_mul_of_nonneg_right (HR' (N+(m+1))) (norm_nonneg _)
        _ ≤ _ := by
          have hbase : (((N+(m+1) : ℕ) : ℝ)+1) ≤ (1+((m+1 : ℕ) : ℝ))*(N+1 : ℝ) := by
            push_cast
            have hh := mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (Nat.cast_nonneg (α := ℝ) N)
            nlinarith [Nat.cast_nonneg (α := ℝ) N]
          calc
            _ ≤ K*((1+((m+1 : ℕ) : ℝ))*(N+1 : ℝ))*‖v‖ := by gcongr
            _ = _ := by ring
  refine ⟨K, hK, ?_⟩
  simpa only [pow_one] using U.physical_energyBound_of_cutoffs ha hK.le Hcut

end UnitaryStructure
end CFTTypeVOA

end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_HilbertRegularization
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

universe u

noncomputable section
open scoped Topology
open Filter
namespace StronglyRationalVOA.HilbertScale
open Filter
open scoped Topology
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [DecidableEq ι] [∀ i, CompleteSpace (G i)]
def regularized (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (M : finiteCore (G := G) →ₗ[ℂ] Space G) (n : ℕ) : Space G →L[ℂ] Space G :=
  (energyExtension h M).comp (((n : ℂ)+1) • complement h hh n)

theorem regularized_core (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (M : finiteCore (G := G) →ₗ[ℂ] Space G) {C : ℝ}
    (hM : ∀ x, ‖M x‖ ≤ C * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (n : ℕ) (x : finiteCore (G := G)) :
    regularized h hh M n x = M (coreMultiplier (fun i => (resolventWeight h n i : ℂ)) x) := by
  change energyExtension h M (((n : ℂ)+1) • complement h hh n x) = _
  rw [← weighted_resolvent_core h hh n x,energyExtension_weighted h hh M hM]


omit [∀ i, CompleteSpace (G i)] in
theorem coreOperator_formalAdjoint (M : finiteCore (G := G) →ₗ[ℂ] Space G)
    (hM : ∀ x y : finiteCore (G := G), inner ℂ (M x) (y : Space G) = inner ℂ (x : Space G) (M y)) :
    (coreOperator M).IsFormalAdjoint (coreOperator M) := hM

theorem coreOperator_closable (M : finiteCore (G := G) →ₗ[ℂ] Space G)
    (hM : ∀ x y : finiteCore (G := G), inner ℂ (M x) (y : Space G) = inner ℂ (x : Space G) (M y)) :
    (coreOperator M).IsClosable :=
  ((coreOperator M).adjoint_isClosed finiteCore_dense).isClosable.leIsClosable
    ((coreOperator_formalAdjoint M hM).le_adjoint finiteCore_dense)

 
theorem regularized_graph_closure (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (M : finiteCore (G := G) →ₗ[ℂ] Space G) {C : ℝ}
    (hM : ∀ x, ‖M x‖ ≤ C * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (hc : (coreOperator M).IsClosable) (n : ℕ) (x : Space G) :
    (resolvent h hh n x,regularized h hh M n x) ∈ (coreOperator M).closure.graph := by
  have hclosed : IsClosed {z : Space G |
      (resolvent h hh n z,regularized h hh M n z) ∈ (coreOperator M).closure.graph} :=
    hc.closure_isClosed.preimage ((resolvent h hh n).continuous.prodMk (regularized h hh M n).continuous)
  have hin : (finiteCore (G := G) : Set (Space G)) ⊆ {z : Space G |
      (resolvent h hh n z,regularized h hh M n z) ∈ (coreOperator M).closure.graph} := by
    intro z hz
    let v : finiteCore (G := G) := ⟨z,hz⟩
    apply LinearPMap.le_graph_of_le (coreOperator M).le_closure
    apply (coreOperator M).mem_graph_iff.mpr
    refine ⟨coreMultiplier (fun i => (resolventWeight h n i : ℂ)) v,rfl,?_⟩
    exact (regularized_core h hh M hM n v).symm
  exact closure_minimal hin hclosed (finiteCore_dense x)

end StronglyRationalVOA.HilbertScale

open scoped Topology
open Filter

namespace StronglyRationalVOA.HilbertScale
open Filter
open scoped Topology
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [DecidableEq ι] [∀ i, CompleteSpace (G i)]

theorem weighted_resolvent_difference (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (n : ℕ)
    (x : finiteCore (G := G)) :
    coreDiagonal (fun i => (h i : ℂ))
      (coreMultiplier (fun i => (resolventWeight h n i : ℂ)) x) =
      ((n : ℂ)+1) • (x : Space G) -
        ((n : ℂ)+1) • (coreMultiplier (fun i => (resolventWeight h n i : ℂ)) x : Space G) := by
  rw [weighted_resolvent_core,← smul_sub]
  congr 1
  change complement h hh n x = (x : Space G)-resolvent h hh n x
  exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans (resolvent_add_complement (G := G) h hh n (x : Space G)))

 

theorem regularized_defect_pairing (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (M K : finiteCore (G := G) →ₗ[ℂ] Space G) {C D : ℝ}
    (hM : ∀ x, ‖M x‖ ≤ C * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (hK : ∀ x, ‖K x‖ ≤ D * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (hs : ∀ x y : finiteCore (G := G),
      inner ℂ (M x) (y : Space G) = inner ℂ (x : Space G) (M y))
    (hk : ∀ x y : finiteCore (G := G),
      inner ℂ (M x) (coreDiagonal (fun i => (h i : ℂ)) y) -
        inner ℂ (coreDiagonal (fun i => (h i : ℂ)) x) (M y) = inner ℂ (K x) (y : Space G))
    (n : ℕ) (x y : finiteCore (G := G)) :
    inner ℂ (regularized h hh M n x) (y : Space G) -
      inner ℂ (x : Space G) (regularized h hh M n y) =
    inner ℂ (resolvent h hh n (energyExtension h K (complement h hh n x))) (y : Space G) := by
  let rx := coreMultiplier (fun i => (resolventWeight h n i : ℂ)) x
  let ry := coreMultiplier (fun i => (resolventWeight h n i : ℂ)) y
  let t : ℂ := (n : ℂ)+1
  have ht : t ≠ 0 := by dsimp [t]; exact_mod_cast (show n+1 ≠ 0 by omega)
  have htstar : star t = t := by simp [t]
  have htx : coreDiagonal (fun i => (h i : ℂ)) rx = t • (x : Space G)-t • (rx : Space G) :=
    weighted_resolvent_difference h hh n x
  have hty : coreDiagonal (fun i => (h i : ℂ)) ry = t • (y : Space G)-t • (ry : Space G) :=
    weighted_resolvent_difference h hh n y
  have hnormK : K rx = t • energyExtension h K (complement h hh n x) := by
    rw [← energyExtension_weighted h hh K hK rx,weighted_resolvent_core h hh n x,map_smul]
  have hR : (resolvent (G := G) h hh n).adjoint = resolvent h hh n := resolvent_selfAdjoint h hh n
  have hinner : inner ℂ (energyExtension h K (complement h hh n x)) (ry : Space G) =
      inner ℂ (resolvent h hh n (energyExtension h K (complement h hh n x))) (y : Space G) := by
    change inner ℂ _ (resolvent h hh n (y : Space G)) = _
    simpa only [hR] using (ContinuousLinearMap.adjoint_inner_left (resolvent h hh n)
      (y : Space G) (energyExtension h K (complement h hh n x))).symm
  rw [regularized_core h hh M hM n x,regularized_core h hh M hM n y]
  change inner ℂ (M rx) (y : Space G)-inner ℂ (x : Space G) (M ry) = _
  apply mul_left_cancel₀ ht
  calc
    t * (inner ℂ (M rx) (y : Space G)-inner ℂ (x : Space G) (M ry)) =
        inner ℂ (M rx) (coreDiagonal (fun i => (h i : ℂ)) ry)-
          inner ℂ (coreDiagonal (fun i => (h i : ℂ)) rx) (M ry) := by
      rw [htx,hty]
      simp only [inner_sub_right,inner_sub_left,inner_smul_right,inner_smul_left,
        starRingEnd_apply,htstar]
      rw [hs rx ry]
      ring
    _ = inner ℂ (K rx) (ry : Space G) := hk rx ry
    _ = _ := by rw [hnormK,inner_smul_left,starRingEnd_apply,htstar,hinner]

theorem regularized_defect (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (M K : finiteCore (G := G) →ₗ[ℂ] Space G) {C D : ℝ}
    (hM : ∀ x, ‖M x‖ ≤ C * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (hK : ∀ x, ‖K x‖ ≤ D * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (hs : ∀ x y : finiteCore (G := G),
      inner ℂ (M x) (y : Space G) = inner ℂ (x : Space G) (M y))
    (hk : ∀ x y : finiteCore (G := G),
      inner ℂ (M x) (coreDiagonal (fun i => (h i : ℂ)) y) -
        inner ℂ (coreDiagonal (fun i => (h i : ℂ)) x) (M y) = inner ℂ (K x) (y : Space G))
    (n : ℕ) :
    regularized h hh M n - (regularized h hh M n).adjoint =
      (resolvent h hh n).comp ((energyExtension h K).comp (complement h hh n)) := by
  let B := regularized h hh M n
  let Q := (resolvent h hh n).comp ((energyExtension h K).comp (complement h hh n))
  have hd : DenseRange ((finiteCore (G := G)).subtype) := by simpa [DenseRange] using (finiteCore_dense (G := G))
  have hp : ∀ x y : Space G, inner ℂ (B x) y-inner ℂ x (B y) = inner ℂ (Q x) y := by
    intro x y
    refine hd.induction_on₂ ?_ ?_ x y
    · exact isClosed_eq
        (((B.continuous.comp continuous_fst).inner continuous_snd).sub
          (continuous_fst.inner (B.continuous.comp continuous_snd)))
        ((Q.continuous.comp continuous_fst).inner continuous_snd)
    · intro x y
      exact regularized_defect_pairing h hh M K hM hK hs hk n x y
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  change inner ℂ (B x-B.adjoint x) y = inner ℂ (Q x) y
  rw [inner_sub_left,ContinuousLinearMap.adjoint_inner_left]
  exact hp x y



end StronglyRationalVOA.HilbertScale

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

theorem coreEnergyCoordinates_energyShift (a : V) :
    HilbertScale.coreDiagonal (fun d : ℕ => ((1+(d : ℝ) : ℝ) : ℂ)) (U.coreEnergyCoordinates a) =
      U.energyCoordinates (A.energyShift a : Completion V) := by
  apply lp.ext
  funext d
  apply Subtype.ext
  simp only [HilbertScale.coreDiagonal_apply,coreEnergyCoordinates_coe,
    Submodule.coe_smul,U.energyCoordinates_coe]
  simp only [energyShift,LinearMap.add_apply,Module.End.one_apply,map_add,
    A.gradeComponent_energy,Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_natCast,
    add_smul,one_smul]


end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_InverseEnergySelf
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

universe u

noncomputable section
open scoped Topology
open Filter

namespace StronglyRationalVOA.HilbertScale
open scoped Topology
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [DecidableEq ι] [∀ i, CompleteSpace (G i)]

theorem energyExtension_weakCommutation (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (M N : finiteCore (G := G) →ₗ[ℂ] Space G) {C D : ℝ}
    (hM : ∀ x, ‖M x‖ ≤ C * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (hN : ∀ x, ‖N x‖ ≤ D * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (hw : ∀ x y, inner ℂ (M x) (N y) = inner ℂ (N x) (M y)) (x y : Space G) :
    inner ℂ (energyExtension h M x) (energyExtension h N y) =
      inner ℂ (energyExtension h N x) (energyExtension h M y) := by
  have hd : DenseRange ((finiteCore (G := G)).subtype) := by
    simpa [DenseRange] using (finiteCore_dense (G := G))
  refine hd.induction_on₂ ?_ ?_ x y
  · exact isClosed_eq
      (((energyExtension h M).continuous.comp continuous_fst).inner
        ((energyExtension h N).continuous.comp continuous_snd))
      (((energyExtension h N).continuous.comp continuous_fst).inner
        ((energyExtension h M).continuous.comp continuous_snd))
  · intro a b
    change inner ℂ (energyExtension h M (a : Space G)) (energyExtension h N (b : Space G)) =
      inner ℂ (energyExtension h N (a : Space G)) (energyExtension h M (b : Space G))
    rw [energyExtension_core h hh M hM,energyExtension_core h hh N hN,
      energyExtension_core h hh N hN,energyExtension_core h hh M hM]
    exact hw _ _

end StronglyRationalVOA.HilbertScale

namespace StronglyRationalVOA.SmoothCircleFunction
local instance inverseEnergySelfProductPeriodPos : Fact (0 < 2*Real.pi) := ⟨period_pos⟩


end StronglyRationalVOA.SmoothCircleFunction

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_ApproximatingFlowDerivative
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory

open scoped Topology
open Filter

open scoped Topology
open Filter

open UniformSpace

open scoped Topology
open Filter MeasureTheory
namespace StronglyRationalVOA.StrongLimit
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

lemma tendsto_of_denseRange {ι E : Type*} {l : Filter ι}
    (S : E → H) (hSd : DenseRange S) (F : ι → H →L[ℂ] H) (L : H →L[ℂ] H)
    {C : ℝ} (hC : 0 ≤ C) (hF : ∀ᶠ i in l, ‖F i‖ ≤ C)
    (hcore : ∀ x, Tendsto (fun i => F i (S x)) l (𝓝 (L (S x)))) (x : H) :
    Tendsto (fun i => F i x) l (𝓝 (L x)) := by
  classical
  let G (i : ι) : H →L[ℂ] H := if ‖F i‖ ≤ C then F i else 0
  have hg : ∀ i, ‖G i‖ ≤ C := by
    intro i
    dsimp [G]
    split_ifs with hi
    · exact hi
    · simpa only [norm_zero] using hC
  have he : ∀ᶠ i in l, G i = F i := hF.mono fun i hi => ite_eq_left hi
  have hclosed := (equicontinuous_of_norm_bound G hg).isClosed_setOfPred_tendsto
    (l := l) L.continuous
  have hlim : Tendsto (fun i => G i x) l (𝓝 (L x)) := by
    apply hSd.induction_on (p := fun x => Tendsto (fun i => G i x) l (𝓝 (L x))) x hclosed
    intro v
    exact (hcore v).congr' (he.mono fun i hi => congrArg (fun Q : H →L[ℂ] H => Q (S v)) hi.symm)
  exact hlim.congr' (he.mono fun i hi => congrArg (fun Q : H →L[ℂ] H => Q x) hi)
end StronglyRationalVOA.StrongLimit

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_CoefficientDifferentiated
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

universe u

noncomputable section
open scoped Topology
open Filter

namespace StronglyRationalVOA.CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (A : CFTTypeVOA V)

 
theorem physicalMode_energy_eigenvalue {d e : ℕ} {a x : V}
    (ha : a ∈ A.grade d) (hx : x ∈ A.grade e) (m : ℤ) :
    A.virasoroMode 0 (A.physicalMode a d m x) =
      ((e : ℂ)-m) • A.physicalMode a d m x := by
  rw [physicalMode,A.mode_energy_eigenvalue ha hx]
  congr 1
  push_cast
  ring

 

theorem physicalMode_commutator_finite {a b : V} {d e : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (m n : ℤ) (y : V) :
    A.physicalMode a d m (A.physicalMode b e n y)-
      A.physicalMode b e n (A.physicalMode a d m y) =
    ∑ j ∈ Finset.range (d+e), Ring.choose ((m : ℂ)+d-1) j •
      mode A.fields (mode A.fields a j b) (m+n+d+e-2-j) y := by
  simp only [physicalMode]
  rw [A.toVertexAlgebra.mode_commutator]
  have hi (j : ℕ) : (m+(d : ℤ)-1)+(n+e-1)-j = m+n+d+e-2-j := by omega
  simp only [hi,Int.cast_sub,Int.cast_add,Int.cast_natCast,Int.cast_one]
  apply finsum_eq_sum_of_support_subset
  intro j hj
  simp only [Finset.coe_range,Set.mem_Iio]
  by_contra h
  apply hj
  have hz := A.mode_eq_zero_of_negative_energy ha hb (j : ℤ) (by omega)
  simp only [hz,mode_zero,LinearMap.zero_apply,smul_zero]

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)

include U in
 

theorem physicalMode_cross_orthogonal {a b x y : V} {d e D E : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hx : x ∈ A.grade D) (hy : y ∈ A.grade E) (m n : ℤ)
    (hne : n ≠ m+(E : ℤ)-D) :
    inner ℂ (A.physicalMode a d m x) (A.physicalMode b e n y) = 0 := by
  have h := U.virasoro_adjoint 0 (A.physicalMode a d m x) (A.physicalMode b e n y)
  simp only [neg_zero,A.physicalMode_energy_eigenvalue ha hx,
    A.physicalMode_energy_eigenvalue hb hy,inner_smul_left,inner_smul_right,
    map_sub,map_natCast,map_intCast] at h
  have hc : ((D : ℂ)-m)-((E : ℂ)-n) ≠ 0 := by
    intro hz
    apply hne
    have heq : (n : ℂ) = (m : ℂ)+E-D := by linear_combination hz
    exact_mod_cast heq
  apply (mul_eq_zero.mp (show (((D : ℂ)-m)-((E : ℂ)-n))*
      inner ℂ (A.physicalMode a d m x) (A.physicalMode b e n y) = 0 from ?_)).resolve_left hc
  rw [sub_mul,h,sub_self]

end UnitaryStructure
end StronglyRationalVOA.CFTTypeVOA

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

 

theorem hasSum_smeared_inner_homogeneous {a b x y : V} {d e D E : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hx : x ∈ A.grade D) (hy : y ∈ A.grade E)
    (hqa : A.IsQuasiPrimary a) (hha : U.IsHermitian d a)
    (hea : A.PolynomialEnergyBound a) (heb : A.PolynomialEnergyBound b)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g)
    (hreal : ∀ n, star (f n) = f (-n)) :
    HasSum (fun m : ℤ => f m*g ((E : ℤ)-D-m)*
      inner ℂ x (A.physicalMode a d m (A.physicalMode b e ((E : ℤ)-D-m) y)))
      (inner ℂ (A.smearedMap a d hea f hf x) (A.smearedMap b e heb g hg y)) := by
  let u (m : ℤ) : Completion V := f m • (A.physicalMode a d m x : Completion V)
  let v (n : ℤ) : Completion V := g n • (A.physicalMode b e n y : Completion V)
  have hu : Summable (fun m => ‖u m‖) := A.summable_norm_physicalSmear hea d hf x
  have hv : Summable (fun n => ‖v n‖) := A.summable_norm_physicalSmear heb e hg y
  have hz : ∀ m n, n ≠ m+((E : ℤ)-D) → inner ℂ (u m) (v n) = 0 := by
    intro m n hne
    dsimp only [u,v]
    simp only [inner_smul_left,inner_smul_right,Completion.inner_coe]
    rw [U.physicalMode_cross_orthogonal ha hb hx hy m n (by omega),mul_zero,mul_zero]
  have H := (summable_inner_diagonal hu hv ((E : ℤ)-D)).hasSum
  rw [← inner_tsum_diagonal hu.of_norm hv.of_norm ((E : ℤ)-D) hz] at H
  have H' := (Equiv.neg ℤ).hasSum_iff.mpr H
  convert H' using 1
  all_goals try with_reducible_and_instances rfl
  ext m
  dsimp only [Function.comp_def,Equiv.neg_apply,u,v]
  simp only [Equiv.neg_apply,inner_smul_left,inner_smul_right,Completion.inner_coe,
    starRingEnd_apply,hreal,neg_neg,U.physicalMode_adjoint ha hqa hha]
  rw [show -m+((E : ℤ)-D) = (E : ℤ)-D-m by omega]
  ring
  rfl

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.ClosedGraphData
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace H] [CompleteSpace K]

def doubleUnitary (E : H ≃ₗᵢ[ℂ] K) : Double H ≃ₗᵢ[ℂ] Double K :=
  E.withLpProdCongr 2 E

omit [CompleteSpace H] [CompleteSpace K] in
@[simp] theorem doubleUnitary_apply (E : H ≃ₗᵢ[ℂ] K) (x : Double H) :
    doubleUnitary E x = WithLp.toLp 2 (E x.ofLp.1,E x.ofLp.2) := rfl

omit [CompleteSpace H] [CompleteSpace K] in
@[simp] theorem doubleUnitary_symm_apply (E : H ≃ₗᵢ[ℂ] K) (x : Double K) :
    (doubleUnitary E).symm x = WithLp.toLp 2 (E.symm x.ofLp.1,E.symm x.ofLp.2) := rfl

omit [CompleteSpace H] [CompleteSpace K] in
theorem mem_graph_transport (E : H ≃ₗᵢ[ℂ] K) (T : K →ₗ.[ℂ] K) (x : Double H) :
    x ∈ graph (OperatorTransport.transport E T) ↔ doubleUnitary E x ∈ graph T :=
  OperatorTransport.mem_graph_iff E T x.ofLp.1 x.ofLp.2

 

theorem projection_transport (E : H ≃ₗᵢ[ℂ] K) (T : K →ₗ.[ℂ] K) (hT : T.IsClosed)
    (x : Double H) :
    projection (OperatorTransport.transport E T) (OperatorTransport.closed E hT) x =
      (doubleUnitary E).symm (projection T hT (doubleUnitary E x)) := by
  let : IsClosed (graph T : Set (Double K)) := graph_closed hT
  let : IsClosed (graph (OperatorTransport.transport E T) : Set (Double H)) :=
    graph_closed (OperatorTransport.closed E hT)
  change (graph (OperatorTransport.transport E T)).starProjection x = _
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · apply (mem_graph_transport E T _).mpr
    rw [(doubleUnitary E).apply_symm_apply]
    exact (graph T).starProjection_apply_mem _
  · intro y hy
    rw [← (doubleUnitary E).inner_map_map,map_sub,(doubleUnitary E).apply_symm_apply]
    exact (graph T).starProjection_inner_eq_zero _ _ ((mem_graph_transport E T y).mp hy)

omit [CompleteSpace H] [CompleteSpace K] in
theorem coordinate_doubleUnitary (E : H ≃ₗᵢ[ℂ] K) (i : Bool) (x : Double H) :
    coordinate i (doubleUnitary E x) = E (coordinate i x) := by
  cases i <;> rfl

omit [CompleteSpace H] [CompleteSpace K] in
theorem doubleUnitary_inclusion (E : H ≃ₗᵢ[ℂ] K) (i : Bool) (x : H) :
    doubleUnitary E (inclusion i x) = inclusion i (E x) := by
  cases i <;> simp [doubleUnitary_apply,inclusion]

 
theorem entry_transport (E : H ≃ₗᵢ[ℂ] K) (T : K →ₗ.[ℂ] K) (hT : T.IsClosed)
    (i j : Bool) (x : H) :
    entry (OperatorTransport.transport E T) (OperatorTransport.closed E hT) i j x =
      E.symm (entry T hT i j (E x)) := by
  change coordinate i (projection (OperatorTransport.transport E T)
      (OperatorTransport.closed E hT) (inclusion j x)) = _
  rw [projection_transport,doubleUnitary_inclusion]
  change coordinate i (doubleUnitary E.symm (projection T hT (inclusion j (E x)))) = _
  rw [coordinate_doubleUnitary]
  rfl

end StronglyRationalVOA.ClosedGraphData

open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_RegularizerFactorAdd
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace

open scoped Topology
open UniformSpace

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
local instance regularizerCommutationGradeFiniteDimensional :
    ∀ d : ℕ, FiniteDimensional ℂ (A.grade d) := A.grade_finite

lemma sobolevExtension_weakCommutation (r : ℕ) (M N : V →ₗ[ℂ] Completion V) {C D : ℝ}
    (hM : ∀ v, ‖M v‖ ≤ C*‖(A.energyShift^r) v‖)
    (hN : ∀ v, ‖N v‖ ≤ D*‖(A.energyShift^r) v‖)
    (hw : ∀ x y, inner ℂ (M x) (N y) = inner ℂ (N x) (M y)) (x y : Completion V) :
    inner ℂ (U.sobolevExtension r M x) (U.sobolevExtension r N y) =
      inner ℂ (U.sobolevExtension r N x) (U.sobolevExtension r M y) := by
  have hw' : ∀ x y, inner ℂ (U.spectralCoreMap M x) (U.spectralCoreMap N y) =
      inner ℂ (U.spectralCoreMap N x) (U.spectralCoreMap M y) := by
    intro x y
    obtain ⟨v,rfl⟩ := U.coreEnergyCoordinates.surjective x
    obtain ⟨w,rfl⟩ := U.coreEnergyCoordinates.surjective y
    simpa only [U.spectralCoreMap_apply,U.energyCoordinates.inner_map_map] using hw v w
  simpa only [sobolevExtension_apply,U.energyCoordinates.symm.inner_map_map] using
    HilbertScale.energyExtension_weakCommutation (fun d : ℕ => (1+(d : ℝ))^r)
      (fun d => one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) d; linarith))
      _ _ (U.spectralCoreMap_bound r M hM) (U.spectralCoreMap_bound r N hN) hw'
      (U.energyCoordinates x) (U.energyCoordinates y)


end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_HighFieldGraph
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace

namespace StronglyRationalVOA.CFTTypeVOA
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (A : CFTTypeVOA V)

 

theorem virasoro_primary_physical_commutator {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (hp : A.IsPrimary a) (m n : ℤ) (v : V) :
    A.virasoroMode m (A.physicalMode a d n v)-
      A.physicalMode a d n (A.virasoroMode m v) =
        (((d : ℂ)-1)*m-n) • A.physicalMode a d (m+n) v := by
  have h := A.toVertexAlgebra.mode_commutator A.conformalVector a v (m+1) (n+d-1)
  have htail (j : ℕ) (hj : 2 ≤ j) : mode A.fields A.conformalVector j a = 0 := by
    have hj1 : ((j-1 : ℕ) : ℤ)+1 = j := by omega
    simpa only [virasoroMode,hj1] using hp (j-1) (by omega)
  have hsum : (∑ᶠ j : ℕ, Ring.choose ((m+1 : ℤ) : ℂ) j •
      mode A.fields (mode A.fields A.conformalVector j a) ((m+1)+(n+d-1)-j) v) =
      ∑ j ∈ Finset.range 2, Ring.choose ((m+1 : ℤ) : ℂ) j •
      mode A.fields (mode A.fields A.conformalVector j a) ((m+1)+(n+d-1)-j) v := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    simp only [Finset.coe_range,Set.mem_Iio]
    by_contra H
    apply hj
    simp only [htail j (by omega),mode_zero,LinearMap.zero_apply,smul_zero]
  rw [hsum] at h
  have h0 : mode A.fields A.conformalVector 0 a = A.toVertexAlgebra.translation a := by
    rw [A.conformal_translation]
  have h1 : mode A.fields A.conformalVector 1 a = (d : ℂ) • a := A.virasoro_zero_on_grade ha
  have ht := congrArg (fun L : Module.End ℂ V => L v)
    (A.translation_covariance a (m+n+d))
  simp only [LinearMap.smul_apply] at ht
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Ring.choose_zero_right,
    Ring.choose_one_right,one_smul, Nat.cast_zero, Nat.cast_one,h0,h1,mode_smul,LinearMap.smul_apply] at h
  rw [show (m+1)+(n+(d : ℤ)-1)-0 = m+n+d by omega,ht] at h
  change mode A.fields A.conformalVector (m+1) (mode A.fields a (n+d-1) v)-
    mode A.fields a (n+d-1) (mode A.fields A.conformalVector (m+1) v) = _
  rw [h]
  simp only [show (m+1)+(n+(d : ℤ)-1)-1=m+n+d-1 by omega,physicalMode]
  push_cast
  module
end StronglyRationalVOA.CFTTypeVOA

namespace StronglyRationalVOA.CFTTypeVOA
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (A : CFTTypeVOA V)

 

def primarySpace (d : ℕ) : Submodule ℂ V where
  carrier := {a | a ∈ A.grade d ∧ A.IsPrimary a}
  zero_mem' := ⟨(A.grade d).zero_mem,fun _ _ => map_zero _⟩
  add_mem' := by
    intro a b ha hb
    exact ⟨(A.grade d).add_mem ha.1 hb.1,fun n hn => by rw [map_add,ha.2 n hn,hb.2 n hn,add_zero]⟩
  smul_mem' := by
    intro c a ha
    exact ⟨(A.grade d).smul_mem c ha.1,fun n hn => by rw [map_smul,ha.2 n hn,smul_zero]⟩

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
lemma pct_primary {a : V} (ha : A.IsPrimary a) : A.IsPrimary (U.pct a) := by
  intro n hn
  rw [← U.pct_virasoro,ha n hn,map_zero]

 
theorem exists_hermitian_primary_spanning (d : ℕ) :
    ∃ S : Finset V,
      (∀ a ∈ S, a ∈ A.grade d ∧ A.IsPrimary a ∧ U.IsHermitian d a) ∧
      (∀ a ∈ A.grade d, A.IsPrimary a → a ∈ Submodule.span ℂ (S : Set V)) := by
  classical
  let E := A.primarySpace d
  let J := U.hermitianConjugation d
  let H := {a : V | a ∈ E ∧ J a = a}
  have hJin (a : V) (ha : a ∈ E) : J a ∈ E := by
    refine ⟨(A.grade d).smul_mem _ (U.pct_mem_grade ha.1),?_⟩
    intro n hn
    change A.virasoroMode n (((-1 : ℂ)^d) • U.pct a) = 0
    rw [map_smul,U.pct_primary ha.2 n hn,smul_zero]
  have hJ (a : V) : J (J a) = a := U.hermitianConjugation_involutive d a
  have hfix (a : V) (ha : a ∈ E) : a+J a ∈ H := by
    refine ⟨E.add_mem ha (hJin a ha),?_⟩
    rw [map_add,hJ,add_comm]
  have hspan : E ≤ Submodule.span ℂ H := by
    intro a ha
    have hx := Submodule.subset_span (R := ℂ) (hfix a ha)
    have hy := Submodule.subset_span (R := ℂ) (hfix (Complex.I • a) (E.smul_mem _ ha))
    have he : a = (2 : ℂ)⁻¹ • (a+J a) +
        (-Complex.I/2 : ℂ) • (Complex.I • a+J (Complex.I • a)) := by
      rw [map_smulₛₗ,show starRingEnd ℂ Complex.I = -Complex.I from Complex.conj_I]
      simp only [smul_add,smul_smul]
      have hI : (-Complex.I/2 : ℂ)*Complex.I = (2 : ℂ)⁻¹ := by
        rw [div_mul_eq_mul_div,neg_mul,Complex.I_mul_I]
        norm_num
      rw [hI,mul_neg,hI]
      module
    rw [he]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hx) (Submodule.smul_mem _ _ hy)
  let := A.grade_finite d
  have : FiniteDimensional ℂ E := Submodule.finiteDimensional_of_le (show E ≤ A.grade d from fun _ h => h.1)
  obtain ⟨T,hT⟩ := Submodule.FG.of_finite (N := E)
  have hTspan : (T : Set V) ⊆ Submodule.span ℂ H := by
    intro a ha
    exact hspan (hT ▸ Submodule.subset_span ha)
  obtain ⟨S,hSH,hTS⟩ := Submodule.subset_span_finite_of_subset_span hTspan
  refine ⟨S,?_,?_⟩
  · intro a ha
    have h := hSH ha
    exact ⟨h.1.1,h.1.2,h.2⟩
  · intro a ha hp
    have hle : E ≤ Submodule.span ℂ (S : Set V) := by
      rw [← hT]
      exact Submodule.span_le.mpr hTS
    exact hle ⟨ha,hp⟩

end UnitaryStructure
end StronglyRationalVOA.CFTTypeVOA

open scoped ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_PrimaryStressWeak
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff

open UniformSpace

open Filter
open scoped Topology
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]



lemma graph_entries_commute_of_regularizers (T S : H →ₗ.[ℂ] H)
    (hT : T.IsClosed) (hS : S.IsClosed)
    (R B : ℕ → H →L[ℂ] H)
    (hg : ∀ n x, (R n x,B n x) ∈ T.graph)
    (hlim : ∀ x, Tendsto (fun n => R n x) atTop (𝓝 x))
    (hreg : ∀ n x y, (x,y) ∈ T.graph → B n x = R n y)
    (hR : ∀ n k l, ClosedGraphData.entry S hS k l * R n = R n * ClosedGraphData.entry S hS k l)
    (hB : ∀ n k l, ClosedGraphData.entry S hS k l * B n = B n * ClosedGraphData.entry S hS k l)
    (i j k l : Bool) :
    ClosedGraphData.entry T hT i j * ClosedGraphData.entry S hS k l =
      ClosedGraphData.entry S hS k l * ClosedGraphData.entry T hT i j := by
  symm
  apply ClosedGraphData.entry_commutes_of_graph_invariant T hT _
    (fun x y hxy => graph_invariant_of_regularizers T hT R B hg hlim hreg _
      (fun n => hR n k l) (fun n => hB n k l) hxy) ?_ i j
  change ∀ x y, (x,y) ∈ T.graph →
    (star (ClosedGraphData.entry S hS k l) x,star (ClosedGraphData.entry S hS k l) y) ∈ T.graph
  rw [ClosedGraphData.star_entry]
  intro x y hxy
  exact graph_invariant_of_regularizers T hT R B hg hlim hreg _
    (fun n => hR n l k) (fun n => hB n l k) hxy
end StronglyRationalVOA.SymmetricOperator

open Filter MeasureTheory
open scoped Topology

open MeasureTheory
open scoped Topology

open Filter MeasureTheory
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_StressCutoffNormalized2
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory

open Filter
open scoped Topology

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (A : CFTTypeVOA V)
lemma smearedMap_smul {a : V} (he : A.PolynomialEnergyBound a) (d : ℕ)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (c : ℂ) :
    A.smearedMap a d he (fun n => c*f n) (hf.smul c)=c • A.smearedMap a d he f hf := by
  ext v
  simp only [smearedMap_apply,LinearMap.smul_apply,mul_smul,tsum_const_smul'']
end StronglyRationalVOA.CFTTypeVOA
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma sobolevExtension_sub (r : ℕ) (M N : V →ₗ[ℂ] Completion V) {C D : ℝ}
    (hM : ∀ v, ‖M v‖ ≤ C*‖(A.energyShift^r) v‖)
    (hN : ∀ v, ‖N v‖ ≤ D*‖(A.energyShift^r) v‖) :
    U.sobolevExtension r (M-N)=U.sobolevExtension r M-U.sobolevExtension r N := by
  have hMN (v : V) : ‖(M-N) v‖ ≤ (C+D)*‖(A.energyShift^r) v‖ := by
    exact (norm_sub_le (M v) (N v)).trans ((add_le_add (hM v) (hN v)).trans_eq (add_mul ..).symm)
  ext x
  have hd : DenseRange (fun v : V => (v : Completion V)) := Completion.denseRange_coe
  apply hd.induction_on (p := fun x => U.sobolevExtension r (M-N) x=(U.sobolevExtension r M-U.sobolevExtension r N) x) x
    (isClosed_eq (U.sobolevExtension r _).continuous (ContinuousLinearMap.continuous _))
  intro v
  simp only [sub_apply,U.sobolevExtension_coe r _ hMN,
    U.sobolevExtension_coe r _ hM,U.sobolevExtension_coe r _ hN,LinearMap.sub_apply]

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

include U in
lemma physicalMode_inner_orthogonal {a x y : V} {d D E : ℕ}
    (ha : a ∈ A.grade d) (hx : x ∈ A.grade D) (hy : y ∈ A.grade E) (n : ℤ)
    (hne : n ≠ (E:ℤ)-D) : inner ℂ x (A.physicalMode a d n y)=0 := by
  have h := U.virasoro_adjoint 0 x (A.physicalMode a d n y)
  simp only [neg_zero,A.virasoro_zero_on_grade hx,A.physicalMode_energy_eigenvalue ha hy,
    inner_smul_left,inner_smul_right,map_natCast] at h
  have hc : (D:ℂ)-((E:ℂ)-n) ≠ 0 := by
    intro hz
    apply hne
    have heq : (n:ℂ)=(E:ℂ)-D := by linear_combination hz
    exact_mod_cast heq
  apply (mul_eq_zero.mp (show ((D:ℂ)-((E:ℂ)-n))*inner ℂ x (A.physicalMode a d n y)=0 from ?_)).resolve_left hc
  rw [sub_mul,h,sub_self]

include U in
lemma inner_smearedMap_homogeneous {a x y : V} {d D E : ℕ}
    (ha : a ∈ A.grade d) (hx : x ∈ A.grade D) (hy : y ∈ A.grade E)
    (he : A.PolynomialEnergyBound a) {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    inner ℂ (x : Completion V) (A.smearedMap a d he f hf y)=
      f ((E:ℤ)-D)*inner ℂ x (A.physicalMode a d ((E:ℤ)-D) y) := by
  rw [smearedMap_apply,inner_tsum_right (A.summable_norm_physicalSmear he d hf y).of_norm]
  simp only [inner_smul_right,Completion.inner_coe]
  exact tsum_eq_single ((E:ℤ)-D) (fun n hn => by rw [U.physicalMode_inner_orthogonal ha hx hy n hn,mul_zero])

 

lemma primary_stress_weakCommutator (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a) (hh : U.IsHermitian d a)
    {f g h : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) (hhc : RapidCoefficients h)
    (hfr : ∀ n, star (f n)=f (-n)) (hgr : ∀ n, star (g n)=g (-n))
    (hconv : ∀ r : ℤ, HasSum (fun m : ℤ => (((d:ℂ)-1)*m-(r-m))*f m*g (r-m)) (-Complex.I*h r))
    (x y : V) :
    inner ℂ (A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector) f hf x)
      (A.smearedMap a d (U.polynomialEnergyBounds hc a) g hg y)-
    inner ℂ (A.smearedMap a d (U.polynomialEnergyBounds hc a) g hg x)
      (A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector) f hf y)=
    -Complex.I*inner ℂ (x:Completion V) (A.smearedMap a d (U.polynomialEnergyBounds hc a) h hhc y) := by
  have hν : U.IsHermitian 2 A.conformalVector := by simp [IsHermitian,U.pct_conformal]
  let M := A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector) f hf
  let N := A.smearedMap a d (U.polynomialEnergyBounds hc a) g hg
  let Q := A.smearedMap a d (U.polynomialEnergyBounds hc a) h hhc
  have Hhom (D E : ℕ) (x y : V) (hx : x ∈ A.grade D) (hy : y ∈ A.grade E) :
      inner ℂ (M x) (N y)-inner ℂ (N x) (M y) = -Complex.I*inner ℂ (x:Completion V) (Q y) := by
    let r : ℤ := (E:ℤ)-D
    have H1 := U.hasSum_smeared_inner_homogeneous A.conformal_mem ha hx hy
      A.conformal_quasiPrimary hν (U.polynomialEnergyBounds hc A.conformalVector)
      (U.polynomialEnergyBounds hc a) hf hg hfr
    have H2 := U.hasSum_smeared_inner_homogeneous ha A.conformal_mem hx hy
      (hp 1 (by norm_num)) hh (U.polynomialEnergyBounds hc a)
      (U.polynomialEnergyBounds hc A.conformalVector) hg hf hgr
    let R : ℤ ≃ ℤ :=
      { toFun := fun m => r-m
        invFun := fun m => r-m
        left_inv := fun m => by dsimp; omega
        right_inv := fun m => by dsimp; omega }
    have Hdiff := H1.sub (R.hasSum_iff.mpr H2)
    have Hz := (hconv r).mul_right (inner ℂ x (A.physicalMode a d r y))
    have He : HasSum (fun m : ℤ => f m*g (r-m)*inner ℂ x
        (A.virasoroMode m (A.physicalMode a d (r-m) y)-
          A.physicalMode a d (r-m) (A.virasoroMode m y)))
        (-Complex.I*inner ℂ (x:Completion V) (Q y)) := by
      rw [U.inner_smearedMap_homogeneous ha hx hy]
      rw [mul_assoc] at Hz
      apply Hz.congr_fun
      intro m
      rw [A.virasoro_primary_physical_commutator ha hp,inner_smul_right,
        show m+(r-m)=r by omega]
      push_cast
      ring
    apply Hdiff.unique
    convert He using 1
    all_goals try with_reducible_and_instances rfl
    ext m
    simp only [Function.comp_def,R,Equiv.coe_fn_mk]
    rw [show (E:ℤ)-D-(r-m)=m by dsimp [r]; omega]
    rw [show A.physicalMode A.conformalVector 2 m=A.virasoroMode m by
      unfold physicalMode virasoroMode; congr 1; omega]
    simp only [inner_sub_right]
    ring
  change inner ℂ (M x) (N y)-inner ℂ (N x) (M y) = -Complex.I*inner ℂ (x:Completion V) (Q y)
  apply A.homogeneous_induction (P := fun x => inner ℂ (M x) (N y)-inner ℂ (N x) (M y) =
    -Complex.I*inner ℂ (x:Completion V) (Q y))
  · simp only [map_zero,inner_zero_left,sub_self,Completion.coe_zero,mul_zero]
  · intro D x hx
    apply A.homogeneous_induction (P := fun y => inner ℂ (M x) (N y)-inner ℂ (N x) (M y) =
      -Complex.I*inner ℂ (x:Completion V) (Q y))
    · simp
    · intro E y hy; exact Hhom D E x y hx hy
    · intro y z hy hz
      simp only [map_add,inner_add_right]
      linear_combination hy+hz
  · intro x z hx hz
    simp only [map_add,inner_add_left,Completion.coe_add]
    linear_combination hx+hz

 

lemma sobolevExtension_weakCommutator (r : ℕ) (M N Q : V →ₗ[ℂ] Completion V) {C D E : ℝ}
    (hM : ∀ v, ‖M v‖ ≤ C*‖(A.energyShift^r) v‖)
    (hN : ∀ v, ‖N v‖ ≤ D*‖(A.energyShift^r) v‖)
    (hQ : ∀ v, ‖Q v‖ ≤ E*‖(A.energyShift^r) v‖) (c : ℂ)
    (hw : ∀ x y, inner ℂ (M x) (N y)-inner ℂ (N x) (M y)=c*inner ℂ (x:Completion V) (Q y))
    (x y : Completion V) :
    inner ℂ (U.sobolevExtension r M x) (U.sobolevExtension r N y)-
      inner ℂ (U.sobolevExtension r N x) (U.sobolevExtension r M y)=
      c*inner ℂ (U.inverseSobolev r x) (U.sobolevExtension r Q y) := by
  have hd : DenseRange (fun v : V => (v:Completion V)) := Completion.denseRange_coe
  refine hd.induction_on₂ ?_ ?_ x y
  · exact isClosed_eq
      ((((U.sobolevExtension r M).continuous.comp continuous_fst).inner
        ((U.sobolevExtension r N).continuous.comp continuous_snd)).sub
        (((U.sobolevExtension r N).continuous.comp continuous_fst).inner
          ((U.sobolevExtension r M).continuous.comp continuous_snd)))
      (continuous_const.mul (((U.inverseSobolev r).continuous.comp continuous_fst).inner
        ((U.sobolevExtension r Q).continuous.comp continuous_snd)))
  · intro v w
    simpa only [U.sobolevExtension_coe r M hM,U.sobolevExtension_coe r N hN,
      U.sobolevExtension_coe r Q hQ,← U.inverseCoreEnergy_coe] using
        hw (U.inverseCoreEnergy r v) (U.inverseCoreEnergy r w)

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open scoped Topology ContDiff
namespace StronglyRationalVOA.SmoothCircleFunction
local instance instFactLtRealOfNatHMulPi : Fact (0 < 2*Real.pi) := ⟨period_pos⟩

end StronglyRationalVOA.SmoothCircleFunction

open UniformSpace Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_StressPropagatorDerivative
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff

namespace StronglyRationalVOA.OperatorTransport
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma onSubmodule (E : H ≃ₗᵢ[ℂ] H) (D : Submodule ℂ H) (P Q : Module.End ℂ D)
    (hE : ∀ x ∈ D, E x ∈ D) (hI : ∀ x ∈ D, E.symm x ∈ D)
    (hc : ∀ x : D, (Q ⟨E x,hE x x.property⟩ : H)=E (P x)) :
    transport E (SymmetricOperator.onSubmodule D Q)=SymmetricOperator.onSubmodule D P := by
  apply LinearPMap.eq_of_eq_graph
  ext p
  rw [mem_graph_iff]
  constructor
  · intro hp
    obtain ⟨z,hz,hQ⟩ := (LinearPMap.mem_graph_iff _).mp hp
    let w : D := ⟨E.symm z,hI z z.property⟩
    have hw : (w:H)=p.1 := by change E.symm (z:H)=p.1; rw [hz,E.symm_apply_apply]
    have hzw : (⟨E w,hE w w.property⟩ : D)=z := Subtype.ext (E.apply_symm_apply z)
    have hPw : (P w:H)=p.2 := by
      apply E.injective
      rw [← hc w,hzw]
      exact hQ
    exact (LinearPMap.mem_graph_iff _).mpr ⟨w,hw,hPw⟩
  · intro hp
    obtain ⟨w,hw,hP⟩ := (LinearPMap.mem_graph_iff _).mp hp
    refine (LinearPMap.mem_graph_iff _).mpr ⟨⟨E w,hE w w.property⟩,?_,?_⟩
    · exact congrArg E hw
    · change (Q ⟨E w,hE w w.property⟩:H)=E p.2
      change (P w:H)=p.2 at hP
      rw [hc w,hP]
end StronglyRationalVOA.OperatorTransport

open UniformSpace Filter
open scoped Topology

open Filter
open scoped Topology ContDiff

open Filter
open scoped Topology ContDiff

open Filter
open scoped Topology ContDiff

open Filter MeasureTheory Set
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_CoefficientSummableBound
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
namespace StronglyRationalVOA

lemma coefficientSeminorm_tendsto_zero {ι : Type*} {l : Filter ι} {f : ι → ℤ → ℂ} (r : ℕ)
    {C : ℝ} (hp : ∀ n, Tendsto (fun i => f i n) l (𝓝 0))
    (hb : ∀ᶠ i in l, ∀ n, ‖f i n‖*(1+|(n:ℝ)|)^r ≤ C*((1+|(n:ℝ)|)^2)⁻¹) :
    Tendsto (fun i => coefficientSeminorm (f i) r) l (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (summable_circle_decay.mul_left C)
    (f := fun i n => ‖f i n‖*(1+|(n:ℝ)|)^r) (g := fun _ : ℤ => (0:ℝ)) (fun n => by simpa using (hp n).norm.mul_const ((1+|(n:ℝ)|)^r))
    (hb.mono (fun i hi n => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact hi n))
  simpa only [tsum_zero,coefficientSeminorm] using h


end StronglyRationalVOA

open Filter Set
open scoped Topology ContDiff

open UniformSpace Filter
open scoped Topology ContDiff
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma sobolevExtension_weakCommutator_central (r : ℕ) (M N Q : V →ₗ[ℂ] Completion V) {C D E : ℝ}
    (hM : ∀ v, ‖M v‖ ≤ C*‖(A.energyShift^r) v‖)
    (hN : ∀ v, ‖N v‖ ≤ D*‖(A.energyShift^r) v‖)
    (hQ : ∀ v, ‖Q v‖ ≤ E*‖(A.energyShift^r) v‖) (c w : ℂ)
    (hw : ∀ x y, inner ℂ (M x) (N y)-inner ℂ (N x) (M y)=c*inner ℂ (x:Completion V) (Q y)+w*inner ℂ x y)
    (x y : Completion V) :
    inner ℂ (U.sobolevExtension r M x) (U.sobolevExtension r N y)-
      inner ℂ (U.sobolevExtension r N x) (U.sobolevExtension r M y)=
      c*inner ℂ (U.inverseSobolev r x) (U.sobolevExtension r Q y)+
      w*inner ℂ (U.inverseSobolev r x) (U.inverseSobolev r y) := by
  have hd : DenseRange (fun v : V => (v:Completion V)) := Completion.denseRange_coe
  refine hd.induction_on₂ ?_ ?_ x y
  · exact isClosed_eq
      ((((U.sobolevExtension r M).continuous.comp continuous_fst).inner
        ((U.sobolevExtension r N).continuous.comp continuous_snd)).sub
        (((U.sobolevExtension r N).continuous.comp continuous_fst).inner
          ((U.sobolevExtension r M).continuous.comp continuous_snd)))
      ((continuous_const.mul (((U.inverseSobolev r).continuous.comp continuous_fst).inner
        ((U.sobolevExtension r Q).continuous.comp continuous_snd))).add
        (continuous_const.mul (((U.inverseSobolev r).continuous.comp continuous_fst).inner
          ((U.inverseSobolev r).continuous.comp continuous_snd))))
  · intro v w
    simpa only [U.sobolevExtension_coe r M hM,U.sobolevExtension_coe r N hN,
      U.sobolevExtension_coe r Q hQ,← U.inverseCoreEnergy_coe,Completion.inner_coe] using
        hw (U.inverseCoreEnergy r v) (U.inverseCoreEnergy r w)

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Filter MeasureTheory Set
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_StressSmoothness
attribute [-instance] _root_.OAI.StronglyRationalVOA.PositiveCircleGeometry.SmoothLift.instTopologicalSpace _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set

open Filter MeasureTheory Set
open scoped Topology ContDiff

open Filter MeasureTheory Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.PositiveCircleGeometry.Field
variable (f : Field (2*Real.pi))
def flattening : SmoothLift where
  toFun := f.normalizedCoordinate
  add_one := f.coordinate_add_one SmoothCircleFunction.period_pos
  smooth := f.coordinate_smooth
  derivative_pos := fun x => by
    rw [(f.coordinate_hasDerivAt x).deriv]
    exact f.coordinate_derivative_pos SmoothCircleFunction.period_pos x
lemma flattening_density_one (x : ℝ) : f.flattening.density f.unitParameter 1 1 x=f.frequency := by
  change f.flattening.jacobian 1 (f.flattening.inverse 1 x)^1*f.unitParameter (f.flattening.inverse 1 x)=_
  simp only [SmoothLift.jacobian,Real.smoothTransition.one,pow_one,sub_self,zero_add,one_mul]
  exact f.flatten_identity SmoothCircleFunction.period_pos _
lemma flattening_realDensity_zero (x : ℝ) : f.flattening.realAngularDensity f.unitParameter 1 (0,x)=f x := by
  change f.flattening.density f.unitParameter 1 0 (x/(2*Real.pi))=f x
  rw [SmoothLift.density_zero]
  dsimp only [unitParameter]
  congr 1
  field_simp [Real.pi_ne_zero]
lemma flattening_realDensity_one (x : ℝ) : f.flattening.realAngularDensity f.unitParameter 1 (1,x)=f.frequency :=
  f.flattening_density_one _
lemma flatteningAnomaly_one : f.flattening.normalizedAnomaly f.unitParameter 1=f.frequency := by
  unfold SmoothLift.normalizedAnomaly RealCircleCalculus.anomalyEnergy
  have he : (fun x => f.flattening.realAngularDensity f.unitParameter 1 (1,x))=fun _ => f.frequency :=
    funext f.flattening_realDensity_one
  rw [he]
  simp only [RealCircleCalculus.anomalyDensity,deriv_const,zero_pow (by decide : 2≠0),zero_div,sub_zero,
    intervalIntegral.integral_const,smul_eq_mul,sub_zero]
  field_simp [Real.pi_ne_zero]
lemma flatteningAnomaly_zero : f.flattening.normalizedAnomaly f.unitParameter 0=
    (2*Real.pi)⁻¹*((∫ x in 0..2*Real.pi, f x)-(∫ x in 0..2*Real.pi, (deriv f x)^2/f x)) := by
  unfold SmoothLift.normalizedAnomaly RealCircleCalculus.anomalyEnergy
  have he : (fun x => f.flattening.realAngularDensity f.unitParameter 1 (0,x))=f :=
    funext f.flattening_realDensity_zero
  rw [he]
  dsimp only [RealCircleCalculus.anomalyDensity]
  congr 1
  exact intervalIntegral.integral_sub (f.smooth.continuous.intervalIntegrable _ _)
    ((((contDiff_infty_iff_deriv.mp f.smooth).2.continuous.pow 2).div f.smooth.continuous
      (fun x => ne_of_gt (f.positive x))).intervalIntegrable _ _)
lemma flatteningShift (c : ℝ) : f.flattening.anomalyShift f.unitParameter (c:ℂ) 1=(-(f.stressScalar c):ℝ) := by
  rw [SmoothLift.anomalyShift,f.flatteningAnomaly_one,f.flatteningAnomaly_zero]
  dsimp only [stressScalar]
  push_cast
  ring
end StronglyRationalVOA.PositiveCircleGeometry.Field

open UniformSpace Filter
open scoped Topology ContDiff

open Filter UniformSpace
open scoped Topology ContDiff

open UniformSpace Filter
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_Locality
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace
open Set MeasureTheory

open UniformSpace Set

open Set
open scoped Topology ContDiff

open Filter
open scoped Topology

open UniformSpace Filter
open scoped Topology

open UniformSpace Filter
open scoped Topology

namespace StronglyRationalVOA.ClosedGraphData
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
omit [CompleteSpace H] in
lemma coordinate_ext {x y : Double H} (h : ∀ i, coordinate i x = coordinate i y) : x=y := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ H H).injective
  exact Prod.ext (h false) (h true)
omit [CompleteSpace H] in
lemma inclusion_coordinate_sum (x : Double H) :
    inclusion false (coordinate false x) + inclusion true (coordinate true x) = x := by
  apply coordinate_ext
  intro i
  cases i <;> simp [coordinate,inclusion]
lemma projection_commutes_of_entry_commutes (T : H →ₗ.[ℂ] H) (hT : T.IsClosed)
    (Q : H →L[ℂ] H) (hQ : ∀ i j, Q * entry T hT i j = entry T hT i j * Q) :
    (diagonalAction Q).comp (projection T hT) = (projection T hT).comp (diagonalAction Q) := by
  apply ContinuousLinearMap.ext
  intro x
  apply coordinate_ext
  intro i
  have he (j : Bool) := congrArg (fun L : H →L[ℂ] H => L (coordinate j x)) (hQ i j)
  have h1 := he false
  have h2 := he true
  have hde (j : Bool) : diagonalAction Q (inclusion j (coordinate j x)) =
      inclusion j (Q (coordinate j x)) := by
    exact congrArg (fun L : H →L[ℂ] Double H => L (coordinate j x)) (diagonalAction_inclusion Q j)
  have hc : coordinate i (diagonalAction Q (projection T hT x)) =
      Q (coordinate i (projection T hT x)) := by
    exact congrArg (fun L : Double H →L[ℂ] H => L (projection T hT x)) (coordinate_diagonalAction Q i)
  change coordinate i (diagonalAction Q (projection T hT x)) =
    coordinate i (projection T hT (diagonalAction Q x))
  rw [hc]
  conv_lhs => rw [← inclusion_coordinate_sum x]
  conv_rhs => rw [← inclusion_coordinate_sum x]
  simp only [map_add,hde]
  exact congrArg₂ (·+·) h1 h2
end StronglyRationalVOA.ClosedGraphData

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_GraphInvariantOf
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace
open Set MeasureTheory
open Set
namespace StronglyRationalVOA.ClosedGraphData
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
lemma graph_invariant_of_entry_commutes (T : H →ₗ.[ℂ] H) (hT : T.IsClosed)
    (Q : H →L[ℂ] H) (hQ : ∀ i j, Q * entry T hT i j = entry T hT i j * Q)
    {x y : H} (hxy : (x,y) ∈ T.graph) : (Q x,Q y) ∈ T.graph := by
  let z : Double H := WithLp.toLp 2 (x,y)
  let : IsClosed (graph T : Set (Double H)) := graph_closed hT
  have hz : z ∈ graph T := hxy
  have hp : projection T hT z = z := Submodule.starProjection_eq_self_iff.mpr hz
  have hh := congrArg (fun L : Double H →L[ℂ] Double H => L z)
    (projection_commutes_of_entry_commutes T hT Q hQ)
  change diagonalAction Q (projection T hT z) = projection T hT (diagonalAction Q z) at hh
  rw [hp] at hh
  have hm := (graph T).starProjection_apply_mem (diagonalAction Q z)
  change projection T hT (diagonalAction Q z) ∈ graph T at hm
  rw [← hh] at hm
  exact hm
end StronglyRationalVOA.ClosedGraphData

open UniformSpace Filter
open scoped Topology

open UniformSpace

open Filter MeasureTheory
open scoped Topology

open UniformSpace

open MeasureTheory Filter
open scoped Topology ContDiff

open MeasureTheory Filter
open scoped Topology

open MeasureTheory Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_SmoothSmearShift
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace
open Set MeasureTheory
open Set
open MeasureTheory Filter
open Set MeasureTheory Filter UniformSpace
open Set UniformSpace
open Set UniformSpace Filter
open Set MeasureTheory Filter

open UniformSpace

open UniformSpace

namespace StronglyRationalVOA
 

lemma summable_norm_normal_triangle {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {F : ℤ → H} {K : ℝ} (hK : 0 ≤ K) (P N : ℕ)
    (hF : ∀ r, ‖F r‖ ≤ K*(1+|(r:ℝ)|)^P)
    (hz : ∀ r, r < -(N:ℤ) → F r=0)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) (k : ℤ) :
    Summable (fun q : ℤ × ℕ => ‖(f q.1*g (k-q.1)) • F (q.1-1-q.2)‖) := by
  let G := coefficientSeminorm g 0
  have hG : 0 ≤ G := coefficientSeminorm_nonneg g 0
  have hgB (i : ℤ) : ‖g i‖ ≤ G := by
    have h := (hg 0).le_tsum i (fun n _ => by positivity)
    simpa only [G,coefficientSeminorm,pow_zero,mul_one] using h
  let C := K*G*(N+2 : ℝ)^(P+2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hj : Summable (fun j : ℕ => C/(1+(j:ℝ))^2) := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    have h' : Summable (fun j : ℕ => 1/(1+(j:ℝ))^2) := by
      simpa only [Nat.cast_add,Nat.cast_one,add_comm] using h
    simpa only [mul_one_div] using h'.mul_left C
  have hs := (hf (P+2)).mul_of_nonneg hj (fun _ => by positivity) (fun _ => by positivity)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hs
  rintro ⟨i,j⟩
  change ‖(f i*g (k-i)) • F (i-1-j)‖ ≤
    (‖f i‖*(1+|(i:ℝ)|)^(P+2))*(C/(1+(j:ℝ))^2)
  by_cases hr : i-1-(j:ℤ) < -(N:ℤ)
  · rw [hz _ hr,smul_zero,norm_zero]
    positivity
  · have hlow : -(N:ℝ) ≤ (i:ℝ)-1-j := by exact_mod_cast (show -(N:ℤ) ≤ i-1-j by omega)
    have hjbound : 1+(j:ℝ) ≤ (N+2 : ℝ)*(1+|(i:ℝ)|) := by
      have hi := le_abs_self (i:ℝ)
      have hNi : 0 ≤ (N:ℝ)*|(i:ℝ)| := by positivity
      nlinarith
    have hrabs : |((i-1-(j:ℤ):ℤ):ℝ)| ≤ |(i:ℝ)|+(N:ℝ)+1 := by
      rw [Int.cast_sub,Int.cast_sub,Int.cast_one,Int.cast_natCast]
      apply abs_le.mpr
      constructor
      · linarith [abs_nonneg (i:ℝ)]
      · linarith [le_abs_self (i:ℝ),Nat.cast_nonneg (α := ℝ) j,Nat.cast_nonneg (α := ℝ) N]
    have hrbound : 1+|((i-1-(j:ℤ):ℤ):ℝ)| ≤ (N+2 : ℝ)*(1+|(i:ℝ)|) := by
      have hNi : 0 ≤ (N:ℝ)*|(i:ℝ)| := by positivity
      nlinarith [abs_nonneg (i:ℝ)]
    have hd : 0 < (1+(j:ℝ))^2 := by positivity
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hd).mpr
    calc
      ‖(f i*g (k-i)) • F (i-1-j)‖*(1+(j:ℝ))^2 ≤
          (‖f i‖*G*(K*((N+2 : ℝ)*(1+|(i:ℝ)|))^P))*
            ((N+2 : ℝ)*(1+|(i:ℝ)|))^2 := by
        rw [norm_smul,norm_mul]
        gcongr
        · exact hgB _
        · exact (hF _).trans (by gcongr)
      _ = (‖f i‖*(1+|(i:ℝ)|)^(P+2))*C := by
        dsimp only [C]
        simp only [pow_add,mul_pow]
        ring
end StronglyRationalVOA

open UniformSpace

open UniformSpace

open UniformSpace

open UniformSpace

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_LocalNormalMap
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace
open Set MeasureTheory
open Set
open MeasureTheory Filter
open Set MeasureTheory Filter UniformSpace
open Set UniformSpace
open Set UniformSpace Filter
open Set MeasureTheory Filter

open Set

open Set
namespace StronglyRationalVOA.SmoothCircleFunction
local instance instFactLtRealOfNatHMulPi_4 : Fact (0 < 2*Real.pi) := ⟨period_pos⟩
end StronglyRationalVOA.SmoothCircleFunction

open UniformSpace

open Set UniformSpace Filter
open scoped Topology

open Set UniformSpace

open UniformSpace Set Filter
open scoped Topology

open UniformSpace Set
open scoped Topology

open UniformSpace Set

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_GeometryContinuation
attribute [-instance] _root_.OAI.StronglyRationalVOA.PositiveCircleGeometry.SmoothLift.instTopologicalSpace _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Set
open scoped Topology ContDiff

namespace StronglyRationalVOA.PositiveCircleGeometry.SmoothLift
variable (φ : SmoothLift)

lemma velocity_second_formula (t x : ℝ) :
    iteratedDeriv 2 (φ.velocity t) x =
      deriv Real.smoothTransition t * iteratedDeriv 2 φ (φ.inverse t x) /
        φ.jacobian t (φ.inverse t x)^3 := by
  have hfun : deriv (φ.velocity t) = fun z =>
      deriv Real.smoothTransition t * (deriv φ (φ.inverse t z)-1) /
        φ.jacobian t (φ.inverse t z) :=
    funext fun z => (φ.velocity_space_derivative t z).deriv
  have hi := φ.inverse_space_derivative t x
  have h2 := (φ.jet_hasDerivAt 1 (φ.inverse t x)).comp x hi
  rw [iteratedDeriv_one] at h2
  have hj := (φ.jacobian_space_derivative t (φ.inverse t x)).comp x hi
  have hd := ((h2.sub_const 1).const_mul (deriv Real.smoothTransition t)).div hj
    (ne_of_gt (φ.jacobian_pos t (φ.inverse t x)))
  simp only [Function.comp_def] at hd
  rw [show (2:ℕ)=1+1 by rfl, iteratedDeriv_succ, iteratedDeriv_one, hfun]
  calc _ = _ := hd.deriv
       _ = _ := by
         have hne := ne_of_gt (φ.jacobian_pos t (φ.inverse t x))
         simp only [iteratedDeriv_succ, iteratedDeriv_zero]
         field_simp [hne]
         simp only [jacobian]
         ring

lemma velocity_third_formula (t x : ℝ) :
    iteratedDeriv 3 (φ.velocity t) x = deriv Real.smoothTransition t *
      (iteratedDeriv 3 φ (φ.inverse t x) / φ.jacobian t (φ.inverse t x)^4 -
        3 * Real.smoothTransition t * (iteratedDeriv 2 φ (φ.inverse t x))^2 /
          φ.jacobian t (φ.inverse t x)^5) := by
  have hfun : iteratedDeriv 2 (φ.velocity t) = fun z =>
      deriv Real.smoothTransition t * iteratedDeriv 2 φ (φ.inverse t z) /
        φ.jacobian t (φ.inverse t z)^3 := funext (φ.velocity_second_formula t)
  have hi := φ.inverse_space_derivative t x
  have h3 := (φ.jet_hasDerivAt 2 (φ.inverse t x)).comp x hi
  have hj := (φ.jacobian_space_derivative t (φ.inverse t x)).comp x hi
  have hd := (h3.const_mul (deriv Real.smoothTransition t)).div (hj.pow 3)
    (pow_ne_zero _ (ne_of_gt (φ.jacobian_pos t (φ.inverse t x))))
  simp only [Function.comp_def, Pi.pow_apply] at hd
  rw [show (3:ℕ)=2+1 by rfl, iteratedDeriv_succ, hfun]
  calc _ = _ := hd.deriv
       _ = _ := by
         have hne := ne_of_gt (φ.jacobian_pos t (φ.inverse t x))
         simp only [iteratedDeriv_succ, iteratedDeriv_zero]
         field_simp [hne]
         ring

lemma velocity_fourth_formula (t x : ℝ) :
    iteratedDeriv 4 (φ.velocity t) x = deriv Real.smoothTransition t *
      (iteratedDeriv 4 φ (φ.inverse t x) / φ.jacobian t (φ.inverse t x)^5 -
        10 * Real.smoothTransition t * iteratedDeriv 2 φ (φ.inverse t x) *
          iteratedDeriv 3 φ (φ.inverse t x) / φ.jacobian t (φ.inverse t x)^6 +
        15 * Real.smoothTransition t^2 * (iteratedDeriv 2 φ (φ.inverse t x))^3 /
          φ.jacobian t (φ.inverse t x)^7) := by
  have hfun : iteratedDeriv 3 (φ.velocity t) = fun z => deriv Real.smoothTransition t *
      (iteratedDeriv 3 φ (φ.inverse t z) / φ.jacobian t (φ.inverse t z)^4 -
        3 * Real.smoothTransition t * (iteratedDeriv 2 φ (φ.inverse t z))^2 /
          φ.jacobian t (φ.inverse t z)^5) := funext (φ.velocity_third_formula t)
  have hi := φ.inverse_space_derivative t x
  have h3 := (φ.jet_hasDerivAt 2 (φ.inverse t x)).comp x hi
  have h4 := (φ.jet_hasDerivAt 3 (φ.inverse t x)).comp x hi
  have hj := (φ.jacobian_space_derivative t (φ.inverse t x)).comp x hi
  have hne := ne_of_gt (φ.jacobian_pos t (φ.inverse t x))
  have hd := ((h4.div (hj.pow 4) (pow_ne_zero _ hne)).sub
    (((h3.pow 2).const_mul (3*Real.smoothTransition t)).div (hj.pow 5)
      (pow_ne_zero _ hne))).const_mul (deriv Real.smoothTransition t)
  simp only [Function.comp_def, Pi.div_apply, Pi.pow_apply, Pi.sub_apply] at hd
  rw [show (4:ℕ)=3+1 by rfl, iteratedDeriv_succ, hfun]
  calc _ = _ := hd.deriv
       _ = _ := by
         simp only [iteratedDeriv_succ, iteratedDeriv_zero]
         field_simp [hne]
         ring

lemma velocity_fourth_bound {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1/2)
    (h1 : ∀ x, |deriv φ x-1| ≤ ε)
    (hk : ∀ k ∈ Finset.Icc 2 4, ∀ x, |iteratedDeriv k φ x| ≤ ε)
    (t x : ℝ) :
    |iteratedDeriv 4 (φ.velocity t) x| ≤ 2592*|deriv Real.smoothTransition t| *ε := by
  have hJ := φ.jacobian_lower_near_identity hε1 h1 t (φ.inverse t x)
  have hJ0 := φ.jacobian_pos t (φ.inverse t x)
  have hb0 := Real.smoothTransition.nonneg t
  have hb1 := Real.smoothTransition.le_one t
  have h2 := hk 2 (by norm_num) (φ.inverse t x)
  have h3 := hk 3 (by norm_num) (φ.inverse t x)
  have h4 := hk 4 (by norm_num) (φ.inverse t x)
  rw [φ.velocity_fourth_formula, abs_mul]
  have hi : |iteratedDeriv 4 φ (φ.inverse t x) / φ.jacobian t (φ.inverse t x)^5 -
        10*Real.smoothTransition t*iteratedDeriv 2 φ (φ.inverse t x)*
          iteratedDeriv 3 φ (φ.inverse t x)/φ.jacobian t (φ.inverse t x)^6 +
        15*Real.smoothTransition t^2*(iteratedDeriv 2 φ (φ.inverse t x))^3 /
          φ.jacobian t (φ.inverse t x)^7| ≤ 2592*ε := by
    calc
      _ ≤ |iteratedDeriv 4 φ (φ.inverse t x) / φ.jacobian t (φ.inverse t x)^5| +
          |10*Real.smoothTransition t*iteratedDeriv 2 φ (φ.inverse t x)*
            iteratedDeriv 3 φ (φ.inverse t x)/φ.jacobian t (φ.inverse t x)^6| +
          |15*Real.smoothTransition t^2*(iteratedDeriv 2 φ (φ.inverse t x))^3 /
            φ.jacobian t (φ.inverse t x)^7| :=
        (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ = |iteratedDeriv 4 φ (φ.inverse t x)| / φ.jacobian t (φ.inverse t x)^5 +
          10*Real.smoothTransition t*|iteratedDeriv 2 φ (φ.inverse t x)| *
            |iteratedDeriv 3 φ (φ.inverse t x)|/φ.jacobian t (φ.inverse t x)^6 +
          15*Real.smoothTransition t^2*|iteratedDeriv 2 φ (φ.inverse t x)|^3 /
            φ.jacobian t (φ.inverse t x)^7 := by
        simp only [abs_div, abs_mul, abs_pow, abs_of_pos hJ0, abs_of_nonneg hb0]
        norm_num
      _ ≤ ε / (1/2:ℝ)^5 + 10*1*ε*ε/(1/2:ℝ)^6 +
          15*1^2*ε^3/(1/2:ℝ)^7 := by gcongr
      _ ≤ 2592*ε := by
        have he1 : ε ≤ 1 := by linarith
        have he2 : ε*ε ≤ ε := by nlinarith
        have he3 : ε^3 ≤ ε := by
          calc _ = ε*ε^2 := by ring
               _ ≤ ε*1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hε he1) hε
               _ = ε := mul_one _
        norm_num
        nlinarith
  exact (mul_le_mul_of_nonneg_left hi (abs_nonneg _)).trans_eq (by ring)

end StronglyRationalVOA.PositiveCircleGeometry.SmoothLift

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_SmoothTopology
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.PositiveCircleGeometry.SmoothLift

lemma continuous_identityError : Continuous identityError := by
  apply continuous_finsetSum
  intro k _
  exact ((ContinuousMap.continuous_restrict _).comp
    ((continuous_jet k).sub continuous_const)).norm

lemma periodic_iteratedDeriv {f : ℝ → ℝ} {T : ℝ} (hf : Function.Periodic f T) (k : ℕ) :
    Function.Periodic (iteratedDeriv k f) T := by
  induction k with
  | zero => simpa using hf
  | succ k ih => rw [iteratedDeriv_succ]; exact RealCircleCalculus.periodic_deriv ih

lemma jet_difference_periodic (φ ψ : SmoothLift) (k : ℕ) :
    Function.Periodic (fun x => jet φ k x-jet ψ k x) 1 := by
  have hp : Function.Periodic (fun x => φ x-ψ x) 1 := by
    intro x
    change φ (x+1)-ψ (x+1)=φ x-ψ x
    rw [φ.add_one,ψ.add_one]
    ring
  have he : (fun x => jet φ k x-jet ψ k x) = iteratedDeriv k (fun x => φ x-ψ x) := by
    funext x
    exact (iteratedDeriv_sub (φ.smooth.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt
      (ψ.smooth.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt).symm
  rw [he]
  exact periodic_iteratedDeriv hp k

lemma jet_sub_identity_le (φ : SmoothLift) {k : ℕ} (hk : k < 5) (x : ℝ) :
    |jet φ k x-jet identity k x| ≤ identityError φ := by
  apply periodic_bound_from_unitInterval (φ.jet_difference_periodic identity k) _ x
  intro y hy
  have h := ContinuousMap.norm_coe_le_norm
    ((jet φ k-jet identity k).restrict (Icc (0:ℝ) 1)) ⟨y,hy⟩
  apply h.trans
  exact Finset.single_le_sum (f := fun j => ‖(jet φ j-jet identity j).restrict (Icc (0:ℝ) 1)‖)
    (fun j _ => norm_nonneg _)
    (Finset.mem_range.mpr hk)

lemma identityError_controls_zero (φ : SmoothLift) (x : ℝ) : |φ x-x| ≤ identityError φ := by
  simpa [jet] using φ.jet_sub_identity_le (k := 0) (by norm_num) x
lemma identityError_controls_one (φ : SmoothLift) (x : ℝ) : |deriv φ x-1| ≤ identityError φ := by
  simpa [jet,identity] using φ.jet_sub_identity_le (k := 1) (by norm_num) x
lemma identityError_controls_higher (φ : SmoothLift) (k : ℕ) (hk : k ∈ Finset.Icc 2 4) (x : ℝ) :
    |iteratedDeriv k φ x| ≤ identityError φ := by
  have h2 := (Finset.mem_Icc.mp hk).1
  have h4 := (Finset.mem_Icc.mp hk).2
  simpa [jet,identity,iteratedDeriv_id,show k ≠ 0 by omega,show k ≠ 1 by omega]
    using φ.jet_sub_identity_le (k := k) (by omega) x
end StronglyRationalVOA.PositiveCircleGeometry.SmoothLift

namespace StronglyRationalVOA.SmoothCircleLift

lemma continuous_jet (k : ℕ) : Continuous (fun F : SmoothCircleLift => jet F k) :=
  (continuous_apply k).comp (show Continuous (fun F : SmoothCircleLift => jet F) from continuous_induced_dom)

end StronglyRationalVOA.SmoothCircleLift

end

end OAI
end


