-- Prove2me | Definitions.Def_OAIB3Kr007
-- name    : OAIB3Kr007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T17:00:15.997197+00:00
-- url     : https://prove2.me/theorems/b60080ff-2ff5-4939-b96f-ea9e495da135
-- title:
--   Definitions bundle OAIB3Kr007 of the split of OpenAI, The Kirchberg–Rørdam character criterion
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KirchbergRordam.character_criterion`, carved from OpenAI's openai/math development (OpenAI, *The Kirchberg–Rørdam character criterion*, OpenAI Math Release, September 25, 2026, result family 299, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 121 declarations of OpenAI's Lean: 31 definitions, 1 inductive type or structure, 21 instances and 68 theorems. The definitions and types are `OAI.KirchbergRordam.CStarInductiveLimit.lift`, `OAI.KirchbergRordam.CStarInductiveLimit.of`, `OAI.KirchbergRordam.CStarInductiveLimit.rawInclusion`, `OAI.KirchbergRordam.CStarInductiveLimit.rawLift`, `OAI.KirchbergRordam.GenericRW.AmplifiedComparison.pair`, `OAI.KirchbergRordam.GenericRW.MaxTensor.Algebra`, `OAI.KirchbergRordam.GenericRW.MaxTensor.CrossSeminorm`, `OAI.KirchbergRordam.GenericRW.MaxTensor.Raw`, `OAI.KirchbergRordam.GenericRW.MaxTensor.includeLeft`, `OAI.KirchbergRordam.GenericRW.MaxTensor.includeRight`, `OAI.KirchbergRordam.GenericRW.MaxTensor.leg`, `OAI.KirchbergRordam.GenericRW.MaxTensor.lift`, `OAI.KirchbergRordam.GenericRW.MaxTensor.liftRaw`, `OAI.KirchbergRordam.GenericRW.MaxTensor.of`, `OAI.KirchbergRordam.GenericRW.MaxTensor.powerPack`, `OAI.KirchbergRordam.GenericRW.MaxTensor.rawEquiv`, `OAI.KirchbergRordam.GenericRW.MaxTensor.rawRingSeminorm`, `OAI.KirchbergRordam.GenericRW.MaxTensor.representationSeminorm`, `OAI.KirchbergRordam.GenericRW.MaxTensor.seminorm`, `OAI.KirchbergRordam.M2`, `OAI.KirchbergRordam.M6`, `OAI.KirchbergRordam.MatrixTensor.fiberMap`, `OAI.KirchbergRordam.MaxTensor.Algebra`, `OAI.KirchbergRordam.MaxTensor.includeLeft`, `OAI.KirchbergRordam.MaxTensor.includeRight`, `OAI.KirchbergRordam.MaxTensor.lift`, `OAI.KirchbergRordam.MaxTensor.of`, `OAI.KirchbergRordam.MaxTensor.rawRingSeminorm`, `OAI.KirchbergRordam.MaxTensor.seminorm`, `OAI.KirchbergRordam.PrimeDimensionDrop.evaluation`, `OAI.KirchbergRordam.PrimeDimensionDrop.inclusion`, `OAI.KirchbergRordam.PrimeTensorSections.Square`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`CharacterCriterion_AmplifiedComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/AmplifiedComparison.lean), [`CharacterCriterion_BalancedLimit`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/BalancedLimit.lean), [`CharacterCriterion_FactorIndependence`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/FactorIndependence.lean), [`CharacterCriterion_InductiveLimit`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/InductiveLimit.lean), [`CharacterCriterion_MatrixPaths`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/MatrixPaths.lean), [`CharacterCriterion_MaxTensor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/MaxTensor.lean), [`CharacterCriterion_Pauli`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/Pauli.lean), [`CharacterCriterion_PrimeSpectrum`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/PrimeSpectrum.lean), [`CharacterCriterion_SeparableReduction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/SeparableReduction.lean), [`CharacterCriterion_TensorSections`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/TensorSections.lean).
--
--   **Imports.** It imports the published bundle `Def_CharacterCriterion`; the bundle `OAIB3Kr000` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIB3Kr010`, `OAIB3Kr011` and `OAIB3Kr012`; the statements `OAI.KirchbergRordam.GenericRW.FullSquareZero.exists_full_square_zero`, `OAI.KirchbergRordam.MatrixTensor.representation_bound`, `OAI_KirchbergRordam_PrimeSquareUnitary_exists_half_flip_control`, `OAI_KirchbergRordam_PrimeTensorSections_sectionMap_isometry` and `OAI.KirchbergRordam.spatial_absorption_of_central_maximal_half_flip`.
-- source:
--   OpenAI, The Kirchberg–Rørdam character criterion, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 299; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Kirchberg-Rordam-character-criterion-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_CharacterCriterion
import Definitions.Def_OAIB3Kr000

section
-- module Solutions.OAIB3_Krc.Compat
attribute [-instance] _root_.OAI.KirchbergRordam.NormUltrapower.quotientNormedRing _root_.OAI.KirchbergRordam.StarCompletion.completionNormedAlgebra _root_.OAI.KirchbergRordam.StarCompletion.completionStar _root_.OAI.KirchbergRordam.StarCompletion.completionStarRing
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib d13f23b's `CStarAlgebra.norm_le_norm_of_le_of_nonneg hab ha`; ours is `norm_le_norm_of_nonneg_of_le ha hab`. -/
theorem _root_.CStarAlgebra.norm_le_norm_of_le_of_nonneg {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {a b : A} (hab : a ≤ b) (ha : 0 ≤ a) : ‖a‖ ≤ ‖b‖ :=
  CStarAlgebra.norm_le_norm_of_nonneg_of_le ha hab
end OAICompat434

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_Pauli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


namespace KirchbergRordam.MatrixTensor
open scoped Matrix Kronecker
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]


lemma algebra_legs_commute (a : Matrix ι ι ℂ) (b : Matrix κ κ ℂ) :
    Commute (leftMatrixAlgebra (κ:=κ) a) (rightMatrixAlgebra (ι:=ι) b) := by
  change Matrix.kronecker a 1 * Matrix.kronecker 1 b = Matrix.kronecker 1 b * Matrix.kronecker a 1
  dsimp only [Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul]
  simp

lemma legs_commute (a : Mat ι) (b : Mat κ) :
    Commute (leftMatrix (κ:=κ) a) (rightMatrix (ι:=ι) b) :=
  (algebra_legs_commute (CStarMatrix.ofMatrix.symm a) (CStarMatrix.ofMatrix.symm b)).map
    CStarMatrix.ofMatrixStarAlgEquiv

end KirchbergRordam.MatrixTensor

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_MaxTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped TensorProduct

namespace KirchbergRordam.GenericRW
namespace StarCompletion

open UniformSpace
variable (R : Type*) [SeminormedRing R] [StarRing R] [NormedStarGroup R]

instance completionStar : Star (Completion R) := ⟨Completion.map (star : R → R)⟩

@[simp]
lemma star_coe (x : R) : star (x : Completion R) = (star x : R) :=
  Completion.map_coe star_isometry.uniformContinuous x

instance completionContinuousStar : ContinuousStar (Completion R) where
  continuous_star := Completion.continuous_map

instance completionStarRing : StarRing (Completion R) where
  star_involutive x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (continuous_star.comp continuous_star) continuous_id
    | ih x => simp only [star_coe, star_star]
  star_mul x y := by
    induction x, y using Completion.induction_on₂ with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x y => simp only [← Completion.coe_mul, star_coe, star_mul]
  star_add x y := by
    induction x, y using Completion.induction_on₂ with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x y => simp only [← Completion.coe_add, star_coe, star_add]

variable [NormedAlgebra ℂ R] [StarModule ℂ R]

instance completionNormedAlgebra : NormedAlgebra ℂ (Completion R) where
  norm_smul_le := norm_smul_le

instance completionStarModule : StarModule ℂ (Completion R) where
  star_smul z x := by
    induction x using Completion.induction_on with
    | hp =>
      exact isClosed_eq
        (continuous_star.comp (continuous_const_smul z))
        ((continuous_const_smul (star z)).comp continuous_star)
    | ih x =>
      rw [← Completion.coe_smul, star_coe, star_smul, Completion.coe_smul, star_coe]

end StarCompletion

namespace MaxTensor

variable (A B : Type*) [CStarAlgebra A] [CStarAlgebra B]


structure CrossSeminorm extends Seminorm ℂ (A ⊗[ℂ] B) where
  mul_le : ∀ x y, toSeminorm (x * y) ≤ toSeminorm x * toSeminorm y
  star_eq : ∀ x, toSeminorm (star x) = toSeminorm x
  cstar_eq : ∀ x, toSeminorm (star x * x) = toSeminorm x * toSeminorm x
  tmul_le : ∀ a b, toSeminorm (a ⊗ₜ[ℂ] b) ≤ ‖a‖ * ‖b‖

instance instInhabitedCrossSeminorm : Inhabited (CrossSeminorm A B) := ⟨{
  toSeminorm := 0
  mul_le := by simp
  star_eq := by simp
  cstar_eq := by simp
  tmul_le := by intro a b; simp only [zero_apply]; positivity }⟩

variable {A B}

lemma bounded_at (x : A ⊗[ℂ] B) :
    ∃ C : ℝ, ∀ p : CrossSeminorm A B, p.toSeminorm x ≤ C := by
  induction x using OAI.tensorInductionOn with
  | tmul a b => exact ⟨‖a‖ * ‖b‖, fun p => p.tmul_le a b⟩
  | add x y hx hy =>
      obtain ⟨C, hC⟩ := hx
      obtain ⟨D, hD⟩ := hy
      exact ⟨C + D, fun p => (map_add_le_add p.toSeminorm x y).trans
        (add_le_add (hC p) (hD p))⟩

lemma bounded : BddAbove (Set.range (CrossSeminorm.toSeminorm (A := A) (B := B))) := by
  rw [Seminorm.bddAbove_range_iff]
  intro x
  obtain ⟨C, hC⟩ := bounded_at x
  exact ⟨C, by rintro _ ⟨p, rfl⟩; exact hC p⟩


def seminorm : Seminorm ℂ (A ⊗[ℂ] B) := ⨆ p : CrossSeminorm A B, p.toSeminorm

lemma seminorm_apply (x : A ⊗[ℂ] B) :
    seminorm x = ⨆ p : CrossSeminorm A B, p.toSeminorm x :=
  Seminorm.iSup_apply bounded

lemma le_seminorm (p : CrossSeminorm A B) (x : A ⊗[ℂ] B) :
    p.toSeminorm x ≤ seminorm x := by
  rw [seminorm_apply]
  exact le_ciSup (by obtain ⟨C, hC⟩ := bounded_at x; exact ⟨C, by
    rintro _ ⟨p, rfl⟩; exact hC p⟩) p

lemma seminorm_le {x : A ⊗[ℂ] B} {C : ℝ}
    (h : ∀ p : CrossSeminorm A B, p.toSeminorm x ≤ C) : seminorm x ≤ C := by
  rw [seminorm_apply]
  exact ciSup_le h

lemma seminorm_mul_le (x y : A ⊗[ℂ] B) :
    seminorm (x * y) ≤ seminorm x * seminorm y := by
  apply seminorm_le
  intro p
  exact (p.mul_le x y).trans (mul_le_mul (le_seminorm p x) (le_seminorm p y)
    (apply_nonneg p.toSeminorm y) (apply_nonneg seminorm x))

lemma seminorm_star (x : A ⊗[ℂ] B) : seminorm (star x) = seminorm x := by
  rw [seminorm_apply, seminorm_apply]
  congr 1
  funext p
  exact p.star_eq x

lemma seminorm_cstar (x : A ⊗[ℂ] B) :
    seminorm (star x * x) = seminorm x * seminorm x := by
  apply le_antisymm
  · simpa only [seminorm_star] using seminorm_mul_le (star x) x
  · have h : seminorm x ≤ Real.sqrt (seminorm (star x * x)) := by
      apply seminorm_le
      intro p
      apply (Real.le_sqrt (apply_nonneg p.toSeminorm x) (apply_nonneg seminorm _)).mpr
      simpa only [← p.cstar_eq x, pow_two] using le_seminorm p (star x * x)
    have := mul_self_le_mul_self (apply_nonneg seminorm x) h
    rwa [Real.mul_self_sqrt (apply_nonneg seminorm _)] at this


def Raw (A B : Type*) [CStarAlgebra A] [CStarAlgebra B] := A ⊗[ℂ] B

instance instRingRaw : Ring (Raw A B) := inferInstanceAs (Ring (A ⊗[ℂ] B))
instance instAlgebraComplexRaw : Algebra ℂ (Raw A B) := inferInstanceAs (Algebra ℂ (A ⊗[ℂ] B))
instance instStarRingRaw : StarRing (Raw A B) := inferInstanceAs (StarRing (A ⊗[ℂ] B))
instance instStarModuleComplexRaw : StarModule ℂ (Raw A B) := inferInstanceAs (StarModule ℂ (A ⊗[ℂ] B))

def rawEquiv : (A ⊗[ℂ] B) ≃⋆ₐ[ℂ] Raw A B :=
  StarAlgEquiv.refl ℂ (A ⊗[ℂ] B)

def rawRingSeminorm : RingSeminorm (Raw A B) where
  __ := (seminorm (A := A) (B := B)).toAddGroupSeminorm
  mul_le' := seminorm_mul_le

instance instSeminormedRingRaw : SeminormedRing (Raw A B) := rawRingSeminorm.toSeminormedRing

instance instNormedAlgebraComplexRaw : NormedAlgebra ℂ (Raw A B) where
  norm_smul_le z x := (map_smul_eq_mul seminorm z x).le

instance instNormedStarGroupRaw : NormedStarGroup (Raw A B) where
  norm_star_le x := (seminorm_star x).le

@[simp]
lemma norm_raw (x : Raw A B) : ‖x‖ = seminorm x := rfl


abbrev Algebra (A B : Type*) [CStarAlgebra A] [CStarAlgebra B] :=
  UniformSpace.Completion (Raw A B)

instance instCStarRingAlgebra : CStarRing (Algebra A B) where
  norm_mul_self_le x := by
    induction x using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x =>
      simp only [StarCompletion.star_coe, ← UniformSpace.Completion.coe_mul,
        UniformSpace.Completion.norm_coe, norm_raw]
      exact (seminorm_cstar x).ge

instance instCStarAlgebraAlgebra : CStarAlgebra (Algebra A B) where


def of : Raw A B →⋆ₐ[ℂ] Algebra A B where
  __ := UniformSpace.Completion.coeRingHom
  commutes' _ := rfl
  map_star' x := (StarCompletion.star_coe _ x).symm

@[simp]
lemma norm_of (x : Raw A B) : ‖of x‖ = seminorm x :=
  UniformSpace.Completion.norm_coe x


def includeLeft : A →⋆ₐ[ℂ] Algebra A B := of.comp (rawEquiv.toStarAlgHom.comp {
  toAlgHom := _root_.Algebra.TensorProduct.includeLeft
  map_star' a := by simp })

def includeRight : B →⋆ₐ[ℂ] Algebra A B := of.comp (rawEquiv.toStarAlgHom.comp {
  toAlgHom := _root_.Algebra.TensorProduct.includeRight
  map_star' b := by simp })

variable {C : Type*} [CStarAlgebra C]


def liftRaw (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) : Raw A B →⋆ₐ[ℂ] C where
  toAlgHom := _root_.Algebra.TensorProduct.lift φ.toAlgHom ψ.toAlgHom h
  map_star' x := by
    change _root_.Algebra.TensorProduct.lift φ.toAlgHom ψ.toAlgHom h (star x) =
      star (_root_.Algebra.TensorProduct.lift φ.toAlgHom ψ.toAlgHom h x)
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simpa only [star_add, map_add] using congrArg₂ (· + ·) hx hy
    | tmul a b =>
      change φ (star a) * ψ (star b) = star (φ a * ψ b)
      rw [star_mul, ← map_star, ← map_star]
      exact h (star a) (star b)

@[simp]
lemma liftRaw_tmul (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) (a : A) (b : B) :
    liftRaw φ ψ h (a ⊗ₜ[ℂ] b) = φ a * ψ b := rfl


def representationSeminorm (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) : CrossSeminorm A B where
  toSeminorm := (normSeminorm ℂ C).comp (liftRaw φ ψ h).toLinearMap
  mul_le x y := by
    change ‖liftRaw φ ψ h (rawEquiv x * rawEquiv y)‖ ≤
      ‖liftRaw φ ψ h (rawEquiv x)‖ * ‖liftRaw φ ψ h (rawEquiv y)‖
    rw [map_mul]
    exact norm_mul_le _ _
  star_eq x := by
    change ‖liftRaw φ ψ h (star (rawEquiv x))‖ = ‖liftRaw φ ψ h (rawEquiv x)‖
    rw [map_star, norm_star]
  cstar_eq x := by
    change ‖liftRaw φ ψ h (star (rawEquiv x) * rawEquiv x)‖ =
      ‖liftRaw φ ψ h (rawEquiv x)‖ * ‖liftRaw φ ψ h (rawEquiv x)‖
    rw [map_mul, map_star, CStarRing.norm_star_mul_self]
  tmul_le a b := by
    change ‖liftRaw φ ψ h (a ⊗ₜ[ℂ] b)‖ ≤ ‖a‖ * ‖b‖
    rw [liftRaw_tmul]
    exact (norm_mul_le _ _).trans (mul_le_mul
      (NonUnitalStarAlgHom.norm_apply_le φ a) (NonUnitalStarAlgHom.norm_apply_le ψ b)
      (norm_nonneg _) (norm_nonneg _))

lemma norm_liftRaw_le (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) (x : Raw A B) :
    ‖liftRaw φ ψ h x‖ ≤ ‖x‖ :=
  le_seminorm (representationSeminorm φ ψ h) x

lemma continuous_liftRaw (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) : Continuous (liftRaw φ ψ h) := by
  exact ((liftRaw φ ψ h).toLinearMap.mkContinuous 1
    (fun x => by change ‖liftRaw φ ψ h x‖ ≤ 1 * ‖x‖
                 simpa only [one_mul] using norm_liftRaw_le φ ψ h x)).continuous


def lift (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) : Algebra A B →⋆ₐ[ℂ] C where
  __ := UniformSpace.Completion.extensionHom (liftRaw φ ψ h).toRingHom
    (continuous_liftRaw φ ψ h)
  commutes' z := by
    change UniformSpace.Completion.extensionHom (liftRaw φ ψ h).toRingHom
      (continuous_liftRaw φ ψ h) (algebraMap ℂ (Raw A B) z) = algebraMap ℂ C z
    rw [UniformSpace.Completion.extensionHom_coe]
    exact (liftRaw φ ψ h).commutes z
  map_star' x := by
    induction x using UniformSpace.Completion.induction_on with
    | hp =>
      exact isClosed_eq
        (UniformSpace.Completion.continuous_extension.comp continuous_star)
        (continuous_star.comp UniformSpace.Completion.continuous_extension)
    | ih x =>
      change UniformSpace.Completion.extensionHom (liftRaw φ ψ h).toRingHom
        (continuous_liftRaw φ ψ h) (star (x : Algebra A B)) =
        star (UniformSpace.Completion.extensionHom (liftRaw φ ψ h).toRingHom
          (continuous_liftRaw φ ψ h) (x : Algebra A B))
      simp only [StarCompletion.star_coe, UniformSpace.Completion.extensionHom_coe]
      exact map_star (liftRaw φ ψ h) x

@[simp]
lemma lift_of (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) (x : Raw A B) :
    lift φ ψ h (of x) = liftRaw φ ψ h x :=
  UniformSpace.Completion.extensionHom_coe (liftRaw φ ψ h).toRingHom
    (continuous_liftRaw φ ψ h) x

@[simp]
lemma lift_of_tmul (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) (a : A) (b : B) :
    lift φ ψ h (of (a ⊗ₜ[ℂ] b)) = φ a * ψ b :=
  (lift_of φ ψ h (rawEquiv (a ⊗ₜ[ℂ] b))).trans (liftRaw_tmul φ ψ h a b)


open scoped CStarAlgebra

@[simp]
lemma of_tmul (a : A) (b : B) :
    of (a ⊗ₜ[ℂ] b) = includeLeft (B := B) a * includeRight (A := A) b := by
  change of (rawEquiv (a ⊗ₜ[ℂ] b)) =
    of (rawEquiv (a ⊗ₜ[ℂ] (1 : B))) * of (rawEquiv ((1 : A) ⊗ₜ[ℂ] b))
  rw [← map_mul, ← map_mul]
  congr 2
  simp only [_root_.Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]


@[ext]
theorem hom_ext {f g : Algebra A B →⋆ₐ[ℂ] C}
    (hL : f.comp includeLeft = g.comp includeLeft)
    (hR : f.comp includeRight = g.comp includeRight) : f = g := by
  apply DFunLike.ext
  intro x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (map_continuous f) (map_continuous g)
  | ih x =>
    suffices ∀ tensor : A ⊗[ℂ] B, f (of (rawEquiv tensor)) = g (of (rawEquiv tensor))
      from this x
    intro tensor
    induction tensor using OAI.tensorInductionOn with
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul a b =>
      change f (of (a ⊗ₜ[ℂ] b)) = g (of (a ⊗ₜ[ℂ] b))
      rw [of_tmul, map_mul, map_mul]
      exact congrArg₂ (· * ·) (DFunLike.congr_fun hL a) (DFunLike.congr_fun hR b)

@[simp]
lemma lift_includeLeft (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) : (lift φ ψ h).comp includeLeft = φ := by
  ext a
  change lift φ ψ h (of (a ⊗ₜ[ℂ] (1 : B))) = φ a
  rw [lift_of_tmul, map_one, mul_one]

@[simp]
lemma lift_includeRight (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) : (lift φ ψ h).comp includeRight = ψ := by
  ext b
  change lift φ ψ h (of ((1 : A) ⊗ₜ[ℂ] b)) = ψ b
  rw [lift_of_tmul, map_one, one_mul]


universe u


attribute [instance] CStarPack.inst


def powerPack (D : Type u) [CStarAlgebra D] : ℕ → CStarPack.{u}
  | 0 => ⟨D, inferInstance⟩
  | n + 1 => ⟨Algebra D (powerPack D n), inferInstance⟩


end MaxTensor
end KirchbergRordam.GenericRW
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_FactorIndependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct


open scoped InnerProductSpace

namespace KirchbergRordam.GenericRW.MaxTensor
section
universe u
variable (D : Type u) [CStarAlgebra D]


def leg : (n : ℕ) → Fin (n + 1) → D →⋆ₐ[ℂ] (powerPack D n)
  | 0 => fun _ => StarAlgHom.id ℂ D
  | n + 1 => Fin.cases includeLeft (fun j => includeRight.comp (leg n j))

@[simp] lemma leg_zero (i : Fin 1) (a : D) : leg D 0 i a = a := rfl
@[simp] lemma leg_succ_zero (n : ℕ) : leg D (n+1) 0 = includeLeft := rfl
@[simp] lemma leg_succ_succ (n : ℕ) (i : Fin (n+1)) :
    leg D (n+1) i.succ = (includeRight (A := D)).comp (leg D n i) := rfl

end

end KirchbergRordam.GenericRW.MaxTensor

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_AmplifiedComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.GenericRW.AmplifiedComparison
open scoped CStarAlgebra
open scoped BigOperators
variable {P R B : Type*} [CStarAlgebra P] [CStarAlgebra R] [CStarAlgebra B]
variable {J I : Type*} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
variable (φ : P →⋆ₐ[ℂ] B) (ψ : R →⋆ₐ[ℂ] B)
variable (hc : ∀ a b, Commute (φ a) (ψ b))

def pair (a : P) (b : R) : B := φ a*ψ b
end KirchbergRordam.GenericRW.AmplifiedComparison
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_SeparableReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology


namespace KirchbergRordam.PrimeDimensionDrop
open MatrixTensor
open scoped Matrix Kronecker ComplexOrder CStarAlgebra


@[simp] lemma eval_apply (p q : ℕ) (t : unitInterval) (f : C(unitInterval, Fiber p q)) :
    eval p q t f = f t := rfl


def inclusion (p q : ℕ) : Algebra p q →⋆ₐ[ℂ] C(unitInterval, Fiber p q) :=
  (subalgebra p q).subtype

def evaluation (p q : ℕ) (t : unitInterval) : Algebra p q →⋆ₐ[ℂ] Fiber p q :=
  (eval p q t).comp (inclusion p q)

@[simp] lemma evaluation_apply (p q : ℕ) (t : unitInterval) (f : Algebra p q) :
    evaluation p q t f = f.val t := rfl

end KirchbergRordam.PrimeDimensionDrop

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_InductiveLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology


open scoped TensorProduct CStarAlgebra

namespace KirchbergRordam
namespace StarCompletion

open UniformSpace
variable (R : Type*) [SeminormedRing R] [StarRing R] [NormedStarGroup R]


@[simp]
lemma star_coe (x : R) : star (x : Completion R) = (star x : R) :=
  Completion.map_coe star_isometry.uniformContinuous x


end StarCompletion

end KirchbergRordam


namespace KirchbergRordam.CStarInductiveLimit
section
universe u


attribute [instance] System.cstar


@[simp] lemma rawOf_map (S : System) (i j : ℕ) (h : i ≤ j) (x : S.obj i) :
    rawOf S j (S.map i j h x) = rawOf S i x := DirectLimit.mk_apply _ _ _ _


@[simp] lemma normLift_mk (S : System) (n : ℕ) (x : S.obj n) :
    normLift S (rawOf S n x) = ‖x‖ := rfl


@[simp] theorem norm_rawOf (S : System) (n : ℕ) (x : S.obj n) :
    ‖rawOf S n x‖ = ‖x‖ := rfl


def rawInclusion (S : System) : Raw S →⋆ₐ[ℂ] Algebra S where
  __ := UniformSpace.Completion.coeRingHom
  commutes' _ := rfl
  map_star' _ := (StarCompletion.star_coe _ _).symm

def of (S : System) (n : ℕ) : S.obj n →⋆ₐ[ℂ] Algebra S :=
  (rawInclusion S).comp (rawOf S n)

@[simp] theorem of_map (S : System) (i j : ℕ) (h : i ≤ j) (x : S.obj i) :
    of S j (S.map i j h x) = of S i x := by
  change rawInclusion S (rawOf S j (S.map i j h x)) = _
  rw [rawOf_map]
  rfl

@[simp] theorem norm_of (S : System) (n : ℕ) (x : S.obj n) : ‖of S n x‖ = ‖x‖ :=
  (UniformSpace.Completion.norm_coe _).trans (norm_rawOf S n x)


variable {C : Type*} [CStarAlgebra C]

def rawLift (S : System) (f : ∀ n, S.obj n →⋆ₐ[ℂ] C)
    (hf : ∀ i j (h : i ≤ j) x, f j (S.map i j h x) = f i x) :
    Raw S →⋆ₐ[ℂ] C where
  __ := DirectLimit.Algebra.lift S.obj S.map C (fun n => (f n).toAlgHom) hf
  map_star' x := by
    refine DirectLimit.induction S.map ?_ x
    intro n x
    exact map_star (f n) x

@[simp] theorem rawLift_of (S : System) (f : ∀ n, S.obj n →⋆ₐ[ℂ] C)
    (hf : ∀ i j (h : i ≤ j) x, f j (S.map i j h x) = f i x)
    (n : ℕ) (x : S.obj n) : rawLift S f hf (rawOf S n x) = f n x := rfl

theorem norm_rawLift_le (S : System) (f : ∀ n, S.obj n →⋆ₐ[ℂ] C)
    (hf : ∀ i j (h : i ≤ j) x, f j (S.map i j h x) = f i x)
    (x : Raw S) : ‖rawLift S f hf x‖ ≤ ‖x‖ := by
  refine DirectLimit.induction S.map ?_ x
  intro n x
  exact NonUnitalStarAlgHom.norm_apply_le (f n) x

theorem continuous_rawLift (S : System) (f : ∀ n, S.obj n →⋆ₐ[ℂ] C)
    (hf : ∀ i j (h : i ≤ j) x, f j (S.map i j h x) = f i x) :
    Continuous (rawLift S f hf) := by
  exact ((rawLift S f hf).toLinearMap.mkContinuous 1
    (fun x => by
      change ‖rawLift S f hf x‖ ≤ 1 * ‖x‖
      simpa only [one_mul] using norm_rawLift_le S f hf x)).continuous


def lift (S : System) (f : ∀ n, S.obj n →⋆ₐ[ℂ] C)
    (hf : ∀ i j (h : i ≤ j) x, f j (S.map i j h x) = f i x) :
    Algebra S →⋆ₐ[ℂ] C where
  __ := UniformSpace.Completion.extensionHom (rawLift S f hf).toRingHom
    (continuous_rawLift S f hf)
  commutes' z := by
    change UniformSpace.Completion.extensionHom (rawLift S f hf).toRingHom
      (continuous_rawLift S f hf) (algebraMap ℂ (Raw S) z) = algebraMap ℂ C z
    rw [UniformSpace.Completion.extensionHom_coe]
    exact (rawLift S f hf).commutes z
  map_star' x := by
    induction x using UniformSpace.Completion.induction_on with
    | hp =>
      exact isClosed_eq
        (UniformSpace.Completion.continuous_extension.comp continuous_star)
        (continuous_star.comp UniformSpace.Completion.continuous_extension)
    | ih x =>
      change UniformSpace.Completion.extensionHom (rawLift S f hf).toRingHom
        (continuous_rawLift S f hf) (star (x : Algebra S)) =
        star (UniformSpace.Completion.extensionHom (rawLift S f hf).toRingHom
          (continuous_rawLift S f hf) (x : Algebra S))
      simp only [StarCompletion.star_coe, UniformSpace.Completion.extensionHom_coe]
      exact map_star (rawLift S f hf) x

@[simp] theorem lift_rawInclusion (S : System) (f : ∀ n, S.obj n →⋆ₐ[ℂ] C)
    (hf : ∀ i j (h : i ≤ j) x, f j (S.map i j h x) = f i x) (x : Raw S) :
    lift S f hf (rawInclusion S x) = rawLift S f hf x :=
  UniformSpace.Completion.extensionHom_coe (rawLift S f hf).toRingHom
    (continuous_rawLift S f hf) x

@[simp] theorem lift_of (S : System) (f : ∀ n, S.obj n →⋆ₐ[ℂ] C)
    (hf : ∀ i j (h : i ≤ j) x, f j (S.map i j h x) = f i x)
    (n : ℕ) (x : S.obj n) : lift S f hf (of S n x) = f n x := by
  change lift S f hf (rawInclusion S (rawOf S n x)) = _
  rw [lift_rawInclusion, rawLift_of]


end

universe u


attribute [instance] Chain.cstar


end KirchbergRordam.CStarInductiveLimit


end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_MatrixPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra


open scoped CStarAlgebra ComplexOrder

namespace KirchbergRordam.MatrixDiagonalPath
open scoped ComplexOrder CStarAlgebra Matrix
variable {ι κ ν : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [instDecidableEqκ : DecidableEq κ] [Fintype ν] [DecidableEq ν]


@[simp] lemma block_apply (a : ι → Mat κ) (i j : κ) (k l : ι) :
    block a (i,k) (j,l) = if k=l then a k i j else 0 := rfl

end KirchbergRordam.MatrixDiagonalPath


namespace KirchbergRordam.MatrixBlockReindex
open MatrixTensor (leftMatrix rightMatrix)
open MatrixDiagonalPath
open scoped ComplexOrder CStarAlgebra Matrix Kronecker
variable {P Q L R S T : Type*}
  [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instFintypeL : Fintype L] [instFintypeR : Fintype R] [instFintypeS : Fintype S] [instFintypeT : Fintype T]
  [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [instDecidableEqL : DecidableEq L] [instDecidableEqR : DecidableEq R]
  [instDecidableEqS : DecidableEq S] [instDecidableEqT : DecidableEq T]


@[simp] lemma sumBlock_ll (a : Mat P) (b : Mat Q) (i j : P) :
    sumBlock (a,b) (Sum.inl i) (Sum.inl j) = a i j := rfl
@[simp] lemma sumBlock_lr (a : Mat P) (b : Mat Q) (i : P) (j : Q) :
    sumBlock (a,b) (Sum.inl i) (Sum.inr j) = 0 := rfl
@[simp] lemma sumBlock_rl (a : Mat P) (b : Mat Q) (i : Q) (j : P) :
    sumBlock (a,b) (Sum.inr i) (Sum.inl j) = 0 := rfl
@[simp] lemma sumBlock_rr (a : Mat P) (b : Mat Q) (i j : Q) :
    sumBlock (a,b) (Sum.inr i) (Sum.inr j) = b i j := rfl

@[simp] lemma left_apply (a : Mat P) (i j : P) (k l : Q) :
    leftMatrix a (i,k) (j,l) = a i j * if k=l then 1 else 0 := by
  change (Matrix.kronecker (CStarMatrix.ofMatrix.symm a) (1 : Matrix Q Q ℂ)) (i,k) (j,l)=_
  simp [Matrix.one_apply]
@[simp] lemma right_apply (a : Mat Q) (i j : P) (k l : Q) :
    rightMatrix a (i,k) (j,l) = (if i=j then 1 else 0) * a k l := by
  change (Matrix.kronecker (1 : Matrix P P ℂ) (CStarMatrix.ofMatrix.symm a)) (i,k) (j,l)=_
  simp [Matrix.one_apply]


end KirchbergRordam.MatrixBlockReindex
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_BalancedLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder


namespace KirchbergRordam

open scoped Matrix Kronecker ComplexOrder

abbrev M2 := CStarMatrix (Fin 2) (Fin 2) ℂ
abbrev M6 := CStarMatrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ


end KirchbergRordam


end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_PrimeSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace

namespace KirchbergRordam
namespace MaxTensor

variable (A B : Type*) [CStarAlgebra A] [CStarAlgebra B]


variable {A B}

lemma bounded_at (x : A ⊗[ℂ] B) :
    ∃ C : ℝ, ∀ p : CrossSeminorm A B, p.toSeminorm x ≤ C := by
  induction x using OAI.tensorInductionOn with
  | tmul a b => exact ⟨‖a‖ * ‖b‖, fun p => p.tmul_le a b⟩
  | add x y hx hy =>
      obtain ⟨C, hC⟩ := hx
      obtain ⟨D, hD⟩ := hy
      exact ⟨C + D, fun p => (map_add_le_add p.toSeminorm x y).trans
        (add_le_add (hC p) (hD p))⟩

lemma bounded : BddAbove (Set.range (CrossSeminorm.toSeminorm (A := A) (B := B))) := by
  rw [Seminorm.bddAbove_range_iff]
  intro x
  obtain ⟨C, hC⟩ := bounded_at x
  exact ⟨C, by rintro _ ⟨p, rfl⟩; exact hC p⟩


def seminorm : Seminorm ℂ (A ⊗[ℂ] B) := ⨆ p : CrossSeminorm A B, p.toSeminorm

lemma seminorm_apply (x : A ⊗[ℂ] B) :
    seminorm x = ⨆ p : CrossSeminorm A B, p.toSeminorm x :=
  Seminorm.iSup_apply bounded

lemma le_seminorm (p : CrossSeminorm A B) (x : A ⊗[ℂ] B) :
    p.toSeminorm x ≤ seminorm x := by
  rw [seminorm_apply]
  exact le_ciSup (by obtain ⟨C, hC⟩ := bounded_at x; exact ⟨C, by
    rintro _ ⟨p, rfl⟩; exact hC p⟩) p

lemma seminorm_le {x : A ⊗[ℂ] B} {C : ℝ}
    (h : ∀ p : CrossSeminorm A B, p.toSeminorm x ≤ C) : seminorm x ≤ C := by
  rw [seminorm_apply]
  exact ciSup_le h

lemma seminorm_mul_le (x y : A ⊗[ℂ] B) :
    seminorm (x * y) ≤ seminorm x * seminorm y := by
  apply seminorm_le
  intro p
  exact (p.mul_le x y).trans (mul_le_mul (le_seminorm p x) (le_seminorm p y)
    (apply_nonneg p.toSeminorm y) (apply_nonneg seminorm x))

lemma seminorm_star (x : A ⊗[ℂ] B) : seminorm (star x) = seminorm x := by
  rw [seminorm_apply, seminorm_apply]
  congr 1
  funext p
  exact p.star_eq x

lemma seminorm_cstar (x : A ⊗[ℂ] B) :
    seminorm (star x * x) = seminorm x * seminorm x := by
  apply le_antisymm
  · simpa only [seminorm_star] using seminorm_mul_le (star x) x
  · have h : seminorm x ≤ Real.sqrt (seminorm (star x * x)) := by
      apply seminorm_le
      intro p
      apply (Real.le_sqrt (apply_nonneg p.toSeminorm x) (apply_nonneg seminorm _)).mpr
      simpa only [← p.cstar_eq x, pow_two] using le_seminorm p (star x * x)
    have := mul_self_le_mul_self (apply_nonneg seminorm x) h
    rwa [Real.mul_self_sqrt (apply_nonneg seminorm _)] at this


instance instStarModuleComplexRaw : StarModule ℂ (Raw A B) := inferInstanceAs (StarModule ℂ (A ⊗[ℂ] B))


def rawRingSeminorm : RingSeminorm (Raw A B) where
  __ := (seminorm (A := A) (B := B)).toAddGroupSeminorm
  mul_le' := seminorm_mul_le

instance instSeminormedRingRaw : SeminormedRing (Raw A B) := rawRingSeminorm.toSeminormedRing

instance instNormedAlgebraComplexRaw : NormedAlgebra ℂ (Raw A B) where
  norm_smul_le z x := (map_smul_eq_mul seminorm z x).le

instance instNormedStarGroupRaw : NormedStarGroup (Raw A B) where
  norm_star_le x := (seminorm_star x).le

@[simp]
lemma norm_raw (x : Raw A B) : ‖x‖ = seminorm x := rfl


abbrev Algebra (A B : Type*) [CStarAlgebra A] [CStarAlgebra B] :=
  UniformSpace.Completion (Raw A B)

instance instCStarRingAlgebra : CStarRing (Algebra A B) where
  norm_mul_self_le x := by
    induction x using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x =>
      simp only [StarCompletion.star_coe, ← UniformSpace.Completion.coe_mul,
        UniformSpace.Completion.norm_coe, norm_raw]
      exact (seminorm_cstar x).ge

instance instCStarAlgebraAlgebra : CStarAlgebra (Algebra A B) where


def of : Raw A B →⋆ₐ[ℂ] Algebra A B where
  __ := UniformSpace.Completion.coeRingHom
  commutes' _ := rfl
  map_star' x := (StarCompletion.star_coe _ x).symm

@[simp]
lemma norm_of (x : Raw A B) : ‖of x‖ = seminorm x :=
  UniformSpace.Completion.norm_coe x


def includeLeft : A →⋆ₐ[ℂ] Algebra A B := of.comp (rawEquiv.toStarAlgHom.comp {
  toAlgHom := _root_.Algebra.TensorProduct.includeLeft
  map_star' a := by simp })

def includeRight : B →⋆ₐ[ℂ] Algebra A B := of.comp (rawEquiv.toStarAlgHom.comp {
  toAlgHom := _root_.Algebra.TensorProduct.includeRight
  map_star' b := by simp })

lemma legs_commute (a : A) (b : B) :
    Commute (includeLeft (B := B) a) (includeRight (A := A) b) := by
  change of (rawEquiv (a ⊗ₜ[ℂ] (1 : B))) * of (rawEquiv ((1 : A) ⊗ₜ[ℂ] b)) =
    of (rawEquiv ((1 : A) ⊗ₜ[ℂ] b)) * of (rawEquiv (a ⊗ₜ[ℂ] (1 : B)))
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
  congr 2
  simp only [_root_.Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

variable {C : Type*} [CStarAlgebra C]


@[simp]
lemma liftRaw_tmul (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) (a : A) (b : B) :
    liftRaw φ ψ h (a ⊗ₜ[ℂ] b) = φ a * ψ b := rfl


lemma norm_liftRaw_le (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) (x : Raw A B) :
    ‖liftRaw φ ψ h x‖ ≤ ‖x‖ :=
  le_seminorm (representationSeminorm φ ψ h) x

lemma continuous_liftRaw (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) : Continuous (liftRaw φ ψ h) := by
  exact ((liftRaw φ ψ h).toLinearMap.mkContinuous 1
    (fun x => by change ‖liftRaw φ ψ h x‖ ≤ 1 * ‖x‖
                 simpa only [one_mul] using norm_liftRaw_le φ ψ h x)).continuous


def lift (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) : Algebra A B →⋆ₐ[ℂ] C where
  __ := UniformSpace.Completion.extensionHom (liftRaw φ ψ h).toRingHom
    (continuous_liftRaw φ ψ h)
  commutes' z := by
    change UniformSpace.Completion.extensionHom (liftRaw φ ψ h).toRingHom
      (continuous_liftRaw φ ψ h) (algebraMap ℂ (Raw A B) z) = algebraMap ℂ C z
    rw [UniformSpace.Completion.extensionHom_coe]
    exact (liftRaw φ ψ h).commutes z
  map_star' x := by
    induction x using UniformSpace.Completion.induction_on with
    | hp =>
      exact isClosed_eq
        (UniformSpace.Completion.continuous_extension.comp continuous_star)
        (continuous_star.comp UniformSpace.Completion.continuous_extension)
    | ih x =>
      change UniformSpace.Completion.extensionHom (liftRaw φ ψ h).toRingHom
        (continuous_liftRaw φ ψ h) (star (x : Algebra A B)) =
        star (UniformSpace.Completion.extensionHom (liftRaw φ ψ h).toRingHom
          (continuous_liftRaw φ ψ h) (x : Algebra A B))
      simp only [StarCompletion.star_coe, UniformSpace.Completion.extensionHom_coe]
      exact map_star (liftRaw φ ψ h) x

@[simp]
lemma lift_of (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) (x : Raw A B) :
    lift φ ψ h (of x) = liftRaw φ ψ h x :=
  UniformSpace.Completion.extensionHom_coe (liftRaw φ ψ h).toRingHom
    (continuous_liftRaw φ ψ h) x

@[simp]
lemma lift_of_tmul (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) (a : A) (b : B) :
    lift φ ψ h (of (a ⊗ₜ[ℂ] b)) = φ a * ψ b :=
  (lift_of φ ψ h (rawEquiv (a ⊗ₜ[ℂ] b))).trans (liftRaw_tmul φ ψ h a b)


open scoped CStarAlgebra

@[simp]
lemma of_tmul (a : A) (b : B) :
    of (a ⊗ₜ[ℂ] b) = includeLeft (B := B) a * includeRight (A := A) b := by
  change of (rawEquiv (a ⊗ₜ[ℂ] b)) =
    of (rawEquiv (a ⊗ₜ[ℂ] (1 : B))) * of (rawEquiv ((1 : A) ⊗ₜ[ℂ] b))
  rw [← map_mul, ← map_mul]
  congr 2
  simp only [_root_.Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]


@[ext]
theorem hom_ext {f g : Algebra A B →⋆ₐ[ℂ] C}
    (hL : f.comp includeLeft = g.comp includeLeft)
    (hR : f.comp includeRight = g.comp includeRight) : f = g := by
  apply DFunLike.ext
  intro x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (map_continuous f) (map_continuous g)
  | ih x =>
    suffices ∀ tensor : A ⊗[ℂ] B, f (of (rawEquiv tensor)) = g (of (rawEquiv tensor))
      from this x
    intro tensor
    induction tensor using OAI.tensorInductionOn with
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul a b =>
      change f (of (a ⊗ₜ[ℂ] b)) = g (of (a ⊗ₜ[ℂ] b))
      rw [of_tmul, map_mul, map_mul]
      exact congrArg₂ (· * ·) (DFunLike.congr_fun hL a) (DFunLike.congr_fun hR b)

@[simp]
lemma lift_includeLeft (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) : (lift φ ψ h).comp includeLeft = φ := by
  ext a
  change lift φ ψ h (of (a ⊗ₜ[ℂ] (1 : B))) = φ a
  rw [lift_of_tmul, map_one, mul_one]

@[simp]
lemma lift_includeRight (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, Commute (φ a) (ψ b)) : (lift φ ψ h).comp includeRight = ψ := by
  ext b
  change lift φ ψ h (of ((1 : A) ⊗ₜ[ℂ] b)) = ψ b
  rw [lift_of_tmul, map_one, one_mul]


universe u


end MaxTensor
end KirchbergRordam

namespace KirchbergRordam.MatrixTensor
open scoped CStarAlgebra ComplexOrder TensorProduct
variable {A B R : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra R]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
def fiberMap (eL : A →⋆ₐ[ℂ] Mat ι) (eR : B →⋆ₐ[ℂ] Mat κ) :
    MaxTensor.Algebra A B →⋆ₐ[ℂ] Mat (ι×κ) :=
  MaxTensor.lift (MatrixTensor.leftMatrix.comp eL) (MatrixTensor.rightMatrix.comp eR)
    (fun a b => legs_commute (eL a) (eR b))
@[simp] lemma fiberMap_tmul (eL : A →⋆ₐ[ℂ] Mat ι) (eR : B →⋆ₐ[ℂ] Mat κ) (a : A) (b : B) :
    fiberMap eL eR (MaxTensor.of (a ⊗ₜ[ℂ] b))=MatrixTensor.leftMatrix (eL a)*MatrixTensor.rightMatrix (eR b) :=
  MaxTensor.lift_of_tmul _ _ _ _ _


end KirchbergRordam.MatrixTensor

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_TensorSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace

namespace KirchbergRordam.PrimeTensorSections
open scoped CStarAlgebra ComplexOrder TensorProduct
open PrimeDimensionDrop MatrixTensor
abbrev Square := unitInterval × unitInterval

end KirchbergRordam.PrimeTensorSections
end

end OAI
end


