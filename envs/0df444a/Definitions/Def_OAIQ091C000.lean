-- Prove2me | Definitions.Def_OAIQ091C000
-- name    : OAIQ091C000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T16:48:43.777808+00:00
-- url     : https://prove2.me/theorems/064a96ec-6a2b-4f5f-ad38-802ae0af5138
-- title:
--   Definitions bundle OAIQ091C000 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 276 declarations of OpenAI's Lean: 89 definitions, 4 inductive types or structures and 183 theorems. The definitions and types are `MeasureTheory.Lp.extendByZeroFun`, `MeasureTheory.Lp.extendByZeroₗ`, `MeasureTheory.Lp.extendByZeroₗᵢ`, `OAI.EinsteinFour.UnitSphere`, `OAI.EinsteinFour.antipodalQuotientEquiv`, `OAI.EinsteinFour.antipodalSetoid`, `OAI.EinsteinFour.antipode`, `OAI.EinsteinFour.sphereToProjective`, `OAI.PositiveEinsteinFour.AlgebraicCurvature.DifferentialBianchi`, `OAI.PositiveEinsteinFour.AlgebraicCurvature.EinsteinRelations`, `OAI.PositiveEinsteinFour.AlgebraicCurvature.FirstBianchi`, `OAI.PositiveEinsteinFour.AlgebraicCurvature.FirstSkew`, `OAI.PositiveEinsteinFour.AlgebraicCurvature.LastSkew`, `OAI.PositiveEinsteinFour.AlgebraicCurvature.PairSymmetric`, `OAI.PositiveEinsteinFour.AlgebraicCurvature.blocksTensor`, `OAI.PositiveEinsteinFour.AlgebraicCurvature.canonicalBlock`, `OAI.PositiveEinsteinFour.AlgebraicCurvature.matrixOf`, `OAI.PositiveEinsteinFour.AlgebraicCurvature.minusFormula`, `OAI.PositiveEinsteinFour.AlgebraicCurvature.mixedBlock`, `OAI.PositiveEinsteinFour.AlgebraicCurvature.pair`, `OAI.PositiveEinsteinFour.AlgebraicCurvature.pairIndex`, `OAI.PositiveEinsteinFour.AlgebraicCurvature.pairSign`, `OAI.PositiveEinsteinFour.AlgebraicCurvature.plusFormula`, `OAI.PositiveEinsteinFour.AlgebraicCurvature.ricci`, `OAI.PositiveEinsteinFour.AlgebraicCurvature.tensorOf`, `OAI.PositiveEinsteinFour.Angular.CurvatureArray`, `OAI.PositiveEinsteinFour.Angular.Directions`, `OAI.PositiveEinsteinFour.Angular.FollandMoments`, `OAI.PositiveEinsteinFour.Angular.Gradient`, `OAI.PositiveEinsteinFour.Angular.Mat3`, `OAI.PositiveEinsteinFour.Angular.Mat4`, `OAI.PositiveEinsteinFour.Angular.ThreeSpace`, `OAI.PositiveEinsteinFour.Angular.blockTensor`, `OAI.PositiveEinsteinFour.Angular.delta`, `OAI.PositiveEinsteinFour.Angular.einsteinCurvatureTensor`, `OAI.PositiveEinsteinFour.Angular.faceChart`, `OAI.PositiveEinsteinFour.Angular.faceSign`, `OAI.PositiveEinsteinFour.Angular.faceVector`, `OAI.PositiveEinsteinFour.Angular.momentFour`, `OAI.PositiveEinsteinFour.Angular.momentSix` and 53 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `EinsteinFour_AngularClifford`, `EinsteinFour_AngularCurvature`, `EinsteinFour_AngularGradient`, `EinsteinFour_AngularNormal`, `EinsteinFour_AngularQuadratic`, `EinsteinFour_AngularRotation`, `EinsteinFour_Bianchi`, `EinsteinFour_CurvatureSecondBianchi`, `EinsteinFour_CurvatureTensors02`, `EinsteinFour_GradientCasimir`, `EinsteinFour_GradientOperator`, `EinsteinFour_GradientPairing`, `EinsteinFour_GradientProjection`, `EinsteinFour_HighestCoordinates`, `EinsteinFour_MatrixSlotOperator`, `EinsteinFour_MetricHessian`, `EinsteinFour_QuaternionReflections`, `EinsteinFour_SphericalMeasureCharts`, `EinsteinFour_SphericalMeasureMass`, `EinsteinFour_SphericalMoments`, `EinsteinFour_TraceHessian`, `EinsteinFour_WeylEstimates01`, `EinsteinFour_WeylEstimates03`, `EinsteinFour_WeylGeometry`, `Manifold_ProjectiveSphere`, `MeasureTheory_Function_LpSpace_Restrict`.
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C006`, `OAIQ091C007`, `OAIQ091C008`, `OAIQ091C009`, `OAIQ091C010`, `OAIQ091C011` and `OAIQ091C012`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour

section
-- module Solutions.OAIQ091_EF.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
open scoped Matrix in
/-- Mathlib d13f23b's `Matrix.posSemidef_is_closed` (real matrices): positive semidefinite matrices are
closed (EinsteinFour JacobiCompressionLimit, oaiq-091). -/
theorem _root_.Matrix.posSemidef_is_closed {n : Type*} [Fintype n] :
    IsClosed {M : Matrix n n ℝ | M.PosSemidef} := by
  have h : {M : Matrix n n ℝ | M.PosSemidef} =
      {M : Matrix n n ℝ | M.IsHermitian} ∩
        ⋂ x : n → ℝ, {M : Matrix n n ℝ | 0 ≤ star x ⬝ᵥ (M *ᵥ x)} := by
    ext M
    simp [Matrix.posSemidef_iff_dotProduct_mulVec]
  rw [h]
  refine IsClosed.inter ?_ (isClosed_iInter fun x => ?_)
  · exact isClosed_eq (Continuous.matrix_conjTranspose continuous_id) continuous_id
  · exact isClosed_le continuous_const (by fun_prop)
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ091_EF.Manifold_ProjectiveSphere
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

 

noncomputable section

open scoped Manifold ContDiff BigOperators ENNReal
open Bundle

namespace EinsteinFour



section SphereInvolution

variable {E : Type*} [NormedAddCommGroup E]

 
abbrev UnitSphere (E : Type*) [NormedAddCommGroup E] := {x : E // ‖x‖ = 1}

 
def antipode (x : UnitSphere E) : UnitSphere E :=
  ⟨-x.val, by simpa using x.property⟩

@[simp] theorem antipode_val (x : UnitSphere E) : (antipode x).val = -x.val := rfl

@[simp] theorem antipode_antipode (x : UnitSphere E) : antipode (antipode x) = x := by
  apply Subtype.ext
  simp

theorem unitSphere_ne_zero (x : UnitSphere E) : x.val ≠ 0 := by
  intro h
  have hx := x.property
  simp [h] at hx

end SphereInvolution



section ProjectiveDistance

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

 

theorem normalized_inner_smul (x y : E) (a b : 𝕜) (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖inner 𝕜 (a • x) (b • y)‖ / (‖a • x‖ * ‖b • y‖) =
      ‖inner 𝕜 x y‖ / (‖x‖ * ‖y‖) := by
  simp only [inner_smul_left, inner_smul_right, norm_mul, RCLike.norm_conj, norm_smul]
  calc
    ‖b‖ * (‖a‖ * ‖inner 𝕜 x y‖) / (‖a‖ * ‖x‖ * (‖b‖ * ‖y‖)) =
        (‖a‖ * ‖b‖) * ‖inner 𝕜 x y‖ / ((‖a‖ * ‖b‖) * (‖x‖ * ‖y‖)) := by
      congr 1 <;> ring
    _ = _ := mul_div_mul_left _ _ (mul_ne_zero (norm_ne_zero_iff.mpr ha)
      (norm_ne_zero_iff.mpr hb))

 

theorem normalized_inner_mk_rep (x y : E) (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖inner 𝕜 (Projectivization.mk 𝕜 x hx).rep (Projectivization.mk 𝕜 y hy).rep‖ /
        (‖(Projectivization.mk 𝕜 x hx).rep‖ * ‖(Projectivization.mk 𝕜 y hy).rep‖) =
      ‖inner 𝕜 x y‖ / (‖x‖ * ‖y‖) := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep 𝕜 x hx
  obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep 𝕜 y hy
  rw [← ha, ← hb]
  exact normalized_inner_smul x y (a : 𝕜) (b : 𝕜) a.ne_zero b.ne_zero

end ProjectiveDistance

theorem fubiniStudyDistance_mk (x y : EuclideanSpace ℂ (Fin 3))
    (hx : x ≠ 0) (hy : y ≠ 0) :
    fubiniStudyDistance (Projectivization.mk ℂ x hx) (Projectivization.mk ℂ y hy) =
      Real.arccos (‖inner ℂ x y‖ / (‖x‖ * ‖y‖)) := by
  rw [fubiniStudyDistance, normalized_inner_mk_rep]

section AntipodalQuotient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

 
def sphereToProjective (x : UnitSphere E) : Projectivization ℝ E :=
  Projectivization.mk ℝ x.val (unitSphere_ne_zero x)

 
theorem sphereToProjective_surjective :
    Function.Surjective (sphereToProjective : UnitSphere E → Projectivization ℝ E) := by
  intro p
  have hp : 0 < ‖p.rep‖ := norm_pos_iff.mpr p.rep_nonzero
  let x : UnitSphere E := ⟨‖p.rep‖⁻¹ • p.rep, by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
    exact inv_mul_cancel₀ (ne_of_gt hp)⟩
  refine ⟨x, ?_⟩
  change Projectivization.mk ℝ x.val (unitSphere_ne_zero x) = p
  conv_rhs => rw [← p.mk_rep]
  refine (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr ⟨‖p.rep‖⁻¹, rfl⟩

 
theorem sphereToProjective_eq_iff (x y : UnitSphere E) :
    sphereToProjective x = sphereToProjective y ↔ x = y ∨ x = antipode y := by
  rw [sphereToProjective, sphereToProjective, Projectivization.mk_eq_mk_iff']
  constructor
  · rintro ⟨a, ha⟩
    have habs := congrArg norm ha
    simp only [norm_smul, Real.norm_eq_abs, x.property, y.property, mul_one] at habs
    have ha' : a = 1 ∨ a = -1 := by
      rcases le_total 0 a with h | h
      · left
        rwa [abs_of_nonneg h] at habs
      · right
        rw [abs_of_nonpos h] at habs
        linarith
    rcases ha' with ha' | ha'
    · left
      apply Subtype.ext
      simpa [ha'] using ha.symm
    · right
      apply Subtype.ext
      simpa [ha'] using ha.symm
  · rintro (h | h)
    · exact ⟨1, by simpa using (congrArg Subtype.val h).symm⟩
    · exact ⟨-1, by simpa using (congrArg Subtype.val h).symm⟩

 
def antipodalSetoid (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    Setoid (UnitSphere E) where
  r x y := x = y ∨ x = antipode y
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := fun h => sphereToProjective_eq_iff _ _ |>.mp
      ((sphereToProjective_eq_iff _ _).mpr h).symm
    trans := fun h₁ h₂ => (sphereToProjective_eq_iff _ _).mp
      (((sphereToProjective_eq_iff _ _).mpr h₁).trans
        ((sphereToProjective_eq_iff _ _).mpr h₂)) }

 

def antipodalQuotientEquiv : Quotient (antipodalSetoid E) ≃ Projectivization ℝ E :=
  Equiv.ofBijective
    (Quotient.lift sphereToProjective fun x y h => (sphereToProjective_eq_iff x y).mpr h)
    (by
      constructor
      · intro x y h
        induction x using Quotient.inductionOn with | h x =>
          induction y using Quotient.inductionOn with | h y =>
            exact Quotient.sound ((sphereToProjective_eq_iff x y).mp h)
      · intro p
        obtain ⟨x, hx⟩ := sphereToProjective_surjective (E := E) p
        exact ⟨Quotient.mk _ x, hx⟩)

@[simp] theorem antipodalQuotientEquiv_mk (x : UnitSphere E) :
    antipodalQuotientEquiv (Quotient.mk (antipodalSetoid E) x) = sphereToProjective x := rfl

end AntipodalQuotient



end EinsteinFour

end

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Bianchi
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concrete four-vector coordinates for a Bianchi gradient

The three quaternion actions are left multiplication by `i,j,k` on the real
four-dimensional Euclidean space. A symmetric matrix of four-vectors is
encoded by its three diagonal and three off-diagonal entries. Its divergence
constraint is the actual quaternionic Bianchi constraint of Section 2.
-/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators

abbrev Vec := EuclideanSpace ℝ (Fin 4)

/-- The fixed positive quaternion triple. -/
def quaternion (i : Fin 3) (q : Vec) : Vec :=
  ![WithLp.toLp 2 ![-q 1, q 0, -q 3, q 2],
    WithLp.toLp 2 ![-q 2, q 3, q 0, -q 1],
    WithLp.toLp 2 ![-q 3, -q 2, q 1, q 0]] i

def next (i : Fin 3) : Fin 3 := ![1, 2, 0] i

def previous (i : Fin 3) : Fin 3 := ![2, 0, 1] i

@[simp] theorem quaternion_add (i : Fin 3) (p q : Vec) :
    quaternion i (p + q) = quaternion i p + quaternion i q := by
  fin_cases i <;> ext j <;> fin_cases j <;> simp [quaternion] <;> ring

@[simp] theorem quaternion_smul (i : Fin 3) (a : ℝ) (q : Vec) :
    quaternion i (a • q) = a • quaternion i q := by
  fin_cases i <;> ext j <;> fin_cases j <;> simp [quaternion]

@[simp] theorem quaternion_neg (i : Fin 3) (q : Vec) :
    quaternion i (-q) = -quaternion i q := by
  simpa only [neg_one_smul] using quaternion_smul i (-1) q

@[simp] theorem quaternion_zero (i : Fin 3) : quaternion i 0 = 0 := by
  simpa using quaternion_smul i 0 (0 : Vec)

@[simp] theorem quaternion_square (i : Fin 3) (q : Vec) :
    quaternion i (quaternion i q) = -q := by
  fin_cases i <;> ext j <;> fin_cases j <;> simp [quaternion]

/-- All three quaternion actions preserve the Euclidean metric. -/
@[simp] theorem quaternion_norm_sq (i : Fin 3) (q : Vec) :
    ‖quaternion i q‖ ^ 2 = ‖q‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq]
  fin_cases i <;> simp [quaternion, Fin.sum_univ_succ] <;> ring

@[simp] theorem quaternion_norm (i : Fin 3) (q : Vec) :
    ‖quaternion i q‖ = ‖q‖ := by
  nlinarith [quaternion_norm_sq i q, norm_nonneg (quaternion i q), norm_nonneg q]

/-- The normalized diagonal spectral shape. -/
structure Shape where
  s : Fin 3 → ℝ
  trace : ∑ i, s i = 0
  square : ∑ i, s i ^ 2 = 6

/-- This is `√3 * s̃`; using it avoids divisions by a square root in the
coordinate inverse. -/
def difference (s : Fin 3 → ℝ) (i : Fin 3) : ℝ := s (next i) - s (previous i)

/-- Symmetric three-by-three matrix with four-vector entries. `off i` is the
entry in positions `(next i, previous i)` and its transpose. -/
@[ext] structure Tensor where
  diagonal : Fin 3 → Vec
  off : Fin 3 → Vec

def Tensor.matrix (T : Tensor) : Fin 3 → Fin 3 → Vec :=
  ![![T.diagonal 0, T.off 2, T.off 1],
    ![T.off 2, T.diagonal 1, T.off 0],
    ![T.off 1, T.off 0, T.diagonal 2]]

def Tensor.auxiliary (T : Tensor) (i : Fin 3) : Vec := quaternion i (T.off i)

/-- Explicit equation (2), in terms of `√3 * s̃`. -/
def parameters (S : Shape) (p k l : Vec) : Tensor where
  diagonal i := S.s i • p - difference S.s i • k
  off i := -quaternion i (l + S.s i • k + (difference S.s i / 3) • p)

@[simp] theorem parameters_auxiliary (S : Shape) (p k l : Vec) (i : Fin 3) :
    (parameters S p k l).auxiliary i = l + S.s i • k + (difference S.s i / 3) • p := by
  change quaternion i (-quaternion i _) = _
  rw [quaternion_neg, quaternion_square, neg_neg]

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_TraceHessian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prescribed trace component of the Bianchi Hessian

The arrays are real tensors. The lift is the explicit formula for the
restricted trace adjoint in Section 5; its Bianchi constraint, trace and
squared norm follow by direct calculation in the fixed quaternion frame. -/

namespace PositiveEinsteinFour.TraceHessian

noncomputable section

open scoped BigOperators
open Bianchi

abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ
abbrev Hessian := Fin 4 → Fin 4 → Mat

def symmetric (M : Mat) : Prop := ∀ i j, M i j = M j i

def traceFree (M : Mat) : Prop := ∑ i, M i i = 0

def ofCoordinates (a b c d e : ℝ) : Mat :=
  ![![a, c, d], ![c, b, e], ![d, e, -a-b]]

/-- Matrix coefficients of the same quaternion triple used for gradients. -/
def quaternionMatrix (s : Fin 3) : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![![0, -1, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, -1], ![0, 0, 1, 0]],
    ![![0, 0, -1, 0], ![0, 0, 0, 1], ![1, 0, 0, 0], ![0, -1, 0, 0]],
    ![![0, 0, 0, -1], ![0, 0, -1, 0], ![0, 1, 0, 0], ![1, 0, 0, 0]]] s

/-- Speed-two rotations on the self-dual matrix indices. -/
def rotation (s : Fin 3) : Mat :=
  ![![![0, 0, 0], ![0, 0, -2], ![0, 2, 0]],
    ![![0, 0, 2], ![0, 0, 0], ![-2, 0, 0]],
    ![![0, -2, 0], ![2, 0, 0], ![0, 0, 0]]] s

def matrixAction (s : Fin 3) (M : Mat) : Mat := fun a b =>
  ∑ c, (rotation s a c * M c b - M a c * rotation s c b)

@[simp] theorem matrixAction_coordinates_zero (a b c d e : ℝ) :
    matrixAction 0 (ofCoordinates a b c d e) =
      ofCoordinates 0 (-4 * e) (-2 * d) (2 * c) (2 * a + 4 * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixAction, rotation, ofCoordinates, Fin.sum_univ_succ] <;> ring

@[simp] theorem matrixAction_coordinates_one (a b c d e : ℝ) :
    matrixAction 1 (ofCoordinates a b c d e) =
      ofCoordinates (4 * d) 0 (2 * e) (-4 * a - 2 * b) (-2 * c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixAction, rotation, ofCoordinates, Fin.sum_univ_succ] <;> ring

@[simp] theorem matrixAction_coordinates_two (a b c d e : ℝ) :
    matrixAction 2 (ofCoordinates a b c d e) =
      ofCoordinates (-4 * c) (4 * c) (2 * a - 2 * b) (-2 * e) (2 * d) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixAction, rotation, ofCoordinates, Fin.sum_univ_succ] <;> ring

end
end PositiveEinsteinFour.TraceHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylGeometry
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete orthonormal frames and curvature blocks of the metric in the
classification statement, defined from its chart curvature. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ

namespace OrthonormalFrame

variable {g : SmoothMetric M} {c : M} (e : OrthonormalFrame g c)

@[simp] theorem vector_apply (i a : Fin 4) : e.vector i a = e.matrix a i := rfl

end OrthonormalFrame

/-- The second quaternion triple is obtained by reversing the first frame
axis. This exchanges the two Hodge-star eigenspaces. -/
def oppositeQuaternion (s : Fin 3) (i j : Fin 4) : ℝ :=
  (if i = 0 then (-1 : ℝ) else 1) *
    (if j = 0 then (-1 : ℝ) else 1) * TraceHessian.quaternionMatrix s i j

/-- The factor 1/8 accounts for antisymmetric coordinate pairs and the
`1/sqrt(2)` normalization of the quaternionic two-form basis. -/
def curvatureBlock (R : (Fin 4 × Fin 4) → (Fin 4 × Fin 4) → ℝ)
    (Q : Fin 3 → Mat4) : Mat3 := fun s t =>
  (1 / 8 : ℝ) * ∑ p, ∑ q, R p q * Q s p.1 p.2 * Q t q.1 q.2

/-- Pair symmetry of curvature implies symmetry of its actual block. -/
theorem curvatureBlock_symmetric
    {R : (Fin 4 × Fin 4) → (Fin 4 × Fin 4) → ℝ}
    (hR : ∀ p q, R p q = R q p) (Q : Fin 3 → Mat4) :
    (curvatureBlock R Q)ᵀ = curvatureBlock R Q := by
  ext s t
  change (1 / 8 : ℝ) * (∑ p, ∑ q, R p q * Q t p.1 p.2 * Q s q.1 q.2) =
    (1 / 8 : ℝ) * (∑ p, ∑ q, R p q * Q s p.1 p.2 * Q t q.1 q.2)
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [hR]
  ring

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_SphericalMoments
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite sphere moments needed for the angular Jacobi calculation.
The conditional input below is precisely the degree 2, 4 and 6 specialization
of Folland, *How to Integrate a Polynomial over a Sphere*, American
Mathematical Monthly 108 (2001), 446–448, Theorem on p.447, after division by
the area of S³. DOI: 10.1080/00029890.2001.11919774.
It contains no curvature or geometric inequality.
-/

namespace PositiveEinsteinFour.Angular

open EinsteinFour MeasureTheory

noncomputable section

abbrev Directions := {q : FourSpace // ‖q‖ = 1}

/-- The normalized spherical measure is fixed, not an arbitrary probability
measure satisfying the desired curvature averages. -/
def sphereMeasure : Measure Directions :=
  ((Measure.hausdorffMeasure 3 : Measure Directions) Set.univ)⁻¹ •
    (Measure.hausdorffMeasure 3 : Measure Directions)

def delta (i j : Fin 4) : ℝ := if i = j then 1 else 0

def momentTwo (i j : Fin 4) : ℝ := delta i j / 4

def momentFour (i j k l : Fin 4) : ℝ :=
  (delta i j * delta k l + delta i k * delta j l + delta i l * delta j k) / 24

/-- The fifteen pairings of six indices, grouped by the partner of `i`. -/
def momentSix (i j k l m n : Fin 4) : ℝ :=
  (delta i j * momentFour k l m n + delta i k * momentFour j l m n +
    delta i l * momentFour j k m n + delta i m * momentFour j k l n +
    delta i n * momentFour j k l m) / 8

/-- Finite angular moment identities. -/
structure FollandMoments : Prop where
  probability : IsProbabilityMeasure sphereMeasure
  second (i j : Fin 4) :
    (∫ q : Directions, q.val i * q.val j ∂sphereMeasure) = momentTwo i j
  fourth (i j k l : Fin 4) :
    (∫ q : Directions, q.val i * q.val j * q.val k * q.val l ∂sphereMeasure) =
      momentFour i j k l
  sixth (i j k l m n : Fin 4) :
    (∫ q : Directions, q.val i * q.val j * q.val k * q.val l * q.val m * q.val n
      ∂sphereMeasure) = momentSix i j k l m n

theorem continuous_coordinate (i : Fin 4) : Continuous (fun q : Directions => q.val i) := by
  fun_prop

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular averages of two quadratic forms, from the precise fourth
spherical moment. This is used for the two Weyl blocks in the normal Jacobi
matrix; no curvature average is an input. -/

namespace PositiveEinsteinFour.Angular

open MeasureTheory Matrix

noncomputable section

abbrev Mat4 := Geometry.Mat4

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularRotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual change of normal bases `I_s q` and `J_t q`. Its spherical
orthogonality is a consequence of the fourth monomial moment. -/

namespace PositiveEinsteinFour.Angular

open Matrix

noncomputable section

def oppositeMatrix (s : Fin 3) : Mat4 := Geometry.oppositeQuaternion s

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularClifford
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quaternion matrix identities for the sixth-moment mixed contraction. -/

namespace PositiveEinsteinFour.Angular

open Matrix TraceHessian

noncomputable section

theorem quaternionMatrix_transpose (i : Fin 3) :
    (quaternionMatrix i)ᵀ = -quaternionMatrix i := by
  ext a b
  simp only [Matrix.transpose_apply, Matrix.neg_apply]
  fin_cases i <;> fin_cases a <;> fin_cases b <;> norm_num [quaternionMatrix]

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularNormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pointwise and averaged normal Jacobi curvature form. -/

namespace PositiveEinsteinFour.Angular

open Matrix MeasureTheory

noncomputable section

abbrev Mat3 := Geometry.Mat3

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normal Jacobi form of the actual quaternion curvature decomposition. -/

namespace PositiveEinsteinFour.Angular

open Matrix TraceHessian

noncomputable section

abbrev CurvatureArray := Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ

def twoFormProduct (P Q : Mat4) : CurvatureArray := fun a b c d => P a b * Q d c

def blockTensor (A : Mat3) (Q : Fin 3 → Mat4) : CurvatureArray :=
  (1 / 2 : ℝ) • ∑ s, ∑ t, A s t • twoFormProduct (Q s) (Q t)

/-- Ric=3g removes the off-diagonal curvature blocks. -/
def einsteinCurvatureTensor (T U : Mat3) : CurvatureArray :=
  blockTensor (1 + T) quaternionMatrix + blockTensor (1 + U) oppositeMatrix

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_AngularGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The directional-derivative part of the angular average. -/

namespace PositiveEinsteinFour.Angular

open Matrix MeasureTheory

noncomputable section

abbrev Gradient := Fin 4 → Mat3

end

end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureSecondBianchi
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coordinate second Bianchi identity. The matrix algebra separates
the commuting second derivatives from the Jacobi cancellation. -/

namespace PositiveEinsteinFour.CovariantBianchi

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

abbrev Mat := Matrix (Fin 4) (Fin 4) ℝ

def curvature (C : Fin 4 → Mat) (D : Fin 4 → Fin 4 → Mat) (i j : Fin 4) : Mat :=
  D i j - D j i + C i * C j - C j * C i

end
end PositiveEinsteinFour.CovariantBianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GradientCasimir
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual Bianchi coupling operator on first derivatives. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

/-- Matrix-slot rotation, retaining the actual tangent four-vectors. -/
def matrixRotation (s : Fin 3) (Z : Tensor) (a b : Fin 3) : Vec :=
  (∑ c, TraceHessian.rotation s a c • Z.matrix c b) -
    ∑ c, TraceHessian.rotation s c b • Z.matrix a c

/-- The actual total plus generator on a Bianchi gradient. -/
def gradientGenerator (s : Fin 3) (Z : Tensor) (a b : Fin 3) : Vec :=
  quaternion s (Z.matrix a b) + matrixRotation s Z a b

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GradientOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual generator commutators on the Bianchi gradient coordinates. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

abbrev RawGradient := Fin 3 → Fin 3 → Vec

def rawMatrixRotation (s : Fin 3) (Z : RawGradient) : RawGradient := fun a b =>
  (∑ c, TraceHessian.rotation s a c • Z c b) - ∑ c, TraceHessian.rotation s c b • Z a c

def rawGradientGenerator (s : Fin 3) (Z : RawGradient) : RawGradient := fun a b =>
  quaternion s (Z a b) + rawMatrixRotation s Z a b

@[simp] theorem rawMatrixRotation_matrix (s : Fin 3) (Z : Tensor) (a b : Fin 3) :
    rawMatrixRotation s Z.matrix a b = matrixRotation s Z a b := rfl

@[simp] theorem rawGradientGenerator_matrix (s : Fin 3) (Z : Tensor) (a b : Fin 3) :
    rawGradientGenerator s Z.matrix a b = gradientGenerator s Z a b := rfl

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GradientProjection
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Bianchi.rawGradientGenerator_matrix _root_.OAI.PositiveEinsteinFour.Bianchi.rawMatrixRotation_matrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The compressed derivative generator in the actual quaternion model. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

/-- Apply a quaternion only in the derivative slot of a matrix-valued tensor. -/
def derivativeQuaternion (r : Fin 3) (Z : Tensor) : Tensor where
  diagonal a := quaternion r (Z.diagonal a)
  off a := quaternion r (Z.off a)

@[simp] theorem derivativeQuaternion_matrix (r : Fin 3) (Z : Tensor)
    (a b : Fin 3) :
    (derivativeQuaternion r Z).matrix a b = quaternion r (Z.matrix a b) := by
  fin_cases a <;> fin_cases b <;> rfl

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GradientPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bilinear compression on the actual Bianchi gradient space. -/

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian

abbrev GradientIndex := Fin 4 × Fin 3 × Fin 3

end
end PositiveEinsteinFour.Bianchi

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HighestCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The undetermined Hessian in concrete quaternion coordinates. -/

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

/-- A symmetric derivative array from its ten matrix entries. -/
def symmetricArray (m : Fin 10 → Mat) : Hessian :=
  ![![m 0, m 1, m 2, m 3], ![m 1, m 4, m 5, m 6],
    ![m 2, m 5, m 7, m 8], ![m 3, m 6, m 8, m 9]]

/-- All fifty coordinates before imposing derivative trace and Bianchi. -/
def rawEntries (c : Fin 50 → ℝ) : Fin 10 → Mat :=
  ![
    ofCoordinates (c 0) (c 1) (c 2) (c 3) (c 4),
    ofCoordinates (c 5) (c 6) (c 7) (c 8) (c 9),
    ofCoordinates (c 10) (c 11) (c 12) (c 13) (c 14),
    ofCoordinates (c 15) (c 16) (c 17) (c 18) (c 19),
    ofCoordinates (c 20) (c 21) (c 22) (c 23) (c 24),
    ofCoordinates (c 25) (c 26) (c 27) (c 28) (c 29),
    ofCoordinates (c 30) (c 31) (c 32) (c 33) (c 34),
    ofCoordinates (c 35) (c 36) (c 37) (c 38) (c 39),
    ofCoordinates (c 40) (c 41) (c 42) (c 43) (c 44),
    ofCoordinates (c 45) (c 46) (c 47) (c 48) (c 49)]

def raw (c : Fin 50 → ℝ) : Hessian := symmetricArray (rawEntries c)

@[simp] theorem rawEntries_0 (c : Fin 50 → ℝ) :
    rawEntries c 0 = ofCoordinates (c 0) (c 1) (c 2) (c 3) (c 4) := rfl

@[simp] theorem rawEntries_1 (c : Fin 50 → ℝ) :
    rawEntries c 1 = ofCoordinates (c 5) (c 6) (c 7) (c 8) (c 9) := rfl

@[simp] theorem rawEntries_2 (c : Fin 50 → ℝ) :
    rawEntries c 2 = ofCoordinates (c 10) (c 11) (c 12) (c 13) (c 14) := rfl

@[simp] theorem rawEntries_3 (c : Fin 50 → ℝ) :
    rawEntries c 3 = ofCoordinates (c 15) (c 16) (c 17) (c 18) (c 19) := rfl

@[simp] theorem rawEntries_4 (c : Fin 50 → ℝ) :
    rawEntries c 4 = ofCoordinates (c 20) (c 21) (c 22) (c 23) (c 24) := rfl

@[simp] theorem rawEntries_5 (c : Fin 50 → ℝ) :
    rawEntries c 5 = ofCoordinates (c 25) (c 26) (c 27) (c 28) (c 29) := rfl

@[simp] theorem rawEntries_6 (c : Fin 50 → ℝ) :
    rawEntries c 6 = ofCoordinates (c 30) (c 31) (c 32) (c 33) (c 34) := rfl

@[simp] theorem rawEntries_7 (c : Fin 50 → ℝ) :
    rawEntries c 7 = ofCoordinates (c 35) (c 36) (c 37) (c 38) (c 39) := rfl

@[simp] theorem rawEntries_8 (c : Fin 50 → ℝ) :
    rawEntries c 8 = ofCoordinates (c 40) (c 41) (c 42) (c 43) (c 44) := rfl

@[simp] theorem rawEntries_9 (c : Fin 50 → ℝ) :
    rawEntries c 9 = ofCoordinates (c 45) (c 46) (c 47) (c 48) (c 49) := rfl


@[simp] theorem raw_0_0 (c : Fin 50 → ℝ) :
    raw c 0 0 = ofCoordinates (c 0) (c 1) (c 2) (c 3) (c 4) := rfl

@[simp] theorem raw_0_1 (c : Fin 50 → ℝ) :
    raw c 0 1 = ofCoordinates (c 5) (c 6) (c 7) (c 8) (c 9) := rfl

@[simp] theorem raw_0_2 (c : Fin 50 → ℝ) :
    raw c 0 2 = ofCoordinates (c 10) (c 11) (c 12) (c 13) (c 14) := rfl

@[simp] theorem raw_0_3 (c : Fin 50 → ℝ) :
    raw c 0 3 = ofCoordinates (c 15) (c 16) (c 17) (c 18) (c 19) := rfl

@[simp] theorem raw_1_0 (c : Fin 50 → ℝ) :
    raw c 1 0 = ofCoordinates (c 5) (c 6) (c 7) (c 8) (c 9) := rfl

@[simp] theorem raw_1_1 (c : Fin 50 → ℝ) :
    raw c 1 1 = ofCoordinates (c 20) (c 21) (c 22) (c 23) (c 24) := rfl

@[simp] theorem raw_1_2 (c : Fin 50 → ℝ) :
    raw c 1 2 = ofCoordinates (c 25) (c 26) (c 27) (c 28) (c 29) := rfl

@[simp] theorem raw_1_3 (c : Fin 50 → ℝ) :
    raw c 1 3 = ofCoordinates (c 30) (c 31) (c 32) (c 33) (c 34) := rfl

@[simp] theorem raw_2_0 (c : Fin 50 → ℝ) :
    raw c 2 0 = ofCoordinates (c 10) (c 11) (c 12) (c 13) (c 14) := rfl

@[simp] theorem raw_2_1 (c : Fin 50 → ℝ) :
    raw c 2 1 = ofCoordinates (c 25) (c 26) (c 27) (c 28) (c 29) := rfl

@[simp] theorem raw_2_2 (c : Fin 50 → ℝ) :
    raw c 2 2 = ofCoordinates (c 35) (c 36) (c 37) (c 38) (c 39) := rfl

@[simp] theorem raw_2_3 (c : Fin 50 → ℝ) :
    raw c 2 3 = ofCoordinates (c 40) (c 41) (c 42) (c 43) (c 44) := rfl

@[simp] theorem raw_3_0 (c : Fin 50 → ℝ) :
    raw c 3 0 = ofCoordinates (c 15) (c 16) (c 17) (c 18) (c 19) := rfl

@[simp] theorem raw_3_1 (c : Fin 50 → ℝ) :
    raw c 3 1 = ofCoordinates (c 30) (c 31) (c 32) (c 33) (c 34) := rfl

@[simp] theorem raw_3_2 (c : Fin 50 → ℝ) :
    raw c 3 2 = ofCoordinates (c 40) (c 41) (c 42) (c 43) (c 44) := rfl

@[simp] theorem raw_3_3 (c : Fin 50 → ℝ) :
    raw c 3 3 = ofCoordinates (c 45) (c 46) (c 47) (c 48) (c 49) := rfl


/-- The twenty-one free coordinates after the actual tensor constraints. -/
def entries (c : Fin 21 → ℝ) : Fin 10 → Mat :=
  ![
    ofCoordinates (-c 6 - c 7 - 2 * c 15 + c 17) (-c 0 - c 7 - c 17) (c 2 + c 5 - c 8 - c 18) (c 3 - c 4 - c 9 + c 13) (-c 1 - c 10 - c 20),
    ofCoordinates (-c 10 + c 11 + 2 * c 12 + c 20) (-c 1 - c 12 - c 20) (c 3 - c 4) (-c 2 - c 5 + c 8 + c 14) (c 0 + c 7 + c 15),
    ofCoordinates (c 9 - c 13) (-c 3 + c 13) (c 10 - c 12) (-c 6 - c 7 - c 15) (c 2 - c 8),
    ofCoordinates (c 14 - c 18) (-c 5 + c 18) (c 15 - c 17) (-c 11 - c 12 - c 20) (c 4 - c 13),
    ofCoordinates (c 7 + 2 * c 15 - c 16 - c 17) (c 0) (-c 2 - c 5) (-c 3 + c 4 - c 13 - c 19) (c 1),
    ofCoordinates (-c 8 - c 14) (c 2) (-c 7 - c 15) (-c 10 + c 11 + c 12) (c 3),
    ofCoordinates (-c 13 - c 19) (c 4) (-c 12 - c 20) (-c 15 + c 16 + c 17) (c 5),
    ofCoordinates (c 6) (c 7) (c 8) (c 9) (c 10),
    ofCoordinates (c 11) (c 12) (c 13) (c 14) (c 15),
    ofCoordinates (c 16) (c 17) (c 18) (c 19) (c 20)]

def highest (c : Fin 21 → ℝ) : Hessian := symmetricArray (entries c)

@[simp] theorem entries_0 (c : Fin 21 → ℝ) :
    entries c 0 = ofCoordinates (-c 6 - c 7 - 2 * c 15 + c 17) (-c 0 - c 7 - c 17) (c 2 + c 5 - c 8 - c 18) (c 3 - c 4 - c 9 + c 13) (-c 1 - c 10 - c 20) := rfl

@[simp] theorem entries_1 (c : Fin 21 → ℝ) :
    entries c 1 = ofCoordinates (-c 10 + c 11 + 2 * c 12 + c 20) (-c 1 - c 12 - c 20) (c 3 - c 4) (-c 2 - c 5 + c 8 + c 14) (c 0 + c 7 + c 15) := rfl

@[simp] theorem entries_2 (c : Fin 21 → ℝ) :
    entries c 2 = ofCoordinates (c 9 - c 13) (-c 3 + c 13) (c 10 - c 12) (-c 6 - c 7 - c 15) (c 2 - c 8) := rfl

@[simp] theorem entries_3 (c : Fin 21 → ℝ) :
    entries c 3 = ofCoordinates (c 14 - c 18) (-c 5 + c 18) (c 15 - c 17) (-c 11 - c 12 - c 20) (c 4 - c 13) := rfl

@[simp] theorem entries_4 (c : Fin 21 → ℝ) :
    entries c 4 = ofCoordinates (c 7 + 2 * c 15 - c 16 - c 17) (c 0) (-c 2 - c 5) (-c 3 + c 4 - c 13 - c 19) (c 1) := rfl

@[simp] theorem entries_5 (c : Fin 21 → ℝ) :
    entries c 5 = ofCoordinates (-c 8 - c 14) (c 2) (-c 7 - c 15) (-c 10 + c 11 + c 12) (c 3) := rfl

@[simp] theorem entries_6 (c : Fin 21 → ℝ) :
    entries c 6 = ofCoordinates (-c 13 - c 19) (c 4) (-c 12 - c 20) (-c 15 + c 16 + c 17) (c 5) := rfl

@[simp] theorem entries_7 (c : Fin 21 → ℝ) :
    entries c 7 = ofCoordinates (c 6) (c 7) (c 8) (c 9) (c 10) := rfl

@[simp] theorem entries_8 (c : Fin 21 → ℝ) :
    entries c 8 = ofCoordinates (c 11) (c 12) (c 13) (c 14) (c 15) := rfl

@[simp] theorem entries_9 (c : Fin 21 → ℝ) :
    entries c 9 = ofCoordinates (c 16) (c 17) (c 18) (c 19) (c 20) := rfl

@[simp] theorem highest_0_0 (c : Fin 21 → ℝ) :
    highest c 0 0 = entries c 0 := rfl

@[simp] theorem highest_0_1 (c : Fin 21 → ℝ) :
    highest c 0 1 = entries c 1 := rfl

@[simp] theorem highest_0_2 (c : Fin 21 → ℝ) :
    highest c 0 2 = entries c 2 := rfl

@[simp] theorem highest_0_3 (c : Fin 21 → ℝ) :
    highest c 0 3 = entries c 3 := rfl

@[simp] theorem highest_1_0 (c : Fin 21 → ℝ) :
    highest c 1 0 = entries c 1 := rfl

@[simp] theorem highest_1_1 (c : Fin 21 → ℝ) :
    highest c 1 1 = entries c 4 := rfl

@[simp] theorem highest_1_2 (c : Fin 21 → ℝ) :
    highest c 1 2 = entries c 5 := rfl

@[simp] theorem highest_1_3 (c : Fin 21 → ℝ) :
    highest c 1 3 = entries c 6 := rfl

@[simp] theorem highest_2_0 (c : Fin 21 → ℝ) :
    highest c 2 0 = entries c 2 := rfl

@[simp] theorem highest_2_1 (c : Fin 21 → ℝ) :
    highest c 2 1 = entries c 5 := rfl

@[simp] theorem highest_2_2 (c : Fin 21 → ℝ) :
    highest c 2 2 = entries c 7 := rfl

@[simp] theorem highest_2_3 (c : Fin 21 → ℝ) :
    highest c 2 3 = entries c 8 := rfl

@[simp] theorem highest_3_0 (c : Fin 21 → ℝ) :
    highest c 3 0 = entries c 3 := rfl

@[simp] theorem highest_3_1 (c : Fin 21 → ℝ) :
    highest c 3 1 = entries c 6 := rfl

@[simp] theorem highest_3_2 (c : Fin 21 → ℝ) :
    highest c 3 2 = entries c 8 := rfl

@[simp] theorem highest_3_3 (c : Fin 21 → ℝ) :
    highest c 3 3 = entries c 9 := rfl


end
end PositiveEinsteinFour.HighestHessian

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MetricHessian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted rough-Laplacian identity for the metric's actual Weyl
gradient. Differentiation takes place in the coordinate connection before
the parallel frame is applied. The integration identity follows from
frame-flow invariance, rather than an assumed Hessian integral formula. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular TraceHessian
open scoped Manifold ContDiff

noncomputable section

abbrev GradientVector := EuclideanSpace ℝ (Fin 4 × Fin 3 × Fin 3)

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MatrixSlotOperator
attribute [-simp] _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_4 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_5 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_6 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_7 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_8 _root_.OAI.PositiveEinsteinFour.HighestHessian.entries_9 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_0_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_1_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_2_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.highest_3_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_4 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_5 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_6 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_7 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_8 _root_.OAI.PositiveEinsteinFour.HighestHessian.rawEntries_9 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_0_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_1_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_2_3 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_0 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_1 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_2 _root_.OAI.PositiveEinsteinFour.HighestHessian.raw_3_3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The varying matrix-slot curvature coefficient as an actual bounded
operator. The extension to all matrix arrays is self-adjoint; on trace-free
arrays it is the trace-free anticommutator used in the Weyl equation. -/

namespace PositiveEinsteinFour.Geometry

open scoped BigOperators
open TraceHessian Bianchi

noncomputable section

local instance instNormedAddCommGroupMat_reda1fc_1 : NormedAddCommGroup Mat := Matrix.frobeniusNormedAddCommGroup
local instance instNormedSpaceRealMat_reda1fc_1 : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace
def matrixEntryKernel (A : Mat) (p q : Fin 3 × Fin 3) : ℝ :=
  (1 / 2 : ℝ) * ((if p.2 = q.2 then A p.1 q.1 else 0) +
    (if p.1 = q.1 then A q.2 p.2 else 0)) -
  (1 / 3 : ℝ) * ((if p.1 = p.2 then A q.2 q.1 else 0) +
    (if q.1 = q.2 then A p.1 p.2 else 0))

def matrixSlotKernel (A : Mat) (p q : GradientIndex) : ℝ :=
  if p.1 = q.1 then matrixEntryKernel A p.2 q.2 else 0

theorem matrixEntryKernel_add (A B : Mat) (p q : Fin 3 × Fin 3) :
    matrixEntryKernel (A + B) p q = matrixEntryKernel A p q + matrixEntryKernel B p q := by
  unfold matrixEntryKernel
  simp only [Matrix.add_apply]
  split_ifs <;> ring

theorem matrixEntryKernel_smul (c : ℝ) (A : Mat) (p q : Fin 3 × Fin 3) :
    matrixEntryKernel (c • A) p q = c * matrixEntryKernel A p q := by
  unfold matrixEntryKernel
  simp only [Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem matrixSlotKernel_add (A B : Mat) (p q : GradientIndex) :
    matrixSlotKernel (A + B) p q = matrixSlotKernel A p q + matrixSlotKernel B p q := by
  unfold matrixSlotKernel
  split_ifs <;> simp only [matrixEntryKernel_add, add_zero]

theorem matrixSlotKernel_smul (c : ℝ) (A : Mat) (p q : GradientIndex) :
    matrixSlotKernel (c • A) p q = c * matrixSlotKernel A p q := by
  unfold matrixSlotKernel
  split_ifs <;> simp only [matrixEntryKernel_smul, mul_zero]

def matrixSlotLinear (A : Mat) : GradientVector →ₗ[ℝ] GradientVector where
  toFun Z := WithLp.toLp 2 (fun p => ∑ q, matrixSlotKernel A p q * Z q)
  map_add' Z W := by
    ext p
    change (∑ q, matrixSlotKernel A p q * (Z q + W q)) =
      (∑ q, matrixSlotKernel A p q * Z q) + ∑ q, matrixSlotKernel A p q * W q
    simp only [mul_add, Finset.sum_add_distrib]
  map_smul' c Z := by
    ext p
    change (∑ q, matrixSlotKernel A p q * (c * Z q)) =
      c * (∑ q, matrixSlotKernel A p q * Z q)
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring

/-- The bounded operator that acts on every matrix slice of the Weyl gradient. -/
def matrixSlotOperator (A : Mat) : GradientVector →L[ℝ] GradientVector :=
  (matrixSlotLinear A).toContinuousLinearMap

def matrixSlotOperatorLinear : Mat →ₗ[ℝ] (GradientVector →L[ℝ] GradientVector) where
  toFun := matrixSlotOperator
  map_add' A B := by
    ext Z p
    change (∑ q, matrixSlotKernel (A + B) p q * Z q) =
      (∑ q, matrixSlotKernel A p q * Z q) + ∑ q, matrixSlotKernel B p q * Z q
    simp only [matrixSlotKernel_add, add_mul, Finset.sum_add_distrib]
  map_smul' c A := by
    ext Z p
    change (∑ q, matrixSlotKernel (c • A) p q * Z q) =
      c * (∑ q, matrixSlotKernel A p q * Z q)
    simp only [matrixSlotKernel_smul, mul_assoc, Finset.mul_sum]

/-- Continuous linear dependence on the matrix coefficient. -/
def matrixSlot : Mat →L[ℝ] (GradientVector →L[ℝ] GradientVector) :=
  matrixSlotOperatorLinear.toContinuousLinearMap

@[simp] theorem matrixSlot_apply (A : Mat) : matrixSlot A = matrixSlotOperator A := rfl

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_QuaternionReflections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pure quaternion lifts of the reflections needed to choose a local
spectral frame. Only their concrete action on the two quaternion triples
is used; no global eigenframe or representation theorem is assumed. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem oppositeMatrix_transpose (r : Fin 3) :
    (Angular.oppositeMatrix r)ᵀ = -Angular.oppositeMatrix r := by
  ext i j
  change Geometry.oppositeQuaternion r j i = -Geometry.oppositeQuaternion r i j
  fin_cases r <;> fin_cases i <;> fin_cases j <;>
    norm_num [Geometry.oppositeQuaternion, quaternionMatrix]

end
end PositiveEinsteinFour.QuaternionFrame

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates01
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! A pointwise spectral basis in the positive Weyl block lifts to an
orientation-preserving orthogonal change in four dimensions. The harmless
common sign in the three-dimensional basis cancels from matrix conjugation. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

abbrev ThreeSpace := EuclideanSpace ℝ (Fin 3)

/-- Matrix of a three-dimensional orthogonal change in the fixed Euclidean basis. -/
def frameMatrix (φ : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) : Mat :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis φ.toLinearMap

@[simp] theorem frameMatrix_one : frameMatrix (1 : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) = 1 := by
  exact LinearMap.toMatrix_one _

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The elementary Grassmannian calculation needed for the sectional
criterion. Two arbitrary unit coefficient vectors in the positive and
negative quaternion triples are realized by a genuine two-plane. -/

namespace PositiveEinsteinFour.SectionalPlane

open EinsteinFour Matrix Bianchi TraceHessian QuaternionFrame Angular
open scoped BigOperators

noncomputable section

abbrev Vec4 := EuclideanSpace ℝ (Fin 4)

def act (A : Geometry.Mat4) (v : Vec4) : Vec4 :=
  WithLp.toLp 2 (A *ᵥ (v : Fin 4 → ℝ))

@[simp] theorem act_zero (v : Vec4) : act (0 : Geometry.Mat4) v = 0 := by
  ext i
  simp [act]

@[simp] theorem act_one (v : Vec4) : act (1 : Geometry.Mat4) v = v := by
  ext i
  simp [act]

end
end PositiveEinsteinFour.SectionalPlane
end


section

/-! Covariance of the actual Bianchi projection. The two generator
transformations are derived from the same quaternion frame change and
contract against its orthogonal three-dimensional matrix. -/

namespace PositiveEinsteinFour.QuaternionFrame

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

def rawField (Z : RawGradient) : Angular.Gradient := fun i a b => Z a b i
def fieldRaw (Z : Angular.Gradient) : RawGradient :=
  fun a b => WithLp.toLp 2 (fun i => Z i a b)

@[simp] theorem rawField_fieldRaw (Z : Angular.Gradient) : rawField (fieldRaw Z) = Z := rfl
@[simp] theorem fieldRaw_rawField (Z : RawGradient) : fieldRaw (rawField Z) = Z := rfl

end
end PositiveEinsteinFour.QuaternionFrame
end


section

/-! The six canonical two-form coordinates of an algebraic curvature
array. All reconstruction statements here are finite-dimensional algebra;
the actual metric curvature symmetries are supplied separately. -/

namespace PositiveEinsteinFour.AlgebraicCurvature

open Matrix TraceHessian Angular
open PositiveEinsteinFour.Geometry (curvatureBlock curvatureBlock_symmetric)
open scoped BigOperators

noncomputable section

def pair (i : Fin 6) : Fin 4 × Fin 4 :=
  ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)] i

def pairIndex (i j : Fin 4) : Fin 6 :=
  match i.val, j.val with
  | 0, 1 => 0 | 1, 0 => 0
  | 0, 2 => 1 | 2, 0 => 1
  | 0, 3 => 2 | 3, 0 => 2
  | 1, 2 => 3 | 2, 1 => 3
  | 1, 3 => 4 | 3, 1 => 4
  | 2, 3 => 5 | 3, 2 => 5
  | _, _ => 0

def pairSign (i j : Fin 4) : ℝ :=
  if i < j then 1 else if i = j then 0 else -1

def matrixOf (R : CurvatureArray) : Matrix (Fin 6) (Fin 6) ℝ := fun a b =>
  R (pair a).1 (pair a).2 (pair b).1 (pair b).2

def tensorOf (K : Matrix (Fin 6) (Fin 6) ℝ) : CurvatureArray := fun i j k l =>
  pairSign i j * pairSign k l * K (pairIndex i j) (pairIndex k l)

def FirstSkew (R : CurvatureArray) : Prop := ∀ i j k l, R j i k l = -R i j k l

def LastSkew (R : CurvatureArray) : Prop := ∀ i j k l, R i j l k = -R i j k l

def PairSymmetric (R : CurvatureArray) : Prop := ∀ i j k l, R k l i j = R i j k l

def FirstBianchi (R : CurvatureArray) : Prop :=
  ∀ i j k l, R i j k l + R j k i l + R k i j l = 0

theorem pairSymmetric_of_bianchi {R : CurvatureArray}
    (hf : FirstSkew R) (hl : LastSkew R) (hb : FirstBianchi R) : PairSymmetric R := by
  intro a b c d
  have h1 := hb a b c d
  have h2 := hb a b d c
  have h3 := hb c d a b
  have h4 := hb b d c a
  rw [hf a c b d] at h1
  rw [hl a b c d] at h2
  rw [hl d a b c, hl a c b d] at h3
  rw [hl b d a c, hf c d b a, hl c d a b,
    hf b c d a, hl b c a d] at h4
  linarith

def ricci (R : CurvatureArray) (j k : Fin 4) : ℝ := ∑ i, R i j k i

theorem first_diagonal_zero {R : CurvatureArray} (h : FirstSkew R) (i k l : Fin 4) :
    R i i k l = 0 := by have hh := h i i k l; linarith

theorem last_diagonal_zero {R : CurvatureArray} (h : LastSkew R) (i j k : Fin 4) :
    R i j k k = 0 := by have hh := h i j k k; linarith

theorem tensorOf_matrixOf_row0 {R : CurvatureArray}
    (hf : FirstSkew R) (hl : LastSkew R) (j k l : Fin 4) :
    tensorOf (matrixOf R) 0 j k l = R 0 j k l := by
  have f10 (k l) := hf 0 1 k l
  have f20 (k l) := hf 0 2 k l
  have f30 (k l) := hf 0 3 k l
  have f21 (k l) := hf 1 2 k l
  have f31 (k l) := hf 1 3 k l
  have f32 (k l) := hf 2 3 k l
  have l10 (i j) := hl i j 0 1
  have l20 (i j) := hl i j 0 2
  have l30 (i j) := hl i j 0 3
  have l21 (i j) := hl i j 1 2
  have l31 (i j) := hl i j 1 3
  have l32 (i j) := hl i j 2 3
  fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [tensorOf, matrixOf, pair, pairIndex, pairSign,
      first_diagonal_zero hf, last_diagonal_zero hl,
      f10, f20, f30, f21, f31, f32, l10, l20, l30, l21, l31, l32]

theorem tensorOf_matrixOf_row1 {R : CurvatureArray}
    (hf : FirstSkew R) (hl : LastSkew R) (j k l : Fin 4) :
    tensorOf (matrixOf R) 1 j k l = R 1 j k l := by
  have f10 (k l) := hf 0 1 k l
  have f20 (k l) := hf 0 2 k l
  have f30 (k l) := hf 0 3 k l
  have f21 (k l) := hf 1 2 k l
  have f31 (k l) := hf 1 3 k l
  have f32 (k l) := hf 2 3 k l
  have l10 (i j) := hl i j 0 1
  have l20 (i j) := hl i j 0 2
  have l30 (i j) := hl i j 0 3
  have l21 (i j) := hl i j 1 2
  have l31 (i j) := hl i j 1 3
  have l32 (i j) := hl i j 2 3
  fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [tensorOf, matrixOf, pair, pairIndex, pairSign,
      first_diagonal_zero hf, last_diagonal_zero hl,
      f10, f20, f30, f21, f31, f32, l10, l20, l30, l21, l31, l32]

theorem tensorOf_matrixOf_row2 {R : CurvatureArray}
    (hf : FirstSkew R) (hl : LastSkew R) (j k l : Fin 4) :
    tensorOf (matrixOf R) 2 j k l = R 2 j k l := by
  have f10 (k l) := hf 0 1 k l
  have f20 (k l) := hf 0 2 k l
  have f30 (k l) := hf 0 3 k l
  have f21 (k l) := hf 1 2 k l
  have f31 (k l) := hf 1 3 k l
  have f32 (k l) := hf 2 3 k l
  have l10 (i j) := hl i j 0 1
  have l20 (i j) := hl i j 0 2
  have l30 (i j) := hl i j 0 3
  have l21 (i j) := hl i j 1 2
  have l31 (i j) := hl i j 1 3
  have l32 (i j) := hl i j 2 3
  fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [tensorOf, matrixOf, pair, pairIndex, pairSign,
      first_diagonal_zero hf, last_diagonal_zero hl,
      f10, f20, f30, f21, f31, f32, l10, l20, l30, l21, l31, l32]

theorem tensorOf_matrixOf_row3 {R : CurvatureArray}
    (hf : FirstSkew R) (hl : LastSkew R) (j k l : Fin 4) :
    tensorOf (matrixOf R) 3 j k l = R 3 j k l := by
  have f10 (k l) := hf 0 1 k l
  have f20 (k l) := hf 0 2 k l
  have f30 (k l) := hf 0 3 k l
  have f21 (k l) := hf 1 2 k l
  have f31 (k l) := hf 1 3 k l
  have f32 (k l) := hf 2 3 k l
  have l10 (i j) := hl i j 0 1
  have l20 (i j) := hl i j 0 2
  have l30 (i j) := hl i j 0 3
  have l21 (i j) := hl i j 1 2
  have l31 (i j) := hl i j 1 3
  have l32 (i j) := hl i j 2 3
  fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [tensorOf, matrixOf, pair, pairIndex, pairSign,
      first_diagonal_zero hf, last_diagonal_zero hl,
      f10, f20, f30, f21, f31, f32, l10, l20, l30, l21, l31, l32]

/-- First and last skew symmetry reconstruct the whole four-tensor from
its 36 canonical two-form matrix entries. -/
theorem tensorOf_matrixOf {R : CurvatureArray} (hf : FirstSkew R) (hl : LastSkew R) :
    tensorOf (matrixOf R) = R := by
  funext i j k l
  fin_cases i
  · exact tensorOf_matrixOf_row0 hf hl j k l
  · exact tensorOf_matrixOf_row1 hf hl j k l
  · exact tensorOf_matrixOf_row2 hf hl j k l
  · exact tensorOf_matrixOf_row3 hf hl j k l

theorem matrixOf_symmetric {R : CurvatureArray} (h : PairSymmetric R) :
    (matrixOf R)ᵀ = matrixOf R := by
  ext i j
  exact h _ _ _ _

theorem tensor_eq_of_matrixOf_eq {R S : CurvatureArray}
    (hRf : FirstSkew R) (hRl : LastSkew R)
    (hSf : FirstSkew S) (hSl : LastSkew S) (h : matrixOf R = matrixOf S) : R = S := by
  rw [← tensorOf_matrixOf hRf hRl, h, tensorOf_matrixOf hSf hSl]

theorem pairIndex_reverse (i j : Fin 4) : pairIndex j i = pairIndex i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem pairSign_reverse (i j : Fin 4) : pairSign j i = -pairSign i j := by
  fin_cases i <;> fin_cases j <;> simp [pairSign]

theorem tensorOf_firstSkew (K : Matrix (Fin 6) (Fin 6) ℝ) : FirstSkew (tensorOf K) := by
  intro i j k l
  simp only [tensorOf, pairIndex_reverse i j, pairSign_reverse i j]
  ring

theorem tensorOf_lastSkew (K : Matrix (Fin 6) (Fin 6) ℝ) : LastSkew (tensorOf K) := by
  intro i j k l
  simp only [tensorOf, pairIndex_reverse k l, pairSign_reverse k l]
  ring

/-- Compression of an antisymmetric coordinate sum to the six increasing
index pairs. The factor two records the two orders of each pair. -/
theorem pair_sum (Q : Mat4) (hQ : Qᵀ = -Q) (f : Fin 6 → ℝ) :
    (∑ i : Fin 4, ∑ j : Fin 4, pairSign i j * Q i j * f (pairIndex i j)) =
      2 * ∑ a : Fin 6, Q (pair a).1 (pair a).2 * f a := by
  have hs (i j : Fin 4) : Q j i = -Q i j := by
    have h := congrArg (fun A : Mat4 => A i j) hQ
    exact h
  have hd (i : Fin 4) : Q i i = 0 := by have h := hs i i; linarith
  simp [Fin.sum_univ_succ, pairSign, pairIndex, pair, hd,
    hs 0 1, hs 0 2, hs 0 3, hs 1 2, hs 1 3, hs 2 3] <;> ring

def canonicalBlock (K : Matrix (Fin 6) (Fin 6) ℝ) (Q P : Fin 3 → Mat4) : Mat3 :=
  fun s t => -(1 / 2 : ℝ) * ∑ a, ∑ b,
    K a b * Q s (pair a).1 (pair a).2 * P t (pair b).1 (pair b).2


theorem pair_bilinear_sum (K : Matrix (Fin 6) (Fin 6) ℝ) (Q P : Mat4)
    (hQ : Qᵀ = -Q) (hP : Pᵀ = -P) :
    (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
      pairSign i j * pairSign k l * K (pairIndex i j) (pairIndex k l) * Q i j * P k l) =
      4 * ∑ a : Fin 6, ∑ b : Fin 6,
        K a b * Q (pair a).1 (pair a).2 * P (pair b).1 (pair b).2 := by
  let F : Fin 6 → ℝ := fun a => ∑ b, P (pair b).1 (pair b).2 * K a b
  have hi (i j : Fin 4) := pair_sum P hP (fun b => K (pairIndex i j) b)
  calc
    _ = ∑ i : Fin 4, ∑ j : Fin 4, pairSign i j * Q i j *
        (∑ k : Fin 4, ∑ l : Fin 4, pairSign k l * P k l * K (pairIndex i j) (pairIndex k l)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = ∑ i : Fin 4, ∑ j : Fin 4, pairSign i j * Q i j * (2 * F (pairIndex i j)) := by
      simp_rw [hi]
      rfl
    _ = 2 * (∑ i : Fin 4, ∑ j : Fin 4, pairSign i j * Q i j * F (pairIndex i j)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 4 * (∑ a : Fin 6, Q (pair a).1 (pair a).2 * F a) := by
      rw [pair_sum Q hQ F]
      ring
    _ = _ := by
      simp only [F, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring

def mixedBlock (R : CurvatureArray) (Q P : Fin 3 → Mat4) : Mat3 := fun s t =>
  (1 / 8 : ℝ) * ∑ p : Fin 4 × Fin 4, ∑ q : Fin 4 × Fin 4,
    R p.1 p.2 q.2 q.1 * Q s p.1 p.2 * P t q.1 q.2

theorem mixedBlock_tensorOf (K : Matrix (Fin 6) (Fin 6) ℝ)
    (Q P : Fin 3 → Mat4) (hQ : ∀ i, (Q i)ᵀ = -Q i) (hP : ∀ i, (P i)ᵀ = -P i) :
    mixedBlock (tensorOf K) Q P = canonicalBlock K Q P := by
  have ht (i j k l : Fin 4) : tensorOf K i j l k =
      -(pairSign i j * pairSign k l * K (pairIndex i j) (pairIndex k l)) := by
    rw [tensorOf, pairSign_reverse k l, pairIndex_reverse k l]
    ring
  ext s t
  simp only [mixedBlock, Fintype.sum_prod_type, ht, neg_mul,
    Finset.sum_neg_distrib]
  rw [pair_bilinear_sum K (Q s) (P t) (hQ s) (hP t)]
  simp only [canonicalBlock]
  ring

theorem curvatureBlock_tensorOf (K : Matrix (Fin 6) (Fin 6) ℝ)
    (Q : Fin 3 → Mat4) (hQ : ∀ i, (Q i)ᵀ = -Q i) :
    curvatureBlock (fun p q => tensorOf K p.1 p.2 q.2 q.1) Q = canonicalBlock K Q Q :=
  mixedBlock_tensorOf K Q Q hQ hQ


def plusFormula (K : Matrix (Fin 6) (Fin 6) ℝ) : Mat3 :=
  ![![-(K 0 0 + K 0 5 + K 5 0 + K 5 5) / 2, -(K 0 1 - K 0 4 + K 5 1 - K 5 4) / 2, -(K 0 2 + K 0 3 + K 5 2 + K 5 3) / 2],
    ![-(K 1 0 + K 1 5 - K 4 0 - K 4 5) / 2, -(K 1 1 - K 1 4 - K 4 1 + K 4 4) / 2, -(K 1 2 + K 1 3 - K 4 2 - K 4 3) / 2],
    ![-(K 2 0 + K 2 5 + K 3 0 + K 3 5) / 2, -(K 2 1 - K 2 4 + K 3 1 - K 3 4) / 2, -(K 2 2 + K 2 3 + K 3 2 + K 3 3) / 2]]

theorem plusFormula_row0 (K : Matrix (Fin 6) (Fin 6) ℝ) (j : Fin 3) :
    canonicalBlock K quaternionMatrix quaternionMatrix 0 j = plusFormula K 0 j := by
  fin_cases j <;>
    simp [canonicalBlock, plusFormula, pair, quaternionMatrix, oppositeMatrix,
      Geometry.oppositeQuaternion, Fin.sum_univ_succ] <;> ring

theorem plusFormula_row1 (K : Matrix (Fin 6) (Fin 6) ℝ) (j : Fin 3) :
    canonicalBlock K quaternionMatrix quaternionMatrix 1 j = plusFormula K 1 j := by
  fin_cases j <;>
    simp [canonicalBlock, plusFormula, pair, quaternionMatrix, oppositeMatrix,
      Geometry.oppositeQuaternion, Fin.sum_univ_succ] <;> ring

theorem plusFormula_row2 (K : Matrix (Fin 6) (Fin 6) ℝ) (j : Fin 3) :
    canonicalBlock K quaternionMatrix quaternionMatrix 2 j = plusFormula K 2 j := by
  fin_cases j <;>
    simp [canonicalBlock, plusFormula, pair, quaternionMatrix, oppositeMatrix,
      Geometry.oppositeQuaternion, Fin.sum_univ_succ] <;> ring

theorem plusFormula_eq (K : Matrix (Fin 6) (Fin 6) ℝ) :
    canonicalBlock K quaternionMatrix quaternionMatrix = plusFormula K := by
  ext i j
  fin_cases i
  · exact plusFormula_row0 K j
  · exact plusFormula_row1 K j
  · exact plusFormula_row2 K j

def minusFormula (K : Matrix (Fin 6) (Fin 6) ℝ) : Mat3 :=
  ![![-(K 0 0 - K 0 5 - K 5 0 + K 5 5) / 2, -(K 0 1 + K 0 4 - K 5 1 - K 5 4) / 2, -(K 0 2 - K 0 3 - K 5 2 + K 5 3) / 2],
    ![-(K 1 0 - K 1 5 + K 4 0 - K 4 5) / 2, -(K 1 1 + K 1 4 + K 4 1 + K 4 4) / 2, -(K 1 2 - K 1 3 + K 4 2 - K 4 3) / 2],
    ![-(K 2 0 - K 2 5 - K 3 0 + K 3 5) / 2, -(K 2 1 + K 2 4 - K 3 1 - K 3 4) / 2, -(K 2 2 - K 2 3 - K 3 2 + K 3 3) / 2]]

theorem minusFormula_row0 (K : Matrix (Fin 6) (Fin 6) ℝ) (j : Fin 3) :
    canonicalBlock K oppositeMatrix oppositeMatrix 0 j = minusFormula K 0 j := by
  fin_cases j <;>
    simp [canonicalBlock, minusFormula, pair, quaternionMatrix, oppositeMatrix,
      Geometry.oppositeQuaternion, Fin.sum_univ_succ] <;> ring

theorem minusFormula_row1 (K : Matrix (Fin 6) (Fin 6) ℝ) (j : Fin 3) :
    canonicalBlock K oppositeMatrix oppositeMatrix 1 j = minusFormula K 1 j := by
  fin_cases j <;>
    simp [canonicalBlock, minusFormula, pair, quaternionMatrix, oppositeMatrix,
      Geometry.oppositeQuaternion, Fin.sum_univ_succ] <;> ring

theorem minusFormula_row2 (K : Matrix (Fin 6) (Fin 6) ℝ) (j : Fin 3) :
    canonicalBlock K oppositeMatrix oppositeMatrix 2 j = minusFormula K 2 j := by
  fin_cases j <;>
    simp [canonicalBlock, minusFormula, pair, quaternionMatrix, oppositeMatrix,
      Geometry.oppositeQuaternion, Fin.sum_univ_succ] <;> ring

theorem minusFormula_eq (K : Matrix (Fin 6) (Fin 6) ℝ) :
    canonicalBlock K oppositeMatrix oppositeMatrix = minusFormula K := by
  ext i j
  fin_cases i
  · exact minusFormula_row0 K j
  · exact minusFormula_row1 K j
  · exact minusFormula_row2 K j

structure EinsteinRelations (K : Matrix (Fin 6) (Fin 6) ℝ) : Prop where
  symmetric : Kᵀ = K
  d0 : K 5 5 = K 0 0
  d1 : K 4 4 = K 1 1
  d2 : K 3 3 = K 2 2
  a01 : K 4 5 = -K 0 1
  a02 : K 3 5 = K 0 2
  a03 : K 2 5 = K 0 3
  a04 : K 1 5 = -K 0 4
  a12 : K 3 4 = -K 1 2
  a13 : K 2 4 = -K 1 3

theorem einsteinRelations_of_ricci (K : Matrix (Fin 6) (Fin 6) ℝ) (hs : Kᵀ = K)
    (hr : ∀ j k, ricci (tensorOf K) j k = if j = k then 3 else 0) :
    EinsteinRelations K := by
  have hs10 : K 1 0 = K 0 1 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 1) hs
  have hs20 : K 2 0 = K 0 2 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 2) hs
  have hs21 : K 2 1 = K 1 2 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 2) hs
  have hs30 : K 3 0 = K 0 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 3) hs
  have hs31 : K 3 1 = K 1 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 3) hs
  have hs32 : K 3 2 = K 2 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 3) hs
  have hs40 : K 4 0 = K 0 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 4) hs
  have hs41 : K 4 1 = K 1 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 4) hs
  have hs42 : K 4 2 = K 2 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 4) hs
  have hs43 : K 4 3 = K 3 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 3 4) hs
  have hs50 : K 5 0 = K 0 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 5) hs
  have hs51 : K 5 1 = K 1 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 5) hs
  have hs52 : K 5 2 = K 2 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 5) hs
  have hs53 : K 5 3 = K 3 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 3 5) hs
  have hs54 : K 5 4 = K 4 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 4 5) hs
  have hr00 := hr 0 0
  have hr01 := hr 0 1
  have hr02 := hr 0 2
  have hr03 := hr 0 3
  have hr11 := hr 1 1
  have hr12 := hr 1 2
  have hr13 := hr 1 3
  have hr22 := hr 2 2
  have hr23 := hr 2 3
  have hr33 := hr 3 3
  simp [ricci, tensorOf, pairIndex, pairSign, Fin.sum_univ_succ,
    hs10, hs20, hs21, hs30, hs31, hs32, hs40, hs41, hs42, hs43, hs50, hs51, hs52, hs53, hs54] at hr00 hr01 hr02 hr03 hr11 hr12 hr13 hr22 hr23 hr33
  refine ⟨hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [hr00, hr01, hr02, hr03, hr11, hr12, hr13, hr22, hr23, hr33]
  · linarith only [hr00, hr01, hr02, hr03, hr11, hr12, hr13, hr22, hr23, hr33]
  · linarith only [hr00, hr01, hr02, hr03, hr11, hr12, hr13, hr22, hr23, hr33]
  · linarith only [hr00, hr01, hr02, hr03, hr11, hr12, hr13, hr22, hr23, hr33]
  · linarith only [hr00, hr01, hr02, hr03, hr11, hr12, hr13, hr22, hr23, hr33]
  · linarith only [hr00, hr01, hr02, hr03, hr11, hr12, hr13, hr22, hr23, hr33]
  · linarith only [hr00, hr01, hr02, hr03, hr11, hr12, hr13, hr22, hr23, hr33]
  · linarith only [hr00, hr01, hr02, hr03, hr11, hr12, hr13, hr22, hr23, hr33]
  · linarith only [hr00, hr01, hr02, hr03, hr11, hr12, hr13, hr22, hr23, hr33]

theorem blockTensor_apply (A : Mat3) (Q : Fin 3 → Mat4) (i j k l : Fin 4) :
    blockTensor A Q i j k l = (1 / 2 : ℝ) * ∑ s, ∑ t, A s t * Q s i j * Q t l k := by
  simp only [blockTensor, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, twoFormProduct, mul_assoc]

def blocksTensor (K : Matrix (Fin 6) (Fin 6) ℝ) : CurvatureArray :=
  blockTensor (plusFormula K) quaternionMatrix + blockTensor (minusFormula K) oppositeMatrix

theorem blocksTensor_row0 (K : Matrix (Fin 6) (Fin 6) ℝ) (h : EinsteinRelations K)
    (j : Fin 6) : matrixOf (blocksTensor K) 0 j = K 0 j := by
  have hs10 : K 1 0 = K 0 1 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 1) h.symmetric
  have hs20 : K 2 0 = K 0 2 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 2) h.symmetric
  have hs21 : K 2 1 = K 1 2 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 2) h.symmetric
  have hs30 : K 3 0 = K 0 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 3) h.symmetric
  have hs31 : K 3 1 = K 1 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 3) h.symmetric
  have hs32 : K 3 2 = K 2 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 3) h.symmetric
  have hs40 : K 4 0 = K 0 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 4) h.symmetric
  have hs41 : K 4 1 = K 1 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 4) h.symmetric
  have hs42 : K 4 2 = K 2 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 4) h.symmetric
  have hs43 : K 4 3 = K 3 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 3 4) h.symmetric
  have hs50 : K 5 0 = K 0 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 5) h.symmetric
  have hs51 : K 5 1 = K 1 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 5) h.symmetric
  have hs52 : K 5 2 = K 2 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 5) h.symmetric
  have hs53 : K 5 3 = K 3 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 3 5) h.symmetric
  have hs54 : K 5 4 = K 4 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 4 5) h.symmetric
  change blockTensor (plusFormula K) quaternionMatrix (pair 0).1 (pair 0).2
      (pair j).1 (pair j).2 +
    blockTensor (minusFormula K) oppositeMatrix (pair 0).1 (pair 0).2
      (pair j).1 (pair j).2 = K 0 j
  simp only [blockTensor_apply]
  fin_cases j <;>
    simp [pair,
      plusFormula, minusFormula, quaternionMatrix, oppositeMatrix, Geometry.oppositeQuaternion,
      Fin.sum_univ_succ, hs10, hs20, hs21, hs30, hs31, hs32, hs40, hs41, hs42, hs43, hs50, hs51, hs52, hs53, hs54,
      h.d0, h.d1, h.d2, h.a01, h.a02, h.a03, h.a04, h.a12, h.a13] <;> ring

theorem blocksTensor_row1 (K : Matrix (Fin 6) (Fin 6) ℝ) (h : EinsteinRelations K)
    (j : Fin 6) : matrixOf (blocksTensor K) 1 j = K 1 j := by
  have hs10 : K 1 0 = K 0 1 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 1) h.symmetric
  have hs20 : K 2 0 = K 0 2 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 2) h.symmetric
  have hs21 : K 2 1 = K 1 2 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 2) h.symmetric
  have hs30 : K 3 0 = K 0 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 3) h.symmetric
  have hs31 : K 3 1 = K 1 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 3) h.symmetric
  have hs32 : K 3 2 = K 2 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 3) h.symmetric
  have hs40 : K 4 0 = K 0 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 4) h.symmetric
  have hs41 : K 4 1 = K 1 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 4) h.symmetric
  have hs42 : K 4 2 = K 2 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 4) h.symmetric
  have hs43 : K 4 3 = K 3 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 3 4) h.symmetric
  have hs50 : K 5 0 = K 0 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 5) h.symmetric
  have hs51 : K 5 1 = K 1 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 5) h.symmetric
  have hs52 : K 5 2 = K 2 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 5) h.symmetric
  have hs53 : K 5 3 = K 3 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 3 5) h.symmetric
  have hs54 : K 5 4 = K 4 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 4 5) h.symmetric
  change blockTensor (plusFormula K) quaternionMatrix (pair 1).1 (pair 1).2
      (pair j).1 (pair j).2 +
    blockTensor (minusFormula K) oppositeMatrix (pair 1).1 (pair 1).2
      (pair j).1 (pair j).2 = K 1 j
  simp only [blockTensor_apply]
  fin_cases j <;>
    simp [pair,
      plusFormula, minusFormula, quaternionMatrix, oppositeMatrix, Geometry.oppositeQuaternion,
      Fin.sum_univ_succ, hs10, hs20, hs21, hs30, hs31, hs32, hs40, hs41, hs42, hs43, hs50, hs51, hs52, hs53, hs54,
      h.d0, h.d1, h.d2, h.a01, h.a02, h.a03, h.a04, h.a12, h.a13] <;> ring

theorem blocksTensor_row2 (K : Matrix (Fin 6) (Fin 6) ℝ) (h : EinsteinRelations K)
    (j : Fin 6) : matrixOf (blocksTensor K) 2 j = K 2 j := by
  have hs10 : K 1 0 = K 0 1 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 1) h.symmetric
  have hs20 : K 2 0 = K 0 2 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 2) h.symmetric
  have hs21 : K 2 1 = K 1 2 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 2) h.symmetric
  have hs30 : K 3 0 = K 0 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 3) h.symmetric
  have hs31 : K 3 1 = K 1 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 3) h.symmetric
  have hs32 : K 3 2 = K 2 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 3) h.symmetric
  have hs40 : K 4 0 = K 0 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 4) h.symmetric
  have hs41 : K 4 1 = K 1 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 4) h.symmetric
  have hs42 : K 4 2 = K 2 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 4) h.symmetric
  have hs43 : K 4 3 = K 3 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 3 4) h.symmetric
  have hs50 : K 5 0 = K 0 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 5) h.symmetric
  have hs51 : K 5 1 = K 1 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 5) h.symmetric
  have hs52 : K 5 2 = K 2 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 5) h.symmetric
  have hs53 : K 5 3 = K 3 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 3 5) h.symmetric
  have hs54 : K 5 4 = K 4 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 4 5) h.symmetric
  change blockTensor (plusFormula K) quaternionMatrix (pair 2).1 (pair 2).2
      (pair j).1 (pair j).2 +
    blockTensor (minusFormula K) oppositeMatrix (pair 2).1 (pair 2).2
      (pair j).1 (pair j).2 = K 2 j
  simp only [blockTensor_apply]
  fin_cases j <;>
    simp [pair,
      plusFormula, minusFormula, quaternionMatrix, oppositeMatrix, Geometry.oppositeQuaternion,
      Fin.sum_univ_succ, hs10, hs20, hs21, hs30, hs31, hs32, hs40, hs41, hs42, hs43, hs50, hs51, hs52, hs53, hs54,
      h.d0, h.d1, h.d2, h.a01, h.a02, h.a03, h.a04, h.a12, h.a13] <;> ring

theorem blocksTensor_row3 (K : Matrix (Fin 6) (Fin 6) ℝ) (h : EinsteinRelations K)
    (j : Fin 6) : matrixOf (blocksTensor K) 3 j = K 3 j := by
  have hs10 : K 1 0 = K 0 1 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 1) h.symmetric
  have hs20 : K 2 0 = K 0 2 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 2) h.symmetric
  have hs21 : K 2 1 = K 1 2 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 2) h.symmetric
  have hs30 : K 3 0 = K 0 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 3) h.symmetric
  have hs31 : K 3 1 = K 1 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 3) h.symmetric
  have hs32 : K 3 2 = K 2 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 3) h.symmetric
  have hs40 : K 4 0 = K 0 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 4) h.symmetric
  have hs41 : K 4 1 = K 1 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 4) h.symmetric
  have hs42 : K 4 2 = K 2 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 4) h.symmetric
  have hs43 : K 4 3 = K 3 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 3 4) h.symmetric
  have hs50 : K 5 0 = K 0 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 5) h.symmetric
  have hs51 : K 5 1 = K 1 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 5) h.symmetric
  have hs52 : K 5 2 = K 2 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 5) h.symmetric
  have hs53 : K 5 3 = K 3 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 3 5) h.symmetric
  have hs54 : K 5 4 = K 4 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 4 5) h.symmetric
  change blockTensor (plusFormula K) quaternionMatrix (pair 3).1 (pair 3).2
      (pair j).1 (pair j).2 +
    blockTensor (minusFormula K) oppositeMatrix (pair 3).1 (pair 3).2
      (pair j).1 (pair j).2 = K 3 j
  simp only [blockTensor_apply]
  fin_cases j <;>
    simp [pair,
      plusFormula, minusFormula, quaternionMatrix, oppositeMatrix, Geometry.oppositeQuaternion,
      Fin.sum_univ_succ, hs10, hs20, hs21, hs30, hs31, hs32, hs40, hs41, hs42, hs43, hs50, hs51, hs52, hs53, hs54,
      h.d0, h.d1, h.d2, h.a01, h.a02, h.a03, h.a04, h.a12, h.a13] <;> ring

theorem blocksTensor_row4 (K : Matrix (Fin 6) (Fin 6) ℝ) (h : EinsteinRelations K)
    (j : Fin 6) : matrixOf (blocksTensor K) 4 j = K 4 j := by
  have hs10 : K 1 0 = K 0 1 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 1) h.symmetric
  have hs20 : K 2 0 = K 0 2 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 2) h.symmetric
  have hs21 : K 2 1 = K 1 2 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 2) h.symmetric
  have hs30 : K 3 0 = K 0 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 3) h.symmetric
  have hs31 : K 3 1 = K 1 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 3) h.symmetric
  have hs32 : K 3 2 = K 2 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 3) h.symmetric
  have hs40 : K 4 0 = K 0 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 4) h.symmetric
  have hs41 : K 4 1 = K 1 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 4) h.symmetric
  have hs42 : K 4 2 = K 2 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 4) h.symmetric
  have hs43 : K 4 3 = K 3 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 3 4) h.symmetric
  have hs50 : K 5 0 = K 0 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 5) h.symmetric
  have hs51 : K 5 1 = K 1 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 5) h.symmetric
  have hs52 : K 5 2 = K 2 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 5) h.symmetric
  have hs53 : K 5 3 = K 3 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 3 5) h.symmetric
  have hs54 : K 5 4 = K 4 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 4 5) h.symmetric
  change blockTensor (plusFormula K) quaternionMatrix (pair 4).1 (pair 4).2
      (pair j).1 (pair j).2 +
    blockTensor (minusFormula K) oppositeMatrix (pair 4).1 (pair 4).2
      (pair j).1 (pair j).2 = K 4 j
  simp only [blockTensor_apply]
  fin_cases j <;>
    simp [pair,
      plusFormula, minusFormula, quaternionMatrix, oppositeMatrix, Geometry.oppositeQuaternion,
      Fin.sum_univ_succ, hs10, hs20, hs21, hs30, hs31, hs32, hs40, hs41, hs42, hs43, hs50, hs51, hs52, hs53, hs54,
      h.d0, h.d1, h.d2, h.a01, h.a02, h.a03, h.a04, h.a12, h.a13] <;> ring

theorem blocksTensor_row5 (K : Matrix (Fin 6) (Fin 6) ℝ) (h : EinsteinRelations K)
    (j : Fin 6) : matrixOf (blocksTensor K) 5 j = K 5 j := by
  have hs10 : K 1 0 = K 0 1 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 1) h.symmetric
  have hs20 : K 2 0 = K 0 2 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 2) h.symmetric
  have hs21 : K 2 1 = K 1 2 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 2) h.symmetric
  have hs30 : K 3 0 = K 0 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 3) h.symmetric
  have hs31 : K 3 1 = K 1 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 3) h.symmetric
  have hs32 : K 3 2 = K 2 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 3) h.symmetric
  have hs40 : K 4 0 = K 0 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 4) h.symmetric
  have hs41 : K 4 1 = K 1 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 4) h.symmetric
  have hs42 : K 4 2 = K 2 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 4) h.symmetric
  have hs43 : K 4 3 = K 3 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 3 4) h.symmetric
  have hs50 : K 5 0 = K 0 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 5) h.symmetric
  have hs51 : K 5 1 = K 1 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 5) h.symmetric
  have hs52 : K 5 2 = K 2 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 5) h.symmetric
  have hs53 : K 5 3 = K 3 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 3 5) h.symmetric
  have hs54 : K 5 4 = K 4 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 4 5) h.symmetric
  change blockTensor (plusFormula K) quaternionMatrix (pair 5).1 (pair 5).2
      (pair j).1 (pair j).2 +
    blockTensor (minusFormula K) oppositeMatrix (pair 5).1 (pair 5).2
      (pair j).1 (pair j).2 = K 5 j
  simp only [blockTensor_apply]
  fin_cases j <;>
    simp [pair,
      plusFormula, minusFormula, quaternionMatrix, oppositeMatrix, Geometry.oppositeQuaternion,
      Fin.sum_univ_succ, hs10, hs20, hs21, hs30, hs31, hs32, hs40, hs41, hs42, hs43, hs50, hs51, hs52, hs53, hs54,
      h.d0, h.d1, h.d2, h.a01, h.a02, h.a03, h.a04, h.a12, h.a13] <;> ring

theorem matrixOf_blocksTensor (K : Matrix (Fin 6) (Fin 6) ℝ) (h : EinsteinRelations K) :
    matrixOf (blocksTensor K) = K := by
  ext i j
  fin_cases i
  · exact blocksTensor_row0 K h j
  · exact blocksTensor_row1 K h j
  · exact blocksTensor_row2 K h j
  · exact blocksTensor_row3 K h j
  · exact blocksTensor_row4 K h j
  · exact blocksTensor_row5 K h j


theorem matrixOf_tensorOf (K : Matrix (Fin 6) (Fin 6) ℝ) : matrixOf (tensorOf K) = K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixOf, tensorOf, pair, pairSign, pairIndex]

theorem blockTensor_firstSkew (A : Mat3) (Q : Fin 3 → Mat4)
    (hQ : ∀ s, (Q s)ᵀ = -Q s) : FirstSkew (blockTensor A Q) := by
  intro i j k l
  have he (s : Fin 3) : Q s j i = -Q s i j :=
    congrArg (fun M : Mat4 => M i j) (hQ s)
  simp only [blockTensor_apply, he, mul_neg, neg_mul, Finset.sum_neg_distrib]

theorem blockTensor_lastSkew (A : Mat3) (Q : Fin 3 → Mat4)
    (hQ : ∀ s, (Q s)ᵀ = -Q s) : LastSkew (blockTensor A Q) := by
  intro i j k l
  have he (s : Fin 3) : Q s k l = -Q s l k :=
    congrArg (fun M : Mat4 => M l k) (hQ s)
  simp only [blockTensor_apply, he, mul_neg, Finset.sum_neg_distrib]

theorem blocksTensor_firstSkew (K : Matrix (Fin 6) (Fin 6) ℝ) : FirstSkew (blocksTensor K) := by
  intro i j k l
  change blockTensor (plusFormula K) quaternionMatrix j i k l +
      blockTensor (minusFormula K) oppositeMatrix j i k l = _
  rw [blockTensor_firstSkew _ _ quaternionMatrix_transpose,
    blockTensor_firstSkew _ _ QuaternionFrame.oppositeMatrix_transpose]
  simp only [blocksTensor, Pi.add_apply]
  ring

theorem blocksTensor_lastSkew (K : Matrix (Fin 6) (Fin 6) ℝ) : LastSkew (blocksTensor K) := by
  intro i j k l
  change blockTensor (plusFormula K) quaternionMatrix i j l k +
      blockTensor (minusFormula K) oppositeMatrix i j l k = _
  rw [blockTensor_lastSkew _ _ quaternionMatrix_transpose,
    blockTensor_lastSkew _ _ QuaternionFrame.oppositeMatrix_transpose]
  simp only [blocksTensor, Pi.add_apply]
  ring

theorem tensorOf_eq_blocksTensor (K : Matrix (Fin 6) (Fin 6) ℝ) (h : EinsteinRelations K) :
    tensorOf K = blocksTensor K := by
  apply tensor_eq_of_matrixOf_eq (tensorOf_firstSkew K) (tensorOf_lastSkew K)
    (blocksTensor_firstSkew K) (blocksTensor_lastSkew K)
  rw [matrixOf_tensorOf, matrixOf_blocksTensor K h]

/-- The Einstein block decomposition follows from ordinary algebraic
curvature symmetries and Ricci normalization, using the actual quaternion
contractions. No decomposition or sectional threshold is assumed. -/
theorem einstein_decomposition (R : CurvatureArray) (hf : FirstSkew R)
    (hl : LastSkew R) (hp : PairSymmetric R)
    (hr : ∀ j k, ricci R j k = if j = k then 3 else 0) :
    R = einsteinCurvatureTensor
      (curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) quaternionMatrix - 1)
      (curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) oppositeMatrix - 1) := by
  let K := matrixOf R
  have hn : tensorOf K = R := tensorOf_matrixOf hf hl
  have hk : EinsteinRelations K := einsteinRelations_of_ricci K (matrixOf_symmetric hp)
    (by intro j k; rw [hn]; exact hr j k)
  have hcplus : curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) quaternionMatrix =
      plusFormula K := by
    have hh := curvatureBlock_tensorOf K quaternionMatrix quaternionMatrix_transpose
    rw [plusFormula_eq] at hh
    simpa only [hn] using hh
  have hcminus : curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) oppositeMatrix =
      minusFormula K := by
    have hh := curvatureBlock_tensorOf K oppositeMatrix QuaternionFrame.oppositeMatrix_transpose
    rw [minusFormula_eq] at hh
    simpa only [hn] using hh
  calc
    R = tensorOf K := hn.symm
    _ = blocksTensor K := tensorOf_eq_blocksTensor K hk
    _ = _ := by
      rw [hcplus, hcminus]
      unfold blocksTensor einsteinCurvatureTensor
      have ha : (1 : Mat3) + (plusFormula K - 1) = plusFormula K := by abel
      have hb : (1 : Mat3) + (minusFormula K - 1) = minusFormula K := by abel
      rw [ha, hb]

theorem einstein_decomposition_of_bianchi (R : CurvatureArray) (hf : FirstSkew R)
    (hl : LastSkew R) (hb : FirstBianchi R)
    (hr : ∀ j k, ricci R j k = if j = k then 3 else 0) :
    R = einsteinCurvatureTensor
      (curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) quaternionMatrix - 1)
      (curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) oppositeMatrix - 1) :=
  einstein_decomposition R hf hl (pairSymmetric_of_bianchi hf hl hb) hr

theorem curvaturePairing_symmetric (R : CurvatureArray) (hf : FirstSkew R)
    (hl : LastSkew R) (hp : PairSymmetric R) (p q : Fin 4 × Fin 4) :
    R p.1 p.2 q.2 q.1 = R q.1 q.2 p.2 p.1 := by
  calc
    _ = R q.2 q.1 p.1 p.2 := (hp _ _ _ _).symm
    _ = -R q.1 q.2 p.1 p.2 := hf _ _ _ _
    _ = _ := by rw [hl]; simp

theorem curvatureBlock_sub_one_symmetric (R : CurvatureArray) (hf : FirstSkew R)
    (hl : LastSkew R) (hp : PairSymmetric R) (Q : Fin 3 → Mat4) :
    symmetric (curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) Q - 1) := by
  have hh := curvatureBlock_symmetric (curvaturePairing_symmetric R hf hl hp) Q
  have ht : (curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) Q - 1)ᵀ =
      curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) Q - 1 := by
    rw [Matrix.transpose_sub, hh, Matrix.transpose_one]
  intro i j
  exact congrArg (fun A : Mat3 => A j i) ht

end
end PositiveEinsteinFour.AlgebraicCurvature
end


section

/-! Contracting the differential Bianchi identity, with the same index
convention as the actual frame Ricci tensor. -/

namespace PositiveEinsteinFour.AlgebraicCurvature

open Angular
open scoped BigOperators

noncomputable section

def DifferentialBianchi (D : Fin 4 → CurvatureArray) : Prop :=
  ∀ a i j k l, D a i j k l + D i j a k l + D j a i k l = 0

theorem divergence_eq_ricci_derivatives (D : Fin 4 → CurvatureArray)
    (hp : ∀ a, PairSymmetric (D a)) (hl : ∀ a, LastSkew (D a))
    (hb : DifferentialBianchi D) (j k l : Fin 4) :
    (∑ i, D i i j k l) = -(∑ i, D k i j l i) + ∑ i, D l i k j i := by
  have he (i : Fin 4) : D i i j k l = -D k i j l i + D l i k j i := by
    have h := hb i k l i j
    rw [hp i i j k l, hp k i j l i, hl l i k j i] at h
    linarith only [h]
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]

theorem divergence_zero_of_ricci_parallel (D : Fin 4 → CurvatureArray)
    (hp : ∀ a, PairSymmetric (D a)) (hl : ∀ a, LastSkew (D a))
    (hb : DifferentialBianchi D)
    (hRic : ∀ a j k, ∑ i, D a i j k i = 0) (j k l : Fin 4) :
    (∑ i, D i i j k l) = 0 := by
  rw [divergence_eq_ricci_derivatives D hp hl hb, hRic k j l, hRic l k j]
  simp

end
end PositiveEinsteinFour.AlgebraicCurvature

end


section

/-! The zero-Ricci specialization for a derivative slice of curvature. -/

namespace PositiveEinsteinFour.AlgebraicCurvature

open Matrix TraceHessian Angular
open PositiveEinsteinFour.Geometry (curvatureBlock)
open scoped BigOperators

noncomputable section

theorem ricci_zero_blocks_traceFree (R : CurvatureArray) (hf : FirstSkew R)
    (hl : LastSkew R) (hb : FirstBianchi R)
    (hr : ∀ j, ricci R j j = 0) :
    traceFree (curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) quaternionMatrix) ∧
      traceFree (curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) oppositeMatrix) := by
  let K := matrixOf R
  have hn : tensorOf K = R := tensorOf_matrixOf hf hl
  have hs : Kᵀ = K := matrixOf_symmetric (pairSymmetric_of_bianchi hf hl hb)
  have hs50 : K 5 0 = K 0 5 := congrArg (fun A => A 0 5) hs
  have hs41 : K 4 1 = K 1 4 := congrArg (fun A => A 1 4) hs
  have hs32 : K 3 2 = K 2 3 := congrArg (fun A => A 2 3) hs
  have h0 := hr 0
  have h1 := hr 1
  have h2 := hr 2
  have h3 := hr 3
  have hcycle := hb 0 1 2 3
  rw [← hn] at h0 h1 h2 h3 hcycle
  simp [ricci, tensorOf, pairIndex, pairSign, Fin.sum_univ_succ] at h0 h1 h2 h3
  simp [tensorOf, pairIndex, pairSign, hs32] at hcycle
  have hcplus : curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) quaternionMatrix =
      plusFormula K := by
    have hh := curvatureBlock_tensorOf K quaternionMatrix quaternionMatrix_transpose
    rw [plusFormula_eq] at hh
    simpa only [hn] using hh
  have hcminus : curvatureBlock (fun p q => R p.1 p.2 q.2 q.1) oppositeMatrix =
      minusFormula K := by
    have hh := curvatureBlock_tensorOf K oppositeMatrix QuaternionFrame.oppositeMatrix_transpose
    rw [minusFormula_eq] at hh
    simpa only [hn] using hh
  rw [hcplus, hcminus]
  constructor
  · change (∑ i : Fin 3, plusFormula K i i) = 0
    simp [Fin.sum_univ_three, plusFormula, hs50, hs41, hs32]
    linarith only [h0, h1, h2, h3, hcycle]
  · change (∑ i : Fin 3, minusFormula K i i) = 0
    simp [Fin.sum_univ_three, minusFormula, hs50, hs41, hs32]
    linarith only [h0, h1, h2, h3, hcycle]

end
end PositiveEinsteinFour.AlgebraicCurvature
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureTensors02
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The zero-Ricci block reconstruction needed for the actual curvature derivative. -/

namespace PositiveEinsteinFour.AlgebraicCurvature

open Matrix TraceHessian Angular
open PositiveEinsteinFour.Geometry (curvatureBlock)
open scoped BigOperators

noncomputable section

theorem relations_of_ricci_zero (K : Matrix (Fin 6) (Fin 6) ℝ) (hs : Kᵀ = K)
    (hr : ∀ j k, ricci (tensorOf K) j k = 0) :
    EinsteinRelations K := by
  have hs10 : K 1 0 = K 0 1 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 1) hs
  have hs20 : K 2 0 = K 0 2 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 2) hs
  have hs21 : K 2 1 = K 1 2 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 2) hs
  have hs30 : K 3 0 = K 0 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 3) hs
  have hs31 : K 3 1 = K 1 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 3) hs
  have hs32 : K 3 2 = K 2 3 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 3) hs
  have hs40 : K 4 0 = K 0 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 4) hs
  have hs41 : K 4 1 = K 1 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 4) hs
  have hs42 : K 4 2 = K 2 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 4) hs
  have hs43 : K 4 3 = K 3 4 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 3 4) hs
  have hs50 : K 5 0 = K 0 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 0 5) hs
  have hs51 : K 5 1 = K 1 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 1 5) hs
  have hs52 : K 5 2 = K 2 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 2 5) hs
  have hs53 : K 5 3 = K 3 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 3 5) hs
  have hs54 : K 5 4 = K 4 5 :=
    congrArg (fun A : Matrix (Fin 6) (Fin 6) ℝ => A 4 5) hs
  have hr00 := hr 0 0
  have hr01 := hr 0 1
  have hr02 := hr 0 2
  have hr03 := hr 0 3
  have hr11 := hr 1 1
  have hr12 := hr 1 2
  have hr13 := hr 1 3
  have hr22 := hr 2 2
  have hr23 := hr 2 3
  have hr33 := hr 3 3
  simp [ricci, tensorOf, pairIndex, pairSign, Fin.sum_univ_succ,
    hs10, hs20, hs21, hs30, hs31, hs32, hs40, hs41, hs42, hs43, hs50, hs51, hs52, hs53, hs54] at hr00 hr01 hr02 hr03 hr11 hr12 hr13 hr22 hr23 hr33
  refine ⟨hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [hr00, hr01, hr02, hr03, hr11, hr12, hr13, hr22, hr23, hr33]
  · linarith only [hr00, hr01, hr02, hr03, hr11, hr12, hr13, hr22, hr23, hr33]
  · linarith only [hr00, hr01, hr02, hr03, hr11, hr12, hr13, hr22, hr23, hr33]
  · linarith only [hr00, hr01, hr02, hr03, hr11, hr12, hr13, hr22, hr23, hr33]
  · linarith only [hr00, hr01, hr02, hr03, hr11, hr12, hr13, hr22, hr23, hr33]
  · linarith only [hr00, hr01, hr02, hr03, hr11, hr12, hr13, hr22, hr23, hr33]
  · linarith only [hr00, hr01, hr02, hr03, hr11, hr12, hr13, hr22, hr23, hr33]
  · linarith only [hr00, hr01, hr02, hr03, hr11, hr12, hr13, hr22, hr23, hr33]
  · linarith only [hr00, hr01, hr02, hr03, hr11, hr12, hr13, hr22, hr23, hr33]


end
end PositiveEinsteinFour.AlgebraicCurvature
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_SphericalMeasureCharts
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact smooth coordinate-face charts and a Lipschitz projection for the
actual unit three-sphere. These are used only to establish finite positive
Hausdorff mass; no spherical integration formula is assumed. -/

namespace PositiveEinsteinFour.Angular

open EinsteinFour MeasureTheory
open scoped BigOperators ContDiff _root_.Topology NNReal

noncomputable section

abbrev ThreeSpace := EuclideanSpace ℝ (Fin 3)

def faceSign (t : Bool) : ℝ := if t then 1 else -1

theorem faceSign_ne_zero (t : Bool) : faceSign t ≠ 0 := by
  cases t <;> norm_num [faceSign]

def faceVector (i : Fin 4) (t : Bool) (u : ThreeSpace) : FourSpace :=
  WithLp.toLp 2 (Fin.insertNth i (faceSign t) (fun j => u j))

theorem faceVector_ne_zero (i : Fin 4) (t : Bool) (u : ThreeSpace) :
    faceVector i t u ≠ 0 := by
  intro h
  have hi := congrArg (fun v : FourSpace => v i) h
  exact faceSign_ne_zero t (by simpa [faceVector] using hi)

def faceChart (i : Fin 4) (t : Bool) (u : ThreeSpace) : FourSpace :=
  ‖faceVector i t u‖⁻¹ • faceVector i t u

end
end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_SphericalMeasureMass
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite positive mass of the actual Hausdorff measure on the unit
three-sphere, and hence the probability normalization used by the moments. -/

namespace PositiveEinsteinFour.Angular

open EinsteinFour MeasureTheory
open scoped BigOperators

noncomputable section

theorem threeSpace_hausdorff_haar :
    Measure.IsAddHaarMeasure (Measure.hausdorffMeasure 3 : Measure ThreeSpace) := by
  simpa [ThreeSpace] using
    (inferInstance : Measure.IsAddHaarMeasure
      (Measure.hausdorffMeasure (Module.finrank ℝ ThreeSpace) : Measure ThreeSpace))

/-- Hausdorff measure on the subtype agrees with the ambient measure. -/
theorem direction_hausdorff_mass_eq :
    (Measure.hausdorffMeasure 3 : Measure Directions) Set.univ =
      (Measure.hausdorffMeasure 3 : Measure FourSpace) {v | ‖v‖ = 1} := by
  have hr : (Subtype.val : Directions → FourSpace) '' Set.univ = {v | ‖v‖ = 1} := by
    ext v
    simp
  rw [← hr]
  exact (Isometry.hausdorffMeasure_image
    (show Isometry (Subtype.val : Directions → FourSpace) from isometry_subtype_coe)
    (Or.inl (by norm_num : (0 : ℝ) ≤ 3)) Set.univ).symm

end
end PositiveEinsteinFour.Angular

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates03
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Compactness of the four-dimensional orthogonal matrix parameter used
in the local orthonormal-frame trivializations. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators

noncomputable section

abbrev OrthogonalFour := {S : Mat4 // Sᵀ * S = 1}

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.MeasureTheory_Function_LpSpace_Restrict
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `RellichKondrachov.MeasureTheory.Function.LpSpace.Restrict`

`L^p` extension-by-zero maps for restricted measures.

Mathlib provides the equivalence

`MemLp (s.indicator f) p μ ↔ MemLp f p (μ.restrict s)`

(`MeasureTheory.memLp_indicator_iff_restrict`). This file packages the corresponding map on `Lp`
spaces:

`Lp E p (μ.restrict s) →ₗᵢ[ℝ] Lp E p μ`,

given by extension-by-zero (via `Set.indicator`).

## Main definitions

- `MeasureTheory.Lp.extendByZeroₗ`
- `MeasureTheory.Lp.extendByZeroₗᵢ`
-/

namespace MeasureTheory

open scoped ENNReal

namespace Lp

noncomputable section

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {s : Set α} (hs : MeasurableSet s)

noncomputable def extendByZeroFun (f : Lp E p (μ.restrict s)) : Lp E p μ :=
  let hf : MemLp (fun x : α => f x) p (μ.restrict s) := Lp.memLp f
  let hfi : MemLp (s.indicator fun x : α => f x) p μ :=
    (memLp_indicator_iff_restrict (μ := μ) (p := p) (s := s) (f := fun x : α => f x) hs).2 hf
  hfi.toLp (s.indicator fun x : α => f x)

omit [NormedSpace ℝ E] [Fact (1 ≤ p)] in
lemma extendByZeroFun_coe (f : Lp E p (μ.restrict s)) :
    extendByZeroFun (μ := μ) (p := p) (s := s) hs f =ᵐ[μ] s.indicator fun x : α => f x := by
  dsimp [extendByZeroFun]
  exact MemLp.coeFn_toLp _

/-- Extension-by-zero as a linear map `Lp E p (μ.restrict s) →ₗ[ℝ] Lp E p μ`. -/
noncomputable def extendByZeroₗ : Lp E p (μ.restrict s) →ₗ[ℝ] Lp E p μ where
  toFun := extendByZeroFun (μ := μ) (p := p) (s := s) hs
  map_add' f g := by
    classical
    -- Prove equality by comparing pointwise representatives.
    refine Lp.ext ?_
    have h_add_restrict :
        (fun x : α => (f + g) x) =ᵐ[μ.restrict s] fun x : α => f x + g x := by
      exact Lp.coeFn_add (μ := μ.restrict s) f g
    have h_add_on :
        ∀ᵐ x : α ∂μ, x ∈ s → (f + g) x = f x + g x :=
      (ae_restrict_iff' (μ := μ) (s := s) hs).1 h_add_restrict
    filter_upwards
      [ extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs (f + g)
      , extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs f
      , extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs g
      , coeFn_add (extendByZeroFun (μ := μ) (p := p) (s := s) hs f)
          (extendByZeroFun (μ := μ) (p := p) (s := s) hs g)
      , h_add_on
      ] with x hfg hf hg hadd hsum
    by_cases hx : x ∈ s
    · have hsum' := hsum hx
      have hadd' :
          extendByZeroFun (μ := μ) (p := p) (s := s) hs f x +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g x =
            (extendByZeroFun (μ := μ) (p := p) (s := s) hs f +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g) x := by
        simpa [Pi.add_apply] using hadd.symm
      calc
        extendByZeroFun (μ := μ) (p := p) (s := s) hs (f + g) x
            = s.indicator (fun x : α => (f + g) x) x := hfg
        _ = (f + g) x := by simp [Set.indicator_of_mem, hx]
        _ = f x + g x := hsum'
        _ = s.indicator (fun x : α => f x) x + s.indicator (fun x : α => g x) x := by
            simp [Set.indicator_of_mem, hx]
        _ = extendByZeroFun (μ := μ) (p := p) (s := s) hs f x +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g x := by
            simp [hf, hg]
        _ = (extendByZeroFun (μ := μ) (p := p) (s := s) hs f +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g) x := hadd'
    ·
      have hadd' :
          extendByZeroFun (μ := μ) (p := p) (s := s) hs f x +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g x =
            (extendByZeroFun (μ := μ) (p := p) (s := s) hs f +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g) x := by
        simpa [Pi.add_apply] using hadd.symm
      calc
        extendByZeroFun (μ := μ) (p := p) (s := s) hs (f + g) x
            = s.indicator (fun x : α => (f + g) x) x := hfg
        _ = 0 := by simp [Set.indicator_of_notMem, hx]
        _ = extendByZeroFun (μ := μ) (p := p) (s := s) hs f x +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g x := by
            -- both summands are zero off `s`
            simp [Set.indicator_of_notMem, hx, hf, hg]
        _ = (extendByZeroFun (μ := μ) (p := p) (s := s) hs f +
              extendByZeroFun (μ := μ) (p := p) (s := s) hs g) x := hadd'
  map_smul' c f := by
    classical
    refine Lp.ext ?_
    have h_smul_restrict :
        (fun x : α => (c • f) x) =ᵐ[μ.restrict s] fun x : α => c • f x := by
      exact Lp.coeFn_smul (μ := μ.restrict s) c f
    have h_smul_on :
        ∀ᵐ x : α ∂μ, x ∈ s → (c • f) x = c • f x :=
      (ae_restrict_iff' (μ := μ) (s := s) hs).1 h_smul_restrict
    filter_upwards
      [ extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs (c • f)
      , extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs f
      , coeFn_smul c (extendByZeroFun (μ := μ) (p := p) (s := s) hs f)
      , h_smul_on
      ] with x hcf hf hsmul hsum
    by_cases hx : x ∈ s
    · have hsum' := hsum hx
      have hsmul' :
          c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f x =
            (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x := by
        simpa [Pi.smul_apply] using hsmul.symm
      calc
        extendByZeroFun (μ := μ) (p := p) (s := s) hs (c • f) x
            = s.indicator (fun x : α => (c • f) x) x := hcf
        _ = (c • f) x := by simp [Set.indicator_of_mem, hx]
        _ = c • f x := hsum'
        _ = c • s.indicator (fun x : α => f x) x := by simp [Set.indicator_of_mem, hx]
        _ = c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f x := by simp [hf]
        _ = (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x := hsmul'
    ·
      have hsmul' :
          c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f x =
            (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x := by
        simpa [Pi.smul_apply] using hsmul.symm
      calc
        extendByZeroFun (μ := μ) (p := p) (s := s) hs (c • f) x
            = s.indicator (fun x : α => (c • f) x) x := hcf
        _ = 0 := by simp [Set.indicator_of_notMem, hx]
        _ = (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x := by
            have hf0 :
                extendByZeroFun (μ := μ) (p := p) (s := s) hs f x = 0 := by
              simpa [Set.indicator_of_notMem, hx] using hf
            have hcx :
                (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x = 0 := by
              calc
                (c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f) x =
                    c • extendByZeroFun (μ := μ) (p := p) (s := s) hs f x := by
                      simpa [Pi.smul_apply] using hsmul
                _ = 0 := by simp [hf0]
            simpa using hcx.symm

/-- Extension-by-zero as a linear isometry. -/
noncomputable def extendByZeroₗᵢ : Lp E p (μ.restrict s) →ₗᵢ[ℝ] Lp E p μ where
  toLinearMap := extendByZeroₗ (μ := μ) (p := p) (s := s) hs
  norm_map' f := by
    classical
    -- Unfold into `MemLp.toLp` and reduce to `eLpNorm_indicator_eq_eLpNorm_restrict`.
    have hfi :
        MemLp (s.indicator fun x : α => f x) p μ :=
      (memLp_indicator_iff_restrict (μ := μ) (p := p) (s := s)
        (f := fun x : α => f x) hs).2 (Lp.memLp f)
    -- Norm in the codomain is the `eLpNorm` of the indicator.
    have hnorm_out :
        ‖extendByZeroₗ (μ := μ) (p := p) (s := s) hs f‖ =
          ENNReal.toReal (eLpNorm (s.indicator fun x : α => f x) p μ) := by
      dsimp [extendByZeroₗ, extendByZeroFun]
      simp [norm_toLp (f := s.indicator (fun x : α => f x)) hfi]
    -- Rewrite the `eLpNorm` of the indicator as a restricted `eLpNorm`.
    have hnorm_restrict :
        eLpNorm (s.indicator fun x : α => f x) p μ =
          eLpNorm (fun x : α => f x) p (μ.restrict s) := by
      simpa using (eLpNorm_indicator_eq_eLpNorm_restrict (μ := μ) (p := p) (s := s)
        (f := fun x : α => f x) hs)
    -- Combine with the definition of the `Lp` norm on the restricted space.
    simp [hnorm_out, hnorm_restrict, norm_def]

lemma extendByZeroₗᵢ_ae_eq (f : Lp E p (μ.restrict s)) :
    ((extendByZeroₗᵢ (μ := μ) (p := p) (s := s) hs) f : α → E) =ᵐ[μ]
      s.indicator fun x : α => f x := by
  -- Unfold to the underlying `extendByZeroFun` and use the defining AE equality.
  simpa [extendByZeroₗᵢ, extendByZeroₗ] using
    (extendByZeroFun_coe (μ := μ) (p := p) (s := s) hs f)

end

end Lp

end MeasureTheory
end


