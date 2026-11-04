-- Prove2me | Definitions.Def_FreeGroupFactorProof31
-- name    : FreeGroupFactorProof31
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T05:03:21.373571+00:00
-- url     : https://prove2.me/theorems/42f6ce1f-93ac-47e0-9dc7-c64da76460b3
-- title:
--   Free group factors: supporting development, part 31
-- statement:
--   Part 31 of the supporting Lean development for the isomorphism of all interpolated free group factors. It continues the chain of earlier parts and contains proved upstream lemmas on the polynomial flow and on corners of the stabilization, with the declarations they rest on, in source order. No result is assumed.
--
--   **Formalization Note** Eight of these lemmas were first published as child theorems, but the platform's target-type check rejected their universe-polymorphic solutions even though the solution type and the published statement have the same elaborated term locally. They are therefore proved here, so that the parent theorems can use them. The code is OpenAI's, carved from `lean/OAI/Analysis/FreeGroupFactor` and `lean/OAI/Analysis/InterpolatedFactors` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0)

import Mathlib
import Definitions.Def_FreeGroupFactorProof30

set_option linter.all false

section
namespace OAI

noncomputable section

universe uA uι uκ

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff ENNReal

attribute [local instance] Classical.propDecidable

namespace FreeGroupFactorMain.FiniteActive

section
open UnitaryEvaluation
open scoped ENNReal

end
open UnitaryEvaluation

end FreeGroupFactorMain.FiniteActive

namespace FreeGroupFactorMain.UnitaryEvaluation
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι} {κ : Type uκ}

end FreeGroupFactorMain.UnitaryEvaluation

namespace FreeGroupFactorMain.FiniteActive

section
open UnitaryEvaluation
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

theorem displacement (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ) (h0 : l 0 = 0)
    (hS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l))
    (K : ℝ) (hK : 0 ≤ K)
    (hn : ‖laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l‖ ≤ K) :
    ∃ β : Ambient ι κ ≃⋆ₐ[ℂ] Ambient ι κ,
      (∀ T, canonicalTrace (β T) = canonicalTrace T) ∧
      @Continuous _ _ (groupUltraweakTopology (FreeGroup (Option (ι ⊕ κ))))
        (groupUltraweakTopology (FreeGroup (Option (ι ⊕ κ)))) β ∧
      β (groupUnitary (FreeGroup.of none)) = groupUnitary (FreeGroup.of none) ∧
      (∀ k : κ, β (groupUnitary (FreeGroup.of (some (Sum.inr k)))) =
        groupUnitary (FreeGroup.of (some (Sum.inr k)))) ∧
      (∀ i : ι, ‖β (groupUnitary (FreeGroup.of (some (Sum.inl i) : Option (ι ⊕ κ)))) -
        groupUnitary (FreeGroup.of (some (Sum.inl i) : Option (ι ⊕ κ)))‖ ≤
          3*K*Real.sqrt ((h i).sum (fun _ r => r^2))) ∧
      ∀ w : FreeGroup ι, ‖β (groupUnitary (FreeGroup.map (fun i => some (Sum.inl i)) w)) -
        NormedSpace.exp (Complex.I • laurentValue (generatorUnitary (none : Option (ι ⊕ κ))) l) *
          groupUnitary (FreeGroup.map (fun i => some (Sum.inl i)) w)‖ ≤
            3*K*Real.sqrt ((freeCocycle h w - Finsupp.single 1 1).sum (fun _ r => r^2)) := by
  obtain ⟨U,hU₀,hX,hbound,β,hβt,hβc,hβ⟩ := bounded_flow (ι := ι) (κ := κ) h l h0 hS K hK hn
  obtain ⟨hgen,hword⟩ := displacements_from_bounds (ι := ι) (κ := κ) h l hS K U hU₀ hX hbound
  refine ⟨β,hβt,hβc,?_,?_,?_,?_⟩
  · exact (hβ (FreeGroup.of (none : Option (ι ⊕ κ)))).trans (wordHom_of _ _)
  · intro k
    exact (hβ (FreeGroup.of (some (Sum.inr k) : Option (ι ⊕ κ)))).trans (wordHom_of _ _)
  · intro i
    rw [hβ]
    simpa only [wordHom_of,extendUnitary,Option.elim_some,tuple,Sum.elim_inl] using hgen i
  · intro w
    rw [hβ]
    simpa only [wordHom_tuple_active] using hword w

end

open UnitaryEvaluation

 theorem one_step_from_laurent {κ : Type uκ} [DecidableEq κ]
    (n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (l : ℤ →₀ ℂ) (hl0 : l 0 = 0)
    (hlS : IsSelfAdjoint (laurentValue (generatorUnitary (none : Option (Fin n ⊕ κ))) l))
    (hln : ‖laurentValue (generatorUnitary (none : Option (Fin n ⊕ κ))) l‖ ≤ 2*(Real.pi+1))
    (z : unitary ℂ) (hze : twoNorm (NormedSpace.exp (Complex.I • laurentValue
      (generatorUnitary (none : Option (Fin n ⊕ κ))) l) -
        (z : ℂ) • groupUnitary (FreeGroup.of none)) < ε/2)
    (w : FreeGroup (Fin n)) (h : Coeff (FreeGroup (Fin n)))
    (hh : coefficientNorm h < (ε/2)/(3*(2*(Real.pi+1))))
    (hw : coefficientNorm (freeCocycle (firstCoefficients h) w-Finsupp.single 1 1) <
      (ε/2)/(3*(2*(Real.pi+1)))) :
    ∃ α : Ambient (Fin n) κ ≃⋆ₐ[ℂ] Ambient (Fin n) κ,
      (∀ T, canonicalTrace (α T) = canonicalTrace T) ∧
      (∀ k : κ, α (groupUnitary (FreeGroup.of (some (Sum.inr k)))) =
        groupUnitary (FreeGroup.of (some (Sum.inr k)))) ∧
      ∃ w : FreeGroup (Fin n),
        (∀ i : Fin n, ‖α (groupUnitary (FreeGroup.of (some (Sum.inl i)))) -
          groupUnitary (FreeGroup.of (some (Sum.inl i)))‖ < ε) ∧
        twoNorm (α (groupUnitary (FreeGroup.map (fun i => some (Sum.inl i)) w)) -
          groupUnitary (FreeGroup.of none)) < ε := by
  let K : ℝ := 2*(Real.pi+1)
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨β,hβt,_hβn,_hβC,hβpass,hβgen,hβword⟩ :=
    displacement (κ := κ) (firstCoefficients h) l hl0 hlS K hK.le hln
  obtain ⟨γ,hγt,_hγn,_hγi,hγgen,hγC⟩ :=
    gauged_nielsen_iso (ι := Fin n ⊕ κ) (FreeGroup.map Sum.inl w) z
  have hmap : FreeGroup.map (Option.some : Fin n ⊕ κ → Option (Fin n ⊕ κ))
      (FreeGroup.map Sum.inl w) = FreeGroup.map (fun i => some (Sum.inl i)) w := by
    have he : (FreeGroup.map (Option.some : Fin n ⊕ κ → Option (Fin n ⊕ κ))).comp
        (FreeGroup.map Sum.inl) = FreeGroup.map (fun i => some (Sum.inl i)) := by
      apply FreeGroup.ext_hom
      intro i
      simp
    exact DFunLike.congr_fun he w
  rw [hmap] at hγC
  refine ⟨β.trans γ.symm,?_,?_,w,?_,?_⟩
  · intro T
    change canonicalTrace (γ.symm (β T)) = canonicalTrace T
    rw [trace_symm γ hγt,hβt]
  · intro k
    change γ.symm (β (groupUnitary (FreeGroup.of (some (Sum.inr k))))) = _
    rw [hβpass,← hγgen (Sum.inr k),γ.symm_apply_apply]
    exact (hγgen (Sum.inr k)).symm
  · intro i
    exact one_step_generator_estimate β γ _ (hγgen (Sum.inl i)) hK hε (hβgen i)
      ((firstCoefficients_norm_le h i).trans_lt hh)
  · exact one_step_word_estimate β γ hγt
      (generatorUnitary (none : Option (Fin n ⊕ κ)))
      (groupUnitaryUHom (FreeGroup (Option (Fin n ⊕ κ)))
        (FreeGroup.map (fun i => some (Sum.inl i)) w))
      _ z hγC hK (hβword w) hw hze

end FreeGroupFactorMain.FiniteActive

end

end OAI
end

section
namespace OAI

noncomputable section

namespace FreeGroupFactorMain

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24
universe u_25 u_26 u_27 u_28 u_29 u_30 u_31 u_32 u_33 u_34 u_35 u_36
universe u_37 u_38 u_39 u_40 u_41 u_42 u_43 u_44 u_45

namespace Amplification

section

variable {A : Type u_1} {B : Type u_2} [CStarAlgebra A] [CStarAlgebra B]

end

section
variable {A : Type u_3} {B : Type u_4} [CStarAlgebra A] [CStarAlgebra B]

end

open scoped ENNReal

end Amplification

namespace FreeFock
open scoped ENNReal

variable {α : Type u_15} {β : Type u_16} [DecidableEq α] [DecidableEq β]

end FreeFock
open Filter Topology

namespace Amplification

section
variable {A : Type u_17} {B : Type u_18} [CStarAlgebra A] [CStarAlgebra B]

variable (M : StarSubalgebra ℂ A) [IsClosed (M : Set A)]
variable (p : M) (hp : IsStarProjection p)

variable {E : Type u_19} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section
open scoped ENNReal ComplexConjugate
attribute [local instance] OAI.FreeGroupFactorMain.Amplification.instDecidableEqNestedHilbert

variable {I : Type u_21} {J : Type u_22}
abbrev NestedHilbert (I : Type u_23) (J : Type u_24) := lp (fun _ : I => GroupHilbert J) 2

def nestedDirac (ij : I × J) : NestedHilbert I J := by
  classical
  exact lp.single 2 ij.1 (lp.single 2 ij.2 1)

theorem nestedDirac_inner (x y : I × J) :
    inner ℂ (nestedDirac x) (nestedDirac y) = if x = y then 1 else 0 := by
  classical
  rcases x with ⟨i,j⟩
  rcases y with ⟨k,l⟩
  by_cases hik : i = k
  · subst k
    simp [nestedDirac,lp.inner_single_left,lp.single_apply,Pi.single_apply,RCLike.inner_apply]
  · simp [nestedDirac,lp.inner_single_left,lp.single_apply,hik]

theorem nestedDirac_inner_apply (ij : I × J) (ξ : NestedHilbert I J) :
    inner ℂ (nestedDirac ij) ξ = ξ ij.1 ij.2 := by
  classical
  simp [nestedDirac,lp.inner_single_left,RCLike.inner_apply]

theorem nestedDirac_orthogonal :
    (Submodule.span ℂ (Set.range (nestedDirac (I := I) (J := J))))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro ξ hξ
  apply show ξ = 0 → ξ ∈ (⊥ : Submodule ℂ (NestedHilbert I J)) from fun h => h ▸ Submodule.zero_mem _
  ext i j
  have hh := ((Submodule.mem_orthogonal _ _).mp hξ) (nestedDirac (i,j))
    (Submodule.subset_span (Set.mem_range_self (i,j)))
  simpa only [nestedDirac_inner_apply,lp.coeFn_zero,Pi.zero_apply] using hh

def nestedBasis (I : Type u_25) (J : Type u_26) : HilbertBasis (I × J) ℂ (NestedHilbert I J) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_iff_ite.mpr nestedDirac_inner) nestedDirac_orthogonal

@[simp] theorem nestedBasis_apply (ij : I × J) : nestedBasis I J ij = nestedDirac ij := by
  simp [nestedBasis]

def hilbertFlatten (I : Type u_27) (J : Type u_28) : NestedHilbert I J ≃ₗᵢ[ℂ] GroupHilbert (I × J) :=
  (nestedBasis I J).repr

@[simp] theorem hilbertFlatten_apply (ξ : NestedHilbert I J) (ij : I × J) :
    hilbertFlatten I J ξ ij = ξ ij.1 ij.2 := by
  rw [hilbertFlatten,HilbertBasis.repr_apply_apply,nestedBasis_apply,nestedDirac_inner_apply]

@[simp] theorem hilbertFlatten_symm_apply (ξ : GroupHilbert (I × J)) (i : I) (j : J) :
    (hilbertFlatten I J).symm ξ i j = ξ (i,j) := by
  have hh := congrArg (fun v : GroupHilbert (I × J) => v (i,j))
    ((hilbertFlatten I J).apply_symm_apply ξ)
  simpa only [hilbertFlatten_apply] using hh

def diagonalValue (A : GroupOperator J) (ξ : NestedHilbert I J) : NestedHilbert I J :=
  ⟨fun i => A (ξ i),((lp.memℓp ξ).norm.const_smul ‖A‖).mono (fun i => A.le_opNorm (ξ i))⟩

theorem diagonalValue_norm_le (A : GroupOperator J) (ξ : NestedHilbert I J) :
    ‖diagonalValue A ξ‖ ≤ ‖A‖*‖ξ‖ := by
  have hh := lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0) (x := diagonalValue A ξ) (y := (‖A‖ : ℝ) • ξ) (fun i => by
    change ‖A (ξ i)‖ ≤ ‖(‖A‖ : ℝ) • ξ i‖
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg A)] using A.le_opNorm (ξ i))
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg A)] using hh

theorem diagonalValue_add (operator : GroupOperator J) (left right : NestedHilbert I J) :
    diagonalValue operator (left + right) = diagonalValue operator left + diagonalValue operator right := by
  ext row column
  exact congrArg (fun vector : GroupHilbert J => vector column)
    (map_add operator (left row) (right row))

theorem diagonalValue_smul (operator : GroupOperator J) (scalar : ℂ) (vector : NestedHilbert I J) :
    diagonalValue operator (scalar • vector) = scalar • diagonalValue operator vector := by
  ext row column
  exact congrArg (fun image : GroupHilbert J => image column)
    (map_smul operator scalar (vector row))

theorem continuous_diagonalValue (operator : GroupOperator J) :
    Continuous (diagonalValue (I := I) operator) :=
  (LinearMap.mkContinuous
    { toFun := diagonalValue operator
      map_add' := diagonalValue_add operator
      map_smul' := diagonalValue_smul operator }
    ‖operator‖ (diagonalValue_norm_le operator) :
      NestedHilbert I J →L[ℂ] NestedHilbert I J).continuous

def diagonalOp (I : Type u_29) (A : GroupOperator J) :
    NestedHilbert I J →L[ℂ] NestedHilbert I J where
  toFun := diagonalValue A
  map_add' := diagonalValue_add A
  map_smul' := diagonalValue_smul A
  cont := continuous_diagonalValue A

@[simp] theorem diagonalOp_apply (A : GroupOperator J) (ξ : NestedHilbert I J) (i : I) :
    diagonalOp I A ξ i = A (ξ i) := rfl

theorem diagonalOp_star (A : GroupOperator J) :
    diagonalOp I (star A) = star (diagonalOp I A) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply ext_inner_right ℂ
  intro η
  change inner ℂ (diagonalOp I (star A) ξ) η =
    inner ℂ ((ContinuousLinearMap.adjoint (diagonalOp I A)) ξ) η
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [lp.inner_eq_tsum,diagonalOp_apply]
  apply tsum_congr
  intro i
  simpa only [ContinuousLinearMap.star_eq_adjoint,lp.inner_eq_tsum] using ContinuousLinearMap.adjoint_inner_left A (η i) (ξ i)

def diagonalHom (I : Type u_30) (J : Type u_31) : GroupOperator J →⋆ₐ[ℂ] (NestedHilbert I J →L[ℂ] NestedHilbert I J) where
  toFun := diagonalOp I
  map_one' := by ext ξ i j; rfl
  map_mul' A B := by ext ξ i j; rfl
  map_zero' := by ext ξ i j; rfl
  map_add' A B := by ext ξ i j; rfl
  commutes' z := by ext ξ i j; rfl
  map_star' := diagonalOp_star

def productAmplification (I : Type u_32) (J : Type u_33) : GroupOperator J →⋆ₐ[ℂ] GroupOperator (I × J) :=
  (hilbertFlatten I J).conjStarAlgEquiv.toStarAlgHom.comp (diagonalHom I J)

@[simp] theorem productAmplification_apply (A : GroupOperator J) (ξ : GroupHilbert (I × J))
    (i : I) (j : J) :
    productAmplification I J A ξ (i,j) =
      A ((hilbertFlatten I J).symm ξ i) j := by
  change hilbertFlatten I J (diagonalOp I A ((hilbertFlatten I J).symm ξ)) (i,j) = _
  rw [hilbertFlatten_apply,diagonalOp_apply]

end
section
open scoped ENNReal

variable {I : Type u_35} {J : Type u_36}

variable {G : Type u_37} [Group G]

theorem stabilizedRightTranslations_eq_range :
    stabilizedRightTranslations G = Set.range (fun g : G => productAmplification ℕ G (rightRegular g)) := by
  ext T
  constructor
  · rintro ⟨g,hg⟩
    refine ⟨g,?_⟩
    apply ContinuousLinearMap.ext
    intro ξ
    ext x
    rw [hg]
    rcases x with ⟨i,j⟩
    simp only [productAmplification_apply,rightRegular_apply,hilbertFlatten_symm_apply]
  · rintro ⟨g,rfl⟩
    refine ⟨g,?_⟩
    intro ξ x
    rcases x with ⟨i,j⟩
    simp only [productAmplification_apply,rightRegular_apply,hilbertFlatten_symm_apply]

end

section
open scoped ENNReal
variable {G : Type u_38}

variable [Group G]

end

open scoped ENNReal
variable {G : Type u_45} [Group G]

end Amplification

namespace Interpolation

open Amplification
open scoped ENNReal

end Interpolation

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

namespace FreeGroupFactorMain.Amplification.Polar

section

variable {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end
section
variable {E : Type u_3} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end
section
variable {E : Type u_4} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

 theorem partialIsometry_nonzero {T : Operator E} (hT : T ≠ 0) : partialIsometry T ≠ 0 := by
  intro h
  apply hT
  rw [← partialIsometry_factorization T,h,zero_mul]

end
variable {E : Type u_5} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end FreeGroupFactorMain.Amplification.Polar

namespace FreeGroupFactorMain.WeightedFock
open FreeFock
open Amplification.Polar
variable {ι : Type u_6} [DecidableEq ι]

end FreeGroupFactorMain.WeightedFock
namespace FreeGroupFactorMain.Amplification.Polar
variable {E : Type u_7} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end FreeGroupFactorMain.Amplification.Polar
namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock
open Amplification.Polar
variable {ι : Type u_8} [DecidableEq ι]

end
open FreeFock
open scoped ENNReal
open Amplification.Polar
variable {ι : Type u_9} [DecidableEq ι]

end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24
universe u_25 u_26 u_27 u_28 u_29 u_30 u_31

namespace FreeGroupFactorMain
namespace InfiniteICC

end InfiniteICC

end FreeGroupFactorMain

namespace FreeGroupFactorMain.Amplification

section
variable {A : Type u_9} [CStarAlgebra A]

def equivalentCorner (p q : A) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (u : A) (hu : star u*u=p) (hu' : u*star u=q) : Corner p hp ≃⋆ₐ[ℂ] Corner q hq where
  toFun x := ⟨u*(x : A)*star u,by
    constructor
    · rw [← hu']
      calc
        (u*star u)*(u*(x : A)*star u) = u*((star u*u)*(x : A))*star u := by noncomm_ring
        _ = u*(x : A)*star u := by rw [hu,x.property.1]
    · rw [← hu']
      calc
        (u*(x : A)*star u)*(u*star u) = u*((x : A)*(star u*u))*star u := by noncomm_ring
        _ = u*(x : A)*star u := by rw [hu,x.property.2]⟩
  invFun y := ⟨star u*(y : A)*u,by
    constructor
    · rw [← hu]
      calc
        (star u*u)*(star u*(y : A)*u) = star u*((u*star u)*(y : A))*u := by noncomm_ring
        _ = star u*(y : A)*u := by rw [hu',y.property.1]
    · rw [← hu]
      calc
        (star u*(y : A)*u)*(star u*u) = star u*((y : A)*(u*star u))*u := by noncomm_ring
        _ = star u*(y : A)*u := by rw [hu',y.property.2]⟩
  left_inv x := by
    apply Subtype.ext
    change star u*(u*(x : A)*star u)*u = (x : A)
    rw [← mul_assoc,← mul_assoc,hu,x.property.1,mul_assoc,hu,x.property.2]
  right_inv y := by
    apply Subtype.ext
    change u*(star u*(y : A)*u)*star u = (y : A)
    rw [← mul_assoc,← mul_assoc,hu',y.property.1,mul_assoc,hu',y.property.2]
  map_mul' x y := by
    apply Subtype.ext
    change u*((x : A)*(y : A))*star u = (u*(x : A)*star u)*(u*(y : A)*star u)
    simp only [mul_assoc]
    rw [← mul_assoc (star u),hu,← mul_assoc p,y.property.1]
  map_add' x y := by
    apply Subtype.ext
    change u*((x : A)+(y : A))*star u = _
    simp only [mul_add,add_mul]
    rfl
  map_smul' z x := by
    apply Subtype.ext
    change u*(z • (x : A))*star u = _
    simp only [mul_smul_comm,smul_mul_assoc]
    rfl
  map_star' x := by
    apply Subtype.ext
    change u*star (x : A)*star u = star (u*(x : A)*star u)
    simp only [star_mul,star_star,mul_assoc]

 theorem equivalentCorner_normal (p q : A) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (u : A) (hu : star u*u=p) (hu' : u*star u=q)
    (𝒯 : TopologicalSpace A)
    (hmul : @Continuous _ _ 𝒯 𝒯 (fun x : A => u*x*star u)) :
    @Continuous _ _ (cornerTopology 𝒯 p hp) (cornerTopology 𝒯 q hq)
      (equivalentCorner p q hp hq u hu hu') := by
  let : TopologicalSpace A := 𝒯
  let : TopologicalSpace (Corner p hp) := cornerTopology 𝒯 p hp
  let : TopologicalSpace (Corner q hq) := cornerTopology 𝒯 q hq
  exact (hmul.comp continuous_subtype_val).subtype_mk _

end
section
open scoped ENNReal ComplexConjugate

variable {I : Type u_11} {J : Type u_12}
end
section
open scoped ENNReal

variable {I : Type u_14} {J : Type u_15}

variable {G : Type u_16} [Group G]

end
section
open scoped ENNReal
variable {I : Type u_17} {J : Type u_18}

def productSingle (I : Type u_19) (J : Type u_20) (j : I) : GroupHilbert J →L[ℂ] GroupHilbert (I × J) := by
  classical
  exact (hilbertFlatten I J).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (lp.singleContinuousLinearMap ℂ (fun _ : I => GroupHilbert J) 2 j)

@[simp] theorem productSingle_apply [DecidableEq I] (j i : I) (ξ : GroupHilbert J) (k : J) :
    productSingle I J j ξ (i,k) = if i = j then ξ k else 0 := by
  classical
  by_cases hi : i = j <;> simp [productSingle,hilbertFlatten_apply,lp.single_apply,hi]

variable {G : Type u_21} [Group G]

end
section
variable {I : Type u_22} {J : Type u_23}

 variable {G : Type u_28} [Group G]

end
open scoped ENNReal
variable {I : Type u_29} {J : Type u_30}

 variable {G : Type u_31} [Group G] [DecidableEq G]

end FreeGroupFactorMain.Amplification

end

end OAI
end


