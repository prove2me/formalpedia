-- Prove2me | Definitions.Def_OAIE3v2B021
-- name    : OAIE3v2B021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:58:42.981817+00:00
-- url     : https://prove2.me/theorems/1f74569c-a822-4d11-a2f9-4b4263aee99b
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 22 of 311
-- statement:
--   Definitions bundle 22 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Dynamics/CommonInitialBudget.lean`, `Dynamics/CommonTerminalBudget.lean`, `Estimates/DerivativeIndexBounds.lean`, `Estimates/EuclideanBallVolumeBound.lean`, `Estimates/EuclideanBisectorNull.lean`, `Estimates/EuclideanGraphNorm.lean`, `Estimates/OrthogonalBlockGram.lean`, `Estimates/OrthogonalSection.lean`, `Estimates/PetalComparisonTree.lean`, `Estimates/ProperSubspaceCount.lean`, `Estimates/ScaledSectionGram.lean`, `Estimates/StepDropTerminalContainment.lean`, `Fourier/ExpandingGramSpectrum.lean`, `Geometry/HorizontalCoordinateBounds.lean`, `Geometry/RealSubspaceCoordinateRetraction.lean`, `Lattices/LatticeCoordinateLifts.lean`, `Lattices/UniformDerivativeLatticeExtraction.lean`, `Linear/GramBasisChange.lean`, `Linear/ScaledBasisNorm.lean`, `Linear/SplitSurjectionBasis.lean`, `Linear/ZSpanRounding.lean`, `Nilpotent/FilteredAdjointFirstBracket.lean`, `Nilpotent/SquarefreeBracketHeight.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CommonInitialBudget
namespace OAI

section

namespace Erdos3

def commonExtractionParameter (p : ℝ) : ℝ := 3 * p + 3

def commonInitialParameter (p : ℝ) : ℝ := (commonExtractionParameter p + 2) ^ 3

theorem commonExtractionParameter_controls {p : ℝ} (hp : 0 ≤ p) :
    p ≤ commonExtractionParameter p ∧ 2 * p ≤ commonExtractionParameter p ∧
      1 ≤ commonExtractionParameter p ∧ commonExtractionParameter p ≤ commonInitialParameter p := by
  have hq : 1 ≤ commonExtractionParameter p + 2 := by
    unfold commonExtractionParameter
    linarith
  have hpow := pow_le_pow_right₀ hq (show 1 ≤ (3 : ℕ) by decide)
  simp only [pow_one] at hpow
  unfold commonInitialParameter
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold commonExtractionParameter; linarith
  · unfold commonExtractionParameter; linarith
  · unfold commonExtractionParameter; linarith
  · linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CommonTerminalBudget
namespace OAI

section

namespace Erdos3

def fullInitialParameter (s C : ℕ) (p : ℝ) : ℝ :=
  p + p * (s + 2) * (p + 1) ^ (s + 1) + (p + C) ^ C + 2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.GramBasisChange
namespace OAI

section

namespace Erdos3

open Module

theorem gram_det_basis_change {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : Basis ι ℝ E) (v : ι → E) :
    (Matrix.gram ℝ v).det = (b.det v) ^ 2 * (Matrix.gram ℝ b).det := by
  classical
  let o : OrthonormalBasis ι ℝ E := (stdOrthonormalBasis ℝ E).reindex
    (Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using finrank_eq_card_basis b))
  have hd (w : ι → E) : (Matrix.gram ℝ w).det = (o.toBasis.toMatrix w).det ^ 2 := by
    rw [Matrix.gram_eq_conjTranspose_mul o w, Matrix.det_mul, Matrix.det_conjTranspose]
    have he : o.toBasis.toMatrix w = Matrix.of (fun i j => o.repr (w j) i) := by
      ext i j
      rfl
    rw [he]
    simp [pow_two]
  rw [hd v, hd b, b.det_apply, ← o.toBasis.toMatrix_mul_toMatrix b v, Matrix.det_mul]
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OrthogonalBlockGram
namespace OAI

section

namespace Erdos3

open Module

theorem basis_inr_repr_zero_of_mem_inl_span
    {α β E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : Basis (α ⊕ β) ℝ E) {x : E}
    (hx : x ∈ Submodule.span ℝ (Set.range (fun i : α => b (Sum.inl i)))) (j : β) :
    b.repr x (Sum.inr j) = 0 := by
  classical
  have hle : Submodule.span ℝ (Set.range (fun i : α => b (Sum.inl i))) ≤
      LinearMap.ker (b.coord (Sum.inr j)) := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    simp
  exact hle hx

theorem gram_det_orthogonal_block
    {α β E : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : Basis (α ⊕ β) ℝ E) :
    let U := Submodule.span ℝ (Set.range (fun i : α => b (Sum.inl i)))
    (Matrix.gram ℝ b).det = (Matrix.gram ℝ (fun i : α => b (Sum.inl i))).det *
      (Matrix.gram ℝ (fun j : β => b (Sum.inr j) - U.starProjection (b (Sum.inr j)))).det := by
  classical
  let U := Submodule.span ℝ (Set.range (fun i : α => b (Sum.inl i)))
  let w : β → E := fun j => b (Sum.inr j) - U.starProjection (b (Sum.inr j))
  let g : (α ⊕ β) → E := Sum.elim (fun i => b (Sum.inl i)) w
  let C : Matrix α β ℝ := fun i j => -b.repr (U.starProjection (b (Sum.inr j))) (Sum.inl i)
  have hz (i j : β) : b.repr (U.starProjection (b (Sum.inr j))) (Sum.inr i) = 0 :=
    basis_inr_repr_zero_of_mem_inl_span b (U.starProjection_apply_mem _) i
  have hM : b.toMatrix g = Matrix.fromBlocks 1 C 0 1 := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        change b.repr (b (Sum.inl j)) (Sum.inl i) = (1 : Matrix α α ℝ) i j
        simp [Finsupp.single_apply, Matrix.one_apply, eq_comm]
      | inr j =>
        change b.repr (w j) (Sum.inl i) = C i j
        simp [w, C]
    | inr i =>
      cases j with
      | inl j =>
        change b.repr (b (Sum.inl j)) (Sum.inr i) = 0
        simp
      | inr j =>
        change b.repr (w j) (Sum.inr i) = (1 : Matrix β β ℝ) i j
        simp [w, hz, Finsupp.single_apply, Matrix.one_apply, eq_comm]
  have hdet : b.det g = 1 := by
    rw [b.det_apply, hM, Matrix.det_fromBlocks_zero₂₁]
    simp
  have hgram : (Matrix.gram ℝ g).det = (Matrix.gram ℝ b).det := by
    rw [gram_det_basis_change b g, hdet, one_pow, one_mul]
  have horth (i : α) (j : β) : inner ℝ (b (Sum.inl i)) (w j) = 0 := by
    have hi : b (Sum.inl i) ∈ U := Submodule.subset_span ⟨i, rfl⟩
    exact Submodule.inner_right_of_mem_orthogonal hi
      (Submodule.sub_starProjection_mem_orthogonal (K := U) (b (Sum.inr j)))
  have hblock : Matrix.gram ℝ g = Matrix.fromBlocks
      (Matrix.gram ℝ (fun i : α => b (Sum.inl i))) 0 0 (Matrix.gram ℝ w) := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => rfl
      | inr j => exact horth i j
    | inr i =>
      cases j with
      | inl j =>
        change inner ℝ (w i) (b (Sum.inl j)) = 0
        rw [real_inner_comm]
        exact horth j i
      | inr j => rfl
  rw [← hgram, hblock, Matrix.det_fromBlocks_zero₂₁]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProperSubspaceCount
namespace OAI

section

namespace Erdos3

variable {ι : Type*} [Fintype ι]

theorem exists_coordinate_injective_of_ne_top
    (U : Submodule ℝ (ι → ℝ)) (hU : U ≠ ⊤) :
    ∃ j : ι, ∀ x ∈ U, ∀ y ∈ U, (∀ i, i ≠ j → x i = y i) → x = y := by
  classical
  obtain ⟨f, hf, hzero⟩ := U.exists_dual_map_eq_bot_of_lt_top hU.lt_top inferInstance
  have hfzero : ∀ x ∈ U, f x = 0 := by
    intro x hx
    have hm : f x ∈ U.map f := ⟨x, hx, rfl⟩
    simpa only [hzero, Submodule.mem_bot] using hm
  have hcoord : ∃ j : ι, f (fun i => if j = i then 1 else 0) ≠ 0 := by
    by_contra h
    push Not at h
    apply hf
    apply LinearMap.ext
    intro x
    change f x = 0
    rw [LinearMap.pi_apply_eq_sum_univ]
    simp only [h, smul_zero, Finset.sum_const_zero]
  obtain ⟨j, hj⟩ := hcoord
  refine ⟨j, ?_⟩
  intro x hx y hy hxy
  have he : f (x - y) = (x j - y j) * f (fun i => if j = i then 1 else 0) := by
    rw [LinearMap.pi_apply_eq_sum_univ]
    apply Finset.sum_eq_single j
    · intro i _ hij
      simp only [Pi.sub_apply, hxy i hij, sub_self, zero_smul]
    · simp
  have hjxy : x j = y j := by
    rw [map_sub, hfzero x hx, hfzero y hy, sub_self] at he
    exact sub_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_right hj)
  funext i
  by_cases hij : i = j
  · simpa only [hij] using hjxy
  · exact hxy i hij

theorem integer_points_card_le_of_proper_subspace [DecidableEq ι]
    (U : Submodule ℝ (ι → ℝ)) (hU : U ≠ ⊤)
    (H : Finset (ι → ℤ)) (S : ι → Finset ℤ)
    (hmem : ∀ h ∈ H, (fun i => (h i : ℝ)) ∈ U)
    (hbound : ∀ h ∈ H, ∀ i, h i ∈ S i) :
    ∃ j : ι, H.card ≤ ∏ i : {i : ι // i ≠ j}, (S i.val).card := by
  classical
  obtain ⟨j, hj⟩ := exists_coordinate_injective_of_ne_top U hU
  refine ⟨j, ?_⟩
  let restrict : (ι → ℤ) → ({i : ι // i ≠ j} → ℤ) := fun h i => h i.val
  have hcard : H.card ≤ (Fintype.piFinset (fun i : {i : ι // i ≠ j} => S i.val)).card := by
    apply Finset.card_le_card_of_injOn restrict
    · intro h hh
      exact Fintype.mem_piFinset.mpr (fun i => hbound h hh i.val)
    · intro h hh k hk heq
      have he : (fun i => (h i : ℝ)) = (fun i => (k i : ℝ)) := by
        apply hj _ (hmem h hh) _ (hmem k hk)
        intro i hi
        exact_mod_cast congrFun heq ⟨i, hi⟩
      funext i
      exact_mod_cast congrFun he i
  simpa only [Fintype.card_piFinset] using hcard

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.EuclideanBisectorNull
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem linear_levelset_measure_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (f : E →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) : μ {x : E | f x = c} = 0 := by
  let S : AffineSubspace ℝ E := (affineSpan ℝ ({c} : Set ℝ)).comap f.toAffineMap
  have hS : (S : Set E) = {x : E | f x = c} := by
    ext x
    simp [S]
  have hproper : S ≠ ⊤ := by
    intro he
    have hall : ∀ x : E, f x = c := by
      intro x
      have hx : x ∈ S := by rw [he]; trivial
      change x ∈ (S : Set E) at hx
      simpa only [hS, Set.mem_ofPred_eq] using hx
    have hc : c = 0 := by simpa using (hall 0).symm
    apply hf
    ext x
    simpa only [hc, LinearMap.zero_apply] using hall x
  rw [← hS]
  exact μ.addHaar_affineSubspace S hproper

theorem euclidean_bisector_measure_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] (a b : E) (hab : a ≠ b) :
    μ {x : E | ‖x - a‖ = ‖x - b‖} = 0 := by
  let f : E →ₗ[ℝ] ℝ := (innerSL ℝ (b - a)).toLinearMap
  have hf : f ≠ 0 := by
    intro he
    have hz : inner ℝ (b - a) (b - a) = 0 := by
      simpa only [f, ContinuousLinearMap.coe_coe, innerSL_apply_apply,
        LinearMap.zero_apply] using LinearMap.congr_fun he (b - a)
    exact hab (sub_eq_zero.mp ((inner_self_eq_zero).mp hz)).symm
  apply measure_mono_null (t := {x : E | f x = (‖b‖ ^ 2 - ‖a‖ ^ 2) / 2})
  · intro x hx
    change inner ℝ (b - a) x = (‖b‖ ^ 2 - ‖a‖ ^ 2) / 2
    rw [inner_sub_left, real_inner_comm x b, real_inner_comm x a]
    have he : ‖x - a‖ ^ 2 = ‖x - b‖ ^ 2 := congrArg (fun t : ℝ => t ^ 2) hx
    rw [norm_sub_sq_real, norm_sub_sq_real] at he
    linarith
  · exact linear_levelset_measure_zero μ f hf _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ZSpanRounding
namespace OAI

section

namespace Erdos3

open Module

theorem exists_zspan_near_of_basis_bound {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : Basis ι ℝ E) (R : ℝ) (hb : ∀ i, ‖b i‖ ≤ R) (x : E) :
    ∃ z ∈ Submodule.span ℤ (Set.range b), ‖x - z‖ ≤ (Fintype.card ι : ℝ) * R / 2 := by
  classical
  let a : ι → ℤ := fun i => round (b.repr x i)
  let z : E := ∑ i, (a i : ℝ) • b i
  have hz : z ∈ Submodule.span ℤ (Set.range b) := by
    apply Submodule.sum_mem
    intro i _
    rw [Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have he : x - z = ∑ i, (b.repr x i - (a i : ℝ)) • b i := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [b.sum_repr]
  refine ⟨z, hz, ?_⟩
  rw [he]
  calc
    _ ≤ ∑ i, ‖(b.repr x i - (a i : ℝ)) • b i‖ := norm_sum_le _ _
    _ = ∑ i, |b.repr x i - (a i : ℝ)| * ‖b i‖ := by simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ _i : ι, (1 / 2 : ℝ) * R := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul (abs_sub_round (b.repr x i)) (hb i) (norm_nonneg _) (by norm_num)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FilteredAdjointFirstBracket
namespace OAI

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

def centralPairSpan (a b : L) : Submodule ℚ L :=
  Submodule.span ℚ {a, b, ⁅a, b⁆}

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.SquarefreeBracketHeight
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

variable {L ι κ ν : Type*} [LieRing L] [LieAlgebra ℚ L]
  {E V : Submodule ℚ L}

noncomputable def bracketSystemMatrix (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V))
    (k : κ → L) : Matrix (κ × ι) ν ℚ :=
  fun bi n => f.repr (V.mkQ ⁅(e n : L), k bi.1⁆) bi.2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SplitSurjectionBasis
namespace OAI

section

namespace Erdos3

open Module

variable {R E F : Type*} [Ring R] [AddCommGroup E] [Module R E]
  [AddCommGroup F] [Module R F]

def splitSurjectionEquiv (q : E →ₗ[R] F) (s : F →ₗ[R] E)
    (hs : ∀ x, q (s x) = x) : (LinearMap.ker q × F) ≃ₗ[R] E where
  toFun p := p.1.val + s p.2
  invFun x := (⟨x - s (q x), by rw [LinearMap.mem_ker, map_sub, hs, sub_self]⟩, q x)
  left_inv p := by
    refine Prod.ext (Subtype.ext ?_) ?_
    · change p.1.val + s p.2 - s (q (p.1.val + s p.2)) = p.1.val
      rw [map_add, show q p.1.val = 0 from p.1.property, hs, zero_add, add_sub_cancel_right]
    · change q (p.1.val + s p.2) = p.2
      rw [map_add, show q p.1.val = 0 from p.1.property, hs, zero_add]
  right_inv x := sub_add_cancel x (s (q x))
  map_add' x y := by
    change x.1.val + y.1.val + s (x.2 + y.2) = (x.1.val + s x.2) + (y.1.val + s y.2)
    rw [map_add]
    abel
  map_smul' a x := by
    change a • x.1.val + s (a • x.2) = a • (x.1.val + s x.2)
    rw [map_smul, smul_add]

@[simp] theorem splitSurjectionEquiv_apply (q : E →ₗ[R] F) (s : F →ₗ[R] E)
    (hs : ∀ x, q (s x) = x) (p : LinearMap.ker q × F) :
    splitSurjectionEquiv q s hs p = p.1.val + s p.2 := rfl

theorem exists_basis_of_surjection [Projective R F] {α β : Type*}
    (q : E →ₗ[R] F) (hq : Function.Surjective q)
    (bK : Basis α R (LinearMap.ker q)) (bI : Basis β R F) :
    ∃ b : Basis (α ⊕ β) R E,
      (∀ i, b (Sum.inl i) = (bK i).val) ∧ (∀ j, q (b (Sum.inr j)) = bI j) := by
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  have hret : ∀ x, q (s x) = x := fun x => LinearMap.congr_fun hs x
  let b := (bK.prod bI).map (splitSurjectionEquiv q s hret)
  refine ⟨b, ?_, ?_⟩
  · intro i
    simp [b]
  · intro j
    simp [b, hret]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ExpandingGramSpectrum
namespace OAI

section

namespace Erdos3

open Matrix
open scoped ComplexOrder

theorem one_le_eigenvalues_of_sub_one_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : M.IsHermitian) (h : (M - 1).PosSemidef) (i : ι) :
    1 ≤ hM.eigenvalues i := by
  let v := hM.eigenvectorBasis i
  have hv : star (⇑v) ⬝ᵥ ⇑v = (1 : ℝ) := by
    rw [dotProduct_comm]
    change inner ℝ v v = 1
    rw [real_inner_self_eq_norm_sq, hM.eigenvectorBasis.orthonormal.1 i, one_pow]
  have he : star (⇑v) ⬝ᵥ (M *ᵥ ⇑v) = hM.eigenvalues i := by
    simpa only [RCLike.re_to_real] using (hM.eigenvalues_eq i).symm
  have hp := h.dotProduct_mulVec_nonneg (⇑v)
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, he, hv] at hp
  linarith

theorem one_le_det_of_sub_one_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : M.IsHermitian) (h : (M - 1).PosSemidef) :
    1 ≤ M.det := by
  rw [hM.det_eq_prod_eigenvalues]
  exact Finset.one_le_prod (fun i _ => one_le_eigenvalues_of_sub_one_posSemidef hM h i)

theorem eigenvalues_le_det_of_sub_one_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : M.IsHermitian) (h : (M - 1).PosSemidef) (i : ι) :
    hM.eigenvalues i ≤ M.det := by
  rw [hM.det_eq_prod_eigenvalues]
  have heigen := one_le_eigenvalues_of_sub_one_posSemidef hM h
  have hp := Finset.prod_le_prod_of_subset_of_one_le
    (f := hM.eigenvalues) (Finset.subset_univ ({i} : Finset ι))
    (fun j _ => zero_le_one.trans (heigen j)) (fun j _ _ => heigen j)
  simpa only [Finset.prod_singleton, RCLike.ofReal_real_eq_id, id_eq] using hp

theorem det_smul_one_sub_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : M.IsHermitian) (h : (M - 1).PosSemidef) :
    (M.det • (1 : Matrix ι ι ℝ) - M).PosSemidef := by
  let U : Matrix ι ι ℝ := hM.eigenvectorUnitary
  have hdiag : (Matrix.diagonal (fun i => M.det - hM.eigenvalues i)).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr (fun i =>
      sub_nonneg.mpr (eigenvalues_le_det_of_sub_one_posSemidef hM h i))
  have hd : Matrix.diagonal (fun i => M.det - hM.eigenvalues i) =
      M.det • (1 : Matrix ι ι ℝ) - Matrix.diagonal hM.eigenvalues := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hs : M = U * Matrix.diagonal hM.eigenvalues * U.conjTranspose := by
    simpa only [Unitary.conjStarAlgAut_apply, Function.comp_def, RCLike.ofReal_real_eq_id,
      id_eq, Matrix.star_eq_conjTranspose] using
      hM.spectral_theorem
  have hU : U * U.conjTranspose = 1 := Unitary.coe_mul_star_self hM.eigenvectorUnitary
  have hp := hdiag.mul_mul_conjTranspose_same U
  rw [hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, hU, ← hs] at hp
  exact hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.EuclideanGraphNorm
namespace OAI

section

namespace Erdos3

open Matrix

theorem gram_linearMap_quadratic
    {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : (ι → ℝ) →ₗ[ℝ] E) (x : ι → ℝ) :
    star x ⬝ᵥ (Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ ι i))) *ᵥ x = ‖G x‖ ^ 2 := by
  have hsum : (∑ i, x i • G (Pi.basisFun ℝ ι i)) = G x := by
    simp_rw [← map_smul]
    rw [← map_sum]
    apply congrArg G
    simpa only [Pi.basisFun_repr] using (Pi.basisFun ℝ ι).sum_repr x
  rw [Matrix.star_dotProduct_gram_mulVec, hsum, real_inner_self_eq_norm_sq]

theorem norm_le_sqrt_gram_det_mul
    {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : (ι → ℝ) →ₗ[ℝ] E)
    (hG : (Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ ι i)) - 1).PosSemidef)
    (x : ι → ℝ) :
    ‖G x‖ ≤ Real.sqrt (Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ ι i))).det *
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ := by
  let M := Matrix.gram ℝ (fun i => G (Pi.basisFun ℝ ι i))
  have hM : M.IsHermitian := Matrix.isHermitian_gram ℝ _
  have hdet : 0 ≤ M.det := zero_le_one.trans (one_le_det_of_sub_one_posSemidef hM hG)
  have hp := (det_smul_one_sub_posSemidef hM hG).dotProduct_mulVec_nonneg x
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] at hp
  have hx : star x ⬝ᵥ x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ ^ 2 := by
    rw [dotProduct_comm]
    exact real_inner_self_eq_norm_sq (WithLp.toLp 2 x : EuclideanSpace ℝ ι)
  rw [hx, gram_linearMap_quadratic G x] at hp
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hdet]
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OrthogonalSection
namespace OAI

section

namespace Erdos3

theorem exists_orthogonal_section
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] (π : E →ₗ[ℝ] F) (hπ : Function.Surjective π) :
    ∃ L : F →ₗ[ℝ] E, (∀ y, π (L y) = y) ∧
      ∀ x, L (π x) = x - (LinearMap.ker π).starProjection x := by
  obtain ⟨s, hs⟩ := π.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hπ)
  have hret : ∀ y, π (s y) = y := fun y => LinearMap.congr_fun hs y
  let K := LinearMap.ker π
  let L : F →ₗ[ℝ] E := (LinearMap.id - K.starProjection.toLinearMap).comp s
  have hL (y : F) : L y = s y - K.starProjection (s y) := rfl
  have hzero (x : E) : π (K.starProjection x) = 0 := K.starProjection_apply_mem x
  have hright (y : F) : π (L y) = y := by rw [hL, map_sub, hret, hzero, sub_zero]
  have horth (y : F) : L y ∈ Kᗮ :=
    Submodule.sub_starProjection_mem_orthogonal (s y)
  refine ⟨L, hright, ?_⟩
  intro x
  let w := x - K.starProjection x
  have hw : w ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal x
  have hpw : π w = π x := by change π (x - K.starProjection x) = π x; rw [map_sub, hzero, sub_zero]
  have hk : L (π x) - w ∈ K := by
    change π (L (π x) - w) = 0
    rw [map_sub, hright, hpw, sub_self]
  have ho : L (π x) - w ∈ Kᗮ := Kᗮ.sub_mem (horth _) hw
  have hz : inner ℝ (L (π x) - w) (L (π x) - w) = 0 :=
    Submodule.inner_right_of_mem_orthogonal hk ho
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ScaledSectionGram
namespace OAI

section

namespace Erdos3

open Module

theorem gram_det_injective_map_basis
    {ι V E : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : V →ₗ[ℝ] E) (hf : Function.Injective f) (b₀ b₁ : Basis ι ℝ V) :
    (Matrix.gram ℝ (fun i => f (b₁ i))).det =
      (b₀.det b₁) ^ 2 * (Matrix.gram ℝ (fun i => f (b₀ i))).det := by
  let e := LinearEquiv.ofInjective f hf
  have h := gram_det_basis_change (b₀.map e) (fun i => e (b₁ i))
  have hd : (b₀.map e).det (fun i => e (b₁ i)) = b₀.det b₁ := by
    rw [Basis.det_map]
    apply congrArg b₀.det
    funext i
    exact e.symm_apply_apply (b₁ i)
  have h₀ : Matrix.gram ℝ (b₀.map e) = Matrix.gram ℝ (fun i => f (b₀ i)) := by
    ext i j
    simp only [Matrix.gram_apply, Basis.map_apply]
    rfl
  have h₁ : Matrix.gram ℝ (fun i => e (b₁ i)) = Matrix.gram ℝ (fun i => f (b₁ i)) := by
    ext i j
    rfl
  rw [hd, h₀, h₁] at h
  exact h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeCoordinateLifts
namespace OAI

section

namespace Erdos3

open Module MeasureTheory

variable {ι : Type*} [Fintype ι]

noncomputable def integerCoordinateLattice : Submodule ℤ (ι → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))

instance integerCoordinateLattice_discrete :
    DiscreteTopology (integerCoordinateLattice (ι := ι)) :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))))

instance integerCoordinateLattice_full : IsZLattice ℝ (integerCoordinateLattice (ι := ι)) :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))))

theorem integerCoordinateLattice_covolume :
    ZLattice.covolume (integerCoordinateLattice (ι := ι)) = 1 := by
  change ZLattice.covolume (Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))) = 1
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ ι) volume), measureReal_def]
  have hv : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ ι)) = 1 := by
    rw [ZSpan.fundamentalDomain_pi_basisFun, volume_pi, Measure.pi_pi]
    simp only [Real.volume_Ico, sub_zero, ENNReal.ofReal_one, Finset.prod_const_one]
  rw [hv]
  simp

theorem integer_lattice_covolume_eq_index
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : L ≤ integerCoordinateLattice) :
    ZLattice.covolume L = L.toAddSubgroup.relIndex integerCoordinateLattice.toAddSubgroup := by
  have h := ZLattice.covolume_div_covolume_eq_relIndex L integerCoordinateLattice hL
  simpa only [integerCoordinateLattice_covolume, div_one] using h

theorem integer_lattice_index_pos
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (hL : L ≤ integerCoordinateLattice) :
    0 < L.toAddSubgroup.relIndex integerCoordinateLattice.toAddSubgroup := by
  have h := ZLattice.covolume_pos L volume
  rw [integer_lattice_covolume_eq_index L hL] at h
  exact_mod_cast h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.EuclideanBallVolumeBound
namespace OAI

section

namespace Erdos3

open MeasureTheory Module

theorem euclidean_closedBall_volume_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (B : ℝ) (hB : 0 ≤ B) :
    volume.real (Metric.closedBall (0 : E) B) ≤ (2 * B) ^ finrank ℝ E := by
  let b := stdOrthonormalBasis ℝ E
  let e : E ≃ᵐ (Fin (finrank ℝ E) → ℝ) :=
    b.repr.toMeasurableEquiv.trans (MeasurableEquiv.toLp 2 _).symm
  have he : MeasurePreserving e :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _).comp b.measurePreserving_repr
  let C : Set (Fin (finrank ℝ E) → ℝ) := Set.Icc (fun _ => -B) (fun _ => B)
  have hsub : Metric.closedBall (0 : E) B ⊆ e ⁻¹' C := by
    intro x hx
    have hxnorm : ‖x‖ ≤ B := mem_closedBall_zero_iff.mp hx
    have hi : ∀ i, |e x i| ≤ B := by
      intro i
      change |b.repr x i| ≤ B
      rw [← Real.norm_eq_abs]
      exact (PiLp.norm_apply_le (b.repr x) i).trans ((b.repr.norm_map x).le.trans hxnorm)
    exact ⟨fun i => (abs_le.mp (hi i)).1, fun i => (abs_le.mp (hi i)).2⟩
  have hmeas : MeasurableSet C := measurableSet_Icc
  have hfinite : volume C ≠ ⊤ := by
    simp only [C, Real.volume_Icc_pi]
    exact ENNReal.prod_ne_top (fun _ _ => ENNReal.ofReal_ne_top)
  have hvolume : volume.real (e ⁻¹' C) = (2 * B) ^ finrank ℝ E := by
    rw [measureReal_def, he.measure_preimage hmeas.nullMeasurableSet]
    have horder : (fun _ : Fin (finrank ℝ E) => -B) ≤ (fun _ => B) := fun _ => by linarith
    simp only [C, Real.volume_Icc_pi_toReal horder, sub_neg_eq_add, ← two_mul,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← hvolume]
  exact measureReal_mono hsub (by rw [he.measure_preimage hmeas.nullMeasurableSet]; exact hfinite)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DerivativeIndexBounds
namespace OAI

section

namespace Erdos3

theorem scaled_covolume_product_le {z k I E t C δ : ℝ} (ht : 0 < t) (hδ : 0 < δ)
    (hfactor : z = k * (I / t) * E) (hbound : z ≤ C / (δ * t)) :
    k * I * E ≤ C / δ := by
  calc
    k * I * E = z * t := by rw [hfactor]; field_simp [ht.ne']
    _ ≤ C / (δ * t) * t := mul_le_mul_of_nonneg_right hbound ht.le
    _ = C / δ := by field_simp

open Module

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PetalComparisonTree
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem real_baseChange_pi {η V : Type*} {W : η → Type*}
    [AddCommGroup V] [Module ℚ V] [∀ j, AddCommGroup (W j)] [∀ j, Module ℚ (W j)]
    (f : ∀ j, V →ₗ[ℚ] W j) :
    (TensorProduct.piRightHom ℚ ℝ ℝ W).comp ((LinearMap.pi f).baseChange ℝ) =
      LinearMap.pi (fun j => (f j).baseChange ℝ) := by
  ext a v
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.HorizontalCoordinateBounds
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {L ι μ ν : Type*} [LieRing L] [LieAlgebra ℚ L]
  {E V : Submodule ℚ L}

noncomputable def subspaceQuotientMatrix (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) :
    Matrix ι ν ℚ := fun i n => f.repr (V.mkQ (e n : L)) i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealSubspaceCoordinateRetraction
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem real_matrix_right_inverse {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (D : Matrix κ ι ℚ) (S : Matrix ι κ ℚ) (hDS : D * S = 1) :
    D.map (Rat.castHom ℝ) * S.map (Rat.castHom ℝ) = 1 := by
  rw [← Matrix.map_mul, hDS]
  exact Matrix.map_one _ (map_zero (Rat.castHom ℝ)) (map_one (Rat.castHom ℝ))

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℝ W]
  (U : Submodule ℚ V)

theorem realification_mkQ_surjective : Function.Surjective (U.mkQ.baseChange ℝ) :=
  LinearMap.lTensor_surjective ℝ U.mkQ_surjective

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ δ V : Type*} [Fintype ι] [Fintype κ]
  [AddCommGroup V] [Module ℝ V] (e : Basis ι ℝ V) (S : Matrix ι κ ℚ)

noncomputable def rationalCoordinateSection : (κ → ℝ) →ₗ[ℝ] V :=
  e.equivFun.symm.toLinearMap.comp (S.map (Rat.castHom ℝ)).mulVecLin

theorem rationalCoordinateSection_coordinates (y : κ → ℝ) :
    e.equivFun (rationalCoordinateSection e S y) = S.map (Rat.castHom ℝ) *ᵥ y :=
  e.equivFun.apply_symm_apply _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StepDropTerminalContainment
namespace OAI

section

namespace Erdos3

open Module

variable {R L ι : Type*} [Field R] [LieRing L] [LieAlgebra R L]

def stepDropBracketKernel (K V : Submodule R L) : Submodule R L where
  carrier := {x | ∀ k ∈ K, ⁅x, k⁆ ∈ V}
  zero_mem' := by intro k _; rw [zero_lie]; exact V.zero_mem
  add_mem' := by
    intro x y hx hy k hk
    rw [add_lie]
    exact V.add_mem (hx k hk) (hy k hk)
  smul_mem' := by
    intro a x hx k hk
    rw [smul_lie]
    exact V.smul_mem a (hx k hk)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ScaledBasisNorm
namespace OAI

section

namespace Erdos3

theorem divided_basisFun_eq_smul {σ : Type*} [Fintype σ] [DecidableEq σ]
    (T : σ → ℝ) (i : σ) :
    (fun j => (Pi.basisFun ℝ σ i) j / T j) = (1 / T i) • Pi.basisFun ℝ σ i := by
  funext j
  by_cases hij : i = j
  · subst j
    simp
  · simp [Pi.basisFun_apply, Ne.symm hij]

theorem linearMap_divided_basis_norm_le {E σ : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Fintype σ] [DecidableEq σ]
    (G : (σ → ℝ) →ₗ[ℝ] E) (T : σ → ℝ) (i : σ) (hTi : 0 < T i)
    (B : ℝ) (hB : ‖G (Pi.basisFun ℝ σ i)‖ ≤ B) :
    ‖G (fun j => (Pi.basisFun ℝ σ i) j / T j)‖ ≤ B / T i := by
  rw [divided_basisFun_eq_smul, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr hTi)]
  calc
    _ ≤ (1 / T i) * B := mul_le_mul_of_nonneg_left hB (one_div_pos.mpr hTi).le
    _ = B / T i := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformDerivativeLatticeExtraction
namespace OAI

section

namespace Erdos3

theorem derivative_extended_budget_le_exp (k l : ℕ) (C p : ℝ)
    (hp : 0 ≤ p) (hk : (k : ℝ) ≤ p) (hl : (l : ℝ) ≤ Real.exp p)
    (hC : C ≤ Real.exp (3 * p ^ 2 + 2 * p)) :
    C * (l : ℝ) ^ k ≤ Real.exp (4 * p ^ 2 + 2 * p) := by
  calc
    _ ≤ Real.exp (3 * p ^ 2 + 2 * p) * Real.exp p ^ k := by
      exact mul_le_mul hC (pow_le_pow_left₀ (Nat.cast_nonneg l) hl k)
        (pow_nonneg (Nat.cast_nonneg l) k) (Real.exp_nonneg _)
    _ = Real.exp (3 * p ^ 2 + 2 * p + (k : ℝ) * p) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ Real.exp (4 * p ^ 2 + 2 * p) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hk hp]

end Erdos3

end

end OAI
end


