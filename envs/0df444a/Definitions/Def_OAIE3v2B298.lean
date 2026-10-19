-- Prove2me | Definitions.Def_OAIE3v2B298
-- name    : OAIE3v2B298
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:33:12.873341+00:00
-- url     : https://prove2.me/theorems/a46ff9f2-2c0c-42a2-9c01-cb7f443837d5
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 96 of 311
-- statement:
--   Definitions bundle 96 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B094` of this split.
--
--   Modules: `Estimates/FiniteSeriesCoefficientBounds.lean`, `Estimates/LieTreeMultidegree.lean`, `Estimates/LowerStepSquare.lean`, `Estimates/SourceUnitCover.lean`, `Fourier/JoinedFrequencyQuotientInjectivity.lean`, `Geometry/ControlledSumCoordinates.lean`, `Lattices/ScaledLatticeCovolume.lean`, `Lattices/SharedFreeAffineBudget.lean`, `Linear/BasisGradedCoordinateBasis.lean`, `Linear/RationalSpanCoordinates.lean`, `Nilpotent/BCHNonlinearRemainder.lean`, `Nilpotent/RealPolynomialBCH.lean`, `Polynomial/UniformPolynomialPeriodBudget.lean`, `Sampling/RationalSpanGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B094

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalSpanGrid
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ V : Type*} [Fintype ι] [Fintype κ] [AddCommGroup V] [Module ℚ V]

theorem rationalSpanGridStep_pos (e : Basis ι ℚ V) (v : κ → V) (l : ℕ) (hl : 0 < l) :
    0 < rationalSpanGridStep e v l :=
  Nat.mul_pos hl (matrixDenominator_pos _)

theorem rationalSpanGridStep_le (e : Basis ι ℚ V) (v : κ → V) (l : ℕ) {H : ℕ}
    (hv : ∀ i j, RationalHeightLE (e.repr (v j) i) H) :
    rationalSpanGridStep e v l ≤ l * H ^ (Fintype.card ι * Fintype.card κ) :=
  Nat.mul_le_mul_left l (matrixDenominator_le _ hv)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHNonlinearRemainder
namespace OAI

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem lieBCH_sub_left_mem_of_mem_ideal
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (I : LieIdeal ℚ L)
    (a : L) {b : L} (hb : b ∈ I) : lieBCH s a b - a ∈ I := by
  apply (lieQuotientMap_eq_zero I _).mp
  rw [map_sub, map_lieBCH, (lieQuotientMap_eq_zero I b).mpr hb,
    lieBCH_eq_add_of_lie_eq_zero (lie_quotient_lowerCentralSeries_eq_bot hnil I) (lie_zero _),
    add_zero, sub_self]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteSeriesCoefficientBounds
namespace OAI

section

namespace Erdos3

variable {X : Type*}

theorem finiteExp_freeCoefficientBound (s : ℕ) (x : X) :
    FreeCoefficientBound s (finiteSeriesDenominator s)
      ((s + 1) * finiteSeriesNumeratorBound s) (finiteExp (s + 1) (FreeAlgebra.ι ℚ x)) := by
  have hterm : ∀ i ∈ Finset.range (s + 1),
      FreeCoefficientBound s (finiteSeriesDenominator s) (finiteSeriesNumeratorBound s)
        ((i.factorial : ℚ)⁻¹ • (FreeAlgebra.ι ℚ x) ^ i) := by
    intro i hi
    let j : Fin 2 × Fin (s + 1) := (0, ⟨i, Finset.mem_range.mp hi⟩)
    have h := (FreeCoefficientBound.word s ((FreeMonoid.of x) ^ i)).smul
      (finiteSeriesNumerator_cast s j) (finiteSeriesNumerator_le s j)
    simpa only [j, finiteSeriesWeight, ite_true, mul_one, map_pow, freeWord_of] using h
  simpa only [finiteExp, Finset.card_range] using
    FreeCoefficientBound.sum_finset (Finset.range (s + 1)) _ hterm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LieTreeMultidegree
namespace OAI

section

namespace Erdos3

variable {I J L : Type*} [LieRing L]

def lieTreeOccurrenceLabel : (a : FreeMagma I) → LieTreeOccurrences a → I
  | .of i => fun _ => i
  | .mul a b => Sum.elim (lieTreeOccurrenceLabel a) (lieTreeOccurrenceLabel b)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalSpanCoordinates
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem realification_layer_eq_span (n : ℕ) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = (LieModule.lowerCentralSeries ℚ L L n).toSubmodule) :
    (LieModule.lowerCentralSeries ℚ (ℝ ⊗[ℚ] L) (ℝ ⊗[ℚ] L) n : Set (ℝ ⊗[ℚ] L)) =
      (Submodule.span ℝ (Set.range (fun j => rationalLieInclusion (v j))) : Set (ℝ ⊗[ℚ] L)) := by
  calc
    _ = (LieModule.lowerCentralSeries ℝ (ℝ ⊗[ℚ] L) (ℝ ⊗[ℚ] L) n : Set (ℝ ⊗[ℚ] L)) := by
      rw [LieModule.coe_lowerCentralSeries_eq_int ℚ,
        LieModule.coe_lowerCentralSeries_eq_int ℝ]
    _ = ((LieModule.lowerCentralSeries ℚ L L n).baseChange ℝ : Set (ℝ ⊗[ℚ] L)) := by
      rw [LieSubmodule.lowerCentralSeries_tensor_eq_baseChange]
    _ = ((LieModule.lowerCentralSeries ℚ L L n).toSubmodule.baseChange ℝ : Set (ℝ ⊗[ℚ] L)) := rfl
    _ = _ := congrArg (fun P : Submodule ℝ (ℝ ⊗[ℚ] L) => (P : Set (ℝ ⊗[ℚ] L)))
      (real_span_rational_family _ v hspan).symm

theorem rationalLieInclusion_integer_combination [Fintype κ] (v : κ → L) (z : κ → ℤ) (m : ℕ) :
    rationalLieInclusion (∑ j, ((z j : ℚ) * (m : ℚ)) • v j) =
      ∑ j, ((z j : ℝ) * (m : ℝ)) • rationalLieInclusion (v j) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  rw [← algebraMap_smul ℝ ((z j : ℚ) * (m : ℚ))]
  simp only [map_mul, map_intCast, map_natCast]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ η L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem real_span_sum_family (v : κ → L) (w : η → L) :
    Submodule.span ℝ (Set.range (fun j => rationalLieInclusion (Sum.elim v w j))) =
      Submodule.span ℝ (Set.range (fun j => rationalLieInclusion (v j))) ⊔
        Submodule.span ℝ (Set.range (fun j => rationalLieInclusion (w j))) := by
  have heq : (fun j => rationalLieInclusion (Sum.elim v w j)) =
      Sum.elim (fun j => rationalLieInclusion (v j)) (fun j => rationalLieInclusion (w j)) := by
    funext j
    cases j <;> rfl
  rw [heq, Set.Sum.elim_range, Submodule.span_union]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BasisGradedCoordinateBasis
namespace OAI

section

namespace Erdos3

open Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem sub_basisCoordinateProjection_mem (b : Basis ι K V) (S : Set ι) (x : V) :
    x - basisCoordinateProjection b S x ∈ Submodule.span K (b '' Sᶜ) := by
  apply (basisCoordinateProjection_eq_zero_iff b S _).mp
  rw [map_sub, basisCoordinateProjection_idempotent, sub_self]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowerStepSquare
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem scaled_basis_mem_bchSubgroup (b : Basis κ ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (N : ℕ)
    (hgrid : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ) (j : κ) :
    (⟨(N : ℚ) • b j⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ := by
  classical
  have hx : b.equivFun ((N : ℚ) • b j) ∈ scaledIntegerGrid N := by
    refine ⟨fun k => if k = j then 1 else 0, ?_⟩
    ext k
    by_cases h : k = j
    · subst k
      simp [Basis.equivFun_apply]
    · simp [Basis.equivFun_apply, h]
  have h := hgrid hx
  change (⟨b.equivFun.symm (b.equivFun ((N : ℚ) • b j))⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ at h
  simpa only [LinearEquiv.symm_apply_apply] using h

theorem scaled_real_basis_mem_realification (b : Basis κ ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (N : ℕ)
    (hgrid : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ) (j : κ) :
    (⟨(N : ℝ) • (b.baseChange ℝ) j⟩ : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s
      (realification_lowerCentralSeries_eq_bot hnil)) ∈ Γ.map realificationHom := by
  refine Subgroup.mem_map.mpr ⟨⟨(N : ℚ) • b j⟩, scaled_basis_mem_bchSubgroup b Γ N hgrid j, ?_⟩
  apply NilpotentLieBCHGroup.ext
  change rationalLieInclusion ((N : ℚ) • b j) = (N : ℝ) • (b.baseChange ℝ) j
  simp only [Nat.cast_smul_eq_nsmul, map_nsmul, Basis.baseChange_apply, rationalLieInclusion_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ControlledSumCoordinates
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem exists_rational_sum_coordinates {ι κ ν : Type*}
    [Fintype ι] [Fintype κ] [Fintype ν]
    (A : Matrix ι κ ℚ) (B : Matrix ι ν ℚ) {H : ℕ} (hH : 1 ≤ H)
    (hA : ∀ i j, RationalHeightLE (A i j) H) (hB : ∀ i j, RationalHeightLE (B i j) H) :
    ∃ S : Matrix (κ ⊕ ν) ι ℚ,
      (∀ i j, RationalHeightLE (S i j) (rationalKernelHeight (Fintype.card ι) H)) ∧
      ∀ x, x ∈ Submodule.span ℝ (Set.range (A.map (Rat.castHom ℝ)).col) ⊔
        Submodule.span ℝ (Set.range (B.map (Rat.castHom ℝ)).col) →
        A.map (Rat.castHom ℝ) *ᵥ ((S.map (Rat.castHom ℝ) *ᵥ x) ∘ Sum.inl) +
          B.map (Rat.castHom ℝ) *ᵥ ((S.map (Rat.castHom ℝ) *ᵥ x) ∘ Sum.inr) = x := by
  let C := Matrix.fromCols A B
  have hC : ∀ i j, RationalHeightLE (C i j) H := by
    intro i j
    cases j with
    | inl j => exact hA i j
    | inr j => exact hB i j
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_image_section C hH hC
  refine ⟨S, hSH, fun x hx => ?_⟩
  have hx' : x ∈ LinearMap.range (C.map (Rat.castHom ℝ)).mulVecLin := by
    apply (real_column_span_mem_iff C x).mp
    change x ∈ Submodule.span ℝ (Set.range ((Matrix.fromCols A B).map (Rat.castHom ℝ)).col)
    rw [real_column_span_fromCols]
    exact hx
  have he := real_matrix_image_section_apply C S hS x hx'
  change C.map (Rat.castHom ℝ) *ᵥ (S.map (Rat.castHom ℝ) *ᵥ x) = x at he
  dsimp only [C] at he
  rw [Matrix.fromCols_map, Matrix.fromCols_mulVec] at he
  exact he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.JoinedFrequencyQuotientInjectivity
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem realifyFunctional_comp {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (eta : W →ₗ[ℚ] ℚ) (f : V →ₗ[ℚ] W) (x : ℝ ⊗[ℚ] V) :
    realifyFunctional (eta.comp f) x = realifyFunctional eta (f.baseChange ℝ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v => simp only [realifyFunctional_tmul, LinearMap.baseChange_tmul, LinearMap.comp_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScaledLatticeCovolume
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem real_rational_kernel_eq_span_integer {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) :
    LinearMap.ker (Matrix.mulVecLin (fun i j => (A i j : ℝ))) =
      Submodule.span ℝ {x : κ → ℝ | x ∈ realIntegerGrid ∧
        x ∈ LinearMap.ker (Matrix.mulVecLin (fun i j => (A i j : ℝ)))} := by
  classical
  obtain ⟨H, hH, hA⟩ := exists_rational_matrix_height A
  obtain ⟨S, hS, _⟩ := exists_bounded_rational_image_section A hH hA
  let Ar : Matrix ι κ ℝ := fun i j => (A i j : ℝ)
  let Sr : Matrix κ ι ℝ := fun i j => (S i j : ℝ)
  let P : Matrix κ κ ℚ := 1 - S * A
  let Pr : Matrix κ κ ℝ := fun i j => (P i j : ℝ)
  have hSr : Ar * Sr * Ar = Ar := real_matrix_image_section A S hS
  have hPr : Pr = (1 : Matrix κ κ ℝ) - Sr * Ar := by
    ext i j
    change (P i j : ℝ) = (if i = j then 1 else 0) - ∑ k, (S i k : ℝ) * (A k j : ℝ)
    by_cases hij : i = j <;> simp [P, Matrix.sub_apply, Matrix.mul_apply, hij]
  have hzero : Ar * (1 - Sr * Ar) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hSr, sub_self]
  have hrange : LinearMap.range ((1 - Sr * Ar).mulVecLin) = LinearMap.ker Ar.mulVecLin := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change Ar *ᵥ ((1 - Sr * Ar) *ᵥ y) = 0
      rw [Matrix.mulVec_mulVec, hzero, Matrix.zero_mulVec]
    · intro hx
      change Ar *ᵥ x = 0 at hx
      refine ⟨x, ?_⟩
      change (1 - Sr * Ar) *ᵥ x = x
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
        hx, Matrix.mulVec_zero, sub_zero]
  have hspan : Submodule.span ℝ (Set.range Pr.col) = LinearMap.ker Ar.mulVecLin := by
    rw [← Matrix.range_mulVecLin, hPr]
    exact hrange
  apply le_antisymm
  · change LinearMap.ker Ar.mulVecLin ≤ _
    calc
      LinearMap.ker Ar.mulVecLin = Submodule.span ℝ (Set.range Pr.col) := hspan.symm
      _ ≤ _ := by
        apply Submodule.span_le.mpr
        rintro x ⟨j, rfl⟩
        apply rational_vector_mem_span_integer_points _ (P.col j)
        exact hspan ▸ (Submodule.subset_span ⟨j, rfl⟩)
  · exact Submodule.span_le.mpr (fun _ hx => hx.2)

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

theorem kernel_eq_span_integer_inter_of_basis
    {E ι κ : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι] [Fintype κ]
    (b : Basis κ ℝ E) (Λ : Submodule ℤ E) (hb : Submodule.span ℤ (Set.range b) = Λ)
    (π : E →ₗ[ℝ] (ι → ℝ)) (hπ : ∀ j, π (b j) ∈ realIntegerGrid) :
    LinearMap.ker π = Submodule.span ℝ {x : E | x ∈ Λ ∧ π x = 0} := by
  classical
  choose z hz using hπ
  let A : Matrix ι κ ℚ := fun i j => (z j i : ℚ)
  let Ar : Matrix ι κ ℝ := fun i j => (A i j : ℝ)
  let f : (κ → ℝ) →ₗ[ℝ] E := b.equivFun.symm.toLinearMap
  have hA (y : κ → ℝ) : π (b.equivFun.symm y) = Ar *ᵥ y := by
    funext i
    rw [b.equivFun_symm_apply, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    have hj : (z j i : ℝ) = π (b j) i := congrFun (hz j) i
    rw [← hj]
    simp only [Ar, A, Rat.cast_intCast, mul_comm]
  have hmap : (LinearMap.ker Ar.mulVecLin).map f ≤
      Submodule.span ℝ {x : E | x ∈ Λ ∧ π x = 0} := by
    change (LinearMap.ker (Matrix.mulVecLin (fun i j => (A i j : ℝ)))).map f ≤ _
    rw [real_rational_kernel_eq_span_integer, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro x ⟨y, ⟨⟨a, ha⟩, hy⟩, rfl⟩
    apply Submodule.subset_span
    constructor
    · rw [← hb, b.mem_span_iff_repr_mem ℤ]
      intro j
      refine ⟨a j, ?_⟩
      change (a j : ℝ) = b.equivFun (b.equivFun.symm y) j
      rw [LinearEquiv.apply_symm_apply]
      exact congrFun ha j
    · change π (b.equivFun.symm y) = 0
      rw [hA]
      exact hy
  apply le_antisymm
  · intro x hx
    apply hmap
    refine ⟨b.equivFun x, ?_, b.equivFun.symm_apply_apply x⟩
    change Ar *ᵥ b.equivFun x = 0
    rw [← hA, LinearEquiv.symm_apply_apply]
    exact hx
  · apply Submodule.span_le.mpr
    intro x hx
    exact hx.2

end Erdos3

end

section

namespace Erdos3

open Module

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]
  (Λ : Submodule ℤ E) (π : E →ₗ[ℝ] (ι → ℝ))

theorem kernel_eq_span_lattice_inter [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hπ : ∀ x ∈ Λ, π x ∈ realIntegerGrid) :
    LinearMap.ker π = Submodule.span ℝ {x : E | x ∈ Λ ∧ π x = 0} := by
  let b := (Free.chooseBasis ℤ Λ).ofZLatticeBasis ℝ Λ
  exact kernel_eq_span_integer_inter_of_basis b Λ
    ((Free.chooseBasis ℤ Λ).ofZLatticeBasis_span ℝ)
    π (fun j => hπ _ (by
      simpa only [b, Basis.ofZLatticeBasis_apply] using ((Free.chooseBasis ℤ Λ) j).property))

theorem latticeKernel_full [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (hπ : ∀ x ∈ Λ, π x ∈ realIntegerGrid) : IsZLattice ℝ (latticeKernel Λ π) := by
  constructor
  apply (Submodule.map_injective_of_injective (LinearMap.ker π).injective_subtype)
  rw [Submodule.map_top, Submodule.range_subtype, Submodule.map_span]
  refine Eq.trans ?_ (kernel_eq_span_lattice_inter Λ π hπ).symm
  apply congrArg (Submodule.span ℝ)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.property⟩
  · rintro ⟨hx, hzero⟩
    exact ⟨⟨x, hzero⟩, hx, rfl⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SourceUnitCover
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators NNReal

theorem frozen_quotient_map_smul {G : Type*} [Group G]
    (Γ Λ : Subgroup G) (a r : G) (f : G ⧸ Γ → G ⧸ Λ)
    (hf : ∀ x : G, f (QuotientGroup.mk x) = QuotientGroup.mk (a * x * r))
    (z : G) (hz : Commute z a) (x : G ⧸ Γ) : f (z • x) = z • f x := by
  induction x using Quotient.inductionOn with
  | h x =>
    change f (QuotientGroup.mk (z * x)) = z • f (QuotientGroup.mk x)
    rw [hf, hf]
    change (QuotientGroup.mk (a * (z * x) * r) : G ⧸ Λ) = QuotientGroup.mk (z * (a * x * r))
    congr 1
    calc
      _ = (a * z) * x * r := by group
      _ = (z * a) * x * r := by rw [hz.eq]
      _ = _ := by group

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RealPolynomialBCH
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

noncomputable def polynomialBCHPeriod (e : Basis ι ℚ L) (s l : ℕ)
    (P : ι → MvPolynomial σ ℚ) : ℕ :=
  (l * polynomialFamilyDenominator (conjugationCoordinatePolynomial e s) *
    polynomialFamilyDenominator P ^ s) * polynomialFamilyDenominator P

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.UniformPolynomialPeriodBudget
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

noncomputable def uniformPolynomialBCHPeriod (e : Basis ι ℚ L) (s r l q : ℕ) : ℕ :=
  let Q := q ^ (((r + 1) * (Fintype.card σ + 1) ^ r) * Fintype.card ι)
  (l * polynomialFamilyDenominator (conjugationCoordinatePolynomial e s) * Q ^ s) * Q

theorem uniformPolynomialBCHPeriod_pos (e : Basis ι ℚ L) (s r l q : ℕ)
    (hl : 0 < l) (hq : 0 < q) : 0 < uniformPolynomialBCHPeriod (σ := σ) e s r l q := by
  unfold uniformPolynomialBCHPeriod
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hl (polynomialFamilyDenominator_pos _))
    (pow_pos (pow_pos hq _) _)) (pow_pos hq _)

theorem polynomialBCHPeriod_dvd_uniform (e : Basis ι ℚ L) (s r l q : ℕ)
    (P : ι → MvPolynomial σ ℚ) (hdegree : ∀ i, (P i).totalDegree ≤ r)
    (hden : ∀ i α, ((P i).coeff α).den ∣ q) :
    polynomialBCHPeriod e s l P ∣ uniformPolynomialBCHPeriod (σ := σ) e s r l q := by
  have h := polynomialFamilyDenominator_dvd_power P q ((r + 1) * (Fintype.card σ + 1) ^ r)
    hden (fun i => polynomial_support_card_le (P i) (hdegree i))
  exact mul_dvd_mul (mul_dvd_mul_left _ (pow_dvd_pow_of_dvd h s)) h

end Erdos3

end

section

namespace Erdos3

open Module _root_.MvPolynomial
open scoped TensorProduct

theorem uniformPolynomialBCHPeriod_le_exp {ι σ L : Type*} [Fintype ι] [Fintype σ]
    [LieRing L] [LieAlgebra ℚ L] (e : Basis ι ℚ L) (K s r l q : ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hn : (Fintype.card σ : ℝ) ≤ p) (hl : (l : ℝ) ≤ Real.exp p) (hq : (q : ℝ) ≤ Real.exp p)
    (hD : (polynomialFamilyDenominator (conjugationCoordinatePolynomial e s) : ℝ) ≤
      Real.exp ((p + K) ^ K)) :
    (uniformPolynomialBCHPeriod (σ := σ) e s r l q : ℝ) ≤
      Real.exp ((p + (K + r + s + 10)) ^ (K + r + s + 10)) := by
  let N := ((r + 1) * (Fintype.card σ + 1) ^ r) * Fintype.card ι
  let Q := q ^ N
  let t : ℝ := p + (r + 3)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := le_add_of_nonneg_right (by positivity)
  have hdt : (Fintype.card ι : ℝ) ≤ t := hd.trans hpt
  have hnt : (Fintype.card σ : ℝ) + 1 ≤ t := by dsimp [t]; linarith [Nat.cast_nonneg (α := ℝ) r]
  have hrt : (r : ℝ) + 1 ≤ t := by dsimp [t]; linarith
  have hlength : (N : ℝ) * p ≤ t ^ (r + 3) := by
    dsimp only [N]
    push_cast
    calc
      _ ≤ t * t ^ r * t * t := by gcongr
      _ = _ := by rw [pow_add]; ring
  have hQ : (Q : ℝ) ≤ Real.exp ((p + (r + 3)) ^ (r + 3)) := by
    dsimp only [Q]
    rw [Nat.cast_pow]
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hq N).trans
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr hlength
  exact polynomial_period_cost_le_exp K r s l _ Q hp hl hD hQ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SharedFreeAffineBudget
namespace OAI

section

namespace Erdos3

open CyclicCrootSisask

noncomputable def properAffineScaleLog (P : ℝ) (n : ℕ) : ℝ :=
  2 * properAffineRankBound P n + properAffineVolumeLog P n + affineRecoveryLogLoss P n + 2

noncomputable def properAffineRecoveryLogLoss (P : ℝ) (n : ℕ) : ℝ :=
  affineRecoveryLogLoss P n + (4 + properAffineScaleLog P n) * properAffineRankBound P n

end Erdos3

end

section

namespace Erdos3

open CyclicCrootSisask

theorem exists_sharedFreeProperAffineSelection_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → ∀ n : ℕ, (n : ℝ) ≤ 4 * (s : ℝ) * p →
      properAffineRecoveryLogLoss ((p + 2) ^ 3 + 2 * p) n ≤ (p + C) ^ C ∧
      properAffineScaleLog ((p + 2) ^ 3 + 2 * p) n ≤ (p + C) ^ C ∧
      properAffineRankBound ((p + 2) ^ 3 + 2 * p) n ≤ (p + C) ^ C := by
  let c := ⌈max quarticBogolyubovProgressionConstant quarticBogolyubovConstant⌉₊
  have hc₀ : quarticBogolyubovProgressionConstant ≤ (c : ℝ) :=
    (le_max_left _ _).trans (Nat.le_ceil _)
  have hc₁ : quarticBogolyubovConstant ≤ (c : ℝ) :=
    (le_max_right _ _).trans (Nat.le_ceil _)
  let PB : Polynomial ℕ := (Polynomial.X + 2) ^ 3 + 2 * Polynomial.X
  let PD : Polynomial ℕ := 4 * Polynomial.C s * Polynomial.X
  let PZ : Polynomial ℕ := 736 + 96 * PB + 1504 * PD
  let PR : Polynomial ℕ := 2 + Polynomial.C c * (PZ + 1) ^ 4
  let PA : Polynomial ℕ := Polynomial.C c * (PZ + 1) ^ 8 + (PB + 13 * PD) + 16 * (PD + 3)
  let PV : Polynomial ℕ := 2 + 16 * (44 + 6 * PB + 94 * PD)
  let PT : Polynomial ℕ := 2 * PR + PV + PA + 2
  let PL : Polynomial ℕ := PA + (4 + PT) * PR
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (PL + PT + PR)
  refine ⟨C, hC, ?_⟩
  intro p hp n hn
  let B := (p + 2) ^ 3 + 2 * p
  let D := 4 * (s : ℝ) * p
  let Z := 736 + 96 * B + 1504 * D
  let R := 2 + (c : ℝ) * (Z + 1) ^ 4
  let A := (c : ℝ) * (Z + 1) ^ 8 + (B + 13 * D) + 16 * (D + 3)
  let V := 2 + 16 * (44 + 6 * B + 94 * D)
  let T := 2 * R + V + A + 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hz : roundedModelLogBudget B n ≤ Z := by
    unfold roundedModelLogBudget
    rw [max_eq_left hB]
    dsimp [Z]
    gcongr
  have hz0 : 0 ≤ roundedModelLogBudget B n + 1 := by
    linarith [roundedModelLogBudget_nonneg B n]
  have hrank : properAffineRankBound B n ≤ R := by
    unfold properAffineRankBound
    dsimp [R]
    gcongr
  have hloss : affineRecoveryLogLoss B n ≤ A := by
    unfold affineRecoveryLogLoss
    dsimp [A]
    gcongr
  have hvolume : properAffineVolumeLog B n ≤ V := by
    unfold properAffineVolumeLog
    rw [max_eq_left hB]
    dsimp [V]
    gcongr
  have hscale : properAffineScaleLog B n ≤ T := by
    unfold properAffineScaleLog
    dsimp [T]
    linarith only [hrank, hloss, hvolume]
  have hrank0 : 0 ≤ properAffineRankBound B n := by
    have hc := quarticBogolyubovConstant_pos.le
    unfold properAffineRankBound
    positivity
  have hloss0 : 0 ≤ affineRecoveryLogLoss B n := by
    have hc := quarticBogolyubovProgressionConstant_pos.le
    unfold affineRecoveryLogLoss
    positivity
  have hscale0 : 0 ≤ properAffineScaleLog B n := by
    unfold properAffineScaleLog properAffineVolumeLog
    positivity
  have hproper : properAffineRecoveryLogLoss B n ≤ A + (4 + T) * R := by
    unfold properAffineRecoveryLogLoss
    exact add_le_add hloss (mul_le_mul (by linarith only [hscale]) hrank hrank0
      (by linarith only [hT]))
  have heval : (PL + PT + PR).eval₂ (Nat.castRingHom ℝ) p = A + (4 + T) * R + T + R := by
    simp [PL, PT, PV, PA, PR, PZ, PD, PB, B, D, Z, R, A, V, T, Polynomial.eval₂_pow]
  have htotal := hbound p hp
  rw [heval] at htotal
  have hproper0 : 0 ≤ A + (4 + T) * R := by positivity
  exact ⟨hproper.trans (by linarith only [htotal, hT, hR]),
    hscale.trans (by linarith only [htotal, hproper0, hR]),
    hrank.trans (by linarith only [htotal, hproper0, hT])⟩

end Erdos3

end

end OAI
end


