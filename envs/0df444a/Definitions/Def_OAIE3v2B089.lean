-- Prove2me | Definitions.Def_OAIE3v2B089
-- name    : OAIE3v2B089
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:20:25.526776+00:00
-- url     : https://prove2.me/theorems/746ebf6a-80a4-4783-a658-1a8852854a15
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 90 of 311
-- statement:
--   Definitions bundle 90 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B068`, `OAIE3v2B069` of this split.
--
--   Modules: `Estimates/DilationPairFiltration.lean`, `Estimates/HorizontalAmbientQuotient.lean`, `Estimates/LowerStepSquare.lean`, `Estimates/MultidegreeDilationPair.lean`, `Estimates/RealificationFixedSubmodule.lean`, `Estimates/SquarefreeAdaptedLieAlgebra.lean`, `Estimates/SquarefreePermutationFiltration.lean`, `Estimates/SquarefreeSplitCount.lean`, `Geometry/ConjugationCoordinates.lean`, `Geometry/SquarefreeAlgebraCoordinates.lean`, `Geometry/SquarefreeSupportPermutation.lean`, `Lattices/AffineCoefficientSubspace.lean`, `Lattices/IntegerWeightedLoweringGroup.lean`, `Linear/SquarefreeBasisPermutation.lean`, `Nilpotent/BCHLatticeImageGap.lean`, `Nilpotent/BCHOuterGridChangeBasis.lean`, `Nilpotent/BCHSmoothPartitionBudget.lean`, `Nilpotent/BCHUniformQuotientCharts.lean`, `Nilpotent/SquarefreeBracketCoefficients.lean`, `Nilpotent/SquarefreeSupportBracket.lean`, `Polynomial/DegreeRankSunflower.lean`, `Polynomial/MajorWeightedDegreeTools.lean`, `Polynomial/PolynomialDownsetQuotients.lean`, `Polynomial/PolynomialShearAffineExponential.lean`, `Polynomial/PolynomialShearRealGroup.lean`, `Polynomial/SquarefreePolynomialPermutation.lean`, `Polynomial/SquarefreePolynomialQuotient.lean`, `Polynomial/SquarefreeTotalDegree.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B068
import Definitions.Def_OAIE3v2B069

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DilationPairFiltration
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def dilationPairFirst (q : ℚ) : F.dilationPairSubalgebra q →ₗ⁅ℚ⁆ L :=
  (LieHom.fst ℚ L L).comp (F.dilationPairSubalgebra q).incl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DegreeRankSunflower
namespace OAI

section

namespace Erdos3

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t r : ℕ} (F : NilpotentLieFiltration L s) (G : DegreeRankLieFiltration M t r)
  (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ d, ∀ x ∈ F.layer d, φ x ∈ G.layer d 0)

include hφ in
theorem FilteredLieTree.map_eval_mem_degreeRank {d k : ℕ} (a : FilteredLieTree F d k) :
    φ a.eval ∈ G.layer d k := by
  induction a with
  | leaf hd x hx =>
    rw [FilteredLieTree.eval_leaf, ← G.rank_zero_eq_one]
    exact hφ _ x hx
  | bracket a b ha hb =>
    rw [FilteredLieTree.eval_bracket, φ.map_lie]
    exact G.lie_mem ha hb

include hφ in
theorem NilpotentLieFiltration.map_rankLayer {d k : ℕ} {x : L}
    (hx : x ∈ F.rankLayer d k) : φ x ∈ G.layer d k := by
  have hle : F.rankLayer d k ≤ (G.layer d k).comap φ.toLinearMap := by
    apply sup_le
    · intro y hy
      exact G.lex_antitone (Or.inl (Nat.lt_succ_self d)) (hφ (d + 1) y hy)
    · apply Submodule.span_le.mpr
      rintro y ⟨n, hn, a, rfl⟩
      exact G.rank_antitone d hn (a.map_eval_mem_degreeRank F G φ hφ)
  exact hle hx

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.HorizontalAmbientQuotient
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

def higherHorizontalAmbient (d : ℕ) : F.HigherHorizontal d →ₗ[ℚ] L ⧸ F.layer d 2 :=
  (F.higherHorizontalKernel d).liftQ
    ((F.layer d 2).mkQ.comp (F.layer d 1).subtype) (by
      intro x hx
      exact (Submodule.Quotient.mk_eq_zero (F.layer d 2)).mpr hx)

@[simp] theorem higherHorizontalAmbient_mk (d : ℕ) (x : F.layer d 1) :
    F.higherHorizontalAmbient d (F.higherHorizontalMk d x) = (F.layer d 2).mkQ x.val := rfl

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SquarefreePolynomialQuotient
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem squarefreeMk_monomial_zero (a : ι →₀ ℕ) (ha : ¬SquarefreeExponent a) (v : L) :
    squarefreeMk (monomial a v) = (0 : SquarefreePolynomial ι L) :=
  (lieQuotientMap_eq_zero _ _).mpr (monomial_mem_squarefreeKernel a ha v)

noncomputable def squarefreeMonomial (a : SquarefreeIndex ι) : L →ₗ[ℚ] SquarefreePolynomial ι L where
  toFun v := squarefreeMk (monomial a.val v)
  map_add' v w := by simp only [monomial, TensorProduct.tmul_add, map_add]
  map_smul' r v := by simp only [monomial, TensorProduct.tmul_smul, map_smul, RingHom.id_apply]

theorem squarefreeMonomial_apply (a : SquarefreeIndex ι) (v : L) :
    squarefreeMonomial a v = squarefreeMk (monomial a.val v) := rfl

theorem squarefreePolynomialEquiv_monomial_self [Fintype ι] (a : SquarefreeIndex ι) (v : L) :
    squarefreePolynomialEquiv (squarefreeMonomial a v) a = v :=
  squarefreeCoefficients_monomial_self a v

theorem squarefreePolynomialEquiv_monomial_ne [Fintype ι]
    (a b : SquarefreeIndex ι) (hab : a ≠ b) (v : L) :
    squarefreePolynomialEquiv (squarefreeMonomial a v) b = 0 :=
  squarefreeCoefficients_monomial_ne a b hab v

theorem sum_squarefreeMonomial [Fintype ι] (x : SquarefreePolynomial ι L) :
    (∑ a : SquarefreeIndex ι, squarefreeMonomial a (squarefreePolynomialEquiv x a)) = x := by
  classical
  apply squarefreePolynomialEquiv.injective
  ext b
  simp only [map_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single b]
  · exact squarefreePolynomialEquiv_monomial_self b _
  · intro a _ h
    exact squarefreePolynomialEquiv_monomial_ne a b h _
  · simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.SquarefreeBracketCoefficients
namespace OAI

section

namespace Erdos3

open VectorPolynomial

noncomputable def SquarefreeIndex.disjointAdd {ι : Type*} (a b : SquarefreeIndex ι)
    (h : Disjoint a.val.support b.val.support) : SquarefreeIndex ι :=
  ⟨a.val + b.val, (squarefreeExponent_add_iff a.val b.val a.property b.property).mpr h⟩

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem squarefreeMonomial_lie_disjoint (a b : SquarefreeIndex ι)
    (h : Disjoint a.val.support b.val.support) (v w : L) :
    ⁅squarefreeMonomial a v, squarefreeMonomial b w⁆ =
      squarefreeMonomial (a.disjointAdd b h) ⁅v, w⁆ := by
  simp only [squarefreeMonomial_apply, ← LieHom.map_lie, lie_monomial]
  rfl

theorem squarefreeMonomial_lie_overlap (a b : SquarefreeIndex ι)
    (h : ¬Disjoint a.val.support b.val.support) (v w : L) :
    ⁅squarefreeMonomial a v, squarefreeMonomial b w⁆ = 0 := by
  simp only [squarefreeMonomial_apply, ← LieHom.map_lie, lie_monomial]
  exact squarefreeMk_monomial_zero _
    (fun hs => h ((squarefreeExponent_add_iff a.val b.val a.property b.property).mp hs)) _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MultidegreeDilationPair
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def squarefreeAdaptedModule : Submodule ℚ (SquarefreePolynomial ι L) where
  carrier := {x | ∀ a : SquarefreeIndex ι,
    squarefreePolynomialEquiv x a ∈ F.layer (blockDegree π a.val) ∧
      (a.val = 0 → squarefreePolynomialEquiv x a = 0)}
  zero_mem' := by
    intro a
    simp only [map_zero, Pi.zero_apply]
    exact ⟨(F.layer _).zero_mem, fun _ => True.intro⟩
  add_mem' := by
    intro x y hx hy a
    simp only [map_add, Pi.add_apply]
    exact ⟨(F.layer _).add_mem (hx a).1 (hy a).1,
      fun ha => by rw [(hx a).2 ha, (hy a).2 ha, add_zero]⟩
  smul_mem' := by
    intro r x hx a
    simp only [map_smul, Pi.smul_apply]
    exact ⟨(F.layer _).smul_mem r (hx a).1,
      fun ha => by rw [(hx a).2 ha, smul_zero]⟩

theorem squarefreeMonomial_mem_adapted (a : SquarefreeIndex ι) (ha : a.val ≠ 0)
    (v : L) (hv : v ∈ F.layer (blockDegree π a.val)) :
    squarefreeMonomial a v ∈ F.squarefreeAdaptedModule π := by
  intro b
  by_cases hab : a = b
  · subst b
    rw [squarefreePolynomialEquiv_monomial_self]
    exact ⟨hv, fun he => False.elim (ha he)⟩
  · rw [squarefreePolynomialEquiv_monomial_ne a b hab v]
    exact ⟨(F.layer _).zero_mem, fun _ => rfl⟩

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHLatticeImageGap
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Manifold
open scoped Manifold ContDiff Bundle NNReal ENNReal

section Norm

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem norm_tangent_eq_coordinateL2Norm (e : Basis ι ℝ L) (g : NilpotentLieBCHGroup L s hnil) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := rightRiemannianBundle (hnil := hnil) e
    ∀ v : TangentSpace 𝓘(ℝ, ι → ℝ) g, ‖v‖ = coordinateL2Norm (rightVelocity e g v) := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  intro v
  rw [norm_eq_sqrt_real_inner]
  change Real.sqrt (rightInnerForm e g v v) = _
  simpa only [coordinateL2Norm, pow_two] using
    congrArg Real.sqrt (rightInnerForm_apply e g v v)

end Norm

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Manifold
open scoped Manifold ContDiff Bundle NNReal ENNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem rightTranslate_fderiv_zero_rightVelocity (e : Basis ι ℝ L)
    (g : NilpotentLieBCHGroup L s hnil) :
    (fderiv ℝ (rightTranslate e g) 0).comp (rightVelocity e g) =
      ContinuousLinearMap.id ℝ (ι → ℝ) := by
  have h := rightTranslate_fderiv_leftInverse e g⁻¹ (basisHomeomorph e g)
  rw [rightTranslate_coordinates, mul_inv_cancel] at h
  simpa only [inv_inv, rightTranslate_coordinates, mul_inv_cancel, basisHomeomorph_apply,
    coord_one, map_zero, rightVelocity] using h

omit [IsScalarTower ℚ ℝ L] in
theorem mfderiv_basisHomeomorph_coordinates (e : Basis ι ℝ L)
    (g : NilpotentLieBCHGroup L s hnil) (v : ι → ℝ) :
    letI := basisChartedSpace (hnil := hnil) e
    mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (basisHomeomorph e) g v = v := by
  let := basisChartedSpace (hnil := hnil) e
  have hm := (contMDiff_basisHomeomorph (hnil := hnil) e 1).mdifferentiableAt (x := g) one_ne_zero
  have heq : writtenInExtChartAt 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) g (basisHomeomorph e) = id := by
    funext x
    simp only [writtenInExtChartAt, Function.comp_apply, basis_extChartAt_symm_apply,
      extChartAt_model_space_eq_id, Homeomorph.apply_symm_apply, id_eq]
    rfl
  rw [hm.mfderiv, heq]
  simp only [modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ, fderiv_id]
  rfl

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Manifold
open scoped Manifold ContDiff Bundle

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (v : ι → ℝ)

theorem contMDiff_coordinateLine (n : ℕ∞ω) :
    letI := basisChartedSpace (hnil := hnil) e
    ContMDiff 𝓘(ℝ) 𝓘(ℝ, ι → ℝ) n (coordinateLine (hnil := hnil) e v) := by
  let := basisChartedSpace (hnil := hnil) e
  exact (contMDiff_basisHomeomorph_symm e n).comp (contMDiff_id.smul contMDiff_const)

theorem rightTranslate_coordinateLine_inv (t u : ℝ) :
    rightTranslate e (coordinateLine (hnil := hnil) e v t)⁻¹ (u • v) = (u - t) • v := by
  change e.equivFun (lieBCH s (e.equivFun.symm (u • v)) (-e.equivFun.symm (t • v))) = _
  rw [map_smul, map_smul, lieBCH_eq_add_of_lie_eq_zero hnil (by simp [smul_lie, lie_smul])]
  simp only [map_add, map_neg, map_smul, LinearEquiv.apply_symm_apply, sub_eq_add_neg, add_smul, neg_smul]

variable [IsScalarTower ℚ ℝ L]

theorem rightVelocity_coordinateLine (t : ℝ) :
    rightVelocity e (coordinateLine (hnil := hnil) e v t) v = v := by
  have hl : HasDerivAt (fun u : ℝ => u • v) v t := by
    simpa using (hasDerivAt_id t).smul_const v
  have hr := ((contDiff_rightTranslate e (coordinateLine (hnil := hnil) e v t)⁻¹ 1).differentiable
    one_ne_zero).differentiableAt (x := t • v) |>.hasFDerivAt
  have hcomp := hr.comp_hasDerivAt t hl
  have heq : rightTranslate e (coordinateLine (hnil := hnil) e v t)⁻¹ ∘ (fun u : ℝ => u • v) =
      fun u : ℝ => (u - t) • v := funext (rightTranslate_coordinateLine_inv e v t)
  rw [heq] at hcomp
  have hd : HasDerivAt (fun u : ℝ => (u - t) • v) v t := by
    simpa using ((hasDerivAt_id t).sub_const t).smul_const v
  simpa only [rightVelocity, coordinateLine, Homeomorph.apply_symm_apply] using hcomp.unique hd

omit [IsScalarTower ℚ ℝ L] in
theorem mfderiv_coordinateLine (t : ℝ) :
    letI := basisChartedSpace (hnil := hnil) e
    mfderiv 𝓘(ℝ) 𝓘(ℝ, ι → ℝ) (coordinateLine (hnil := hnil) e v) t 1 = v := by
  let := basisChartedSpace (hnil := hnil) e
  have hm := (contMDiff_coordinateLine (hnil := hnil) e v 1).mdifferentiableAt (x := t) one_ne_zero
  have heq : writtenInExtChartAt 𝓘(ℝ) 𝓘(ℝ, ι → ℝ) t (coordinateLine (hnil := hnil) e v) =
      fun u : ℝ => u • v := by
    funext u
    simp [writtenInExtChartAt, coordinateLine]
    rfl
  rw [hm.mfderiv, heq]
  simp only [modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ]
  change deriv (fun u : ℝ => u • v) t = v
  exact (show HasDerivAt (fun u : ℝ => u • v) v t by
    simpa using (hasDerivAt_id t).smul_const v).deriv

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeAdaptedLieAlgebra
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem squarefreeAdapted_lie_mem (x y : SquarefreePolynomial ι L)
    (hx : x ∈ F.squarefreeAdaptedModule π) (hy : y ∈ F.squarefreeAdaptedModule π) :
    ⁅x, y⁆ ∈ F.squarefreeAdaptedModule π := by
  classical
  rw [← sum_squarefreeMonomial x, ← sum_squarefreeMonomial y, sum_lie_sum]
  apply Submodule.sum_mem
  intro a _
  apply Submodule.sum_mem
  intro b _
  by_cases ha : a.val = 0
  · rw [(hx a).2 ha, map_zero, zero_lie]
    exact (F.squarefreeAdaptedModule π).zero_mem
  by_cases hb : b.val = 0
  · rw [(hy b).2 hb, map_zero, lie_zero]
    exact (F.squarefreeAdaptedModule π).zero_mem
  by_cases hab : Disjoint a.val.support b.val.support
  · rw [squarefreeMonomial_lie_disjoint a b hab]
    apply F.squarefreeMonomial_mem_adapted π
    · change a.val + b.val ≠ 0
      intro he
      apply ha
      ext i
      have hi := congrArg (fun c : ι →₀ ℕ => c i) he
      simp only [Finsupp.add_apply, Finsupp.zero_apply] at hi ⊢
      omega
    · change ⁅squarefreePolynomialEquiv x a, squarefreePolynomialEquiv y b⁆ ∈
        F.layer (blockDegree π (a.val + b.val))
      rw [blockDegree_add]
      exact F.lie_mem (hx a).1 (hy b).1
  · rw [squarefreeMonomial_lie_overlap a b hab]
    exact (F.squarefreeAdaptedModule π).zero_mem

noncomputable def squarefreeAdaptedSubalgebra : LieSubalgebra ℚ (SquarefreePolynomial ι L) :=
  { F.squarefreeAdaptedModule π with
    lie_mem' := fun hx hy => F.squarefreeAdapted_lie_mem π _ _ hx hy }

abbrev SquarefreeAlgebra := ↥(F.squarefreeAdaptedSubalgebra π)

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SquarefreeAlgebraCoordinates
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def squarefreeCoefficientLayer (a : SquarefreeIndex ι) : Submodule ℚ L := by
  classical
  exact if a.val = 0 then ⊥ else F.layer (blockDegree π a.val)

theorem mem_squarefreeCoefficientLayer (a : SquarefreeIndex ι) (v : L) :
    v ∈ F.squarefreeCoefficientLayer π a ↔
      v ∈ F.layer (blockDegree π a.val) ∧ (a.val = 0 → v = 0) := by
  classical
  by_cases ha : a.val = 0 <;> simp [squarefreeCoefficientLayer, ha, F.zero_eq_top]

noncomputable def squarefreeAlgebraEquiv :
    F.SquarefreeAlgebra π ≃ₗ[ℚ] ((a : SquarefreeIndex ι) → F.squarefreeCoefficientLayer π a) where
  toFun x a := ⟨squarefreePolynomialEquiv x.val a,
    (F.mem_squarefreeCoefficientLayer π a _).mpr (x.property a)⟩
  invFun f := ⟨squarefreePolynomialEquiv.symm (fun a => (f a).val), by
    intro a
    simpa only [LinearEquiv.apply_symm_apply] using
      (F.mem_squarefreeCoefficientLayer π a _).mp (f a).property⟩
  left_inv x := by
    apply Subtype.ext
    exact squarefreePolynomialEquiv.symm_apply_apply x.val
  right_inv f := by
    ext a
    exact congrFun (squarefreePolynomialEquiv.apply_symm_apply (fun b => (f b).val)) a
  map_add' x y := by
    ext a
    exact congrFun (map_add squarefreePolynomialEquiv x.val y.val) a
  map_smul' r x := by
    ext a
    exact congrFun (map_smul squarefreePolynomialEquiv r x.val) a

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeSplitCount
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι κ σ : Type*}

def SquarefreeIndex.permute (e : ι ≃ κ) : SquarefreeIndex ι ≃ SquarefreeIndex κ where
  toFun a := ⟨Finsupp.equivMapDomain e a.val, fun j => a.property (e.symm j)⟩
  invFun b := ⟨Finsupp.equivMapDomain e.symm b.val, fun i => b.property (e i)⟩
  left_inv a := Subtype.ext ((Finsupp.equivCongrLeft e).left_inv a.val)
  right_inv b := Subtype.ext ((Finsupp.equivCongrLeft e).right_inv b.val)

@[simp] theorem SquarefreeIndex.permute_apply (e : ι ≃ κ) (a : SquarefreeIndex ι) (j : κ) :
    (permute e a).val j = a.val (e.symm j) := rfl

theorem SquarefreeIndex.permute_disjoint (e : ι ≃ κ) (a b : SquarefreeIndex ι) :
    Disjoint (permute e a).val.support (permute e b).val.support ↔
      Disjoint a.val.support b.val.support := Finset.disjoint_map e.toEmbedding

theorem SquarefreeIndex.permute_disjointAdd (e : ι ≃ κ) (a b : SquarefreeIndex ι)
    (hab : Disjoint a.val.support b.val.support) :
    permute e (a.disjointAdd b hab) =
      (permute e a).disjointAdd (permute e b) ((permute_disjoint e a b).mpr hab) := by
  apply Subtype.ext
  ext j
  rfl

theorem SquarefreeIndex.permute_zero_iff (e : ι ≃ κ) (a : SquarefreeIndex ι) :
    (permute e a).val = 0 ↔ a.val = 0 := by
  constructor
  · intro h
    ext i
    have hi := congrArg (fun c : κ →₀ ℕ => c (e i)) h
    simpa only [permute_apply, Equiv.symm_apply_apply, Finsupp.zero_apply] using hi
  · intro h
    ext j
    simp only [permute_apply, h, Finsupp.zero_apply]

theorem SquarefreeIndex.permute_blockDegree [Fintype ι] (π : ι → σ)
    (e : ι ≃ ι) (he : ∀ i, π (e i) = π i) (a : SquarefreeIndex ι) :
    blockDegree π (permute e a).val = blockDegree π a.val := by
  classical
  ext i
  simp only [blockDegree_apply, permute_apply]
  calc
    (∑ j, if π j = i then a.val (e.symm j) else 0) =
        ∑ j, if π (e j) = i then a.val j else 0 := by
      simpa only [Equiv.symm_apply_apply] using
        (Equiv.sum_comp e (fun j => if π j = i then a.val (e.symm j) else 0)).symm
    _ = _ := by simp only [he]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SquarefreePolynomialPermutation
namespace OAI

section

namespace Erdos3

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]

noncomputable def squarefreePermute (e : ι ≃ κ) :
    SquarefreePolynomial ι L ≃ₗ[ℚ] SquarefreePolynomial κ L :=
  squarefreePolynomialEquiv.trans
    ((LinearEquiv.funCongrLeft ℚ L (SquarefreeIndex.permute e).symm).trans
      squarefreePolynomialEquiv.symm)

theorem squarefreePermute_coefficient (e : ι ≃ κ) (x : SquarefreePolynomial ι L)
    (a : SquarefreeIndex κ) :
    squarefreePolynomialEquiv (squarefreePermute e x) a =
      squarefreePolynomialEquiv x ((SquarefreeIndex.permute e).symm a) := by
  change squarefreePolynomialEquiv (squarefreePolynomialEquiv.symm _) a = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem squarefreePermute_monomial (e : ι ≃ κ) (a : SquarefreeIndex ι) (v : L) :
    squarefreePermute e (squarefreeMonomial a v) =
      squarefreeMonomial (SquarefreeIndex.permute e a) v := by
  apply squarefreePolynomialEquiv.injective
  ext b
  obtain ⟨b, rfl⟩ := (SquarefreeIndex.permute e).surjective b
  rw [squarefreePermute_coefficient, Equiv.symm_apply_apply]
  by_cases h : a = b
  · subst b
    rw [squarefreePolynomialEquiv_monomial_self, squarefreePolynomialEquiv_monomial_self]
  · rw [squarefreePolynomialEquiv_monomial_ne a b h,
      squarefreePolynomialEquiv_monomial_ne _ _
        (fun he => h ((SquarefreeIndex.permute e).injective he))]

theorem squarefreePermute_symm_apply (e : ι ≃ κ) (x : SquarefreePolynomial ι L) :
    squarefreePermute e.symm (squarefreePermute e x) = x := by
  apply squarefreePolynomialEquiv.injective
  ext a
  rw [squarefreePermute_coefficient, squarefreePermute_coefficient]
  change squarefreePolynomialEquiv x
    ((SquarefreeIndex.permute e).symm (SquarefreeIndex.permute e a)) = _
  rw [Equiv.symm_apply_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SquarefreeSupportPermutation
namespace OAI

section

namespace Erdos3

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

noncomputable def squarefreeSupportModule (P : SquarefreeIndex ι → Prop) :
    Submodule ℚ (SquarefreePolynomial ι L) where
  carrier := {x | ∀ a, ¬P a → squarefreePolynomialEquiv x a = 0}
  zero_mem' := by
    intro a _
    exact congrFun (map_zero squarefreePolynomialEquiv) a
  add_mem' := by
    intro x y hx hy a ha
    rw [map_add, Pi.add_apply, hx a ha, hy a ha, add_zero]
  smul_mem' := by
    intro r x hx a ha
    rw [map_smul, Pi.smul_apply, hx a ha, smul_zero]

theorem squarefreeMonomial_mem_support {P : SquarefreeIndex ι → Prop}
    (a : SquarefreeIndex ι) (ha : P a) (v : L) :
    squarefreeMonomial a v ∈ squarefreeSupportModule P := by
  intro b hb
  exact squarefreePolynomialEquiv_monomial_ne a b
    (fun he => hb (he ▸ ha)) v

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.SquarefreeSupportBracket
namespace OAI

section

namespace Erdos3

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem squarefreeSupportModule_lie_mem {P Q R : SquarefreeIndex ι → Prop}
    (h : ∀ a b (hab : Disjoint a.val.support b.val.support),
      P a → Q b → R (a.disjointAdd b hab))
    {x y : SquarefreePolynomial ι L}
    (hx : x ∈ squarefreeSupportModule P) (hy : y ∈ squarefreeSupportModule Q) :
    ⁅x, y⁆ ∈ squarefreeSupportModule R := by
  classical
  rw [← sum_squarefreeMonomial x, ← sum_squarefreeMonomial y, sum_lie_sum]
  apply Submodule.sum_mem
  intro a _
  apply Submodule.sum_mem
  intro b _
  by_cases ha : P a
  · by_cases hb : Q b
    · by_cases hab : Disjoint a.val.support b.val.support
      · rw [squarefreeMonomial_lie_disjoint a b hab]
        exact squarefreeMonomial_mem_support _ (h a b hab ha hb) _
      · rw [squarefreeMonomial_lie_overlap a b hab]
        exact (squarefreeSupportModule R).zero_mem
    · rw [hy b hb, map_zero, lie_zero]
      exact (squarefreeSupportModule R).zero_mem
  · rw [hx a ha, map_zero, zero_lie]
    exact (squarefreeSupportModule R).zero_mem

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SquarefreeTotalDegree
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem squarefreeExponent_total_le (a : SquarefreeIndex ι) :
    (∑ i, a.val i) ≤ Fintype.card ι := by
  calc
    _ ≤ ∑ _i : ι, 1 := Finset.sum_le_sum fun i _ => a.property i
    _ = _ := by simp

theorem squarefreeDisjointAdd_total (a b : SquarefreeIndex ι)
    (hab : Disjoint a.val.support b.val.support) :
    (∑ i, (a.disjointAdd b hab).val i) = (∑ i, a.val i) + ∑ i, b.val i := by
  change (∑ i, (a.val + b.val) i) = _
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreePermutationFiltration
namespace OAI

section

namespace Erdos3

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]

theorem squarefreePermute_monomial_lie (e : ι ≃ κ) (a b : SquarefreeIndex ι) (v w : L) :
    squarefreePermute e ⁅squarefreeMonomial a v, squarefreeMonomial b w⁆ =
      ⁅squarefreePermute e (squarefreeMonomial a v),
        squarefreePermute e (squarefreeMonomial b w)⁆ := by
  by_cases hab : Disjoint a.val.support b.val.support
  · rw [squarefreeMonomial_lie_disjoint a b hab]
    simp only [squarefreePermute_monomial]
    rw [squarefreeMonomial_lie_disjoint _ _ ((SquarefreeIndex.permute_disjoint e a b).mpr hab),
      SquarefreeIndex.permute_disjointAdd]
  · rw [squarefreeMonomial_lie_overlap a b hab, map_zero]
    simp only [squarefreePermute_monomial]
    rw [squarefreeMonomial_lie_overlap _ _
      (fun h => hab ((SquarefreeIndex.permute_disjoint e a b).mp h))]

theorem squarefreePermute_lie (e : ι ≃ κ) (x y : SquarefreePolynomial ι L) :
    squarefreePermute e ⁅x, y⁆ = ⁅squarefreePermute e x, squarefreePermute e y⁆ := by
  classical
  conv_lhs =>
    rw [← sum_squarefreeMonomial x, ← sum_squarefreeMonomial y, sum_lie_sum]
    simp only [map_sum]
  conv_rhs =>
    rw [← sum_squarefreeMonomial x, ← sum_squarefreeMonomial y]
    simp only [map_sum]
    rw [sum_lie_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact squarefreePermute_monomial_lie e a b _ _

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def squarefreeDegreeLayer (n : ℕ) : Submodule ℚ (F.SquarefreeAlgebra π) :=
  (squarefreeSupportModule (fun a : SquarefreeIndex ι => n ≤ ∑ i, a.val i)).comap
    (F.squarefreeAdaptedSubalgebra π).incl.toLinearMap

theorem squarefreeDegreeLayer_antitone : Antitone (F.squarefreeDegreeLayer π) := by
  intro n m h x hx a ha
  exact hx a (fun hm => ha (h.trans hm))

theorem squarefreeDegreeLayer_lie_mem {n m : ℕ} {x y : F.SquarefreeAlgebra π}
    (hx : x ∈ F.squarefreeDegreeLayer π n) (hy : y ∈ F.squarefreeDegreeLayer π m) :
    ⁅x, y⁆ ∈ F.squarefreeDegreeLayer π (n + m) := by
  apply squarefreeSupportModule_lie_mem (x := x.val) (y := y.val) ?_ hx hy
  intro a b hab ha hb
  rw [squarefreeDisjointAdd_total]
  exact Nat.add_le_add ha hb

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem squarefreeDegreeLayer_one : F.squarefreeDegreeLayer π 1 = ⊤ := by
  apply top_unique
  intro x _ a ha
  have hzero : a.val = 0 := (exponent_total_eq_zero_iff a.val).mp (by omega)
  exact (x.property a).2 hzero

theorem squarefreeDegreeLayer_terminal : F.squarefreeDegreeLayer π (Fintype.card ι + 1) = ⊥ := by
  apply bot_unique
  intro x hx
  change x = 0
  apply Subtype.ext
  apply squarefreePolynomialEquiv.injective
  ext a
  apply hx a
  have h := squarefreeExponent_total_le a
  omega

noncomputable def squarefreeOrdinaryFiltration :
    NilpotentLieFiltration (F.SquarefreeAlgebra π) (Fintype.card ι) where
  layer := F.squarefreeDegreeLayer π
  antitone := F.squarefreeDegreeLayer_antitone π
  one_eq_top := F.squarefreeDegreeLayer_one π
  lie_mem := F.squarefreeDegreeLayer_lie_mem π
  terminal := F.squarefreeDegreeLayer_terminal π

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem squarefreePermute_mem_adapted (e : ι ≃ ι) (he : ∀ i, π (e i) = π i)
    (x : SquarefreePolynomial ι L) (hx : x ∈ F.squarefreeAdaptedModule π) :
    squarefreePermute e x ∈ F.squarefreeAdaptedModule π := by
  intro a
  rw [squarefreePermute_coefficient]
  have hd : blockDegree π ((SquarefreeIndex.permute e).symm a).val = blockDegree π a.val :=
    SquarefreeIndex.permute_blockDegree π e.symm (blockPermutation_symm π e he) a
  refine ⟨?_, ?_⟩
  · rw [← hd]
    exact (hx _).1
  · intro ha
    exact (hx _).2 ((SquarefreeIndex.permute_zero_iff e.symm a).mpr ha)

noncomputable def squarefreeBlockPermute (e : ι ≃ ι) (he : ∀ i, π (e i) = π i) :
    F.SquarefreeAlgebra π ≃ₗ⁅ℚ⁆ F.SquarefreeAlgebra π where
  toFun x := ⟨squarefreePermute e x.val, F.squarefreePermute_mem_adapted π e he _ x.property⟩
  invFun x := ⟨squarefreePermute e.symm x.val,
    F.squarefreePermute_mem_adapted π e.symm (blockPermutation_symm π e he) _ x.property⟩
  left_inv x := Subtype.ext (squarefreePermute_symm_apply e x.val)
  right_inv x := Subtype.ext (squarefreePermute_symm_apply e.symm x.val)
  map_add' x y := Subtype.ext (map_add (squarefreePermute e) x.val y.val)
  map_smul' r x := Subtype.ext (map_smul (squarefreePermute e) r x.val)
  map_lie' {x y} := Subtype.ext (squarefreePermute_lie e x.val y.val)

theorem squarefreeBlockPermute_apply (e : ι ≃ ι) (he : ∀ i, π (e i) = π i)
    (x : F.SquarefreeAlgebra π) :
    (F.squarefreeBlockPermute π e he x).val = squarefreePermute e x.val := rfl

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

omit [Fintype ι] in
theorem SquarefreeIndex.permute_one (a : SquarefreeIndex ι) : permute (1 : Equiv.Perm ι) a = a := by
  apply Subtype.ext
  ext i
  rfl

theorem squarefreePermute_one (x : SquarefreePolynomial ι L) :
    squarefreePermute (1 : Equiv.Perm ι) x = x := by
  apply squarefreePolynomialEquiv.injective
  ext a
  rw [squarefreePermute_coefficient]
  apply congrArg (squarefreePolynomialEquiv x)
  exact SquarefreeIndex.permute_one a

theorem squarefreePermute_mul (e f : Equiv.Perm ι) (x : SquarefreePolynomial ι L) :
    squarefreePermute (e * f) x = squarefreePermute e (squarefreePermute f x) := by
  apply squarefreePolynomialEquiv.injective
  ext a
  rw [squarefreePermute_coefficient, squarefreePermute_coefficient, squarefreePermute_coefficient]
  apply congrArg (squarefreePolynomialEquiv x)
  apply Subtype.ext
  ext i
  rfl

namespace MultidegreeLieFiltration

variable {σ : Type*} [Fintype σ] {s : ℕ} {bound : σ → ℕ}
  (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem squarefreeBlockPermute_one (x : F.SquarefreeAlgebra π) :
    F.squarefreeBlockPermute π 1 (fun _ => rfl) x = x :=
  Subtype.ext (squarefreePermute_one x.val)

end MultidegreeLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SquarefreeBasisPermutation
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open Module

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)
  {κ : SquarefreeIndex ι → Type*}
  (b : ∀ a, Basis (κ a) ℚ (F.squarefreeCoefficientLayer π a))

noncomputable def squarefreeBasis : Basis (Σ a, κ a) ℚ (F.SquarefreeAlgebra π) :=
  (Pi.basis b).map (F.squarefreeAlgebraEquiv π).symm

theorem squarefreeBasis_repr (x : F.SquarefreeAlgebra π) (j : Σ a, κ a) :
    (F.squarefreeBasis π b).repr x j = (b j.1).repr (F.squarefreeAlgebraEquiv π x j.1) j.2 := by
  rfl

theorem squarefreeBasis_coefficient_self (a : SquarefreeIndex ι) (j : κ a) :
    squarefreePolynomialEquiv (F.squarefreeBasis π b ⟨a, j⟩).val a = (b a j).val := by
  classical
  change (F.squarefreeAlgebraEquiv π (F.squarefreeBasis π b ⟨a, j⟩) a).val = _
  simp only [squarefreeBasis, Basis.map_apply, LinearEquiv.apply_symm_apply, Pi.basis_apply,
    Pi.single_eq_same]

theorem squarefreeBasis_coefficient_ne (a c : SquarefreeIndex ι) (h : a ≠ c) (j : κ a) :
    squarefreePolynomialEquiv (F.squarefreeBasis π b ⟨a, j⟩).val c = 0 := by
  classical
  change (F.squarefreeAlgebraEquiv π (F.squarefreeBasis π b ⟨a, j⟩) c).val = _
  simp only [squarefreeBasis, Basis.map_apply, LinearEquiv.apply_symm_apply, Pi.basis_apply,
    Pi.single_eq_of_ne (Ne.symm h), ZeroMemClass.coe_zero]

theorem squarefreeBasis_monomial (j : Σ a, κ a) :
    (F.squarefreeBasis π b j).val = squarefreeMonomial j.1 (b j.1 j.2).val := by
  apply squarefreePolynomialEquiv.injective
  ext a
  by_cases h : j.1 = a
  · subst a
    rw [F.squarefreeBasis_coefficient_self, squarefreePolynomialEquiv_monomial_self]
  · rw [F.squarefreeBasis_coefficient_ne π b _ _ h,
      squarefreePolynomialEquiv_monomial_ne _ _ h]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)
  {κ : SquarefreeIndex ι → Type*}
  (b : ∀ a, Basis (κ a) ℚ (F.squarefreeCoefficientLayer π a))

theorem squarefreeSupport_eq_span (P : SquarefreeIndex ι → Prop) :
    (squarefreeSupportModule P).comap (F.squarefreeAdaptedSubalgebra π).incl.toLinearMap =
      Submodule.span ℚ (F.squarefreeBasis π b '' {j | P j.1}) := by
  ext x
  rw [basis_mem_span_image_iff]
  constructor
  · intro hx j hj
    have hz : F.squarefreeAlgebraEquiv π x j.1 = 0 := Subtype.ext (hx j.1 hj)
    rw [F.squarefreeBasis_repr, hz, map_zero, Finsupp.zero_apply]
  · intro hx a ha
    have hz : F.squarefreeAlgebraEquiv π x a = 0 := by
      apply (b a).repr.injective
      ext j
      simpa only [F.squarefreeBasis_repr, map_zero, Finsupp.zero_apply] using hx ⟨a, j⟩ ha
    exact congrArg Subtype.val hz

noncomputable def squarefreeSupportedBasis (P : SquarefreeIndex ι → Prop) :
    Basis {j : Σ a, κ a // P j.1} ℚ
      ((squarefreeSupportModule P).comap (F.squarefreeAdaptedSubalgebra π).incl.toLinearMap) :=
  supportedSubmoduleBasis (F.squarefreeBasis π b) _ _ (F.squarefreeSupport_eq_span π b P)

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem squarefreeCoefficientLayer_permute (e : ι ≃ ι) (he : ∀ i, π (e i) = π i)
    (a : SquarefreeIndex ι) :
    F.squarefreeCoefficientLayer π (SquarefreeIndex.permute e a) = F.squarefreeCoefficientLayer π a := by
  classical
  simp only [squarefreeCoefficientLayer, SquarefreeIndex.permute_zero_iff,
    SquarefreeIndex.permute_blockDegree π e he a]

theorem squarefreeBasis_permute
    (b : ∀ U : Submodule ℚ L, Basis (Fin (finrank ℚ U)) ℚ U)
    (e : ι ≃ ι) (he : ∀ i, π (e i) = π i)
    (j : Σ a : SquarefreeIndex ι, Fin (finrank ℚ (F.squarefreeCoefficientLayer π a))) :
    ∃ k, F.squarefreeBlockPermute π e he (F.squarefreeBasis π (fun a => b (F.squarefreeCoefficientLayer π a)) j) =
      F.squarefreeBasis π (fun a => b (F.squarefreeCoefficientLayer π a)) k := by
  have hex : ∃ k,
      (b (F.squarefreeCoefficientLayer π (SquarefreeIndex.permute e j.1)) k).val =
        (b (F.squarefreeCoefficientLayer π j.1) j.2).val := by
    rw [F.squarefreeCoefficientLayer_permute π e he]
    exact ⟨j.2, rfl⟩
  obtain ⟨k, hk⟩ := hex
  refine ⟨⟨SquarefreeIndex.permute e j.1, k⟩, ?_⟩
  apply Subtype.ext
  rw [F.squarefreeBlockPermute_apply, F.squarefreeBasis_monomial, squarefreePermute_monomial,
    F.squarefreeBasis_monomial]
  exact congrArg (squarefreeMonomial (SquarefreeIndex.permute e j.1)) hk.symm

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHSmoothPartitionBudget
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Manifold MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (v : ι → ℝ)

theorem norm_mfderiv_coordinateLine (t : ℝ) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := rightRiemannianBundle (hnil := hnil) e
    ‖mfderiv 𝓘(ℝ) 𝓘(ℝ, ι → ℝ) (coordinateLine (hnil := hnil) e v) t 1‖ = coordinateL2Norm v := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  have hv := (congrArg (fun w : ι → ℝ => rightVelocity e (coordinateLine (hnil := hnil) e v t) w)
    (mfderiv_coordinateLine (hnil := hnil) e v t)).trans (rightVelocity_coordinateLine e v t)
  exact (norm_tangent_eq_coordinateL2Norm e (coordinateLine (hnil := hnil) e v t) _).trans
    (congrArg coordinateL2Norm hv)

theorem enorm_mfderiv_coordinateLine (t : ℝ) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := rightRiemannianBundle (hnil := hnil) e
    ‖mfderiv 𝓘(ℝ) 𝓘(ℝ, ι → ℝ) (coordinateLine (hnil := hnil) e v) t 1‖ₑ =
      ENNReal.ofReal (coordinateL2Norm v) := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  rw [← ofReal_norm]
  exact congrArg ENNReal.ofReal (norm_mfderiv_coordinateLine e v t)

theorem pathELength_coordinateLine :
    letI := basisChartedSpace (hnil := hnil) e
    letI := rightRiemannianBundle (hnil := hnil) e
    pathELength 𝓘(ℝ, ι → ℝ) (coordinateLine (hnil := hnil) e v) 0 1 =
      ENNReal.ofReal (coordinateL2Norm v) := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  rw [pathELength_eq_lintegral_mfderiv_Icc]
  have hf : (fun t : ℝ => ‖mfderiv 𝓘(ℝ) 𝓘(ℝ, ι → ℝ) (coordinateLine (hnil := hnil) e v) t 1‖ₑ) =
      fun _ => ENNReal.ofReal (coordinateL2Norm v) :=
    funext (enorm_mfderiv_coordinateLine e v)
  rw [hf]
  simp

theorem dist_one_le_coordinateL2Norm (g : NilpotentLieBCHGroup L s hnil) :
    letI := rightMetricSpace (hnil := hnil) e
    dist 1 g ≤ coordinateL2Norm (basisHomeomorph e g) := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  let := rightMetricSpace (hnil := hnil) e
  have hedist : edist 1 g ≤ ENNReal.ofReal (coordinateL2Norm (basisHomeomorph e g)) := by
    apply (riemannianEDist_le_pathELength
      (contMDiff_coordinateLine e (basisHomeomorph e g) 1).contMDiffOn
      (coordinateLine_zero e _) (by simp only [coordinateLine_one, Homeomorph.symm_apply_apply])
      zero_le_one).trans_eq
    exact pathELength_coordinateLine e _
  rw [dist_edist]
  exact (ENNReal.toReal_mono (by simp) hedist).trans_eq
    (ENNReal.toReal_ofReal (coordinateL2Norm_nonneg _))

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHUniformQuotientCharts
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

section Quotient

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
  (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))

theorem quotientMetricSpace_lipschitz_orbit (x : NilpotentLieBCHGroup L s hnil ⧸ Γ) :
    letI := rightMetricSpace (hnil := hnil) e
    letI := quotientMetricSpace e Γ hΓ
    LipschitzWith 1 (fun a : NilpotentLieBCHGroup L s hnil => a • x) := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace_isIsometricSMul (hnil := hnil) e
  exact lipschitz_quotient_orbit Γ hΓ x

end Quotient

end Erdos3.NilpotentLieBCHGroup

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

theorem NilpotentLieFiltration.top_layer_central (F : NilpotentLieFiltration L s)
    {v : L} (hv : v ∈ F.layer s) (w : L) : ⁅v, w⁆ = 0 := by
  have hw : w ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have h := F.lie_mem hv hw
  simpa only [F.terminal, Submodule.mem_bot] using h

theorem rationalLieInclusion_central (v : L) (hv : ∀ w : L, ⁅v, w⁆ = 0)
    (w : ℝ ⊗[ℚ] L) : ⁅rationalLieInclusion v, w⁆ = 0 := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul r w => simp only [rationalLieInclusion_apply, LieAlgebra.ExtendScalars.bracket_tmul,
      hv, TensorProduct.tmul_zero]
  | add x y hx hy => rw [lie_add, hx, hy, add_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealificationFixedSubmodule
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem realificationLieHom_eq_self (φ : L →ₗ⁅ℚ⁆ L) (hφ : ∀ x, φ x = x)
    (x : ℝ ⊗[ℚ] L) : realificationLieHom φ x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => rw [realificationLieHom_tmul, hφ]
  | add x y hx hy => rw [map_add, hx, hy]

theorem realificationLieHom_comp_apply (φ ψ θ : L →ₗ⁅ℚ⁆ L)
    (h : ∀ x, θ x = φ (ψ x)) (x : ℝ ⊗[ℚ] L) :
    realificationLieHom θ x = realificationLieHom φ (realificationLieHom ψ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => simp only [realificationLieHom_tmul, h]
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHOuterGridChangeBasis
namespace OAI

section

namespace Erdos3

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem bchSubgroupCoordinates_repr (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (g : NilpotentLieBCHGroup L s hnil) :
    e.equivFun g.coord ∈ bchSubgroupCoordinates e Γ ↔ g ∈ Γ := by
  change (⟨e.equivFun.symm (e.equivFun g.coord)⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ ↔ _
  rw [LinearEquiv.symm_apply_apply]

theorem subgroupPowerCover_inner_grid (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l m : ℕ)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ) :
    scaledIntegerGrid (m * l) ⊆ bchSubgroupCoordinates e (subgroupPowerCover Γ m) := by
  rintro x ⟨z, rfl⟩
  let g : NilpotentLieBCHGroup L s hnil := ⟨e.equivFun.symm ((l : ℚ) • fun i => (z i : ℚ))⟩
  have hg : g ∈ Γ := hinner ⟨z, rfl⟩
  have heq : e.equivFun (g ^ m).coord = ((m * l : ℕ) : ℚ) • fun i => (z i : ℚ) := by
    rw [NilpotentLieBCHGroup.coord_pow_rat, map_smul]
    change (m : ℚ) • e.equivFun (e.equivFun.symm ((l : ℚ) • fun i => (z i : ℚ))) = _
    rw [LinearEquiv.apply_symm_apply, smul_smul, Nat.cast_mul]
  rw [← heq]
  exact (bchSubgroupCoordinates_repr e _ _).mpr (pow_mem_subgroupPowerCover Γ hg m)

end Erdos3

end

section

namespace Erdos3

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem coordinateGridBCHSubgroup_coordinates (e : Basis ι ℚ L) (B : ℕ) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (hstable : ∀ a ∈ coordinateGridModule e B, ∀ b ∈ coordinateGridModule e B,
      lieBCH s a b ∈ coordinateGridModule e B) :
    bchSubgroupCoordinates e (coordinateGridBCHSubgroup e B hnil hstable) = scaledIntegerGrid B := by
  ext x
  change e.equivFun (e.equivFun.symm x) ∈ scaledIntegerGrid B ↔ x ∈ scaledIntegerGrid B
  rw [LinearEquiv.apply_symm_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ConjugationCoordinates
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial

theorem scaledIntegerGrid_mem_denominatorGrid {ι : Type*} (m q : ℕ) {b : ι → ℚ}
    (hb : b ∈ scaledIntegerGrid m) : b ∈ denominatorGrid q := by
  obtain ⟨z, rfl⟩ := hb
  refine ⟨fun i => (q : ℤ) * m * z i, ?_⟩
  intro i
  simp [Pi.smul_apply, smul_eq_mul, mul_assoc]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MajorWeightedDegreeTools
namespace OAI


namespace Erdos3

open _root_.MvPolynomial

variable {σ τ R : Type*} [CommRing R]

theorem totalDegree_le_of_positive_weightedSupport (w : σ → ℕ) (hw : ∀ i, 1 ≤ w i)
    {P : MvPolynomial σ R} {n : ℕ} (hP : P ∈ weightedSupportLE w n) : P.totalDegree ≤ n := by
  apply (mem_weightedSupportLE_one_iff P n).mp
  intro α hα
  have hweight : Finsupp.weight (1 : σ → ℕ) α ≤ Finsupp.weight w α := by
    simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Pi.one_apply]
    exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left (α i) (hw i))
  exact hweight.trans (hP hα)

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerWeightedLoweringGroup
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} {w : σ → ℕ}

theorem integerWeightedLowering_preimage (e : WeightedLoweringAut w ℚ)
    (he : ∀ i, e.val (X i) ∈ integerCoefficientPolynomials σ)
    {P : MvPolynomial σ ℚ} {n : ℕ} (hP : P ∈ integerCoefficientPolynomials σ)
    (hdegree : P ∈ weightedSupportLE w n) :
    ∃ Q, Q ∈ integerCoefficientPolynomials σ ∧ Q ∈ weightedSupportLE w n ∧ e.val Q = P := by
  induction n generalizing P with
  | zero =>
    refine ⟨P, hP, hdegree, ?_⟩
    exact sub_eq_zero.mp (weightedSupportLT_zero_eq (e.difference_lower hdegree))
  | succ n ih =>
    have hI : e.val P - P ∈ integerCoefficientPolynomials σ :=
      (integerCoefficientPolynomials σ).sub_mem (integerPolynomialHom_preserves e.val.toAlgHom he hP) hP
    have hD : e.val P - P ∈ weightedSupportLE w n :=
      weightedSupportLT_succ_le (e.difference_lower hdegree)
    obtain ⟨Q, hQI, hQD, hQ⟩ := ih hI hD
    refine ⟨P - Q, (integerCoefficientPolynomials σ).sub_mem hP hQI,
      (weightedSupportLE w (n + 1)).sub_mem hdegree (weightedSupportLE_mono (Nat.le_succ n) hQD), ?_⟩
    rw [map_sub, hQ]
    abel

theorem integerWeightedLowering_inverse_preserves (e : WeightedLoweringAut w ℚ)
    (he : ∀ i, e.val (X i) ∈ integerCoefficientPolynomials σ)
    {P : MvPolynomial σ ℚ} (hP : P ∈ integerCoefficientPolynomials σ) :
    e.val.symm P ∈ integerCoefficientPolynomials σ := by
  obtain ⟨Q, hQI, _, hQ⟩ := integerWeightedLowering_preimage e he hP
    ((mem_weightedSupportLE_iff w _ P).mpr le_rfl)
  have hEQ : e.val.symm P = Q := by
    apply e.val.injective
    rw [e.val.apply_symm_apply, hQ]
  rw [hEQ]
  exact hQI

noncomputable def integerWeightedLoweringSubgroup (w : σ → ℕ) : Subgroup (WeightedLoweringAut w ℚ) where
  carrier := {e | ∀ i, e.val (X i) ∈ integerCoefficientPolynomials σ}
  one_mem' := fun i => integerCoefficientPolynomials_X i
  mul_mem' := by
    intro e f he hf i
    exact integerPolynomialHom_preserves e.val.toAlgHom he (hf i)
  inv_mem' := by
    intro e he i
    exact integerWeightedLowering_inverse_preserves e he (integerCoefficientPolynomials_X i)

theorem integerWeightedLowering_preserves (e : WeightedLoweringAut w ℚ)
    (he : e ∈ integerWeightedLoweringSubgroup w)
    {P : MvPolynomial σ ℚ} (hP : P ∈ integerCoefficientPolynomials σ) :
    e.val P ∈ integerCoefficientPolynomials σ :=
  integerPolynomialHom_preserves e.val.toAlgHom he hP

theorem integerWeightedLowering_difference_pow (e : WeightedLoweringAut w ℚ)
    (he : e ∈ integerWeightedLoweringSubgroup w)
    {P : MvPolynomial σ ℚ} (hP : P ∈ integerCoefficientPolynomials σ) (k : ℕ) :
    (polynomialHomDifference e.val.toAlgHom ^ k) P ∈ integerCoefficientPolynomials σ := by
  induction k with
  | zero => exact hP
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact (integerCoefficientPolynomials σ).sub_mem (integerWeightedLowering_preserves e he ih) ih

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearAffineExponential
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} [Fintype σ] {w : σ → ℕ}

omit [Fintype σ] in
theorem polynomialShear_pow_degree (D : PolynomialShearLieAlgebra w ℝ)
    {P : MvPolynomial σ ℝ} {n : ℕ} (hP : P ∈ weightedSupportLE w n) (k : ℕ) :
    (D.val.toLinearMap ^ k) P ∈ weightedSupportLE w n := by
  have h := weightedDerivation_pow w D.val 1 D.property
    (show P ∈ weightedSupportDrop w n 0 by rwa [weightedSupportDrop_zero]) k
  exact weightedSupportDrop_le h

theorem polynomialShear_pow_mass (D : PolynomialShearLieAlgebra w ℝ)
    (hpos : ∀ i, 1 ≤ w i) {M : ℝ} (hM : 0 ≤ M)
    (hD : ∀ i, realPolynomialMass (D.val (X i)) ≤ M)
    {P : MvPolynomial σ ℝ} {n : ℕ} (hP : P ∈ weightedSupportLE w n) (k : ℕ) :
    realPolynomialMass ((D.val.toLinearMap ^ k) P) ≤
      (Fintype.card σ * M * n) ^ k * realPolynomialMass P := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      have hdegree := totalDegree_le_of_positive_weightedSupport w hpos
        (polynomialShear_pow_degree D hP k)
      apply (realPolynomialMass_derivation D.val hM hD hdegree).trans
      calc
        _ ≤ (Fintype.card σ * M * n) *
            ((Fintype.card σ * M * n) ^ k * realPolynomialMass P) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
        _ = _ := by rw [pow_succ']; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearRealGroup
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R S : Type*} [CommRing R] [CommRing S] {w : σ → ℕ}

theorem weightedSupportLE_map (f : R →+* S) {P : MvPolynomial σ R} {n : ℕ}
    (hP : P ∈ weightedSupportLE w n) : map f P ∈ weightedSupportLE w n := by
  intro a ha
  exact hP (MvPolynomial.support_map_subset f P ha)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientSubspace
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem affineParameterSubstitution_degree {I K : Type*} [Fintype K]
    (b : Option K → I → ℝ) (j : I) : (affineParameterSubstitution b j).totalDegree ≤ 1 := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  exact max_le (by simp) (rowPolynomial_homogeneous (fun k => b (some k) j)).totalDegree_le

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDownsetQuotients
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
  (P : LieSubalgebra ℚ (VectorPolynomial σ ℚ L))

noncomputable def restrictedOutsideDownsetIdeal
    (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J) : LieIdeal ℚ P :=
  LieIdeal.comap P.incl (outsideDownsetIdeal J hJ)

@[simp] theorem mem_restrictedOutsideDownsetIdeal
    (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J) (p : P) :
    p ∈ restrictedOutsideDownsetIdeal P J hJ ↔ ∀ a ∈ J, coefficients p.val a = 0 :=
  mem_outsideDownsetIdeal J hJ p.val

end Erdos3.VectorPolynomial

end

end OAI
end


