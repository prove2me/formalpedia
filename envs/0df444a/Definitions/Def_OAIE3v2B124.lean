-- Prove2me | Definitions.Def_OAIE3v2B124
-- name    : OAIE3v2B124
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:55:26.363093+00:00
-- url     : https://prove2.me/theorems/960bfd6d-93ca-4f47-a97d-1b212d0773c9
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 126 of 311
-- statement:
--   Definitions bundle 126 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B101`, `OAIE3v2B102`, `OAIE3v2B104`, `OAIE3v2B109`, `OAIE3v2B110` of this split.
--
--   Modules: `Dynamics/LieSubalgebraRepresentativeBudget.lean`, `Estimates/CoefficientSliceEmbedding.lean`, `Estimates/NativeEqualDimension.lean`, `Estimates/PinnedSectionMeans.lean`, `Estimates/RegularCylinderDecomposition.lean`, `Estimates/RelativePatchAmplification.lean`, `Estimates/WeightedLoweringTriangular.lean`, `Fourier/UnbalancedBohrShape.lean`, `Geometry/RationalModelCoordinates.lean`, `Geometry/RelativePatchFiniteCoordinateReduction.lean`, `Lattices/LieSubalgebraLatticeInnerGrid.lean`, `Linear/FixedKernelPatchFunction.lean`, `Linear/NativeChartKernel.lean`, `Linear/ProductANOVAEnergyOrder.lean`, `Linear/RationalTaggedSpanProjection.lean`, `Nilpotent/FactorwiseBCHCovers.lean`, `Nilpotent/IdealInvariantNiltestBudget.lean`, `Nilpotent/PolynomialShearNilmanifold.lean`, `Nilpotent/SumNilmanifoldFactors.lean`, `Nilpotent/UnitComparisonNiltest.lean`, `Polynomial/PolynomialCoefficientNormalization.lean`, `Polynomial/PolynomialPatchShearOrbit.lean`, `Polynomial/PolynomialPatchShearOrbitConverse.lean`, `Polynomial/PolynomialShearFactorialIntegrality.lean`, `Polynomial/PolynomialShearParameterBudget.lean`, `Polynomial/PolynomialShearRealGroup.lean`, `Polynomial/PolynomialShearWeightedOrbitCoordinates.lean`, `Polynomial/PolynomialSymbolicShearWeightedDegree.lean`, `Polynomial/RealAdaptedPolynomialGroup.lean`, `Sampling/FixedPathSlicedGridMeshBudget.lean`, `Sampling/PatchKernelGridBudget.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B101
import Definitions.Def_OAIE3v2B102
import Definitions.Def_OAIE3v2B104
import Definitions.Def_OAIE3v2B109
import Definitions.Def_OAIE3v2B110

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialCoefficientNormalization
namespace OAI


namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R] {d : ℕ}

theorem slotPolynomialLift_lower (v : σ → ℕ) (w : Fin d → ℕ) (i : Fin d)
    {P : MvPolynomial (σ ⊕ Fin i.val) R} {n : ℕ}
    (hP : P ∈ weightedSupportLT (Sum.elim v (fun j => w (earlierSlot i j))) n) :
    slotPolynomialLift i P ∈ weightedSupportLT (Sum.elim v w) n := by
  apply weightedSupportLT_map _ _ (rename (Sum.map id (earlierSlot i))) _ hP
  intro a
  rw [rename_X]
  cases a with
  | inl j => exact weightedSupportLE_X (Sum.elim v w) (Sum.inl j)
  | inr j => exact weightedSupportLE_X (Sum.elim v w) (Sum.inr (earlierSlot i j))

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialSymbolicShearWeightedDegree
namespace OAI

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem residualCoordinate_sub_topPart_lower (A : PolynomialSlots σ d w) (i : Fin d) :
    A.residualCoordinate i - A.topPart.residualCoordinate i ∈
      weightedSupportLT (Sum.elim (fun _ : σ => 0) w) (w i) := by
  have he : A.residualCoordinate i - A.topPart.residualCoordinate i =
      -slotPolynomialLift i (A.center i - A.topPart.center i) := by
    simp only [residualCoordinate, slotPolynomialLift, map_sub]
    abel
  rw [he]
  exact (weightedSupportLT _ _).neg_mem
    (slotPolynomialLift_lower (fun _ => 0) w i (A.sub_topPart_lower i))

theorem residualHom_sub_topPart_lower (A : PolynomialSlots σ d w)
    {n : ℕ} {p : MvPolynomial (Fin d) ℝ} (hp : p ∈ weightedSupportLE w n) :
    A.residualHom p - A.topPart.residualHom p ∈
      weightedSupportLT (Sum.elim (fun _ : σ => 0) w) n := by
  apply weightedComparison_difference w _ A.residualHom A.topPart.residualHom _ _ _ hp
  · intro i
    rw [residualHom_X]
    exact A.residualCoordinate_slot_degree i
  · intro i
    rw [residualHom_X]
    exact A.topPart.residualCoordinate_slot_degree i
  · intro i
    rw [residualHom_X, residualHom_X]
    exact A.residualCoordinate_sub_topPart_lower i

end Erdos3.PolynomialSlots

end

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem loweringHom_X_lower (A : PolynomialSlots σ d w) (i : Fin d) :
    A.loweringHom (X i) - X (Sum.inr i) ∈
      weightedSupportLT (Sum.elim (fun _ : σ => 0) w) (w i) := by
  have h := A.residualHom_sub_topPart_lower
    (A.topResidualEquiv_inverse_degree (weightedSupportLE_X w i))
  have he : A.topPart.residualHom (A.topResidualEquiv.symm (X i)) = X (Sum.inr i) := by
    rw [← A.topResidualEquiv_lift]
    change rename Sum.inr (A.topResidualEquiv (A.topResidualEquiv.symm (X i))) = _
    rw [AlgEquiv.apply_symm_apply, rename_X]
  rw [he] at h
  exact h

end Erdos3.PolynomialSlots

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} {d : ℕ}

theorem patchParameterSpecialization_lower (v : σ → ℕ) (w : Fin d → ℕ) (t : σ → ℝ)
    {n : ℕ} {P : MvPolynomial (σ ⊕ Fin d) ℝ} (hP : P ∈ weightedSupportLT (Sum.elim v w) n) :
    patchParameterSpecialization t P ∈ weightedSupportLT w n := by
  apply weightedSupportLT_map _ _ (patchParameterSpecialization t) _ hP
  intro a
  cases a with
  | inl j =>
      simp only [patchParameterSpecialization, aeval_X, Sum.elim_inl]
      exact weightedSupportLE_C w (v j) (t j)
  | inr j =>
      rw [patchParameterSpecialization_X_slot]
      exact weightedSupportLE_X w j

namespace PolynomialSlots

variable {w : Fin d → ℕ}

theorem loweringAtHom_lower (A : PolynomialSlots σ d w) (t : σ → ℝ) (i : Fin d) :
    A.loweringAtHom t (X i) - X i ∈ weightedSupportLT w (w i) := by
  have h := patchParameterSpecialization_lower (fun _ => 0) w t (A.loweringHom_X_lower i)
  rw [map_sub, patchParameterSpecialization_X_slot] at h
  exact h

noncomputable def loweringAt (A : PolynomialSlots σ d w) (t : σ → ℝ) :
    WeightedLoweringAut w ℝ :=
  WeightedLoweringAut.ofHom w (A.loweringAtHom t) (A.loweringAtHom_lower t)

theorem loweringAt_comp_top (A : PolynomialSlots σ d w) (t : σ → ℝ) :
    (A.loweringAt t).val.toAlgHom.comp A.topResidualEquiv.toAlgHom =
      (patchParameterSpecialization t).comp A.residualHom := by
  apply AlgHom.ext
  intro P
  change patchParameterSpecialization t (A.loweringHom (A.topResidualEquiv P)) =
    patchParameterSpecialization t (A.residualHom P)
  exact congrArg (patchParameterSpecialization t) (DFunLike.congr_fun A.loweringHom_comp_top P)

noncomputable def loweringPoint (A : PolynomialSlots σ d w) (t : σ → ℝ) (b : Fin d → ℝ) :
    Fin d → ℝ := fun i => aeval b ((A.loweringAt t).val (X i))

theorem loweringAt_aeval (A : PolynomialSlots σ d w) (t : σ → ℝ) (b : Fin d → ℝ)
    (P : MvPolynomial (Fin d) ℝ) :
    aeval b ((A.loweringAt t).val P) = aeval (A.loweringPoint t b) P := by
  change aeval b ((A.loweringAt t).val.toAlgHom P) = _
  rw [MvPolynomial.aeval_unique (A.loweringAt t).val.toAlgHom, MvPolynomial.comp_aeval_apply]
  rfl

theorem top_factorization_coordinate (A : PolynomialSlots σ d w)
    (t : σ → ℝ) (b : Fin d → ℝ) (i : Fin d) :
    aeval (A.loweringPoint t b) (A.topResidualEquiv (X i)) =
      b i - (A.slots t).center b i := by
  have he := congrArg (fun F : MvPolynomial (Fin d) ℝ →ₐ[ℝ] MvPolynomial (Fin d) ℝ =>
    aeval b (F (X i))) (A.loweringAt_comp_top t)
  change aeval b ((A.loweringAt t).val (A.topResidualEquiv (X i))) =
    aeval b (patchParameterSpecialization t (A.residualHom (X i))) at he
  rw [A.loweringAt_aeval, patchParameterSpecialization_eval, residualHom_X,
    residualCoordinate_eval] at he
  exact he

theorem top_factorization_residual (A : PolynomialSlots σ d w)
    (t : σ → ℝ) (b : Fin d → ℤ) :
    (fun i => aeval (A.loweringPoint t (fun j => (b j : ℝ))) (A.topResidualEquiv (X i))) =
      (A.slots t).residual b := by
  funext i
  exact A.top_factorization_coordinate t (fun j => (b j : ℝ)) i

end PolynomialSlots

end Erdos3

end

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem symbolicShearDifference_specialization (A : PolynomialSlots σ d w) (t : σ → ℝ)
    (P : MvPolynomial (σ ⊕ Fin d) ℝ) :
    patchParameterSpecialization t (polynomialHomDifference A.symbolicShearHom P) =
      polynomialHomDifference (A.loweringAt t).val.toAlgHom (patchParameterSpecialization t P) := by
  change patchParameterSpecialization t (A.symbolicShearHom P - P) =
    A.loweringAtHom t (patchParameterSpecialization t P) - patchParameterSpecialization t P
  rw [map_sub, symbolicShearHom_specialization]

theorem symbolicShearDifference_pow_specialization (A : PolynomialSlots σ d w)
    (t : σ → ℝ) (k : ℕ) (P : MvPolynomial (σ ⊕ Fin d) ℝ) :
    patchParameterSpecialization t ((polynomialHomDifference A.symbolicShearHom ^ k) P) =
      (polynomialHomDifference (A.loweringAt t).val.toAlgHom ^ k)
        (patchParameterSpecialization t P) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, symbolicShearDifference_specialization, ih,
      pow_succ', Module.End.mul_apply]

end Erdos3.PolynomialSlots

end

section

namespace Erdos3
open _root_.MvPolynomial
variable {σ : Type*} {d : ℕ} (p : σ → ℕ) (w : Fin d → ℕ)
variable [Fintype (PolynomialShearIndex w)]
variable (c : PolynomialShearIndex w → MvPolynomial σ ℝ)

omit [Fintype (PolynomialShearIndex w)] in
theorem polynomialSymbolicShearTerm_weighted_degree
    (hc : ∀ a, c a ∈ weightedSupportLE p (polynomialShearDeficit w a))
    (a : PolynomialShearIndex w) :
    polynomialSymbolicShearTerm w c a ∈
      weightedSupportLE (Sum.elim p w) (w a.1) := by
  have hp := weighted_symbolic_rename_degree p
    (Sum.elim p w) Sum.inl (fun _ => rfl) (hc a)
  have hm := weighted_symbolic_rename_degree w (Sum.elim p w)
    Sum.inr (fun _ => rfl) (weightedSupportLE_monomial w a.2.val (1 : ℝ))
  apply weightedSupportLE_mono _ (weightedSupportLE_mul hp hm)
  have ha := a.2.property
  unfold polynomialShearDeficit
  omega

theorem polynomialSymbolicShearDerivation_weighted_degree
    (hc : ∀ a, c a ∈ weightedSupportLE p (polynomialShearDeficit w a))
    (i : σ ⊕ Fin d) :
    (polynomialSymbolicShearDerivation w c).val (X i) ∈
      weightedSupportLE (Sum.elim p w) (Sum.elim p w i) := by
  classical
  cases i with
  | inl i => rw [polynomialSymbolicShearDerivation_X_parameter]; exact Submodule.zero_mem _
  | inr i =>
    rw [polynomialSymbolicShearDerivation_X_slot]
    apply Submodule.sum_mem
    intro a ha
    split_ifs with hi
    · simpa only [hi, Sum.elim_inr] using polynomialSymbolicShearTerm_weighted_degree p w c hc a
    · exact Submodule.zero_mem _

theorem polynomialSymbolicShearExp_weighted_degree
    (hc : ∀ a, c a ∈ weightedSupportLE p (polynomialShearDeficit w a))
    {P : MvPolynomial (σ ⊕ Fin d) ℝ} {n : ℕ}
    (hP : P ∈ weightedSupportLE (Sum.elim p w) n) :
    polynomialShearExp (polynomialSymbolicShearDerivation w c) P ∈
      weightedSupportLE (Sum.elim p w) n :=
  polynomialShearExp_weightedSupportLE _ (polynomialSymbolicShearDerivation_weighted_degree p w c hc) hP

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearFactorialIntegrality
namespace OAI

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

theorem symbolicLogSlot_specialization (A : PolynomialSlots σ d w) (t : σ → ℝ) (i : Fin d) :
    patchParameterSpecialization t (A.symbolicLogSlot i) =
      (polynomialShearLog (A.loweringAt t)).val (X i) := by
  change patchParameterSpecialization t (A.symbolicLogSlot i) = polynomialShearLogValue (A.loweringAt t) (X i)
  rw [polynomialShearLogValue_eq_sum (A.loweringAt t) (weightedSupportLE_X w i)]
  unfold symbolicLogSlot
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_rat_smul, symbolicShearDifference_pow_specialization, patchParameterSpecialization_X_slot]

end Erdos3.PolynomialSlots

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearRealGroup
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped TensorProduct

variable {σ : Type*} [Fintype σ] (w : σ → ℕ)

theorem polynomialShearRealAutEquiv_apply (s : ℕ) (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).realification.Group) :
    polynomialShearRealAutEquiv w s hw g =
      polynomialShearExpAut (polynomialShearRealificationEquiv w g.coord) := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FactorwiseBCHCovers
namespace OAI

section

namespace Erdos3

open NilpotentLieBCHGroup

variable {α : Type*} {M : α → Type*} [∀ a, LieRing (M a)] [∀ a, LieAlgebra ℚ (M a)]
  [DecidableEq α] {s : ℕ}

noncomputable def bchPiEquiv (F : ∀ a, NilpotentLieFiltration (M a) s) :
    (NilpotentLieFiltration.pi F).Group ≃* (∀ a, (F a).Group) where
  toFun g a := ⟨g.coord a⟩
  invFun g := ⟨fun a => (g a).coord⟩
  left_inv g := by cases g; rfl
  right_inv g := by funext a; exact NilpotentLieBCHGroup.ext rfl
  map_mul' g h := by
    funext a
    exact (map (hnil := (NilpotentLieFiltration.pi F).lowerCentralSeries_eq_bot)
      (hM := (F a).lowerCentralSeries_eq_bot) (liePiEval a)).map_mul g h

noncomputable def bchPiSingle (F : ∀ a, NilpotentLieFiltration (M a) s) (a : α) :
    (F a).Group →* (NilpotentLieFiltration.pi F).Group :=
  map (hnil := (F a).lowerCentralSeries_eq_bot)
    (hM := (NilpotentLieFiltration.pi F).lowerCentralSeries_eq_bot) (liePiSingle a)

theorem bchPiEquiv_single (F : ∀ a, NilpotentLieFiltration (M a) s) (a : α) (g : (F a).Group) :
    bchPiEquiv F (bchPiSingle F a g) = Pi.mulSingle a g := by
  funext i
  apply NilpotentLieBCHGroup.ext
  change Pi.single a g.coord i = ((Pi.mulSingle a g : ∀ i, (F i).Group) i).coord
  by_cases hi : i = a
  · subst i
    simp only [Pi.single_eq_same, Pi.mulSingle_eq_same]
  · simp only [Pi.single_eq_of_ne hi, Pi.mulSingle_eq_of_ne hi, coord_one]

theorem bchPiSingle_eq_symm_mulSingle (F : ∀ a, NilpotentLieFiltration (M a) s)
    (a : α) (g : (F a).Group) :
    bchPiSingle F a g = (bchPiEquiv F).symm (Pi.mulSingle a g) := by
  apply (bchPiEquiv F).injective
  rw [bchPiEquiv_single, MulEquiv.apply_symm_apply]

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup

variable {α : Type*} [Fintype α] [DecidableEq α] {M : α → Type*}
  [∀ a, LieRing (M a)] [∀ a, LieAlgebra ℚ (M a)] {s : ℕ}
  (F : ∀ a, NilpotentLieFiltration (M a) s)
  {κ : α → Type*} [∀ a, Fintype (κ a)] (f : ∀ a, Basis (κ a) ℚ (M a))

theorem bchPiSingle_comap_inner_grid (Λ : Subgroup (NilpotentLieFiltration.pi F).Group)
    (m : ℕ) (hΛ : scaledIntegerGrid m ⊆ bchSubgroupCoordinates (Pi.basis f) Λ) (a : α) :
    scaledIntegerGrid m ⊆ bchSubgroupCoordinates (f a) (Λ.comap (bchPiSingle F a)) := by
  classical
  rintro x ⟨z, rfl⟩
  change bchPiSingle F a ⟨(f a).equivFun.symm ((m : ℚ) • fun i => (z i : ℚ))⟩ ∈ Λ
  apply (bchSubgroupCoordinates_repr (Pi.basis f) Λ _).mp
  apply hΛ
  refine ⟨fun i : Σ a, κ a => (Pi.single a z : ∀ a, κ a → ℤ) i.1 i.2, ?_⟩
  ext ⟨i, j⟩
  change (f i).repr (Pi.single a ((f a).equivFun.symm ((m : ℚ) • fun k => (z k : ℚ))) i) j = _
  by_cases hi : i = a
  · subst i
    simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul]
    change (f a).equivFun ((f a).equivFun.symm ((m : ℚ) • fun k => (z k : ℚ))) j = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  · simp only [Pi.single_eq_of_ne hi, map_zero, Finsupp.zero_apply, Pi.zero_apply,
      Int.cast_zero, Pi.smul_apply, smul_eq_mul, mul_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealAdaptedPolynomialGroup
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s t : ℕ}
    (F : NilpotentLieFiltration L s) (I : LieIdeal ℚ L)
    (hI : F.layer (t + 1) ≤ I.toSubmodule) {w : σ → ℕ}

theorem realQuotientPolynomialOrbit_realEval
    (g : F.realification.PolynomialOrbit w) (z : σ → ℝ) :
    (F.quotientLie I hI).realification.polynomialOrbitRealEval w z
      (F.realQuotientPolynomialOrbit I hI g) =
      F.realQuotientStepHom I hI (F.realification.polynomialOrbitRealEval w z g) := by
  apply NilpotentLieBCHGroup.ext
  exact eval₂_map (realificationLieHom (lieQuotientMap I)).toLinearMap z g.log

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalTaggedSpanProjection
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem rationalKernelSeparationConstant_ceil_le_exp_power
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Q : Matrix ι κ ℚ) {H : ℕ} {p : ℝ} (hp : 0 ≤ p)
    (a : ℕ) (ha : 1 ≤ a)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp ((p+2)^a))
    (hQ : ∀ i j, RationalHeightLE (Q i j) H) :
    (⌈(matrixDenominator Q : ℝ) *
      (((Fintype.card κ : ℝ)+1)*((H : ℝ)+1))⌉₊ : ℝ) ≤
        Real.exp ((p+2)^(a+4)) := by
  let c : ℝ := (matrixDenominator Q : ℝ) *
    (((Fintype.card κ : ℝ)+1)*((H : ℝ)+1))
  have hden := matrixDenominator_le_exp_power Q hp a hι hκ
    (fun i j => (Nat.cast_le.mpr (hQ i j).2).trans hH)
  have hfactor : ((Fintype.card κ : ℝ)+1)*((H : ℝ)+1) ≤
      Real.exp ((p+2)^(a+2)) := by
    apply le_trans _ (matrix_weighted_factor_le_exp_power (Fintype.card κ) hp hκ a ha)
    exact mul_le_mul_of_nonneg_left (by linarith only [hH]) (by positivity)
  have hc : c ≤ Real.exp ((p+2)^(a+3)) := by
    calc
      _ ≤ Real.exp ((p+2)^(a+2)) * Real.exp ((p+2)^(a+2)) :=
        mul_le_mul hden hfactor (by positivity) (Real.exp_nonneg _)
      _ = Real.exp (2*(p+2)^(a+2)) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        calc
          _ ≤ (p+2)*(p+2)^(a+2) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = _ := by rw [pow_succ]; ring
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hceil : (⌈c⌉₊ : ℝ) ≤ c+1 := (Nat.ceil_lt_add_one hc0).le
  change (⌈c⌉₊ : ℝ) ≤ _
  calc
    _ ≤ Real.exp ((p+2)^(a+3))+1 := hceil.trans (by linarith only [hc])
    _ ≤ Real.exp ((p+2)^(a+3)) * 2 := by
      have hExp := Real.one_le_exp_iff.mpr (show 0 ≤ (p+2)^(a+3) by positivity)
      linarith only [hExp]
    _ ≤ Real.exp ((p+2)^(a+3)) * Real.exp 1 :=
      mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (1:ℝ)]) (Real.exp_nonneg _)
    _ = Real.exp ((p+2)^(a+3)+1) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hbase : 1 ≤ (p+2)^(a+3) := one_le_pow₀ (by linarith)
      calc
        _ ≤ 2*(p+2)^(a+3) := by linarith only [hbase]
        _ ≤ (p+2)*(p+2)^(a+3) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = _ := by rw [pow_succ]; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.LieSubalgebraRepresentativeBudget
namespace OAI

section

namespace Erdos3
open Module
open scoped Matrix

variable {ι κ L : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [LieRing L] [LieAlgebra ℚ L]

theorem lieSubalgebraRepresentative_bracket_height (b : Basis ι ℚ L)
    (K : LieSubalgebra ℚ L) (bk : Basis κ ℚ K) {H : ℕ} (hH : 1 ≤ H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
    (hinc : ∀ i j, RationalHeightLE (b.repr (bk j : L) i) H) :
    ∀ i j k, RationalHeightLE (lieStructureConstants bk i j k)
      (lieSubalgebraRepresentativeHeight (Fintype.card ι) (Fintype.card κ) H) := by
  obtain ⟨P, hP, hPH, hsource⟩ := exists_bounded_lie_embedding_retraction bk b K.incl
    (fun _ _ h => Subtype.ext h) hH hc (by
      intro i j
      rw [LinearMap.toMatrix_apply]
      exact hinc i j)
  exact hsource

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchShearOrbit
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

noncomputable def weightedLoweringPointAction (w : σ → ℕ) :
    WeightedLoweringAut w R →* Equiv.Perm (σ → R) :=
  polynomialPointAction.comp (weightedLoweringSubgroup w).subtype

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} {w : σ → ℕ}

noncomputable def integerWeightedLoweringPoint (e : WeightedLoweringAut w ℚ)
    (he : e ∈ integerWeightedLoweringSubgroup w) (b : σ → ℤ) : σ → ℤ :=
  fun i => Classical.choose (integerCoefficientPolynomials_aeval
    ((integerWeightedLoweringSubgroup w).inv_mem he i) b)

theorem integerWeightedLoweringPoint_cast (e : WeightedLoweringAut w ℚ)
    (he : e ∈ integerWeightedLoweringSubgroup w) (b : σ → ℤ) :
    (fun i => (integerWeightedLoweringPoint e he b i : ℚ)) =
      weightedLoweringPointAction w e (fun i => (b i : ℚ)) := by
  funext i
  exact (Classical.choose_spec (integerCoefficientPolynomials_aeval
    ((integerWeightedLoweringSubgroup w).inv_mem he i) b)).symm

theorem integerWeightedLoweringPoint_inv (e : WeightedLoweringAut w ℚ)
    (he : e ∈ integerWeightedLoweringSubgroup w) (b : σ → ℤ) :
    integerWeightedLoweringPoint e⁻¹ ((integerWeightedLoweringSubgroup w).inv_mem he)
      (integerWeightedLoweringPoint e he b) = b := by
  apply integerTupleRatCast_injective
  change (fun i => (integerWeightedLoweringPoint e⁻¹ _ (integerWeightedLoweringPoint e he b) i : ℚ)) =
    (fun i => (b i : ℚ))
  rw [integerWeightedLoweringPoint_cast, integerWeightedLoweringPoint_cast, map_inv]
  exact (weightedLoweringPointAction w e).symm_apply_apply _

noncomputable def integerWeightedLoweringPointEquiv (e : WeightedLoweringAut w ℚ)
    (he : e ∈ integerWeightedLoweringSubgroup w) : Equiv.Perm (σ → ℤ) where
  toFun := integerWeightedLoweringPoint e he
  invFun := integerWeightedLoweringPoint e⁻¹ ((integerWeightedLoweringSubgroup w).inv_mem he)
  left_inv := integerWeightedLoweringPoint_inv e he
  right_inv b := by
    apply integerTupleRatCast_injective
    change (fun i => (integerWeightedLoweringPoint e he (integerWeightedLoweringPoint e⁻¹ _ b) i : ℚ)) =
      (fun i => (b i : ℚ))
    rw [integerWeightedLoweringPoint_cast, integerWeightedLoweringPoint_cast, map_inv]
    exact (weightedLoweringPointAction w e).apply_symm_apply _

theorem integerWeightedLoweringPointEquiv_cast (e : WeightedLoweringAut w ℚ)
    (he : e ∈ integerWeightedLoweringSubgroup w) (b : σ → ℤ) :
    (fun i => (integerWeightedLoweringPointEquiv e he b i : ℚ)) =
      weightedLoweringPointAction w e (fun i => (b i : ℚ)) :=
  integerWeightedLoweringPoint_cast e he b

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial Module

variable {σ : Type*} [Fintype σ] {w : σ → ℕ}

theorem polynomialShear_integral_iff (D : PolynomialShearLieAlgebra w ℚ) :
    (∀ i, D.val (X i) ∈ integerCoefficientPolynomials σ) ↔
      ∀ a : PolynomialShearIndex w, ∃ z : ℤ, (polynomialShearBasis (R := ℚ) w).repr D a = (z : ℚ) := by
  constructor
  · intro h a
    exact (mem_integerCoefficientPolynomials_iff _).mp (h a.1) a.2.val
  · intro h i
    apply (mem_integerCoefficientPolynomials_iff _).mpr
    intro a
    by_cases ha : Finsupp.weight w a + 1 ≤ w i
    · exact h ⟨i, a, ha⟩
    · refine ⟨0, ?_⟩
      apply not_ne_iff.mp
      intro hc
      apply ha
      exact D.property i (MvPolynomial.mem_support_iff.mpr hc)

variable [Fintype (PolynomialShearIndex w)]

theorem polynomialShear_integralVector_iff (D : PolynomialShearLieAlgebra w ℚ) :
    (∀ i, D.val (X i) ∈ integerCoefficientPolynomials σ) ↔
      IntegralVector ((polynomialShearBasis (R := ℚ) w).equivFun D) := by
  rw [polynomialShear_integral_iff]
  constructor
  · intro h
    choose z hz using h
    exact ⟨z, hz⟩
  · rintro ⟨z, hz⟩ a
    exact ⟨z a, hz a⟩

theorem polynomialShear_denominatorGrid_iff (B : ℕ) (D : PolynomialShearLieAlgebra w ℚ) :
    (polynomialShearBasis (R := ℚ) w).equivFun D ∈ denominatorGrid B ↔
      ∀ i, ((B : ℚ) • D).val (X i) ∈ integerCoefficientPolynomials σ := by
  change IntegralVector ((B : ℚ) • (polynomialShearBasis (R := ℚ) w).equivFun D) ↔ _
  rw [← map_smul]
  exact (polynomialShear_integralVector_iff _).symm

theorem polynomialShear_scaledGrid_normalize (B : ℕ) (hB : 0 < B)
    (D : PolynomialShearLieAlgebra w ℚ)
    (hD : (polynomialShearBasis (R := ℚ) w).equivFun D ∈ scaledIntegerGrid B) :
    ∀ i, ((B : ℚ)⁻¹ • D).val (X i) ∈ integerCoefficientPolynomials σ := by
  obtain ⟨z, hz⟩ := hD
  apply (polynomialShear_integralVector_iff _).mpr
  have hBq : (B : ℚ) ≠ 0 := by exact_mod_cast hB.ne'
  have hv : (polynomialShearBasis (R := ℚ) w).equivFun ((B : ℚ)⁻¹ • D) = fun i => (z i : ℚ) := by
    rw [map_smul, hz, smul_smul, inv_mul_cancel₀ hBq, one_smul]
  exact ⟨z, congrFun hv⟩

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial Module

variable {σ : Type*} {w : σ → ℕ}

theorem polynomialShearMonomial_pderiv (a : PolynomialShearIndex w) :
    (polynomialShearMonomial (R := ℚ) w a).val =
      monomial a.2.val (1 : ℚ) • pderiv a.1 := by
  classical
  apply MvPolynomial.derivation_ext
  intro i
  rw [polynomialShearMonomial_X]
  change (if i = a.1 then monomial a.2.val (1 : ℚ) else 0) =
    monomial a.2.val (1 : ℚ) * pderiv a.1 (X i)
  by_cases h : i = a.1
  · subst i
    simp
  · simp [h]

theorem polynomialShearMonomial_monomial (a : PolynomialShearIndex w)
    (b : σ →₀ ℕ) (c : ℚ) :
    (polynomialShearMonomial (R := ℚ) w a).val (monomial b c) =
      monomial (a.2.val + (b - Finsupp.single a.1 1)) (c * b a.1) := by
  rw [polynomialShearMonomial_pderiv]
  change monomial a.2.val (1 : ℚ) * pderiv a.1 (monomial b c) = _
  rw [pderiv_monomial, MvPolynomial.monomial_mul, one_mul]

theorem polynomialShearMonomial_bracket_X [DecidableEq σ] (a b : PolynomialShearIndex w) (i : σ) :
    (⁅polynomialShearMonomial (R := ℚ) w a, polynomialShearMonomial w b⁆).val (X i) =
      (if i = b.1 then monomial (a.2.val + (b.2.val - Finsupp.single a.1 1)) (b.2.val a.1 : ℚ) else 0) -
      (if i = a.1 then monomial (b.2.val + (a.2.val - Finsupp.single b.1 1)) (a.2.val b.1 : ℚ) else 0) := by
  classical
  change ⁅(polynomialShearMonomial (R := ℚ) w a).val,
    (polynomialShearMonomial (R := ℚ) w b).val⁆ (X i) = _
  rw [Derivation.commutator_apply, polynomialShearMonomial_X, polynomialShearMonomial_X]
  split_ifs <;> simp only [map_zero, polynomialShearMonomial_monomial, one_mul]

noncomputable def polynomialShearBracketCoefficient (a b c : PolynomialShearIndex w) : ℤ := by
  classical
  exact (if c.1 = b.1 then
      if a.2.val + (b.2.val - Finsupp.single a.1 1) = c.2.val then (b.2.val a.1 : ℤ) else 0 else 0) -
    (if c.1 = a.1 then
      if b.2.val + (a.2.val - Finsupp.single b.1 1) = c.2.val then (a.2.val b.1 : ℤ) else 0 else 0)

variable [Fintype σ]

theorem polynomialShear_structureConstants (a b c : PolynomialShearIndex w) :
    lieStructureConstants (polynomialShearBasis w) a b c =
      (polynomialShearBracketCoefficient a b c : ℚ) := by
  classical
  rw [lieStructureConstants, polynomialShearBasis_repr,
    polynomialShearBasis_eq_monomial, polynomialShearBasis_eq_monomial,
    polynomialShearMonomial_bracket_X, coeff_sub]
  simp only [polynomialShearBracketCoefficient, Int.cast_sub, Int.cast_ite,
    Int.cast_natCast, Int.cast_zero]
  split_ifs <;> simp_all [coeff_monomial]

omit [Fintype σ] in
theorem polynomialShearBracketCoefficient_natAbs_le (s : ℕ)
    (hpos : ∀ i, 0 < w i) (hw : ∀ i, w i ≤ s) (a b c : PolynomialShearIndex w) :
    (polynomialShearBracketCoefficient a b c).natAbs ≤ 2 * s := by
  classical
  have ha : a.2.val b.1 ≤ s := (Finsupp.le_weight w (hpos b.1).ne' a.2.val).trans
    ((Nat.le_add_right _ 1).trans (a.2.property.trans (hw a.1)))
  have hb : b.2.val a.1 ≤ s := (Finsupp.le_weight w (hpos a.1).ne' b.2.val).trans
    ((Nat.le_add_right _ 1).trans (b.2.property.trans (hw b.1)))
  unfold polynomialShearBracketCoefficient
  have hleft : (if c.1 = b.1 then
      if a.2.val + (b.2.val - Finsupp.single a.1 1) = c.2.val then (b.2.val a.1 : ℤ) else 0 else 0).natAbs ≤ s := by
    split_ifs <;> simp_all
  have hright : (if c.1 = a.1 then
      if b.2.val + (a.2.val - Finsupp.single b.1 1) = c.2.val then (a.2.val b.1 : ℤ) else 0 else 0).natAbs ≤ s := by
    split_ifs <;> simp_all
  exact (Int.natAbs_sub_le _ _).trans ((Nat.add_le_add hleft hright).trans_eq (by omega))

theorem polynomialShear_structureConstants_height (s : ℕ)
    (hpos : ∀ i, 0 < w i) (hw : ∀ i, w i ≤ s) (a b c : PolynomialShearIndex w) :
    RationalHeightLE (lieStructureConstants (polynomialShearBasis w) a b c) (2 * s + 1) := by
  rw [polynomialShear_structureConstants]
  constructor
  · simpa using (polynomialShearBracketCoefficient_natAbs_le s hpos hw a b c).trans
      (Nat.le_succ (2 * s))
  · simp

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial Module
open scoped TensorProduct

variable {σ : Type*}

noncomputable def polynomialShearLattice (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s) :
    Subgroup (polynomialShearFiltration w s hw).Group :=
  (integerWeightedLoweringSubgroup w).comap (polynomialShearBCHEquiv w s hw).toMonoidHom

variable [Fintype σ] {w : σ → ℕ} [Fintype (PolynomialShearIndex w)]

theorem polynomialShearLattice_outer_grid (s : ℕ) (hw : ∀ i, w i ≤ s) :
    bchSubgroupCoordinates (polynomialShearBasis w) (polynomialShearLattice w s hw) ⊆
      denominatorGrid s.factorial := by
  intro x hx
  let D := (polynomialShearBasis (R := ℚ) w).equivFun.symm x
  have hE : polynomialShearExpAut D ∈ integerWeightedLoweringSubgroup w := hx
  have hI (i : σ) := polynomialShear_factorial_log_integral s hw (polynomialShearExpAut D) hE i
  simp only [polynomialShearLog_exp] at hI
  have h := (polynomialShear_denominatorGrid_iff s.factorial D).mpr hI
  simpa only [D, LinearEquiv.apply_symm_apply] using h

noncomputable def polynomialShearRealLattice (s : ℕ) (hw : ∀ i, w i ≤ s) :
    Subgroup (polynomialShearFiltration w s hw).realification.Group :=
  (polynomialShearLattice w s hw).map NilpotentLieBCHGroup.realificationHom

variable [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]
  [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]

theorem polynomialShearRealLattice_closed_discrete (s : ℕ) (hw : ∀ i, w i ≤ s) :
    IsClosed (polynomialShearRealLattice s hw : Set (polynomialShearFiltration w s hw).realification.Group) ∧
      IsDiscrete (polynomialShearRealLattice s hw : Set (polynomialShearFiltration w s hw).realification.Group) :=
  NilpotentLieBCHGroup.realification_subgroup_closed_discrete (polynomialShearBasis w)
    (polynomialShearLattice w s hw) s.factorial (Nat.factorial_pos s)
    (polynomialShearLattice_outer_grid s hw)

end Erdos3

end

section

namespace Erdos3

open Module

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) [Fintype (PolynomialShearIndex w)]

noncomputable def polynomialShearIndexOrder :
    PolynomialShearIndex w ≃ Fin (Fintype.card (PolynomialShearIndex w)) :=
  let ρ := Fintype.equivFin (PolynomialShearIndex w)
  let u := fun j => polynomialShearDeficit w (ρ.symm j)
  ρ.trans (Tuple.sort u).symm

noncomputable def polynomialShearOrderedBasis :
    Basis (Fin (Fintype.card (PolynomialShearIndex w))) ℚ (PolynomialShearLieAlgebra w ℚ) :=
  (polynomialShearBasis w).reindex (polynomialShearIndexOrder w)

noncomputable def polynomialShearOrderedWeight (j : Fin (Fintype.card (PolynomialShearIndex w))) : ℕ :=
  polynomialShearDeficit w ((polynomialShearIndexOrder w).symm j)

theorem polynomialShearOrderedBasis_layers (r : ℕ) :
    polynomialShearLayer (R := ℚ) w r = Submodule.span ℚ
      (polynomialShearOrderedBasis w '' {j | r ≤ polynomialShearOrderedWeight w j}) := by
  change polynomialShearLayer w r = Submodule.span ℚ
    (((polynomialShearBasis (R := ℚ) w).reindex (polynomialShearIndexOrder w)) ''
      {j | r ≤ polynomialShearDeficit w ((polynomialShearIndexOrder w).symm j)})
  rw [basis_reindex_span_weights, polynomialShearLayer_span]

theorem polynomialShearOrderedBasis_structure_height (s : ℕ)
    (hpos : ∀ i, 0 < w i) (hw : ∀ i, w i ≤ s) (a b c) :
    RationalHeightLE (lieStructureConstants (polynomialShearOrderedBasis w) a b c) (2 * s + 1) := by
  rw [polynomialShearOrderedBasis, lieStructureConstants_reindex]
  exact polynomialShear_structureConstants_height s hpos hw _ _ _

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s)

noncomputable def polynomialShearRealPointAction :
    (polynomialShearFiltration w s hw).realification.Group →* Equiv.Perm (σ → ℝ) :=
  (weightedLoweringPointAction w).comp (polynomialShearRealAutEquiv w s hw).toMonoidHom

end Erdos3

end

section

namespace Erdos3

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s)

noncomputable def polynomialShearOrbitSum (K : (σ → ℝ) → ℝ)
    (g : (polynomialShearFiltration w s hw).realification.Group) : ℝ :=
  ∑' b : σ → ℤ, K (polynomialShearRealPointAction w s hw g (fun i => (b i : ℝ)))

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

noncomputable def shearGroupLift (A : PolynomialSlots σ d w)
    (s : ℕ) (hw : ∀ i, w i ≤ s) (t : σ → ℝ) :
    (polynomialShearFiltration w s hw).realification.Group :=
  (polynomialShearRealAutEquiv w s hw).symm (A.loweringAt t)⁻¹

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s d : ℕ}

noncomputable def shearKernel (A : PolynomialPatch σ s d) (x : Fin d → ℝ) : ℝ :=
  A.kernel.value (fun i => aeval x (A.form.topResidualEquiv (X i)))

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {τ : Type*} [Fintype τ] (w : τ → ℕ)

theorem polynomialShearRealAutEquiv_symm_coord (s : ℕ) (hw : ∀ i, w i ≤ s)
    (e : WeightedLoweringAut w ℝ) :
    polynomialShearRealificationEquiv w ((polynomialShearRealAutEquiv w s hw).symm e).coord =
      polynomialShearLog e := by
  change polynomialShearRealificationEquiv w ((polynomialShearRealificationEquiv w).symm
    (polynomialShearLog e)) = _
  exact LieEquiv.apply_symm_apply _ _

end Erdos3

end

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial Module
open scoped TensorProduct

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

noncomputable def shearCoordinatePolynomial (A : PolynomialSlots σ d w)
    (a : PolynomialShearIndex w) : MvPolynomial σ ℝ :=
  -polynomialSlotCoefficient a.2.val (A.symbolicLogSlot a.1)

theorem shearCoordinatePolynomial_degree (A : PolynomialSlots σ d w) (a : PolynomialShearIndex w) :
    A.shearCoordinatePolynomial a ∈ weightedSupportLE (fun _ : σ => 1) (polynomialShearDeficit w a) := by
  exact (weightedSupportLE _ _).neg_mem
    (polynomialSlotCoefficient_degree (fun _ : σ => 1) w (A.symbolicLogSlot_degree a.1) a.2.val)

end Erdos3.PolynomialSlots

end

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial Module VectorPolynomial
open scoped TensorProduct

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ} [Fintype (PolynomialShearIndex w)]

noncomputable def shearLogPolynomial (A : PolynomialSlots σ d w) :
    VectorPolynomial σ ℚ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ) :=
  VectorPolynomial.ofCoordinates ((polynomialShearBasis (R := ℚ) w).baseChange ℝ)
    A.shearCoordinatePolynomial

theorem shearLogPolynomial_coordinate (A : PolynomialSlots σ d w) (a : PolynomialShearIndex w) :
    VectorPolynomial.coordinate
      (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a).toAddMonoidHom A.shearLogPolynomial =
      A.shearCoordinatePolynomial a :=
  VectorPolynomial.coordinate_ofCoordinates _ _ _

end Erdos3.PolynomialSlots

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.PolynomialShearNilmanifold
namespace OAI

section

namespace Erdos3

open Module

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) [Fintype (PolynomialShearIndex w)]

noncomputable def polynomialShearLayerBasis (r : ℕ) :
    Basis {j : Fin (Fintype.card (PolynomialShearIndex w)) // r ≤ polynomialShearOrderedWeight w j}
      ℚ (polynomialShearLayer (R := ℚ) w r) :=
  supportedSubmoduleBasis (polynomialShearOrderedBasis w) (polynomialShearLayer w r)
    {j | r ≤ polynomialShearOrderedWeight w j} (polynomialShearOrderedBasis_layers w r)

noncomputable def polynomialShearLayerIndexEquiv (r : ℕ) :
    {j : Fin (Fintype.card (PolynomialShearIndex w)) // r ≤ polynomialShearOrderedWeight w j} ≃
      Fin (finrank ℚ (polynomialShearLayer (R := ℚ) w r)) := by
  classical
  exact Fintype.equivFinOfCardEq (finrank_eq_card_basis (polynomialShearLayerBasis w r)).symm

noncomputable def polynomialShearLayerFinBasis (r : ℕ) :
    Basis (Fin (finrank ℚ (polynomialShearLayer (R := ℚ) w r)))
      ℚ (polynomialShearLayer (R := ℚ) w r) :=
  (polynomialShearLayerBasis w r).reindex (polynomialShearLayerIndexEquiv w r)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedLoweringTriangular
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

variable {d : ℕ} {w : Fin d → ℕ}

theorem weightedLoweringSubstitution_difference (e : WeightedLoweringAut w R) (hw : Monotone w)
    (i : Fin d) (x y : Fin d → R) (hxy : ∀ j, j < i → x j = y j) :
    polynomialSubstitutionPoint e.val.toAlgHom x i - x i =
      polynomialSubstitutionPoint e.val.toAlgHom y i - y i := by
  have h := aeval_eq_of_weightedSupportLT (e.property i) x y (fun j hj =>
    hxy j (lt_of_not_ge (fun hij => (not_le_of_gt hj) (hw hij))))
  change aeval x (e.val (X i)) - x i = aeval y (e.val (X i)) - y i
  simpa only [map_sub, aeval_X] using h

theorem weightedLoweringSubstitution_prefix (e : WeightedLoweringAut w R) (hw : Monotone w)
    (i : Fin d) (x y : Fin d → R) (hxy : ∀ j, j < i → x j = y j)
    (j : Fin d) (hj : j < i) :
    polynomialSubstitutionPoint e.val.toAlgHom x j =
      polynomialSubstitutionPoint e.val.toAlgHom y j := by
  have h := weightedLoweringSubstitution_difference e hw j x y
    (fun k hk => hxy k (hk.trans hj))
  rw [hxy j hj] at h
  simpa only [sub_add_cancel] using congrArg (fun z => z + y j) h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearWeightedOrbitCoordinates
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial Module VectorPolynomial
open scoped TensorProduct

section Coordinates

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}
variable (s : ℕ) (hw : ∀ i, w i ≤ s) (weight : σ → ℕ)

theorem weightedPolynomialShearReal_adapted_iff_coordinate_support
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)) :
    (polynomialShearFiltration w s hw).realification.Adapted weight p ↔
      ∀ a : PolynomialShearIndex w,
        VectorPolynomial.coordinate
          (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a).toAddMonoidHom p ∈
          weightedSupportLE weight (polynomialShearDeficit w a) := by
  rw [NilpotentLieFiltration.adapted_iff_coefficients]
  constructor
  · intro hp a α hα
    change α ∈ (VectorPolynomial.coordinate
      (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a).toAddMonoidHom p).support at hα
    by_contra hdeg
    have hc := ((polynomialShearFiltration w s hw).real_mem_layer_iff_basis_coordinates
      (polynomialShearBasis (R := ℚ) w) (polynomialShearDeficit w)
      (fun j => polynomialShearLayer_span w j) _ _).mp (hp α) a hdeg
    apply (MvPolynomial.mem_support_iff.mp hα)
    rw [VectorPolynomial.coeff_coordinate]
    exact hc
  · intro hp α
    apply ((polynomialShearFiltration w s hw).real_mem_layer_iff_basis_coordinates
      (polynomialShearBasis (R := ℚ) w) (polynomialShearDeficit w)
      (fun j => polynomialShearLayer_span w j) _ _).mpr
    intro a ha
    change (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a)
      (VectorPolynomial.coefficients p α) = 0
    have hc : (VectorPolynomial.coordinate
        (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a).toAddMonoidHom p).coeff α = 0 := by
      by_contra hne
      exact ha (hp a (MvPolynomial.mem_support_iff.mpr hne))
    exact (VectorPolynomial.coeff_coordinate _ p α).symm.trans hc

noncomputable def weightedPolynomialShearOrbitParameterCoordinates
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit weight)
    (a : PolynomialShearIndex w) : MvPolynomial σ ℝ :=
  VectorPolynomial.coordinate
    (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a).toAddMonoidHom g.log

theorem weightedPolynomialShearOrbitParameterCoordinates_degree
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit weight)
    (a : PolynomialShearIndex w) :
    weightedPolynomialShearOrbitParameterCoordinates s hw weight g a ∈
      weightedSupportLE weight (polynomialShearDeficit w a) :=
  (weightedPolynomialShearReal_adapted_iff_coordinate_support s hw weight g.log).mp g.adapted a

end Coordinates

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchShearOrbitConverse
namespace OAI

section

namespace Erdos3.PolynomialSlots

open _root_.MvPolynomial

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

noncomputable def shearTransformedSlots (A : PolynomialSlots σ d w)
    (hw : Monotone w) (e : WeightedLoweringAut w ℝ) : TriangularSlots d where
  center x i := x i - aeval (polynomialSubstitutionPoint e.val.toAlgHom x)
    (A.topResidualEquiv (X i))
  lower i x y hxy := by
    have hd := weightedLoweringSubstitution_difference e hw i x y hxy
    have htop :
        aeval (polynomialSubstitutionPoint e.val.toAlgHom x)
            (rename (earlierSlot i) (A.topPart.specializeCenter 0 i)) =
        aeval (polynomialSubstitutionPoint e.val.toAlgHom y)
            (rename (earlierSlot i) (A.topPart.specializeCenter 0 i)) := by
      rw [MvPolynomial.aeval_rename, MvPolynomial.aeval_rename]
      apply congrArg (fun f : Fin i.val → ℝ => aeval f (A.topPart.specializeCenter 0 i))
      funext j
      exact weightedLoweringSubstitution_prefix e hw i x y hxy (earlierSlot i j) j.isLt
    rw [A.topResidualEquiv_X, map_sub, map_sub, aeval_X, aeval_X, htop]
    linarith

theorem shearTransformedSlots_residual (A : PolynomialSlots σ d w)
    (hw : Monotone w) (e : WeightedLoweringAut w ℝ) (b : Fin d → ℤ) :
    (A.shearTransformedSlots hw e).residual b =
      fun i => aeval (polynomialSubstitutionPoint e.val.toAlgHom (fun j => (b j : ℝ)))
        (A.topResidualEquiv (X i)) := by
  funext i
  change (b i : ℝ) - ((b i : ℝ) - _) = _
  ring

end Erdos3.PolynomialSlots

end

section

namespace Erdos3.PolynomialPatch

variable {σ : Type*} {s d : ℕ}

theorem shearSummand_eq_residual (A : PolynomialPatch σ s d)
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.Group) (b : Fin d → ℤ) :
    A.shearKernel (polynomialShearRealPointAction A.weight s A.weight_le g (fun i => (b i : ℝ))) =
      A.kernel.value ((A.form.shearTransformedSlots A.weight_mono
        (polynomialShearRealAutEquiv A.weight s A.weight_le g)⁻¹).residual b) := by
  rw [PolynomialSlots.shearTransformedSlots_residual]
  rfl

theorem shearSummand_unique (A : PolynomialPatch σ s d)
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.Group)
    {b c : Fin d → ℤ}
    (hb : A.shearKernel (polynomialShearRealPointAction A.weight s A.weight_le g
      (fun i => (b i : ℝ))) ≠ 0)
    (hc : A.shearKernel (polynomialShearRealPointAction A.weight s A.weight_le g
      (fun i => (c i : ℝ))) ≠ 0) : b = c := by
  rw [A.shearSummand_eq_residual] at hb hc
  exact TriangularSlots.contributing_unique _ A.kernel hb hc

theorem shearOrbitSum_eq_patchValue (A : PolynomialPatch σ s d)
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.Group) :
    polynomialShearOrbitSum A.weight s A.weight_le A.shearKernel g =
      (A.form.shearTransformedSlots A.weight_mono
        (polynomialShearRealAutEquiv A.weight s A.weight_le g)⁻¹).patchValue A.kernel := by
  unfold polynomialShearOrbitSum TriangularSlots.patchValue
  exact tsum_congr (A.shearSummand_eq_residual g)

end Erdos3.PolynomialPatch

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearParameterBudget
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial Module
open scoped NNReal TensorProduct

variable {σ : Type*} [Fintype σ] (w : σ → ℕ)

theorem polynomialShearRealPointAction_eq_exp (s : ℕ) (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).realification.Group) (x : σ → ℝ) (i : σ) :
    polynomialShearRealPointAction w s hw g x i =
      aeval x (polynomialShearExp (-(polynomialShearRealificationEquiv w g.coord)) (X i)) := by
  change aeval x ((polynomialShearRealAutEquiv w s hw g).val.symm (X i)) = _
  have he := congrArg (fun e : WeightedLoweringAut w ℝ => aeval x (e.val (X i)))
    (polynomialShearRealAutEquiv_apply w s hw g⁻¹)
  simpa only [map_inv, Subgroup.coe_inv, AlgEquiv.aut_inv, NilpotentLieBCHGroup.coord_inv,
    map_neg, polynomialShearExpAut_apply] using he

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped NNReal

namespace PolynomialPatch

variable {σ : Type*} {s d : ℕ}

noncomputable def shearKernelLipBound (A : PolynomialPatch σ s d) (M : ℝ≥0) : ℝ≥0 :=
  max 1 (A.kernel.lip * ((1 + M) * d * s *
    ((1 + M) ^ (s * d) + 1) ^ (s * (d + 1))))

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3.PolynomialPatch

open NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {σ : Type*} {s d : ℕ} (A : PolynomialPatch σ s d)
  [Fintype (PolynomialShearIndex A.weight)]

noncomputable def shearObservableLipBound (M : ℝ≥0) : ℝ≥0 :=
  let C := bchLogMetricConstant s (Fintype.card (PolynomialShearIndex A.weight)) (2 * s + 1) 1
  max C (A.shearKernelLipBound M *
    polynomialShearDisplacementBound s d ((1 + M) ^ (s * d)) * C)

end Erdos3.PolynomialPatch

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchAmplification
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def relativePatchDistinctWeights {X : Type*} {s d : ℕ}
    (A : PolynomialPatch X s d) : ℕ :=
  (Finset.univ.image A.weight).card

noncomputable def relativePatchBoxScore {X : Type*} [Fintype X] [DecidableEq X]
    {s d : ℕ} (N : X → ℕ) (f : (X → ℤ) → ℝ) (a : ℝ)
    (A : PolynomialPatch X s d) : ℝ :=
  𝔼 x ∈ integerBox N, (f x - a) * A.value (fun i => (x i : ℝ))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.FixedPathSlicedGridMeshBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def fixedPathSlicedGridMeshLog (D C V cost E : ℝ) : ℝ :=
  Real.log (D + C + 8) + V + cost + E + 2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientSliceEmbedding
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NormalizedScalarCubeSource

theorem coefficientDensity_nonneg (s : NormalizedScalarCubeSource Empty) (z : s.CoefficientDomain) :
    0 ≤ s.coefficientDensity z := (s.weight_range _).1

end NormalizedScalarCubeSource

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.IdealInvariantNiltestBudget
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d n : ℕ}
  (D : RationalFilteredNilmanifold L s d) (I : LieIdeal ℚ L)
  (hI : D.filtration.layer (t + 1) ≤ I.toSubmodule)
  (Q : RationalFilteredNilmanifold (L ⧸ I) t n)
  (hQF : Q.filtration = D.filtration.quotientLie I hI)

noncomputable def idealQuotientOrbit {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) :
    Q.filtration.realification.PolynomialOrbit w :=
  let q := D.filtration.realQuotientPolynomialOrbit I hI g
  NilpotentLieFiltration.polynomialOrbitOfLog q.log (by rw [hQF]; exact q.adapted)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def intervalClip (T : D.Niltest w) : D.Niltest w where
  orbit := T.orbit
  observable := fun z => ((max 0 (min 1 (T.observable z).re) : ℝ) : ℂ)
  normBound := T.normBound
  lipBound := T.lipBound
  norm_le z := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    exact (max_le (norm_nonneg _) ((min_le_right _ _).trans (Complex.re_le_norm _))).trans (T.norm_le z)
  lipschitz := by
    let := D.metricSpace
    have hr : LipschitzWith T.lipBound (fun z => (T.observable z).re) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      calc
        dist (T.observable x).re (T.observable y).re ≤ dist (T.observable x) (T.observable y) := by
          simpa only [Real.dist_eq, dist_eq_norm, Complex.sub_re, Real.norm_eq_abs] using
            Complex.abs_re_le_norm (T.observable x - T.observable y)
        _ ≤ T.lipBound * dist x y := T.lipschitz.dist_le_mul x y
    simpa only [one_mul, Function.comp_def] using
      Complex.isometry_ofReal.lipschitz.comp ((hr.const_min 1).const_max 0)

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def withUnitBound (T : D.Niltest w) (hcap : ∀ x, ‖T.observable x‖ ≤ 1) : D.Niltest w :=
  { T with normBound := 1, norm_le := hcap }

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeEqualDimension
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d k : ℕ}

def castDimension (D : RationalFilteredNilmanifold L s d) (h : d = k) :
    RationalFilteredNilmanifold L s k := h ▸ D

theorem castDimension_geometry (D : RationalFilteredNilmanifold L s d) (h : d = k) (p : ℝ) :
    (D.castDimension h).GeometryComplexityLE p ↔ D.GeometryComplexityLE p := by
  cases h
  rfl

namespace Niltest

variable {σ : Type*} {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

noncomputable def castDimension (T : D.Niltest w) (h : d = k) : (D.castDimension h).Niltest w := by
  cases h
  exact T

theorem castDimension_normBound (T : D.Niltest w) (h : d = k) :
    (T.castDimension h).normBound = T.normBound := by
  cases h
  rfl

theorem castDimension_eval (T : D.Niltest w) (h : d = k) (x : σ → ℤ) :
    (T.castDimension h).eval x = T.eval x := by
  cases h
  rfl

theorem castDimension_complexity (T : D.Niltest w) (h : d = k) (p : ℝ) :
    (T.castDimension h).ComplexityLE p ↔ T.ComplexityLE p := by
  cases h
  rfl

end Niltest
end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PinnedSectionMeans
namespace OAI

section

namespace Erdos3.ProductCylinder

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i) (f : (∀ i, X i) → ℝ)

noncomputable def score (K : ℝ) (c : ProductCylinder X) : ℝ := c.mass μ base f / K ^ c.1.card

def Maximizes (K : ℝ) (b : ℕ) (c : ProductCylinder X) : Prop :=
  c.1.card ≤ b ∧ ∀ d : ProductCylinder X, d.1.card ≤ b → score μ base f K d ≤ score μ base f K c

end Erdos3.ProductCylinder

end

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

def ProductMarginalsClose (rho : (∀ i, X i) → ℝ) (eta : ℝ) (s : ℕ) : Prop :=
  ∀ B : Finset I, B.card ≤ s → ∀ x, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
    |productConditionalMean μ B rho x - 1| ≤ eta

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ProductANOVAEnergyOrder
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

noncomputable def productANOVA (S : Finset I) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) : ℝ :=
  ∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card * productConditionalMean μ (S \ U) f x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RegularCylinderDecomposition
namespace OAI

section

namespace Erdos3.ProductCylinder

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
  {X : ι → Type*} [∀ i, Fintype (X i)]
  (μ : ∀ i, FiniteProbabilityWeights (X i)) (base : ∀ i, X i)
  (p : FiniteProbabilityWeights Ω) (F : Ω → ∀ i, X i)

noncomputable def positiveCandidates (b : ℕ) (w : Ω → ℝ) : Finset (ProductCylinder X) := by
  classical
  exact (bounded (X := X) b).filter (fun c => 0 < c.mass μ base (observedProductDensity μ p F w))

end Erdos3.ProductCylinder

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UnbalancedBohrShape
namespace OAI

section

namespace Erdos3.Peeling

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

def admissibleBohrShape (B : CyclicBohr.Set N) (scale : ℝ≥0) (rankExtra : ℕ)
    (minimumWidth : ℝ) (C : CyclicBohr.Set N) : Prop :=
  C.IsRankRegular ∧ C.carrier ⊆ (B.ndilate scale).carrier ∧
    C.rank ≤ B.rank + rankExtra ∧ minimumWidth ≤ C.radius

def admissibleBohrCarriers (B : CyclicBohr.Set N) (scale : ℝ≥0) (rankExtra : ℕ)
    (minimumWidth : ℝ) (A : Finset (ZMod N)) : Prop :=
  ∃ C : CyclicBohr.Set N, admissibleBohrShape B scale rankExtra minimumWidth C ∧ A = C.carrier

end Erdos3.Peeling

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RationalModelCoordinates
namespace OAI

section

namespace Erdos3

open Module

namespace RationalFilteredNilmanifold

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

noncomputable def paddedLayerVector (i : Fin (s + 1)) (k : Fin d) : L :=
  if h : k.val < finrank ℚ (D.filtration.layer (i.val + 1)) then
    (D.layerBasis i ⟨k.val, h⟩ : L) else 0

theorem paddedLayerVector_span (i : Fin (s + 1)) :
    Submodule.span ℚ (Set.range (D.paddedLayerVector i)) = D.filtration.layer (i.val + 1) := by
  classical
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  have hd : finrank ℚ (D.filtration.layer (i.val + 1)) ≤ d := by
    simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using
      (D.filtration.layer (i.val + 1)).finrank_le
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    dsimp only [paddedLayerVector]
    split_ifs
    · exact (D.layerBasis i _).property
    · exact Submodule.zero_mem _
  · intro x hx
    have hb (k : Fin (finrank ℚ (D.filtration.layer (i.val + 1)))) :
        (D.layerBasis i k : L) ∈ Submodule.span ℚ (Set.range (D.paddedLayerVector i)) := by
      apply Submodule.subset_span
      refine ⟨⟨k.val, k.isLt.trans_le hd⟩, ?_⟩
      simp only [paddedLayerVector, k.isLt, dite_true]
    have heq : (∑ k, (D.layerBasis i).repr ⟨x, hx⟩ k • (D.layerBasis i k : L)) = x := by
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using
        congrArg Subtype.val ((D.layerBasis i).sum_repr ⟨x, hx⟩)
    rw [← heq]
    exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (hb k))

theorem paddedLayerVector_height {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (i : Fin (s + 1)) (j k : Fin d) :
    rationalLogHeight (D.basis.repr (D.paddedLayerVector i j) k) ≤ p := by
  dsimp only [paddedLayerVector]
  split_ifs
  · exact hD.2.2.2 i _ k
  · simpa [rationalLogHeight] using hp

noncomputable def rationalModelCoordinates : RationalModelCoordinateIndex s d → ℚ
  | .inl z => lieStructureConstants D.basis z.1 z.2.1 z.2.2
  | .inr z => D.basis.repr (D.paddedLayerVector z.1 z.2.1) z.2.2

theorem rationalModelCoordinates_height {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (z : RationalModelCoordinateIndex s d) :
    rationalLogHeight (D.rationalModelCoordinates z) ≤ p := by
  rcases z with z | z
  · exact hD.2.2.1 z.1 z.2.1 z.2.2
  · exact D.paddedLayerVector_height hp hD z.1 z.2.1 z.2.2

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RelativePatchFiniteCoordinateReduction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace PolynomialPatch

variable {X Y : Type*} {s d : ℕ}

noncomputable def coordinateEquiv (A : PolynomialPatch X s d) (e : X ≃ Y) :
    PolynomialPatch Y s d :=
  A.reparam (fun i => MvPolynomial.X (e i)) (fun i => weightedSupportLE_X _ (e i))

@[simp] theorem coordinateEquiv_kernel (A : PolynomialPatch X s d) (e : X ≃ Y) :
    (A.coordinateEquiv e).kernel = A.kernel := rfl

@[simp] theorem coordinateEquiv_weight (A : PolynomialPatch X s d) (e : X ≃ Y) :
    (A.coordinateEquiv e).weight = A.weight := rfl

end PolynomialPatch

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LieSubalgebraLatticeInnerGrid
namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators Matrix TensorProduct

theorem bchSubgroup_comap_inner_grid_of_columns
    {ι κ L M : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}
    (b : Basis κ ℚ M) (e : Basis ι ℚ L) (φ : M →ₗ⁅ℚ⁆ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) (l q : ℕ)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (hcolumns : ∀ j, e.equivFun (φ (b j)) ∈ denominatorGrid q) :
    scaledIntegerGrid (l * q) ⊆ bchSubgroupCoordinates b
      (Γ.comap (NilpotentLieBCHGroup.map (hnil := hM) φ)) := by
  rw [bchSubgroupCoordinates_comap b e φ Γ]
  have hB : ∀ j, (LinearMap.toMatrix b e φ.toLinearMap).col j ∈ denominatorGrid q := by
    intro j
    have he : (LinearMap.toMatrix b e φ.toLinearMap).col j =
        e.equivFun (φ (b j)) := by
      funext i
      exact LinearMap.toMatrix_apply b e φ.toLinearMap i j
    rw [he]
    exact hcolumns j
  intro x hx
  exact hinner (scaledIntegerGrid_mulVec_of_column_denominators _ l q hB hx)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FixedKernelPatchFunction
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

namespace PolynomialSlots

theorem loweringAt_patchValue {X : Type*} {d : ℕ} {w : Fin d → ℕ}
    (A : PolynomialSlots X d w) (hw : Monotone w) (Φ : PatchKernel d) (t : X → ℝ) :
    ((A.shearTransformedSlots hw (A.loweringAt t)).patchValue Φ) = (A.slots t).patchValue Φ := by
  unfold TriangularSlots.patchValue
  apply tsum_congr
  intro b
  congr 1
  rw [shearTransformedSlots_residual]
  exact A.top_factorization_residual t b

end PolynomialSlots
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeChartKernel
namespace OAI

section

namespace Erdos3

open _root_.Set
open scoped NNReal

variable {ι X : Type*} [Fintype ι] [MetricSpace X]

theorem chartCoordinateKernel_support (phi : OpenPartialHomeomorph (ι → ℝ) X)
    (F : X → ℝ) {r : ℝ} (hr : 0 < r)
    (hsource : phi.source = {v | ∀ i, |v i| < r})
    (hinner : tsupport F ⊆ phi '' Metric.closedBall 0 (3 * r / 4)) :
    Function.support (chartCoordinateKernel phi F) ⊆ Metric.closedBall 0 (3 * r / 4) := by
  intro v hv
  change chartCoordinateKernel phi F v ≠ 0 at hv
  have hvs : v ∈ phi.source := by
    by_contra h
    exact hv (chartCoordinateKernel_of_not_mem phi F h)
  have hFv : F (phi v) ≠ 0 := by
    rwa [chartCoordinateKernel_of_mem phi F hvs] at hv
  obtain ⟨u, hu, heq⟩ := hinner (subset_closure hFv)
  have hus := closedBox_subset_chart_source phi hr hsource hu
  have huv : u = v := by
    calc
      u = phi.symm (phi u) := (phi.left_inv hus).symm
      _ = phi.symm (phi v) := congrArg phi.symm heq
      _ = v := phi.left_inv hvs
  exact huv ▸ hu

theorem chartCoordinateKernel_lipschitz (phi : OpenPartialHomeomorph (ι → ℝ) X)
    (F : X → ℝ) (A K r : ℝ≥0) (hr : 0 < r)
    (hF : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (hLip : LipschitzWith A F)
    (hsource : phi.source = {v | ∀ i, |v i| < (r : ℝ)})
    (hinner : tsupport F ⊆ phi '' Metric.closedBall 0 (3 * (r : ℝ) / 4))
    (hForward : LipschitzOnWith K phi phi.source) :
    LipschitzWith (A * K + 1 / (r / 4)) (chartCoordinateKernel phi F) := by
  apply lipschitz_chartCutoff phi.symm F A K (r / 4) (by positivity) hF hLip hForward
  intro v hv hFv y hy
  change v ∈ phi.source at hv
  change y ∉ phi.source at hy
  have hvk : chartCoordinateKernel phi F v ≠ 0 := by
    rwa [chartCoordinateKernel_of_mem phi F hv]
  have hball := chartCoordinateKernel_support phi F hr hsource hinner hvk
  rw [Metric.mem_closedBall, dist_zero_right] at hball
  obtain ⟨i, hyi⟩ : ∃ i, (r : ℝ) ≤ |y i| := by
    simpa only [hsource, mem_ofPred_eq, not_forall, not_lt] using hy
  have hvi : |v i| ≤ 3 * (r : ℝ) / 4 := by
    calc
      |v i| = ‖v i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖v‖ := norm_le_pi_norm v i
      _ ≤ _ := hball
  have hd : |y i - v i| ≤ dist v y := by
    simpa only [Real.dist_eq, abs_sub_comm] using dist_le_pi_dist v y i
  have ht : |y i| ≤ |y i - v i| + |v i| := by
    simpa only [sub_add_cancel] using abs_add_le (y i - v i) (v i)
  change (r : ℝ) / 4 ≤ dist v y
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {X : Type*} [MetricSpace X] {d : ℕ}
  (phi : OpenPartialHomeomorph (Fin d → ℝ) X) (F : X → ℝ)
  (A K r : ℝ≥0) (hr : 0 < r) (hr1 : r ≤ 1)
  (hF : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (hLip : LipschitzWith A F)
  (hsource : phi.source = {v | ∀ i, |v i| < (r : ℝ)})
  (hinner : tsupport F ⊆ phi '' Metric.closedBall 0 (3 * (r : ℝ) / 4))
  (hForward : LipschitzOnWith K phi phi.source) (B : ℕ) (hB : 4 ≤ B)

noncomputable def scaledChartKernel : PatchKernel d where
  value x := chartCoordinateKernel phi F ((B : ℝ) • x)
  nonneg x := (chartCoordinateKernel_range phi F hF _).1
  le_one x := (chartCoordinateKernel_range phi F hF _).2
  support x hx i := by
    have hb := chartCoordinateKernel_support phi F hr hsource hinner hx
    rw [Metric.mem_closedBall, dist_zero_right] at hb
    have hi : (B : ℝ) * |x i| ≤ 3 * (r : ℝ) / 4 := by
      calc
        (B : ℝ) * |x i| = ‖((B : ℝ) • x) i‖ := by
          simp only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (Nat.cast_nonneg (α := ℝ) B)]
        _ ≤ ‖(B : ℝ) • x‖ := norm_le_pi_norm ((B : ℝ) • x) i
        _ ≤ _ := hb
    have hBr : (4 : ℝ) ≤ B := by exact_mod_cast hB
    have hsmall := mul_le_mul_of_nonneg_right hBr (abs_nonneg (x i))
    have hr1' : (r : ℝ) ≤ 1 := hr1
    linarith
  lip := (A * K + 1 / (r / 4)) * B
  lipschitz := by
    simpa only [Function.comp_def] using
      (chartCoordinateKernel_lipschitz phi F A K r hr hF hLip hsource hinner hForward).comp
        (chartKernelScaling_lipschitz d B)

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} (T : D.Niltest w)

theorem realObservable_lipschitz :
    letI := D.metricSpace
    LipschitzWith T.lipBound (fun x => (T.observable x).re) := by
  let := D.metricSpace
  simpa only [one_mul, Function.comp_def, RCLike.re_eq_complex_re] using
    (RCLike.lipschitzWith_re (K := ℂ)).comp T.lipschitz

theorem realObservable_tsupport :
    tsupport (fun x => (T.observable x).re) ⊆ tsupport T.observable := by
  apply closure_mono
  intro x hx
  change T.observable x ≠ 0
  intro hzero
  apply hx
  change (T.observable x).re = 0
  rw [hzero, Complex.zero_re]

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.SumNilmanifoldFactors
namespace OAI

section

universe u

namespace Erdos3

open scoped TensorProduct

namespace RationalFilteredNilmanifold

variable {ι κ σ : Type*} {L : ι → Type u} {M : κ → Type u}
  [∀ i, LieRing (L i)] [∀ j, LieRing (M j)]
  [∀ i, LieAlgebra ℚ (L i)] [∀ j, LieAlgebra ℚ (M j)] {s : ℕ} {d : ι → ℕ} {e : κ → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  (E : ∀ j, RationalFilteredNilmanifold (M j) s (e j))

noncomputable def sumFactors : ∀ k : ι ⊕ κ,
    RationalFilteredNilmanifold (sumLieSpace L M k) s (Sum.elim d e k)
  | .inl i => D i
  | .inr j => E j

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.UnitComparisonNiltest
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  (T U : D.Niltest w) (hT : ∀ x, ‖T.observable x‖ ≤ 1)
  (hU : ∀ x, ‖U.observable x‖ ≤ 1)

noncomputable def unitComparison : D.Niltest w where
  orbit := T.orbit
  observable x := T.observable x * star (U.observable x)
  normBound := 1
  lipBound := U.lipBound + T.lipBound
  norm_le x := by
    change ‖T.observable x * star (U.observable x)‖ ≤ (1 : ℝ)
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hT x)).trans (hU x)
  lipschitz := by
    let := D.metricSpace
    simpa only [one_mul] using lipschitz_mul_star_of_bounds T.observable U.observable
      (Bf := 1) (Bg := 1) T.lipschitz U.lipschitz hT hU

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PatchKernelGridBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace PolynomialPatch

variable {X : Type*} {s d N : ℕ}

theorem gridKernelReplacement_score (A : PolynomialPatch X s d) (hN : 8 ≤ N)
    {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)
    (point : Ω → X → ℝ) (score : Ω → ℝ) (hscore : ∀ x, |score x| ≤ 1) :
    p.mean (fun x => score x * A.value (point x)) - 2 * A.kernel.lip * (patchKernelGridRadius N : ℝ) ≤
      ∑ i : Fin d → Fin (N + 1), A.kernel.value (uniformBoxGrid (1 / 4) N i) *
        p.mean (fun x => score x * (A.gridKernelReplacement hN i).value (point x)) := by
  let c := fun i : Fin d → Fin (N + 1) => A.kernel.value (uniformBoxGrid (1 / 4) N i)
  let g := fun x => ∑ i : Fin d → Fin (N + 1), c i * (A.gridKernelReplacement hN i).value (point x)
  have hpoint (x) : score x * A.value (point x) ≤ score x * g x +
      2 * A.kernel.lip * (patchKernelGridRadius N : ℝ) := by
    have hbound : |score x * (A.value (point x) - g x)| ≤
        2 * A.kernel.lip * (patchKernelGridRadius N : ℝ) := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (hscore x) (abs_nonneg _)).trans
        (by simpa only [one_mul, g, c] using A.gridKernelReplacement_approx hN (point x))
    linarith [le_abs_self (score x * (A.value (point x) - g x))]
  have hmean := p.mean_mono hpoint
  rw [p.mean_add, p.mean_const] at hmean
  have hidentity : p.mean (fun x => score x * g x) =
      ∑ i, c i * p.mean (fun x => score x * (A.gridKernelReplacement hN i).value (point x)) := by
    dsimp only [g]
    simp_rw [Finset.mul_sum]
    rw [p.mean_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← p.mean_const_mul]
    congr 1
    funext x
    ring
  rw [hidentity] at hmean
  exact (sub_le_iff_le_add).mpr hmean

theorem exists_gridKernelReplacement_score (A : PolynomialPatch X s d) (hN : 8 ≤ N)
    {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)
    (point : Ω → X → ℝ) (score : Ω → ℝ) (hscore : ∀ x, |score x| ≤ 1)
    {δ : ℝ} (hδ : 0 < δ)
    (hpositive : δ ≤ p.mean (fun x => score x * A.value (point x)))
    (hmesh : 2 * A.kernel.lip * (patchKernelGridRadius N : ℝ) ≤ δ / 2) :
    ∃ i : Fin d → Fin (N + 1), δ / (2 * ((N + 1 : ℕ) : ℝ) ^ d) ≤
      p.mean (fun x => score x * (A.gridKernelReplacement hN i).value (point x)) := by
  have h := A.gridKernelReplacement_score hN p point score hscore
  have hs : δ / 2 ≤ ∑ i : Fin d → Fin (N + 1),
      A.kernel.value (uniformBoxGrid (1 / 4) N i) *
        p.mean (fun x => score x * (A.gridKernelReplacement hN i).value (point x)) := by linarith
  obtain ⟨i, hi⟩ := exists_positive_combination_term _ _
    (fun i => ⟨A.kernel.nonneg _, A.kernel.le_one _⟩) (by positivity : 0 < δ / 2) hs
  refine ⟨i, ?_⟩
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, div_div] using hi

end PolynomialPatch
end Erdos3

end

end OAI
end


