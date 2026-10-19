-- Prove2me | Definitions.Def_OAIE3v2B121
-- name    : OAIE3v2B121
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:51:46.095484+00:00
-- url     : https://prove2.me/theorems/7138537f-f559-4d3d-aee0-795524f26b0d
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 123 of 311
-- statement:
--   Definitions bundle 123 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B101`, `OAIE3v2B102`, `OAIE3v2B104`, `OAIE3v2B107`, `OAIE3v2B108` of this split.
--
--   Modules: `Estimates/CurrentLayerPreservation.lean`, `Estimates/HomogeneousSubspaceCorrections.lean`, `Estimates/LinearCoefficientSplitting.lean`, `Estimates/RationalPowerHeight.lean`, `Estimates/UniformFormalCurrentLayerStep.lean`, `Fourier/BoundedFrequencyKernel.lean`, `Fourier/ControlledReplicatedFrequency.lean`, `Fourier/JoinedFrequencyQuotientInjectivity.lean`, `Fourier/LogCharacterBudget.lean`, `Geometry/CentralOrbitMetric.lean`, `Geometry/HorizontalCoordinateBounds.lean`, `Geometry/RealSubspaceCoordinateRetraction.lean`, `Lattices/RationalLatticeFunctional.lean`, `Linear/DualDerivativeRemoval.lean`, `Linear/DualIdealSteps.lean`, `Linear/GradeProjectionRemainder.lean`, `Linear/RankQuotientHeightBudget.lean`, `Linear/RationalTaggedSpanProjection.lean`, `Linear/WeightedTranslationBasisHeight.lean`, `Polynomial/ControlledPositivePolynomialDownsets.lean`, `Polynomial/ControlledSubspaceCorrectionPolynomials.lean`, `Polynomial/PolynomialSymbolBounds.lean`, `Polynomial/RealPolynomialChartSubstitution.lean`, `Polynomial/ScaledPolynomialDualBounds.lean`, `Polynomial/ShiftedPolynomialBasis.lean`, `Polynomial/SubspacePolynomialCoordinates.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B101
import Definitions.Def_OAIE3v2B102
import Definitions.Def_OAIE3v2B104
import Definitions.Def_OAIE3v2B107
import Definitions.Def_OAIE3v2B108

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ShiftedPolynomialBasis
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

theorem eq_affine_of_degreeLE_one {σ R V : Type*} [Fintype σ]
    [CommRing R] [AddCommGroup V] [Module R V]
    (p : VectorPolynomial σ R V) (hp : DegreeLE (fun _ : σ => 1) 1 p) :
    p = monomial 0 (coefficients p 0) +
      linearPolynomial (fun i => coefficients p (Finsupp.single i 1)) := by
  classical
  apply coefficients.injective
  ext α
  rw [map_add, Finsupp.add_apply, coefficients_monomial]
  by_cases hz : α = 0
  · subst α
    rw [Finsupp.single_eq_same, coefficients_linearPolynomial_zero, add_zero]
  · rw [Finsupp.single_eq_of_ne hz, zero_add]
    by_cases hα : Finsupp.weight (fun _ : σ => 1) α ≤ 1
    · obtain hzero | ⟨i, rfl⟩ := exponent_of_weight_le_one α hα
      · exact (hz hzero).elim
      · rw [coefficients_linearPolynomial_single]
    · rw [hp α (Nat.lt_of_not_ge hα)]
      symm
      apply coefficients_linearPolynomial_of_ne
      intro i hi
      apply hα
      rw [← hi]
      simp only [Finsupp.weight_single, one_smul, le_refl]

theorem eval₂_affine_of_degreeLE_one {σ R S V : Type*} [Fintype σ]
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]
    (p : VectorPolynomial σ R V) (hp : DegreeLE (fun _ : σ => 1) 1 p) (t : σ → S) :
    eval₂ t p = coefficients p 0 + ∑ i, t i • coefficients p (Finsupp.single i 1) := by
  conv_lhs => rw [eq_affine_of_degreeLE_one p hp]
  rw [map_add, eval₂_monomial, Finsupp.prod_zero_index, one_smul, eval₂_linearPolynomial]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.GradeProjectionRemainder
namespace OAI

section

namespace Erdos3

open Module

namespace NilpotentLieFiltration

open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem realGradeProjection_bch_triple (k : ℕ) (a p d : ℝ ⊗[ℚ] L)
    (ha : a ∈ F.realification.layer k) (hd : d ∈ F.realification.layer k) :
    basisGradeProjection (b.baseChange ℝ) w k (lieBCH s (lieBCH s a p) d) =
      basisGradeProjection (b.baseChange ℝ) w k a +
        basisGradeProjection (b.baseChange ℝ) w k p +
        basisGradeProjection (b.baseChange ℝ) w k d := by
  have h := F.realGradeProjection_eq_zero_of_mem_next_layer b w hlayers k _
    (F.realification.bch_triple_sub_sum_mem_next_layer k a p d ha hd)
  simpa only [map_sub, map_add, sub_eq_zero] using h

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.DualIdealSteps
namespace OAI


namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualAdjoint_conjugation_mod (I J : LieIdeal ℚ L)
    (hIJ : ∀ a ∈ I, ∀ b ∈ I, ⁅a, b⁆ ∈ J)
    (g : NilpotentLieBCHGroup L s hnil) (x : L) (hx : x ∈ I) :
    lieQuotientMap J (dualAdjoint g x) =
      lieQuotientMap J (g * (⟨x⟩ : NilpotentLieBCHGroup L s hnil) * g⁻¹).coord := by
  have hc : dualConstantLie g.coord ∈ dualIdealSubalgebra I := by
    change dualTangentLinear (dualConstantLie g.coord) ∈ I
    rw [dualTangentLinear_constant]
    exact I.zero_mem
  have ht : dualInfinitesimal x ∈ dualIdealSubalgebra I := by
    change dualTangentLinear (dualInfinitesimal x) ∈ I
    rwa [dualTangentLinear_infinitesimal]
  calc
    _ = dualQuotientEvaluate J
        (dualConstantHom g * dualTangentElement x * (dualConstantHom g)⁻¹).coord := by
      rw [dualAdjoint_spec]
      exact (dualQuotientEvaluate_infinitesimal J _).symm
    _ = _ := by
      change dualQuotientEvaluate J
        (lieBCH s (lieBCH s (dualConstantLie g.coord) (dualInfinitesimal x))
          (-dualConstantLie g.coord)) =
        lieQuotientMap J (lieBCH s (lieBCH s g.coord x) (-g.coord))
      rw [dualQuotientEvaluate_lieBCH I J hIJ s
        (lieBCH_mem (dualIdealSubalgebra I) s hc ht) ((dualIdealSubalgebra I).neg_mem hc),
        dualQuotientEvaluate_lieBCH I J hIJ s hc ht,
        map_neg, dualQuotientEvaluate_constant, dualQuotientEvaluate_infinitesimal,
        map_lieBCH, map_lieBCH, map_neg]

theorem dualAdjoint_eq_conjugation_of_abelian_ideal (I : LieIdeal ℚ L)
    (hI : ∀ a ∈ I, ∀ b ∈ I, ⁅a, b⁆ = 0)
    (g : NilpotentLieBCHGroup L s hnil) (x : L) (hx : x ∈ I) :
    dualAdjoint g x = (g * (⟨x⟩ : NilpotentLieBCHGroup L s hnil) * g⁻¹).coord := by
  have he := dualAdjoint_conjugation_mod I ⊥
    (fun a ha b hb => (Submodule.mem_bot ℚ).mpr (hI a ha b hb)) g x hx
  have hz : lieQuotientMap (⊥ : LieIdeal ℚ L)
      (dualAdjoint g x - (g * (⟨x⟩ : NilpotentLieBCHGroup L s hnil) * g⁻¹).coord) = 0 := by
    rw [map_sub, he, sub_self]
  exact sub_eq_zero.mp ((Submodule.mem_bot ℚ).mp ((lieQuotientMap_eq_zero _ _).mp hz))

end Erdos3.NilpotentLieBCHGroup


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.DualDerivativeRemoval
namespace OAI

section

namespace Erdos3

namespace NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualLogDerivative_inv (z : DualGroup hnil) :
    dualLogDerivative z⁻¹ = -dualAdjoint (dualBaseHom z)⁻¹ (dualLogDerivative z) := by
  have h := dualLogDerivative_mul z z⁻¹
  rw [mul_inv_cancel, dualLogDerivative_one] at h
  have he := congrArg (dualAdjoint (dualBaseHom z)⁻¹) h
  rw [dualAdjoint_zero, dualAdjoint_add, dualAdjoint_inv_cancel] at he
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [add_comm] using he.symm

theorem dualLogDerivative_remove (a z c : DualGroup hnil) :
    dualLogDerivative (a⁻¹ * z * c⁻¹) =
      dualAdjoint (dualBaseHom a)⁻¹ (dualLogDerivative z - dualLogDerivative a) -
        dualAdjoint (dualBaseHom (a⁻¹ * z * c⁻¹)) (dualLogDerivative c) := by
  simp only [dualLogDerivative_mul, dualLogDerivative_inv, map_mul, map_inv,
    dualAdjoint_mul, dualAdjoint_neg, dualAdjoint_sub]
  abel

end NilpotentLieBCHGroup

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPolynomialChartSubstitution
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem formalLogDerivative_remove (i : σ) (A P B : PolynomialGroup σ hnil) :
    formalLogDerivative i (A⁻¹ * P * B⁻¹) =
      dualAdjoint A⁻¹ (formalLogDerivative i P - formalLogDerivative i A) -
        dualAdjoint (A⁻¹ * P * B⁻¹) (formalLogDerivative i B) := by
  have h := dualLogDerivative_remove
    (formalPolynomialJetHom i A) (formalPolynomialJetHom i P) (formalPolynomialJetHom i B)
  simpa only [map_mul, map_inv, formalPolynomialJet_baseHom, formalLogDerivative] using h

theorem formalLogDerivative_mem_of_invariant
    (U : LieSubalgebra ℚ (VectorPolynomial σ ℚ L))
    (V : Submodule ℚ (VectorPolynomial σ ℚ L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (i : σ) (P : PolynomialGroup σ hnil) (hP : P.coord ∈ U)
    (hD : (MvPolynomial.pderiv i).toLinearMap.rTensor L P.coord ∈ V) :
    formalLogDerivative i P ∈ V := by
  apply dualLogDerivative_mem_of_invariant U V hUV (formalPolynomialJetHom i P)
  · simpa only [formalPolynomialJet_base] using hP
  · simpa only [formalPolynomialJet_tangent] using hD

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem eval₂_formalLogDerivative (i : σ) (t : σ → ℝ) (P : PolynomialGroup σ hnil) :
    eval₂ t (formalLogDerivative i P) = dualLogDerivative (realPolynomialJet i t P) := by
  have h := dualLinearLift_logDerivative hnil ⊤ (eval₂Lie (R := ℚ) (S := ℝ) (L := L) t)
    (eval₂ t) (fun a b _ => (eval₂Lie (R := ℚ) (S := ℝ) (L := L) t).map_lie a b)
    (formalPolynomialJetHom i P) (by trivial)
  simp only [dualLinearLift_apply, formalPolynomialJet_base, formalPolynomialJet_tangent,
    eval₂Lie_apply] at h
  exact h

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedTranslationBasisHeight
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
variable {σ : Type*} [Fintype σ]

omit [Fintype σ] in
theorem topProjection_mem_top (w : σ → ℕ) (d : ℕ) (x : PolynomialTranslationLie σ) :
    topProjection w d x ∈ weightedLayer w d d := by
  refine ⟨fun i hi => ?_, ?_⟩
  · simp [Nat.ne_of_lt hi]
  · exact (monomial_mem_restrictSupport ℚ).mpr (Or.inl (by simp))

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ScaledPolynomialDualBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ)

theorem polynomialSlowBound_mono (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M N : ℝ} (hMN : M ≤ N) (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hg : F.PolynomialSlowBound b w T M g) : F.PolynomialSlowBound b w T N g := by
  intro α i
  exact (hg α i).trans (div_le_div_of_nonneg_right hMN (monomialScale_pos T hT α).le)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalPowerHeight
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_layer_basis (a : σ → ℕ) (ha : a ≤ bound) {p : ℝ}
    (hM : M.ComplexityLE p) :
    ∃ b : Basis (Fin (finrank ℚ (M.filtration.layer a))) ℚ (M.filtration.layer a),
      ∀ j k, rationalLogHeight (D.basis.repr (b j : L) k) ≤ p := by
  let a' : ∀ i, Fin (bound i + 1) := fun i => ⟨a i, Nat.lt_succ_of_le (ha i)⟩
  exact ⟨M.basis a', hM.2 a'⟩

theorem exists_ordinary_layer_basis (n : Fin (s + 1)) {p : ℝ}
    (hM : M.ComplexityLE p) :
    ∃ b : Basis (Fin (finrank ℚ (M.filtration.ordinary.layer (n.val + 1)))) ℚ
        (M.filtration.ordinary.layer (n.val + 1)),
      ∀ j k, rationalLogHeight (D.basis.repr (b j : L) k) ≤ p := by
  rw [M.ordinary]
  exact ⟨D.layerBasis n, hM.1.2.2.2 n⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem exists_positive_layer_basis (n : ℕ) (hn : 1 ≤ n) {p : ℝ}
    (hD : D.GeometryComplexityLE p) :
    ∃ b : Basis (Fin (finrank ℚ (D.filtration.layer n))) ℚ (D.filtration.layer n),
      ∀ j k, rationalLogHeight (D.basis.repr (b j : L) k) ≤ p := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  by_cases hms : m < s + 1
  · exact ⟨D.layerBasis ⟨m, hms⟩, hD.2.2.2 ⟨m, hms⟩⟩
  · have hzero : D.filtration.layer (m + 1) = ⊥ := by
      apply bot_unique
      exact (D.filtration.antitone (by omega : s + 1 ≤ m + 1)).trans_eq D.filtration.terminal
    let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
    let b := Module.finBasis ℚ (D.filtration.layer (m + 1))
    refine ⟨b, fun j k => ?_⟩
    have hb : (b j : L) = 0 := by
      have h := (b j).property
      simpa only [hzero, Submodule.mem_bot] using h
    rw [hb]
    simpa [rationalLogHeight] using (Nat.cast_nonneg d).trans hD.1

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

theorem RationalHeightLE.pow {q : ℚ} {H : ℕ} (hq : RationalHeightLE q H) (n : ℕ) :
    RationalHeightLE (q ^ n) (H ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using rationalHeightLE_one (by decide : 1 ≤ 1)
  | succ n ih => simpa only [pow_succ] using ih.mul hq

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CurrentLayerPreservation
namespace OAI

section

namespace Erdos3

open Module

theorem basisBelowProjection_succ {K L ι : Type*} [Field K] [AddCommGroup L] [Module K L]
    (b : Basis ι K L) (w : ι → ℕ) (j : ℕ) (x : L) :
    basisBelowProjection b w (j + 1) x =
      basisBelowProjection b w j x + basisGradeProjection b w j x := by
  rw [basisBelowProjection_eq_sum_grades, Finset.sum_range_succ,
    ← basisBelowProjection_eq_sum_grades]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalTaggedSpanProjection
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct Matrix BigOperators

variable {ι κ V : Type*} [Fintype ι] [Fintype κ] [AddCommGroup V] [Module ℚ V]
  (b : Basis ι ℚ V) (e : Basis κ ℚ V)

omit [Fintype κ] in
theorem real_basis_coordinates_bound {H : ℕ} {B : ℝ}
    (hentries : ∀ i j, RationalHeightLE (e.repr (b j) i) H)
    (x : ℝ ⊗[ℚ] V) (hx : ∀ j, |(b.baseChange ℝ).repr x j| ≤ B) (i : κ) :
    |(e.baseChange ℝ).repr x i| ≤ (Fintype.card ι : ℝ) * H * B := by
  have hcoord := congrFun (real_basis_coordinates_transfer b e x) i
  rw [hcoord]
  calc
    _ ≤ ∑ j, |(e.repr (b j) i : ℝ) * (b.baseChange ℝ).repr x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : ι, (H : ℝ) * B := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hentries i j).abs_real_le (hx j) (abs_nonneg _) (Nat.cast_nonneg H)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

omit [Fintype κ] in
theorem real_basis_coordinates_exp_bound {H : ℕ} {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hentries : ∀ i j, RationalHeightLE (e.repr (b j) i) H)
    (x : ℝ ⊗[ℚ] V) (hx : ∀ j, |(b.baseChange ℝ).repr x j| ≤ Real.exp p) (i : κ) :
    |(e.baseChange ℝ).repr x i| ≤ Real.exp ((p + 2) ^ 2) := by
  have hdim : (Fintype.card ι : ℝ) ≤ Real.exp p := hι.trans (by linarith [Real.add_one_le_exp p])
  calc
    _ ≤ (Fintype.card ι : ℝ) * H * Real.exp p := real_basis_coordinates_bound b e hentries x hx i
    _ ≤ Real.exp p * Real.exp p * Real.exp p :=
      mul_le_mul_of_nonneg_right (mul_le_mul hdim hHp (Nat.cast_nonneg H) (Real.exp_nonneg p))
        (Real.exp_nonneg p)
    _ = Real.exp (3 * p) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])

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

theorem subspaceQuotientMatrix_height [Fintype μ] (b : Basis μ ℚ L)
    (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) {H J : ℕ}
    (hq : ∀ i n, RationalHeightLE (f.repr (V.mkQ (b i)) n) H)
    (he : ∀ n i, RationalHeightLE (b.repr (e n : L) i) J) (i : ι) (n : ν) :
    RationalHeightLE (subspaceQuotientMatrix e f i n)
      ((Fintype.card μ + 1) * (J * H) ^ Fintype.card μ) :=
  linearMap_coordinate_height b f V.mkQ hq (e n : L) (he n) i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ControlledSubspaceCorrectionPolynomials
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped Matrix TensorProduct

variable {L μ ι ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype ι] [Fintype ν] {E V : Submodule ℚ L}

theorem exists_controlled_subspace_correction_polynomials
    (b : Basis μ ℚ L) (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V))
    {H J l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i n, RationalHeightLE (subspaceQuotientMatrix e f i n) H)
    (he : ∀ i j, RationalHeightLE (b.repr (e j : L) i) J)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card ν : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (P small rational : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hPE : ∀ α, coefficients P α ∈ E.baseChange ℝ)
    (hsmall0 : coefficients small 0 = 0) (hrational0 : coefficients rational 0 = 0)
    (hsmall : ∀ α, ‖realQuotientCoordinateMap f (coefficients small α)‖ ≤
      Real.exp p / monomialScale T α)
    (hrational : ∀ α, realQuotientCoordinateMap f (coefficients rational α) ∈
      realDenominatorGrid l)
    (hsplit : ∀ α, coefficients (P - small - rational) α ∈ V.baseChange ℝ) :
    ∃ (m : ℕ) (A B : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      map ((realQuotientCoordinateMap f).restrictScalars ℚ) A =
        map ((realQuotientCoordinateMap f).restrictScalars ℚ) small ∧
      map ((realQuotientCoordinateMap f).restrictScalars ℚ) B =
        map ((realQuotientCoordinateMap f).restrictScalars ℚ) rational ∧
      (∀ α, coefficients A α ∈ E.baseChange ℝ ∧ coefficients B α ∈ E.baseChange ℝ) ∧
      (∀ α, coefficients small α = 0 → coefficients A α = 0) ∧
      (∀ α, coefficients rational α = 0 → coefficients B α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A α)‖ ≤
        (((Fintype.card ν : ℝ) + 1) * (J + 1)) *
          Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B α) ∈
        realDenominatorGrid (matrixDenominator (bracketLiftMatrix b e) * m)) ∧
      ∀ α, coefficients (P - A - B) α ∈ (E ⊓ V).baseChange ℝ := by
  have h := exists_controlled_linear_splitting (subspaceQuotientMatrix e f)
    hH hl hA hp hrows hcols hHp hlp T hT
  obtain ⟨Q, m, hm, hmp, hQ⟩ := h
  let q := realQuotientCoordinateMap f
  let C : (ι → ℝ) →ₗ[ℝ] (ν → ℝ) := Matrix.mulVecLin (fun i j => (Q i j : ℝ))
  let D := (bracketSystemLift e).comp (C.comp q)
  let A := map (D.restrictScalars ℚ) small
  let B := map (D.restrictScalars ℚ) rational
  have hAc (α : σ →₀ ℕ) : coefficients A α =
      bracketSystemLift e (C (q (coefficients small α))) := coefficients_map _ _ _
  have hBc (α : σ →₀ ℕ) : coefficients B α =
      bracketSystemLift e (C (q (coefficients rational α))) := coefficients_map _ _ _
  have hcoeff (α : σ →₀ ℕ) :
      q (bracketSystemLift e (C (q (coefficients small α)))) = q (coefficients small α) ∧
      q (bracketSystemLift e (C (q (coefficients rational α)))) = q (coefficients rational α) ∧
      ‖C (q (coefficients small α))‖ ≤
        Real.exp ((p + 2) ^ 18 + p) / monomialScale T α ∧
      C (q (coefficients rational α)) ∈ realDenominatorGrid m := by
    by_cases hα : α = 0
    · simp only [hα, hsmall0, hrational0, map_zero, norm_zero, monomialScale_zero, div_one]
      exact ⟨True.intro, True.intro, Real.exp_nonneg _, ⟨0, by ext i; simp⟩⟩
    · obtain ⟨v, hv⟩ := exists_subspace_basis_coordinates e _ (hPE α)
      have hz : q (coefficients P α) - q (coefficients small α) -
          q (coefficients rational α) = 0 := by
        have hz := (realQuotientCoordinateMap_eq_zero_iff f _).mpr (hsplit α)
        simpa only [map_sub, Finsupp.sub_apply] using hz
      have heq : (fun i n => (subspaceQuotientMatrix e f i n : ℝ)) *ᵥ v =
          q (coefficients small α) + q (coefficients rational α) := by
        rw [subspaceQuotientMatrix_real_apply, hv]
        exact sub_eq_zero.mp (by simpa only [sub_sub] using hz)
      have hd := hQ α hα (q (coefficients small α)) (q (coefficients rational α)) v
        (hsmall α) (hrational α) heq
      rcases hd with ⟨hleft, hright, hnorm, hgrid, _⟩
      rw [subspaceQuotientMatrix_real_apply] at hleft hright
      exact ⟨hleft, hright, hnorm, hgrid⟩
  refine ⟨m, A, B, hm, hmp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply coefficients.injective
    apply Finsupp.ext
    intro α
    simp only [coefficients_map, LinearMap.restrictScalars_apply, hAc]
    exact (hcoeff α).1
  · apply coefficients.injective
    apply Finsupp.ext
    intro α
    simp only [coefficients_map, LinearMap.restrictScalars_apply, hBc]
    exact (hcoeff α).2.1
  · intro α
    rw [hAc, hBc]
    exact ⟨bracketSystemLift_mem e _, bracketSystemLift_mem e _⟩
  · intro α hα
    rw [hAc, hα, map_zero, map_zero, map_zero]
  · intro α hα
    rw [hBc, hα, map_zero, map_zero, map_zero]
  · intro α
    rw [hAc]
    apply (bracketSystemLift_norm_bound b e he _).trans
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left (hcoeff α).2.2.1
      (by positivity : 0 ≤ ((Fintype.card ν : ℝ) + 1) * (J + 1))
  · intro α
    rw [hBc]
    exact bracketSystemLift_grid b e m _ (hcoeff α).2.2.2
  · intro α
    rw [realification_inf]
    refine ⟨?_, ?_⟩
    · simp only [map_sub, Finsupp.sub_apply, hAc, hBc]
      exact (E.baseChange ℝ).sub_mem
        ((E.baseChange ℝ).sub_mem (hPE α) (bracketSystemLift_mem e _))
        (bracketSystemLift_mem e _)
    · apply (realQuotientCoordinateMap_eq_zero_iff f _).mp
      simp only [map_sub, Finsupp.sub_apply, hAc, hBc]
      change q (coefficients P α) - q (bracketSystemLift e (C (q (coefficients small α)))) -
        q (bracketSystemLift e (C (q (coefficients rational α)))) = 0
      rw [(hcoeff α).1, (hcoeff α).2.1]
      have hz := (realQuotientCoordinateMap_eq_zero_iff f _).mpr (hsplit α)
      simpa only [map_sub, Finsupp.sub_apply] using hz

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.HomogeneousSubspaceCorrections
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {σ V : Type*} [Fintype σ] [AddCommGroup V] [Module ℚ V]

theorem reconstructDerivatives_coordinate_bound {d : ℕ} (hd : 0 < d)
    (f : V →ₗ[ℚ] ℝ) (P : σ → VectorPolynomial σ ℚ V)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (hP : ∀ i α, |f (coefficients (P i) α)| ≤ M / (T i * monomialScale T α))
    (β : σ →₀ ℕ) :
    |f (coefficients (reconstructDerivatives d P) β)| ≤
      ((Fintype.card σ : ℝ) / d * M) / monomialScale T β := by
  classical
  have hscale (i : σ) (hi : i ∈ β.support) :
      T i * monomialScale T (β - Finsupp.single i 1) = monomialScale T β := by
    calc
      _ = monomialScale T ((β - Finsupp.single i 1) + Finsupp.single i 1) := by
        rw [monomialScale_add]
        simp [monomialScale, mul_comm]
      _ = _ := by rw [Finsupp.sub_add_single_one_cancel (Finsupp.mem_support_iff.mp hi)]
  have hc : f (coefficients (reconstructDerivatives d P) β) =
      (d : ℝ)⁻¹ * ∑ i, if i ∈ β.support then f (coefficients (P i) (β - Finsupp.single i 1)) else 0 := by
    rw [coefficients_reconstructDerivatives, map_smul, map_sum]
    simp only [apply_ite, map_zero, Rat.smul_def, Rat.cast_inv, Rat.cast_natCast]
  have hsum : |∑ i, if i ∈ β.support then f (coefficients (P i) (β - Finsupp.single i 1)) else 0| ≤
      (Fintype.card σ : ℝ) * (M / monomialScale T β) := by
    calc
      _ ≤ ∑ i, |if i ∈ β.support then f (coefficients (P i) (β - Finsupp.single i 1)) else 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : σ, M / monomialScale T β := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs with hi
        · exact (hP i (β - Finsupp.single i 1)).trans_eq
            (congrArg (fun q : ℝ => M / q) (hscale i hi))
        · rw [abs_zero]
          exact div_nonneg hM (monomialScale_pos T hT β).le
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hc, abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_pos.mpr hd).le)]
  calc
    _ ≤ (d : ℝ)⁻¹ * ((Fintype.card σ : ℝ) * (M / monomialScale T β)) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_pos.mpr hd).le)
    _ = _ := by ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.LogCharacterBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

namespace NilpotentLieBCHGroup

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem logCharacter_dist_one_le (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (η : L →ₗ[ℝ] ℝ) (A : ℝ≥0) (hη : ∀ x, |η x| ≤ A * ‖e.equivFun x‖)
    (g : NilpotentLieBCHGroup L s hnil) :
    letI := rightMetricSpace (hnil := hnil) e
    ‖logCharacter η g - 1‖ ≤ logCharacterMetricConstant s (Fintype.card ι) H A * dist 1 g := by
  let := rightMetricSpace (hnil := hnil) e
  let C := bchLogMetricConstant s (Fintype.card ι) H 1
  change ‖logCharacter η g - 1‖ ≤
    (2 + (CircleFourier.characterLipConstant : ℝ) * A) * C * dist 1 g
  by_cases hnear : (C : ℝ) * dist 1 g < 1
  · have hcoord := norm_coordinates_le_of_near_one e c hstructure hc 1 le_rfl g hnear
    have hchar := norm_character_real_sub_one_le (η g.coord)
    have hlinear := hη g.coord
    have hscale := mul_le_mul_of_nonneg_left hcoord A.coe_nonneg
    change ‖e.equivFun g.coord‖ ≤ (C : ℝ) * dist 1 g at hcoord
    have hbound : |η g.coord| ≤ A * ((C : ℝ) * dist 1 g) := hlinear.trans hscale
    apply hchar.trans
    have h := mul_le_mul_of_nonneg_left hbound CircleFourier.characterLipConstant.coe_nonneg
    nlinarith [C.coe_nonneg, dist_nonneg (x := (1 : NilpotentLieBCHGroup L s hnil)) (y := g)]
  · have hfar : 1 ≤ (C : ℝ) * dist 1 g := le_of_not_gt hnear
    apply (CircleFourier.norm_character_sub_one_le_two _).trans
    nlinarith [CircleFourier.characterLipConstant.coe_nonneg, A.coe_nonneg,
      C.coe_nonneg, dist_nonneg (x := (1 : NilpotentLieBCHGroup L s hnil)) (y := g),
      mul_nonneg CircleFourier.characterLipConstant.coe_nonneg A.coe_nonneg]

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem bchLogMetricConstant_le_inverse (s d H : ℕ) :
    bchLogMetricConstant s d H 1 ≤ bchInverseBoxConstant s d H 1 := by
  change bchBoxCoordinateBound s d H 1 + 1 ≤
    (bchBoxCoordinateBound s d H 1 + 2 * 1) * (bchBoxCoordinateBound s d H 1 + 1)
  have h := bchBoxCoordinateBound_nonneg s d H (by norm_num : (0 : ℝ) ≤ 1)
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CentralOrbitMetric
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal ENNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem central_logCharacter_coset_dist_le (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ T : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)))
    (hT : ∀ z ∈ T, ∀ v : L, ⁅z.coord, v⁆ = 0)
    (η : L →ₗ[ℝ] ℝ) (A : ℝ≥0) (hη : ∀ x, |η x| ≤ A * ‖e.equivFun x‖)
    (hint : ∀ γ ∈ Γ, ∃ n : ℤ, η γ.coord = n) (x y : T) :
    letI := quotientMetricSpace e Γ hΓ
    dist (logCharacter η x.val) (logCharacter η y.val) ≤
      logCharacterMetricConstant s (Fintype.card ι) H A *
        dist (QuotientGroup.mk x.val : _ ⧸ Γ) (QuotientGroup.mk y.val) := by
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace_isIsometricSMul (hnil := hnil) e
  let := quotientMetricSpace e Γ hΓ
  let K := logCharacterMetricConstant s (Fintype.card ι) H A
  have hdist (γ : Γ) : dist (logCharacter η x.val) (logCharacter η y.val) ≤
      K * dist x.val (y.val * γ.val) := by
    rw [dist_eq_norm, logCharacter_norm_sub_eq_relative η x.val y.val γ.val
      (hT x.val x.property) (hT y.val y.property) (logCharacter_of_integral η γ.val (hint γ.val γ.property))]
    have h := logCharacter_dist_one_le e c hstructure hc η A hη (y.val * γ.val * x.val⁻¹)
    have heq : dist (1 : NilpotentLieBCHGroup L s hnil) (y.val * γ.val * x.val⁻¹) =
        dist x.val (y.val * γ.val) := by
      simpa only [mul_inv_cancel] using dist_mul_right x.val (y.val * γ.val) x.val⁻¹
    exact h.trans_eq (congrArg (fun r : ℝ => (K : ℝ) * r) heq)
  have he : edist (logCharacter η x.val) (logCharacter η y.val) ≤
      (K : ℝ≥0∞) * edist (QuotientGroup.mk x.val : _ ⧸ Γ) (QuotientGroup.mk y.val) := by
    rw [quotientMetricSpace_edist_mk, ENNReal.mul_iInf (by simp)]
    apply le_iInf
    intro γ
    simpa only [edist_dist, ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal] using
      ENNReal.ofReal_le_ofReal (hdist γ)
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top _ _)) he
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, edist_dist,
    ENNReal.toReal_ofReal dist_nonneg] using h

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.JoinedFrequencyQuotientInjectivity
namespace OAI

section

namespace Erdos3

open Module

theorem RationalHeightLE.inv {q : ℚ} {H : ℕ} (hq : RationalHeightLE q H) (hne : q ≠ 0) :
    RationalHeightLE q⁻¹ H := by
  have hn : q.num ≠ 0 := by
    intro hn
    apply hne
    rw [← q.num_div_den, hn, Int.cast_zero, zero_div]
  have h := rationalHeightLE_fraction (q.den : ℤ) q.num hn
    (by simpa only [Int.natAbs_natCast] using hq.2) hq.1
  have he : q⁻¹ = (q.den : ℚ) / q.num := by
    calc
      q⁻¹ = ((q.num : ℚ) / q.den)⁻¹ := congrArg Inv.inv q.num_div_den.symm
      _ = _ := inv_div _ _
  simpa only [he, Int.cast_natCast] using h

theorem exists_bounded_frequency_direction {ι V : Type*} [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (η : V →ₗ[ℚ] ℚ) (hη : η ≠ 0)
    {H : ℕ} (hH : 1 ≤ H) (hheight : ∀ i, RationalHeightLE (η (b i)) H) :
    ∃ (v : V) (m : ℕ), 0 < m ∧ m ≤ H ∧ η v = 1 ∧
      (∀ i, RationalHeightLE (b.repr v i) H) ∧
      (fun i => b.repr v i) ∈ denominatorGrid m := by
  classical
  have hex : ∃ i, η (b i) ≠ 0 := by
    by_contra h
    push Not at h
    apply hη
    apply b.ext
    intro i
    exact h i
  obtain ⟨i, hi⟩ := hex
  let c := (η (b i))⁻¹
  let v := c • b i
  have hc : RationalHeightLE c H := (hheight i).inv hi
  have hcoord (j : ι) : b.repr v j = if i = j then c else 0 := by
    simp only [v, map_smul, Finsupp.smul_apply, Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
    split_ifs <;> simp
  refine ⟨v, c.den, c.den_pos, hc.2, ?_, ?_, ?_⟩
  · change η (c • b i) = 1
    rw [map_smul, smul_eq_mul]
    exact inv_mul_cancel₀ hi
  · intro j
    rw [hcoord]
    split_ifs
    · exact hc
    · exact rationalHeightLE_zero hH
  · refine ⟨fun j => if i = j then c.num else 0, ?_⟩
    intro j
    change (c.den : ℚ) * b.repr v j = ((if i = j then c.num else 0 : ℤ) : ℚ)
    rw [hcoord]
    by_cases hj : i = j
    · simp only [hj, ite_true]
      have hcden := (div_eq_iff (show (c.den : ℚ) ≠ 0 from Nat.cast_ne_zero.mpr c.den_ne_zero)).mp c.num_div_den
      simpa only [mul_comm] using hcden.symm
    · simp only [hj, ite_false, mul_zero, Int.cast_zero]

end Erdos3

end

section

namespace Erdos3

open Module

variable {ι V : Type*} [AddCommGroup V] [Module ℚ V]

theorem frequencyKernel_spanning_height (b : Basis ι ℚ V) (η : V →ₗ[ℚ] ℚ) (v : V)
    {H : ℕ} (hη : ∀ i, RationalHeightLE (η (b i)) H)
    (hv : ∀ i, RationalHeightLE (b.repr v i) H) :
    ∀ i j, RationalHeightLE (b.repr (b i - η (b i) • v) j) (2 * H ^ 2) := by
  classical
  intro i j
  rw [map_sub, Finsupp.sub_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have hbase : RationalHeightLE (b.repr (b i) j) 1 := by
    rw [Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact rationalHeightLE_one le_rfl
    · exact rationalHeightLE_zero le_rfl
  have h := hbase.sub ((hη i).mul (hv j))
  convert h using 1
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LinearCoefficientSplitting
namespace OAI

section

namespace Erdos3

open Module CircleFourier
open scoped TensorProduct

theorem exists_biased_linear_coefficient_splitting
    {σ ι V : Type*} [Fintype σ] [DecidableEq σ] [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (η : V →ₗ[ℚ] ℚ) (hη : η ≠ 0)
    {H : ℕ} (hH : 1 ≤ H) (hheight : ∀ i, RationalHeightLE (η (b i)) H)
    (T : σ → ℕ) (hT : ∀ i, 0 < T i) (a : σ → ℝ ⊗[ℚ] V)
    {δ : ℝ} (hδ : 0 < δ)
    (hbias : δ ≤ ‖linearPhaseMean T (fun i => (realifyFunctional η (a i) : CircleFourier.Circle))‖) :
    ∃ (m : ℕ) (e p r : σ → ℝ ⊗[ℚ] V),
      0 < m ∧ m ≤ H ∧
      (∀ i, e i + p i + r i = a i) ∧
      (∀ i, realifyFunctional η (p i) = 0) ∧
      (∀ i j, |(b.baseChange ℝ).repr (e i) j| ≤ (H : ℝ) / (2 * T i * δ)) ∧
      (fun z : σ × ι => (b.baseChange ℝ).repr (r z.1) z.2) ∈ realDenominatorGrid m := by
  classical
  obtain ⟨v, m, hm, hmH, hv, hvheight, z, hz⟩ := exists_bounded_frequency_direction b η hη hH hheight
  let vR : ℝ ⊗[ℚ] V := (1 : ℝ) ⊗ₜ[ℚ] v
  let c : σ → ℝ := fun i => realifyFunctional η (a i)
  let n : σ → ℤ := fun i => round (c i)
  let e := fun i => (c i - (n i : ℝ)) • vR
  let p := fun i => a i - c i • vR
  let r := fun i => (n i : ℝ) • vR
  have hvR : realifyFunctional η vR = 1 := by simp only [vR, realifyFunctional_tmul, hv, Rat.cast_one, one_mul]
  have hcoord (j : ι) : (b.baseChange ℝ).repr vR j = (b.repr v j : ℝ) := by
    simp only [vR, Basis.baseChange_repr_tmul, Rat.smul_def, mul_one]
  have hnear : ∀ i, |c i - (n i : ℝ)| ≤ 1 / (2 * T i * δ) :=
    linear_phase_near_integers T hT c hδ hbias
  refine ⟨m, e, p, r, hm, hmH, ?_, ?_, ?_, ?_⟩
  · intro i
    dsimp [e, p, r]
    rw [sub_smul]
    abel
  · intro i
    simp only [p, map_sub, map_smul, hvR, smul_eq_mul, mul_one, c, sub_self]
  · intro i j
    change |(b.baseChange ℝ).repr ((c i - (n i : ℝ)) • vR) j| ≤ _
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, abs_mul, hcoord]
    calc
      _ ≤ |c i - (n i : ℝ)| * H :=
        mul_le_mul_of_nonneg_left (hvheight j).abs_real_le (abs_nonneg _)
      _ ≤ (1 / (2 * T i * δ)) * H := mul_le_mul_of_nonneg_right (hnear i) (Nat.cast_nonneg H)
      _ = _ := by ring
  · refine ⟨fun ij => n ij.1 * z ij.2, ?_⟩
    funext ij
    change ((n ij.1 * z ij.2 : ℤ) : ℝ) = (m : ℝ) * (b.baseChange ℝ).repr ((n ij.1 : ℝ) • vR) ij.2
    rw [Int.cast_mul, map_smul, Finsupp.smul_apply, smul_eq_mul, hcoord]
    have hz' : (m : ℝ) * (b.repr v ij.2 : ℝ) = (z ij.2 : ℝ) := by exact_mod_cast hz ij.2
    calc
      (n ij.1 : ℝ) * (z ij.2 : ℝ) = (n ij.1 : ℝ) * ((m : ℝ) * (b.repr v ij.2 : ℝ)) := by rw [hz']
      _ = _ := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformFormalCurrentLayerStep
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

theorem controlled_zero_sum_separation {ι : Type*} [Fintype ι]
    {l : ℕ} (hl : 0 < l) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hlp : (l : ℝ) ≤ Real.exp p)
    (a b : ι → ℝ) (ha : ‖a‖ ≤ Real.exp p / Real.exp (separationBudget p))
    (hb : b ∈ realDenominatorGrid l) (hsum : a + b = 0) : a = 0 ∧ b = 0 := by
  have h := controlled_small_vector_separation (0 : Matrix ι Empty ℚ)
    (H := 1) (by omega) hl (by intro i j; exact j.elim) hp hι
    (by simpa using hp) (by simpa using Real.one_le_exp hp) hlp a b ha hb
    (by rw [hsum]; exact Submodule.zero_mem _)
  simpa only [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SubspacePolynomialCoordinates
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

variable {L ν σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ν] {E : Submodule ℚ L}

theorem exists_subspace_coordinate_polynomial (e : Basis ν ℚ E)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hP : ∀ α, coefficients P α ∈ E.baseChange ℝ) :
    ∃ Q : VectorPolynomial σ ℚ (ν → ℝ),
      map ((bracketSystemLift e).restrictScalars ℚ) Q = P ∧
        ∀ α, coefficients P α = 0 → coefficients Q α = 0 := by
  classical
  choose v hv using fun α : σ →₀ ℕ => exists_subspace_basis_coordinates e (coefficients P α) (hP α)
  have hzero (α : σ →₀ ℕ) (hα : coefficients P α = 0) : v α = 0 := by
    apply bracketSystemLift_injective e
    rw [hv, hα, map_zero]
  let C : (σ →₀ ℕ) →₀ (ν → ℝ) := {
    support := (coefficients P).support
    toFun := v
    mem_support_toFun := by
      intro α
      rw [Finsupp.mem_support_iff]
      constructor
      · intro h hα
        apply h
        rw [← hv α, hα, map_zero]
      · intro h hα
        exact h (hzero α hα) }
  let Q : VectorPolynomial σ ℚ (ν → ℝ) := coefficients.symm C
  have hcoeff (α : σ →₀ ℕ) : coefficients Q α = v α := by
    change coefficients (coefficients.symm C) α = v α
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hmap : map ((bracketSystemLift e).restrictScalars ℚ) Q = P := by
    apply coefficients.injective
    apply Finsupp.ext
    intro α
    rw [coefficients_map]
    change bracketSystemLift e (coefficients Q α) = _
    rw [hcoeff]
    exact hv α
  refine ⟨Q, hmap, ?_⟩
  intro α hα
  rw [hcoeff]
  exact hzero α hα

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
open scoped Matrix TensorProduct NNReal

variable {L μ κ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype κ] {E : Submodule ℚ L}

theorem exists_bracketLiftMatrix_leftInverse [DecidableEq κ] (b : Basis μ ℚ L) (e : Basis κ ℚ E)
    {H : ℕ} (hH : 1 ≤ H) (he : ∀ i j, RationalHeightLE (b.repr (e j : L) i) H) :
    ∃ Q : Matrix κ μ ℚ, Q * bracketLiftMatrix b e = 1 ∧
      ∀ i j, RationalHeightLE (Q i j) (rationalSolveHeight (Fintype.card κ) H) := by
  classical
  let f : E →ₗ[ℚ] (μ → ℚ) := b.equivFun.toLinearMap.comp E.subtype
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (b.equivFun.injective h)
  have hli : LinearIndependent ℚ (bracketLiftMatrix b e).col :=
    e.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)
  exact exists_bounded_rational_left_inverse (bracketLiftMatrix b e) hli hH he

theorem realSubspaceCoordinateMap_norm (b : Basis μ ℚ L) (Q : Matrix κ μ ℚ)
    {H : ℕ} (hQ : ∀ i j, RationalHeightLE (Q i j) H) (x : ℝ ⊗[ℚ] L) :
    ‖realSubspaceCoordinateMap b Q x‖ ≤
      ((Fintype.card μ : ℝ) + 1) * (H + 1) * ‖(b.baseChange ℝ).equivFun x‖ := by
  rw [realSubspaceCoordinateMap_apply]
  exact norm_matrix_mulVec_le _ (H : ℝ≥0) (fun i j => (hQ i j).abs_real_le) _

theorem realSubspaceCoordinateMap_grid (b : Basis μ ℚ L) (Q : Matrix κ μ ℚ)
    (l : ℕ) (x : ℝ ⊗[ℚ] L) (hx : (b.baseChange ℝ).equivFun x ∈ realDenominatorGrid l) :
    realSubspaceCoordinateMap b Q x ∈ realDenominatorGrid (matrixDenominator Q * l) := by
  rw [realSubspaceCoordinateMap_apply]
  exact real_matrix_denominator_grid Q l _ hx

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialSymbolBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem realPolynomialSymbolHom_eq_of_quotient_eq
    (g h : (F.realification.adaptedPolynomialFiltration w).Group)
    (hgh : F.realification.polynomialSymbolHom w g = F.realification.polynomialSymbolHom w h) :
    F.realPolynomialSymbolHom b ω hlayers w g = F.realPolynomialSymbolHom b ω hlayers w h := by
  apply NilpotentLieBCHGroup.ext
  exact (F.realSymbolOfPolynomial_eq_iff_symbolMap_eq b ω hlayers w g.coord h.coord).mpr
    (congrArg NilpotentLieBCHGroup.coord hgh)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankQuotientHeightBudget
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {L μ υ χ κ ν : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype υ] [Fintype χ] [Fintype κ] [Fintype ν]

omit [Fintype κ] [Fintype ν] in
theorem stepDrop_bracket_height (b : Basis μ ℚ L) (V K : Submodule ℚ L)
    (fV : Basis ν ℚ (L ⧸ V)) (eK : Basis κ ℚ K) {H : ℕ}
    (hV : ∀ i j, RationalHeightLE (fV.repr (V.mkQ (b j)) i) H)
    (heK : ∀ i j, RationalHeightLE (b.repr (eK j : L) i) H)
    (hstructure : ∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) (i : ν) (j : μ) (z : κ) :
    RationalHeightLE (fV.repr (V.mkQ ⁅b j, (eK z : L)⁆) i) (stepDropBracketHeight (Fintype.card μ) H) := by
  have hbr := lie_bracket_coordinate_height b hstructure (b j) (eK z : L)
    (basis_repr_height_one b j) (fun k => heK k z)
  have h := linearMap_coordinate_height b fV V.mkQ (fun a c => hV c a) _ hbr i
  simpa only [stepDropBracketHeight, mul_one] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RationalLatticeFunctional
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem realLattice_functional_integral (η : L →ₗ[ℚ] ℚ)
    (hη : ∀ g : D.filtration.Group, g ∈ D.lattice → ∃ n : ℤ, η g.coord = n)
    (z : D.RealGroup) (hz : z ∈ D.realLattice) :
    ∃ n : ℤ, realifyFunctional η z.coord = n := by
  obtain ⟨g, hg, rfl⟩ := hz
  obtain ⟨n, hn⟩ := hη g hg
  refine ⟨n, ?_⟩
  change realifyFunctional η ((1 : ℝ) ⊗ₜ[ℚ] g.coord) = _
  rw [realifyFunctional_tmul, one_mul, hn, Rat.cast_intCast]

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BoundedFrequencyKernel
namespace OAI

section

namespace Erdos3

open Module CircleFourier
open scoped TensorProduct

theorem exists_bounded_frequency_kernel_spanning {ι V : Type*} [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (η : V →ₗ[ℚ] ℚ)
    {H : ℕ} (hH : 1 ≤ H) (hheight : ∀ i, RationalHeightLE (η (b i)) H) :
    ∃ v : ι → V, Submodule.span ℚ (Set.range v) = LinearMap.ker η ∧
      ∀ i j, RationalHeightLE (b.repr (v i) j) (2 * H ^ 2) := by
  classical
  by_cases hη : η = 0
  · subst η
    refine ⟨b, ?_, ?_⟩
    · rw [LinearMap.ker_zero]
      exact b.span_eq
    · intro i j
      have hh : 1 ≤ 2 * H ^ 2 := (one_le_pow₀ hH).trans (Nat.le_mul_of_pos_left _ (by decide : 0 < 2))
      rw [Basis.repr_self, Finsupp.single_apply]
      split_ifs
      · exact rationalHeightLE_one hh
      · exact rationalHeightLE_zero hh
  · obtain ⟨u, _, _, _, hu, huheight, _⟩ := exists_bounded_frequency_direction b η hη hH hheight
    exact ⟨fun i => b i - η (b i) • u, frequencyKernel_spanning b η u hu,
      frequencyKernel_spanning_height b η u hheight huheight⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ControlledReplicatedFrequency
namespace OAI

section

namespace Erdos3

noncomputable def squarefreeFrequencyModelBudget (t : ℕ) (p : ℝ) : ℝ :=
  squarefreeFrequencyInputBudget t p +
    (squarefreeFrequencyInputBudget t p + (bchIntegralDenominatorBound t + 5 : ℕ)) ^
      (bchIntegralDenominatorBound t + 5)

theorem squarefreeFrequencyInputBudget_le_model (t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    squarefreeFrequencyInputBudget t p ≤ squarefreeFrequencyModelBudget t p := by
  exact le_add_of_nonneg_right
    (pow_nonneg (add_nonneg (squarefreeFrequencyInputBudget_nonneg t hp) (Nat.cast_nonneg _)) _)

theorem squarefree_frequency_grid_budget (t N d l B : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hN : N ≤ 2 ^ t * d)
    (hl : (l : ℝ) ≤ Real.exp (replicatedFrequencyDenominatorBudget t p))
    (hB : B ≤ bchIntegralDenominatorBound t *
      squarefreeStructureHeight d ⌈Real.exp p⌉₊ ^ (N ^ 3) * l) :
    (B : ℝ) ≤ Real.exp (squarefreeFrequencyModelBudget t p) := by
  have hq := squarefreeFrequencyInputBudget_nonneg t hp
  have hbase := squarefreeInputBudget_le_frequency t hp
  have hNq : (N : ℝ) ≤ squarefreeFrequencyInputBudget t p := by
    apply le_trans _ hbase
    calc
      _ ≤ (2 : ℝ) ^ t * d := by exact_mod_cast hN
      _ ≤ (2 : ℝ) ^ t * p := mul_le_mul_of_nonneg_left hd (by positivity)
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  have hHq : (squarefreeStructureHeight d ⌈Real.exp p⌉₊ : ℝ) ≤
      Real.exp (squarefreeFrequencyInputBudget t p) :=
    (squarefreeStructureHeight_ceil_exp d hp hd).trans
      (Real.exp_le_exp.mpr ((le_add_of_nonneg_left (mul_nonneg (by positivity) hp)).trans hbase))
  have hlq : (l : ℝ) ≤ Real.exp (squarefreeFrequencyInputBudget t p) :=
    hl.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_left (squarefreeInputBudget_nonneg t hp)))
  exact (Nat.cast_le.mpr hB).trans ((integral_grid_allowance_le_exp
    (bchIntegralDenominatorBound t) N _ l hq hNq hHq hlq).trans
      (Real.exp_le_exp.mpr (le_add_of_nonneg_left hq)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ControlledPositivePolynomialDownsets
namespace OAI

section

namespace Erdos3

noncomputable def positivePolynomialModelBudget (t : ℕ) (p : ℝ) : ℝ :=
  positivePolynomialDenominatorBudget t p +
    (positivePolynomialDenominatorBudget t p + (bchIntegralDenominatorBound t + 5 : ℕ)) ^
      (bchIntegralDenominatorBound t + 5)

end Erdos3

end

end OAI
end


