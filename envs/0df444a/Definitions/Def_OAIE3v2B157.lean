-- Prove2me | Definitions.Def_OAIE3v2B157
-- name    : OAIE3v2B157
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:24:07.540613+00:00
-- url     : https://prove2.me/theorems/9ae643f8-dbdb-417f-afb9-218176499ec2
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 159 of 311
-- statement:
--   Definitions bundle 159 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B140`, `OAIE3v2B141`, `OAIE3v2B142`, `OAIE3v2B143`, `OAIE3v2B144`, `OAIE3v2B145`, `OAIE3v2B146`, `OAIE3v2B147` of this split.
--
--   Modules: `Dynamics/ComparisonEquivalenceBudget.lean`, `Dynamics/UniformInvariantBudget.lean`, `Estimates/BoundedRealifiedSquareOrbit.lean`, `Estimates/ComparisonAmbient.lean`, `Estimates/ControlledComparisonModel.lean`, `Estimates/LowTaggedGradedSpace.lean`, `Estimates/NativeDilationObservable.lean`, `Estimates/NativeMeanRowCorrelation.lean`, `Estimates/NativeSubspaceFreeModel.lean`, `Estimates/PetalComparisonTree.lean`, `Estimates/PreparedFiniteForwardFixedCenterThreshold.lean`, `Estimates/RealProductInclusion.lean`, `Estimates/SquarefreeQuotientAction.lean`, `Estimates/SquarefreeRealAction.lean`, `Estimates/SymmetricSquarefreeMonotonicity.lean`, `Estimates/UnitVerticalMeanRowCorrelation.lean`, `Fourier/BohrNiltestBudget.lean`, `Fourier/BoundedFrequencyKernel.lean`, `Fourier/WeightedTranslationTwistedCentralFrequency.lean`, `Geometry/NativeProductOrbitMetric.lean`, `Geometry/SquarefreeActionMetric.lean`, `Lattices/NativeIntegerAffinePullbackHom.lean`, `Lattices/NativeIntegerEquivalenceFiniteFamily.lean`, `Lattices/ResidueBoxSliceCoordinateDisintegration.lean`, `Lattices/SharedFreeAffineBudget.lean`, `Linear/CertifiedChartBasisBudget.lean`, `Linear/RationalTagConstraintChartBasis.lean`, `Linear/TripleProductBasisBounds.lean`, `Nilpotent/CyclicNiltestApproximation.lean`, `Nilpotent/LocalMajorDenseSliceNiltest.lean`, `Nilpotent/NiltestComplement.lean`, `Nilpotent/NiltestOrbitOne.lean`, `Polynomial/QuantitativeOuterPolynomialProducts.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B140
import Definitions.Def_OAIE3v2B141
import Definitions.Def_OAIE3v2B142
import Definitions.Def_OAIE3v2B143
import Definitions.Def_OAIE3v2B144
import Definitions.Def_OAIE3v2B145
import Definitions.Def_OAIE3v2B146
import Definitions.Def_OAIE3v2B147

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PetalComparisonTree
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem realification_subgroup_comap_incl (K : LieSubalgebra ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) :
    (Γ.map realificationHom).comap
      (realificationMap (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K) (hM := hnil) K.incl) =
      (Γ.comap (map (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K) K.incl)).map
        (realificationHom (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨g, hg, heq⟩ := Subgroup.mem_map.mp hx
    have hgK : g.coord ∈ K := by
      apply (rational_inclusion_mem_realificationLieSubalgebra_iff K g.coord).mp
      have hm := realificationMap_incl_mem (hnil := hnil) K x
      rw [← heq] at hm
      exact hm
    let a : NilpotentLieBCHGroup K s (lie_subalgebra_lowerCentralSeries_eq_bot hnil K) :=
      ⟨⟨g.coord, hgK⟩⟩
    have hag : map K.incl a = g := ext rfl
    refine Subgroup.mem_map.mpr ⟨a, ?_, ?_⟩
    · change map K.incl a ∈ Γ
      rwa [hag]
    · apply realificationMap_incl_injective (hnil := hnil) K
      rw [realificationMap_realificationHom, hag]
      exact heq
  · rintro ⟨a, ha, rfl⟩
    change realificationMap (hnil := lie_subalgebra_lowerCentralSeries_eq_bot hnil K)
      (hM := hnil) K.incl (realificationHom a) ∈ Γ.map realificationHom
    rw [realificationMap_realificationHom]
    exact Subgroup.mem_map.mpr ⟨map K.incl a, ha, rfl⟩

end NilpotentLieBCHGroup
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.TripleProductBasisBounds
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem triple_product_basis_logHeight (x : L × L × L) {p : ℝ}
    (hx : ∀ k, rationalLogHeight (D.basis.repr x.1 k) ≤ p ∧
      rationalLogHeight (D.basis.repr x.2.1 k) ≤ p ∧
      rationalLogHeight (D.basis.repr x.2.2 k) ≤ p)
    (k : Fin (Fintype.card (Σ _ : Fin 3, Fin d))) :
    rationalLogHeight ((pi (fun _ : Fin 3 => D)).basis.repr (tripleToPi x) k) ≤ p := by
  have h (j : Fin 3) (l : Fin d) :
      rationalLogHeight (D.basis.repr (tripleToPi x j) l) ≤ p := by
    fin_cases j
    · exact (hx l).1
    · exact (hx l).2.1
    · exact (hx l).2.2
  rw [productFinBasis_repr]
  exact h _ _

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CyclicNiltestApproximation
namespace OAI

section

universe u v

namespace Erdos3

namespace RationalFilteredNilmanifold

open Module
open scoped TensorProduct

variable {ι : Type v} [Fintype ι] {L₀ : Type u} {L : ι → Type u}
  [LieRing L₀] [∀ i, LieRing (L i)] [LieAlgebra ℚ L₀] [∀ i, LieAlgebra ℚ (L i)]
  {s d₀ : ℕ} {d : ι → ℕ}
  (D₀ : RationalFilteredNilmanifold L₀ s d₀)
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem optionProduct_geometry {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hD₀ : D₀.GeometryComplexityLE p) (hD : ∀ i, (D i).GeometryComplexityLE p) :
    (optionProduct D₀ D).GeometryComplexityLE ((p + 3) ^ 2) := by
  have hpp : p ≤ p + 1 := le_add_of_nonneg_right zero_le_one
  have h := pi_geometry (optionFactors D₀ D) (p := p + 1) (by linarith)
    (by simp only [Fintype.card_option, Nat.cast_add, Nat.cast_one]; linarith)
    (fun i => by cases i with
      | none => exact hD₀.mono D₀ hpp
      | some i => exact (hD i).mono (D i) hpp)
  simpa only [optionProduct, show p + 1 + 2 = p + 3 by ring] using h

end RationalFilteredNilmanifold
end Erdos3

end

section

open scoped TensorProduct BigOperators

namespace Erdos3.RationalFilteredNilmanifold

variable {ι σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

variable [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
  {w : σ → ℕ}

omit [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))] in
theorem productObservable_vertical (T : ∀ i, (D i).Niltest w)
    (eta : ∀ i, L i →ₗ[ℚ] ℚ)
    (hvert : ∀ i z, z ∈ (D i).filtration.realification.subgroup s → ∀ x,
      (T i).observable (z • x) =
        CircleFourier.character ((realifyFunctional (eta i) z.coord : ℝ) : CircleFourier.Circle) *
          (T i).observable x)
    (z : (pi D).RealGroup) (hz : z ∈ (pi D).filtration.realification.subgroup s)
    (x : (pi D).Space) :
    productObservable D T (z • x) =
      CircleFourier.character ((realifyFunctional (piFrequency eta) z.coord : ℝ) : CircleFourier.Circle) *
        productObservable D T x := by
  have hchar :
      CircleFourier.character ((realifyFunctional (piFrequency eta) z.coord : ℝ) : CircleFourier.Circle) =
        ∏ i, CircleFourier.character
          ((realifyFunctional (eta i) (productProjectionHom D i z).coord : ℝ) : CircleFourier.Circle) := by
    rw [realify_piFrequency]
    have hcoe (f : ι → ℝ) : ((∑ i, f i : ℝ) : CircleFourier.Circle) =
        ∑ i, (f i : CircleFourier.Circle) :=
      map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) f Finset.univ
    simp only [hcoe, CircleFourier.character_fintype_sum,
      productProjectionHom, NilpotentLieBCHGroup.realificationMap_coord]
  rw [hchar, productObservable, productObservable, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [productProjection_smul]
  exact hvert i _ (productProjectionHom_mem_layer D i s z hz) _

theorem piNiltest_vertical (T : ∀ i, (D i).Niltest w)
    (eta : ∀ i, L i →ₗ[ℚ] ℚ) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p)
    (hvert : ∀ i z, z ∈ (D i).filtration.realification.subgroup s → ∀ x,
      (T i).observable (z • x) =
        CircleFourier.character ((realifyFunctional (eta i) z.coord : ℝ) : CircleFourier.Circle) *
          (T i).observable x)
    (z : (pi D).RealGroup) (hz : z ∈ (pi D).filtration.realification.subgroup s)
    (x : (pi D).Space) :
    (piNiltest D T hp hι hT).observable (z • x) =
      CircleFourier.character ((realifyFunctional (piFrequency eta) z.coord : ℝ) : CircleFourier.Circle) *
        (piNiltest D T hp hι hT).observable x :=
  productObservable_vertical D T eta hvert z hz x

end Erdos3.RationalFilteredNilmanifold

end

section

open scoped TensorProduct BigOperators NNReal

namespace Erdos3.RationalFilteredNilmanifold

variable {ι σ : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) {w : σ → ℕ}

omit [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))] in
theorem productObservable_norm_le_one (T : ∀ i, (D i).Niltest w)
    (hcap : ∀ i, (T i).normBound ≤ 1) (x : (pi D).Space) :
    ‖productObservable D T x‖ ≤ 1 := by
  unfold productObservable
  calc
    _ = ∏ i, ‖(T i).observable (productProjection D i x)‖ := norm_prod _ _
    _ ≤ ∏ _i : ι, (1 : ℝ) := Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      (fun i _ => ((T i).norm_le _).trans (by exact_mod_cast hcap i))
    _ = 1 := by simp

noncomputable def unitBoundedPiNiltest (T : ∀ i, (D i).Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p)
    (hcap : ∀ i, (T i).normBound ≤ 1) : (pi D).Niltest w :=
  { piNiltest D T hp hι hT with
    normBound := 1
    norm_le := productObservable_norm_le_one D T hcap }

theorem unitBoundedPiNiltest_eval (T : ∀ i, (D i).Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p)
    (hcap : ∀ i, (T i).normBound ≤ 1) (x : σ → ℤ) :
    (unitBoundedPiNiltest D T hp hι hT hcap).eval x = ∏ i, (T i).eval x :=
  piNiltest_eval D T hp hι hT x

theorem unitBoundedPiNiltest_complexity (T : ∀ i, (D i).Niltest w) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hT : ∀ i, (T i).ComplexityLE p)
    (hcap : ∀ i, (T i).normBound ≤ 1) :
    (unitBoundedPiNiltest D T hp hι hT hcap).ComplexityLE (productNiltestBudget p) := by
  have h := piNiltest_complexity D T hp hι hT
  refine ⟨h.1, le_trans ?_ h.2⟩
  apply Real.log_le_log (by positivity)
  change 2 + 1 + ((piNiltest D T hp hι hT).lipBound : ℝ) ≤
    2 + Real.exp p ^ Fintype.card ι + ((piNiltest D T hp hι hT).lipBound : ℝ)
  have hb : 1 ≤ Real.exp p ^ Fintype.card ι := one_le_pow₀ (Real.one_le_exp_iff.mpr hp)
  linarith

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BoundedRealifiedSquareOrbit
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def realifiedSquareOrbit {σ : Type*} {w : σ → ℕ}
    (q : F.realification.squareFiltration.PolynomialOrbit w) :
    F.squareFiltration.realification.PolynomialOrbit w :=
  polynomialOrbitOfLog (VectorPolynomial.map F.realifiedSquareEquiv.symm.toLinearMap q.log)
    (F.realification.squareFiltration.adapted_map F.squareFiltration.realification
      F.realifiedSquareEquiv.symm.toLinearMap
      (fun j x hx => (F.realifiedSquareEquiv_symm_mem_layer j x).mpr hx) w q.adapted)

theorem realifiedSquareOrbit_eval {σ : Type*} {w : σ → ℕ}
    (q : F.realification.squareFiltration.PolynomialOrbit w) (x : σ → ℤ) :
    F.realifiedSquareGroupEquiv
      (F.squareFiltration.realification.polynomialOrbitEval w x (F.realifiedSquareOrbit q)) =
        F.realification.squareFiltration.polynomialOrbitEval w x q := by
  apply NilpotentLieBCHGroup.ext
  change F.realifiedSquareEquiv (eval (fun i => (x i : ℚ))
    (VectorPolynomial.map F.realifiedSquareEquiv.symm.toLinearMap q.log)) = _
  rw [eval_map]
  exact F.realifiedSquareEquiv.apply_symm_apply _

theorem realifiedSquareOrbit_fst {σ : Type*} {w : σ → ℕ}
    (q : F.realification.squareFiltration.PolynomialOrbit w) (x : σ → ℤ) :
    F.realSquareFstHom (F.squareFiltration.realification.polynomialOrbitEval w x
      (F.realifiedSquareOrbit q)) =
        F.realification.squareFstHom (F.realification.squareFiltration.polynomialOrbitEval w x q) := by
  rw [← F.realifiedSquareGroupEquiv_fst, F.realifiedSquareOrbit_eval]

theorem realifiedSquareOrbit_snd {σ : Type*} {w : σ → ℕ}
    (q : F.realification.squareFiltration.PolynomialOrbit w) (x : σ → ℤ) :
    F.realSquareSndHom (F.squareFiltration.realification.polynomialOrbitEval w x
      (F.realifiedSquareOrbit q)) =
        F.realification.squareSndHom (F.realification.squareFiltration.polynomialOrbitEval w x q) := by
  rw [← F.realifiedSquareGroupEquiv_snd, F.realifiedSquareOrbit_eval]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem exists_bounded_realified_square_orbit (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (h : σ → ℤ) (f : D.filtration.realification.PolynomialOrbit w),
      ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
        (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((p + 1 + C) ^ C)) ∧
        ∃ q : D.filtration.squareFiltration.realification.PolynomialOrbit w,
          ∀ x : σ → ℤ,
            D.filtration.realSquareFstHom
              (D.filtration.squareFiltration.realification.polynomialOrbitEval w x q) =
                ε⁻¹ * D.filtration.realification.polynomialOrbitEval w (fun i => x i + h i) f * γ⁻¹ ∧
            D.filtration.realSquareSndHom
              (D.filtration.squareFiltration.realification.polynomialOrbitEval w x q) =
                D.filtration.realification.polynomialOrbitEval w x f := by
  obtain ⟨C, hC, hnorm⟩ := exists_bounded_normalized_square_orbit s
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d _ _ _ D p hp hD w hw h f
  obtain ⟨ε, γ, hγ, hε, q, hq⟩ := hnorm D p hp hD w hw h f
  refine ⟨ε, γ, hγ, hε, D.filtration.realifiedSquareOrbit q, ?_⟩
  intro x
  rw [D.filtration.realifiedSquareOrbit_fst, D.filtration.realifiedSquareOrbit_snd]
  exact hq x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.QuantitativeOuterPolynomialProducts
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {s : ℕ}

theorem positiveUnivariate_zero (v : Fin s → V) : coefficients (positiveUnivariate v) 0 = 0 := by
  apply positiveUnivariate_coefficient_eq_zero
  intro d h
  have h' := congrArg (fun α : Unit →₀ ℕ => α ()) h
  simp only [Finsupp.single_eq_same, Finsupp.zero_apply] at h'
  omega

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]

theorem positiveUnivariate_coefficientBound (b : Basis ι ℝ L) (v : Fin s → L)
    (T : Unit → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (hv : ∀ d, ‖b.equivFun (v d)‖ ≤ M / monomialScale T (Finsupp.single () (d.val + 1))) :
    CoefficientBound b T M (positiveUnivariate v) := by
  apply (coefficientBound_iff_norm b T hT hM _).mpr
  intro α
  by_cases hα : ∃ d : Fin s, Finsupp.single () (d.val + 1) = α
  · obtain ⟨d, rfl⟩ := hα
    rw [positiveUnivariate_coefficient]
    exact hv d
  · rw [positiveUnivariate_coefficient_eq_zero v α (by simpa only [not_exists] using hα),
      map_zero, norm_zero]
    exact div_nonneg hM (monomialScale_pos T hT α).le

theorem positiveUnivariate_coefficientGrid (b : Basis ι ℝ L) (v : Fin s → L) (l : ℕ)
    (hv : ∀ d, b.equivFun (v d) ∈ realDenominatorGrid l) :
    CoefficientGrid b l (positiveUnivariate v) := by
  intro α
  by_cases hα : ∃ d : Fin s, Finsupp.single () (d.val + 1) = α
  · obtain ⟨d, rfl⟩ := hα
    rw [positiveUnivariate_coefficient]
    simpa only [Basis.equivFun_apply] using hv d
  · rw [positiveUnivariate_coefficient_eq_zero v α (by simpa only [not_exists] using hα)]
    refine ⟨0, ?_⟩
    ext i
    simp

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeRealAction
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem squarefreeFinBasis_multidegree_height (p : ℝ) (c : ReplicatedIndex bound → ℕ) (j k) :
    RationalHeightLE ((M.squarefreeFinBasis p).repr
      (M.filtration.squarefreeMultidegreeBasis (fun j : ReplicatedIndex bound => j.1)
        (M.squarefreeCoefficientBasis p) c j).val k) 1 := by
  rw [squarefreeFinBasis, Basis.repr_reindex_apply]
  exact M.filtration.squarefreeMultidegreeBasis_height _ (M.squarefreeCoefficientBasis p) c j _

theorem squarefreeFinBasis_degree_height (p : ℝ) (n : ℕ) (j k) :
    RationalHeightLE ((M.squarefreeFinBasis p).repr
      (M.filtration.squarefreeDegreeBasis (fun j : ReplicatedIndex bound => j.1)
        (M.squarefreeCoefficientBasis p) n j).val k) 1 := by
  rw [squarefreeFinBasis, Basis.repr_reindex_apply]
  exact M.filtration.squarefreeDegreeBasis_height _ (M.squarefreeCoefficientBasis p) n j _

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem comparisonGraph_chosen_height {p : ℝ} (hM : M.ComplexityLE p)
    (a : σ → ℕ) (ha : a ≠ 0) (hab : a ≤ bound)
    (j : Fin (finrank ℚ (M.filtration.layer a)))
    (k : Fin d ⊕ Fin (Fintype.card M.SquarefreeBasisIndex)) :
    RationalHeightLE ((D.basis.prod (M.squarefreeFinBasis p)).repr
      (M.filtration.comparisonGraph (fun i : ReplicatedIndex bound => i.1) a ha
        (M.comparisonLayerBasis p a j)) k) (comparisonBasisHeight bound p) := by
  cases k with
  | inl k =>
      exact (M.comparisonLayerBasis_height hM a hab j k).mono
        (comparisonBasisHeight_ge_ceil bound p)
  | inr k =>
      change RationalHeightLE ((M.squarefreeFinBasis p).repr
        (M.filtration.blockLayerMap (fun i : ReplicatedIndex bound => i.1) a ha
          (M.comparisonLayerBasis p a j)) k) _
      rw [squarefreeFinBasis, Basis.repr_reindex_apply]
      exact (M.blockLayerMap_chosen_height p a ha j _).mono
        ((multidegreeFactorial_mono hab).trans (comparisonBasisHeight_ge_factorial bound p))

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

noncomputable def squarefreeModelMultidegree (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.SquarefreeGridStable p B) :
    (M.squarefreeModel p B hB hstable).MultidegreeStructure (fun _ : ReplicatedIndex bound => 1) where
  filtration := M.filtration.squarefreeMultidegreeFiltration (fun j : ReplicatedIndex bound => j.1)
  ordinary := rfl
  basis a := M.filtration.squarefreeMultidegreeBasis (fun j : ReplicatedIndex bound => j.1)
    (M.squarefreeCoefficientBasis p) (fun j => (a j).val)

theorem squarefreeModel_complexity {p q : ℝ} (hM : M.ComplexityLE p) (B : ℕ) (hB : 0 < B)
    (hstable : M.SquarefreeGridStable p B) (hq : 0 ≤ q)
    (hd : (Fintype.card M.SquarefreeBasisIndex : ℝ) ≤ q) (hBq : (B : ℝ) ≤ Real.exp q)
    (hHq : (squarefreeStructureHeight d ⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp q) :
    (M.squarefreeModelMultidegree p B hB hstable).ComplexityLE q := by
  have hone : ((1 : ℕ) : ℝ) ≤ Real.exp q := by
    rw [Nat.cast_one]
    exact Real.one_le_exp_iff.mpr hq
  refine ⟨⟨hd, hBq, ?_, ?_⟩, ?_⟩
  · intro i j k
    exact rationalLogHeight_le_of_height (M.squarefreeFinBasis_structure_height hM i j k) hHq
  · intro i j k
    exact rationalLogHeight_le_of_height (M.squarefreeFinBasis_degree_height p (i.val + 1) j k) hone
  · intro a j k
    exact rationalLogHeight_le_of_height
      (M.squarefreeFinBasis_multidegree_height p (fun i => (a i).val) j k) hone

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeQuotientAction
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (p : ℝ) (B : ℕ) (hB : 0 < B)
  (hstable : M.SquarefreeGridStable p B)

theorem squarefreeSpacePermute_smul (e : ReplicatedPermutation bound)
    (g : (M.squarefreeModel p B hB hstable).RealGroup)
    (x : (M.squarefreeModel p B hB hstable).Space) :
    M.squarefreeSpacePermute p B hB hstable e (g • x) =
      M.squarefreeRealPermute p B hB hstable e g • M.squarefreeSpacePermute p B hB hstable e x :=
  cosetMap_smul _ _ _ _ _ _

theorem squarefreeSpacePermute_commutes_top (e : ReplicatedPermutation bound)
    (g : (M.squarefreeModel p B hB hstable).RealGroup)
    (hg : g ∈ (M.squarefreeModel p B hB hstable).filtration.realification.subgroup
      (Fintype.card (ReplicatedIndex bound))) (x : (M.squarefreeModel p B hB hstable).Space) :
    M.squarefreeSpacePermute p B hB hstable e (g • x) =
      g • M.squarefreeSpacePermute p B hB hstable e x := by
  rw [M.squarefreeSpacePermute_smul, M.squarefreeRealPermute_top p B hB hstable e g hg]

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SquarefreeActionMetric
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem squarefreeFinBasis_permute (p : ℝ) (e : ReplicatedPermutation bound)
    (j : Fin (Fintype.card M.SquarefreeBasisIndex)) :
    ∃ k, M.filtration.replicatedLiePermute e (M.squarefreeFinBasis p j) = M.squarefreeFinBasis p k := by
  obtain ⟨k, hk⟩ := M.squarefreeBasis_permute p (replicatedPermutation bound e)
    (replicatedPermutation_block bound e) ((Fintype.equivFin M.SquarefreeBasisIndex).symm j)
  refine ⟨Fintype.equivFin M.SquarefreeBasisIndex k, ?_⟩
  simpa only [squarefreeFinBasis, Basis.reindex_apply, Equiv.symm_apply_apply,
    MultidegreeLieFiltration.replicatedLiePermute] using hk

theorem squarefreePermute_coordinate_height (p : ℝ) (e : ReplicatedPermutation bound)
    {q : ℝ} (hq : 0 ≤ q) (i j : Fin (Fintype.card M.SquarefreeBasisIndex)) :
    rationalLogHeight ((M.squarefreeFinBasis p).repr
      (M.filtration.replicatedLiePermute e (M.squarefreeFinBasis p j)) i) ≤ q := by
  obtain ⟨k, hk⟩ := M.squarefreeFinBasis_permute p e j
  rw [hk]
  simp only [Basis.repr_self, Finsupp.single_apply]
  split_ifs <;> simpa [rationalLogHeight] using hq

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BohrNiltestBudget
namespace OAI

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d t : ℕ}

variable (D : RationalFilteredNilmanifold L s d) (φ : L →ₗ⁅ℚ⁆ RationalTorus.Algebra t)

variable (hphase : ∀ z : D.filtration.Group, z ∈ D.lattice → IntegralVector (φ z.coord))

include hphase in
theorem torusPhase_lattice_map :
    D.lattice ≤ (RationalTorus.nilmanifold t).lattice.comap
      (mapOfSteps (hL := D.filtration.lowerCentralSeries_eq_bot)
        (hM := (RationalTorus.nilmanifold t).filtration.lowerCentralSeries_eq_bot) φ) := by
  intro z hz
  exact hphase z hz

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueBoxSliceCoordinateDisintegration
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {I V : Type*} {N : I → ℕ} {q : ℕ}

def coordinateProjection (A : ResidueBoxSlice N q) (keep : I → Prop) :
    ResidueBoxSlice (fun i : {i // keep i} => N i) q :=
  A.comap Subtype.val

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.LocalMajorDenseSliceNiltest
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def scaleComplex (T : D.Niltest w) (c : ℂ) : D.Niltest w where
  orbit := T.orbit
  observable := fun x => c * T.observable x
  normBound := ‖c‖₊ * T.normBound
  lipBound := ‖c‖₊ * T.lipBound
  norm_le x := by
    simpa only [norm_mul, NNReal.coe_mul, coe_nnnorm] using
      mul_le_mul_of_nonneg_left (T.norm_le x) (norm_nonneg c)
  lipschitz := by
    let := D.metricSpace
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm, ← mul_sub, norm_mul, NNReal.coe_mul, coe_nnnorm, mul_assoc] using
      mul_le_mul_of_nonneg_left (T.lipschitz.dist_le_mul x y) (norm_nonneg c)

theorem scaleComplex_eval (T : D.Niltest w) (c : ℂ) (x : σ → ℤ) :
    (T.scaleComplex c).eval x = c * T.eval x := rfl

theorem scaleComplex_evalCyclic (T : D.Niltest w) (c : ℂ) (N : ℕ) [NeZero N] (x : σ → ZMod N) :
    (T.scaleComplex c).evalCyclic N x = c * T.evalCyclic N x := rfl

theorem scaleComplex_norm (T : D.Niltest w) {c : ℂ} (hc : ‖c‖ ≤ 1) :
    (T.scaleComplex c).normBound ≤ T.normBound := by
  change ‖c‖₊ * T.normBound ≤ T.normBound
  exact mul_le_of_le_one_left (by positivity) (by exact_mod_cast hc)

theorem scaleComplex_complexity (T : D.Niltest w) {c : ℂ} (hc : ‖c‖ ≤ 1)
    {p : ℝ} (hT : T.ComplexityLE p) : (T.scaleComplex c).ComplexityLE p := by
  refine ⟨hT.1, ?_⟩
  change Real.log (2 + ‖c‖ * (T.normBound : ℝ) + ‖c‖ * (T.lipBound : ℝ)) ≤ p
  have hn := mul_le_mul_of_nonneg_right hc T.normBound.coe_nonneg
  have hl := mul_le_mul_of_nonneg_right hc T.lipBound.coe_nonneg
  exact (Real.log_le_log (by positivity) (by linarith)).trans hT.2

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct Manifold ContDiff

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem evalReal_integer (T : D.Niltest w) (x : σ → ℤ) :
    T.evalReal (fun i => (x i : ℝ)) = T.eval x := by
  unfold evalReal eval
  rw [NilpotentLieFiltration.polynomialOrbitRealEval_integer]

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def expNormalize (T : D.Niltest w) (p : ℝ) : D.Niltest w :=
  T.scaleComplex (Real.exp (-p) : ℂ)

theorem expNormalize_norm (T : D.Niltest w) {p : ℝ} (hT : T.ComplexityLE p) :
    (T.expNormalize p).normBound ≤ 1 := by
  have hb := T.observable_budget hT
  have hl := T.lipBound.coe_nonneg
  have hn : (T.normBound : ℝ) ≤ Real.exp p := by linarith
  change ‖(Real.exp (-p) : ℂ)‖₊ * T.normBound ≤ 1
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_mul, coe_nnnorm, NNReal.coe_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-p))]
  calc
    _ ≤ Real.exp (-p) * Real.exp p := mul_le_mul_of_nonneg_left hn (Real.exp_nonneg _)
    _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

theorem expNormalize_complexity (T : D.Niltest w) {p : ℝ} (hT : T.ComplexityLE p) :
    (T.expNormalize p).ComplexityLE p := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hT.1.1
  apply T.scaleComplex_complexity _ hT
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-p))]
  exact Real.exp_le_one_iff.mpr (by linarith)

theorem expNormalize_eval (T : D.Niltest w) (p : ℝ) (x : σ → ℤ) :
    (T.expNormalize p).eval x = (Real.exp (-p) : ℂ) * T.eval x := rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

theorem exists_bounded_niltest_pair_sum {J σ L K : Type*} [Fintype J] [Nonempty J]
    [LieRing L] [LieAlgebra ℚ L] [LieRing K] [LieAlgebra ℚ K]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)]
    {s t d e : ℕ} (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold K t e) (w : σ → ℕ)
    (gD : D.filtration.realification.PolynomialOrbit w)
    (gE : E.filtration.realification.PolynomialOrbit w)
    (A : J → D.Niltest w) (B : J → E.Niltest w) (c : J → ℂ) {p : ℝ}
    (hAnorm : ∀ j, (A j).normBound ≤ 1) (hBnorm : ∀ j, (B j).normBound ≤ 1)
    (hA : ∀ j, (A j).ComplexityLE p) (hB : ∀ j, (B j).ComplexityLE p)
    (hAg : ∀ j, (A j).orbit = gD) (hBg : ∀ j, (B j).orbit = gE)
    (hc : ∀ j, ‖c j‖ ≤ 2) :
    ∃ N : ℕ, 0 < N ∧ N = 2 * Fintype.card J ∧
      ∃ (A' : Fin N → D.Niltest w) (B' : Fin N → E.Niltest w),
        (∀ j, (A' j).normBound ≤ 1) ∧ (∀ j, (B' j).normBound ≤ 1) ∧
        (∀ j, (A' j).ComplexityLE p) ∧ (∀ j, (B' j).ComplexityLE p) ∧
        (∀ j, (A' j).orbit = gD) ∧ (∀ j, (B' j).orbit = gE) ∧
        ∀ x, ∑ j, (A' j).eval x * (B' j).eval x =
          ∑ j, ((A j).eval x * (B j).eval x) * c j := by
  classical
  let f := (Fintype.equivFin (Bool × J)).symm
  let A' (j : Fin (Fintype.card (Bool × J))) :=
    (A (f j).2).scaleComplex (c (f j).2 / 2)
  let B' (j : Fin (Fintype.card (Bool × J))) := B (f j).2
  refine ⟨Fintype.card (Bool × J), Fintype.card_pos, ?_, A', B', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Fintype.card_prod, Fintype.card_bool]
  · intro j
    exact ((A (f j).2).scaleComplex_norm (norm_complex_half_le_one (hc (f j).2))).trans (hAnorm _)
  · intro j
    exact hBnorm _
  · intro j
    exact (A (f j).2).scaleComplex_complexity (norm_complex_half_le_one (hc (f j).2)) (hA _)
  · intro j
    exact hB _
  · intro j
    exact hAg _
  · intro j
    exact hBg _
  · intro x
    exact (f.sum_comp (fun j => (c j.2 / 2 * (A j.2).eval x) * (B j.2).eval x)).trans
      (sum_double_half_products (fun j => (A j).eval x) (fun j => (B j).eval x) c)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.WeightedTranslationTwistedCentralFrequency
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie
open _root_.MvPolynomial CircleFourier
open scoped TensorProduct

variable {m : ℕ} (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]

 theorem central_character_eq_fourierChar (t : ℝ) :
    character (t : CircleFourier.Circle) = (Real.fourierChar t : ℂ) := by
  rw [character_coe_exp, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerAffinePullbackHom
namespace OAI

section

namespace Erdos3.NativeIntegerExpansion

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {σ τ : Type*} {w : σ → ℕ} {v : τ → ℕ} {s : ℕ} {p : ℝ}
  {f : (σ → ℤ) → ℂ}

theorem substitutedValue_eq (E : NativeIntegerExpansion w s p f)
    (P : σ → MvPolynomial τ ℚ) (hP : ∀ i, P i ∈ weightedSupportLE v (w i))
    (x : τ → ℤ) (y : σ → ℤ)
    (hxy : ∀ i, MvPolynomial.aeval (R := ℚ) (fun j => (x j : ℚ)) (P i) = (y i : ℚ)) :
    E.substitutedValue P hP x = f y := by
  rw [E.eval y]
  unfold substitutedValue
  apply Finset.sum_congr rfl
  intro i _
  rw [RationalFilteredNilmanifold.Niltest.eval_substitute _ _ _ x y hxy]

end Erdos3.NativeIntegerExpansion

end

section

namespace Erdos3

namespace NativeIntegerVectorEquivalence

variable {σ J K : Type*} [Fintype J] [Fintype K] {s : ℕ} {p q : ℝ}
  {chi : J → (σ → ℤ) → ℂ} {eta : K → (σ → ℤ) → ℂ}

theorem conjugate (E : NativeIntegerVectorEquivalence s p chi eta) :
    NativeIntegerVectorEquivalence s p (fun j x => star (chi j x))
      (fun k x => star (eta k x)) where
  left_dimension := E.left_dimension
  right_dimension := E.right_dimension
  expansion j k := by
    obtain ⟨R⟩ := E.expansion j k
    have h : Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s p
        (fun x => star (chi j x * star (eta k x)))) := ⟨R.conjugate⟩
    simpa only [star_mul, star_star, mul_comm] using h

theorem affinePullback {τ : Type*} [Fintype τ]
    (E : NativeIntegerVectorEquivalence s p chi eta) (A : σ → τ → ℤ) (b : σ → ℤ) :
    NativeIntegerVectorEquivalence s p
      (fun j x => chi j (integerAffineMap A b x)) (fun k x => eta k (integerAffineMap A b x)) where
  left_dimension := E.left_dimension
  right_dimension := E.right_dimension
  expansion j k := by
    obtain ⟨R⟩ := E.expansion j k
    exact ⟨R.affinePullback A b⟩

end NativeIntegerVectorEquivalence

end Erdos3

end

section

namespace Erdos3.NativeIntegerVectorEquivalence

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {σ J K : Type*} [Fintype J] [Fintype K] {s : ℕ} {p : ℝ}
  {chi : J → (σ → ℤ) → ℂ} {eta : K → (σ → ℤ) → ℂ}
  (E : NativeIntegerVectorEquivalence s p chi eta)

theorem transfer_sample_correlation {X : Type*} (S : Finset X) (x : X → σ → ℤ)
    (j : J) (f : X → ℂ) {q : ℝ}
    (hunit : ∀ u ∈ S, ∑ k, ‖eta k (x u)‖ ^ 2 = 1)
    (hcorr : Real.exp (-q) ≤ ‖𝔼 u ∈ S, f u * star (chi j (x u))‖) :
    ∃ (k : K) (a : Fin (E.selectedExpansion j k).count),
      Real.exp (-(q + 2 * p)) ≤
        ‖𝔼 u ∈ S, f u * star (eta k (x u)) *
          star (((E.selectedExpansion j k).test a).eval (x u))‖ := by
  classical
  let R (k : K) := E.selectedExpansion j k
  have hexp (k : K) (u : X) (_hu : u ∈ S) :
      star (chi j (x u)) * star (star (eta k (x u))) =
        ∑ a, star ((R k).coefficient a) * star (((R k).test a).eval (x u)) := by
    have h := congrArg star ((R k).eval (x u))
    simpa only [star_sum, star_mul, star_star, mul_comm] using h
  obtain ⟨k, a, hka⟩ := exists_unit_expansion_correlation S f
    (fun u => star (chi j (x u))) (fun k u => star (eta k (x u)))
    (fun k a => star ((R k).coefficient a))
    (fun k a u => star (((R k).test a).eval (x u)))
    (fun u hu => by simpa only [norm_star] using hunit u hu) hexp
    (Real.exp_pos (-q)) (Real.exp_pos p) (Real.exp_pos p) E.right_dimension
    (fun k => by simpa only [norm_star] using (R k).cost) hcorr
  have hfrac : Real.exp (-q) / (Real.exp p * Real.exp p) =
      Real.exp (-(q + 2 * p)) := by
    rw [← Real.exp_add, ← Real.exp_sub]
    congr 1
    ring
  rw [hfrac] at hka
  exact ⟨k, a, hka⟩

end Erdos3.NativeIntegerVectorEquivalence

end

section

namespace Erdos3.NativeIntegerVectorEquivalence

open scoped BigOperators

theorem selectedChoice_card_bound {σ I J : Type*} [Fintype I] [Fintype J]
    {s : ℕ} {p : ℝ} {f : I → (σ → ℤ) → ℂ} {g : J → (σ → ℤ) → ℂ}
    (E : NativeIntegerVectorEquivalence s p f g) (i : I) :
    (Fintype.card (Σ j : J, Fin (E.selectedExpansion i j).count) : ℝ) ≤ Real.exp (2 * p) := by
  rw [Fintype.card_sigma, Nat.cast_sum]
  calc
    _ ≤ ∑ _j : J, Real.exp p := Finset.sum_le_sum (fun j _ => by
      simpa only [Fintype.card_fin] using (E.selectedExpansion i j).count_bound)
    _ = (Fintype.card J : ℝ) * Real.exp p := by simp
    _ ≤ Real.exp p * Real.exp p := mul_le_mul_of_nonneg_right E.right_dimension (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, two_mul]

theorem selectedChainedChoice_card_bound {σ I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    {s : ℕ} {p q : ℝ} {f : I → (σ → ℤ) → ℂ} {g : J → (σ → ℤ) → ℂ}
    {h : K → (σ → ℤ) → ℂ} (E : NativeIntegerVectorEquivalence s p f g)
    (F : NativeIntegerVectorEquivalence s q g h) (i : I) :
    (Fintype.card (Σ j : J, Fin (E.selectedExpansion i j).count ×
      (Σ k : K, Fin (F.selectedExpansion j k).count)) : ℝ) ≤ Real.exp (2 * p + 2 * q) := by
  rw [Fintype.card_sigma, Nat.cast_sum]
  calc
    _ ≤ ∑ _j : J, Real.exp p * Real.exp (2 * q) := by
      apply Finset.sum_le_sum
      intro j _
      simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
      exact mul_le_mul (E.selectedExpansion i j).count_bound (F.selectedChoice_card_bound j)
        (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = (Fintype.card J : ℝ) * (Real.exp p * Real.exp (2 * q)) := by simp
    _ ≤ Real.exp p * (Real.exp p * Real.exp (2 * q)) :=
      mul_le_mul_of_nonneg_right E.right_dimension (by positivity)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3.NativeIntegerVectorEquivalence

end

section

namespace Erdos3.NativeIntegerVectorEquivalence

theorem affinePullbackHom {σ τ J K : Type*} [Fintype τ] [Fintype J] [Fintype K]
    {s : ℕ} {p : ℝ} {f : J → (σ → ℤ) → ℂ} {g : K → (σ → ℤ) → ℂ}
    (E : NativeIntegerVectorEquivalence s p f g) (A : σ → ((τ → ℤ) →+ ℤ)) (b : σ → ℤ) :
    NativeIntegerVectorEquivalence s p
      (fun j x => f j (fun i => b i + A i x))
      (fun k x => g k (fun i => b i + A i x)) := by
  classical
  have hinput (x : τ → ℤ) :
      integerAffineMap (fun i j => A i (Pi.single j 1)) b x = fun i => b i + A i x := by
    funext i
    rw [integerAffineMap, ← integerLinearForm_eq_sum]
  simpa only [hinput] using E.affinePullback (fun i j => A i (Pi.single j 1)) b

end Erdos3.NativeIntegerVectorEquivalence

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestComplement
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem raiseStep_top_vertical (T : D.Niltest w) (hst : s < t)
    (z : (D.raiseStep hst.le).RealGroup)
    (hz : z ∈ (D.raiseStep hst.le).filtration.realification.subgroup t)
    (x : (D.raiseStep hst.le).Space) :
    (T.raiseStep hst.le).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (0 : L →ₗ[ℚ] ℚ) z.coord : ℝ) : CircleFourier.Circle) *
          (T.raiseStep hst.le).observable x := by
  have hz' : z = 1 := by
    apply NilpotentLieBCHGroup.ext
    change z.coord = 0
    change z.coord ∈ D.filtration.realification.layer t at hz
    simpa only [D.filtration.realification.layer_eq_bot_above_step hst,
      Submodule.mem_bot] using hz
  subst z
  simp

end Erdos3.RationalFilteredNilmanifold.Niltest

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

theorem exists_linear_frequency_splitting
    {σ ι V : Type*} [Fintype σ] [DecidableEq σ] [AddCommGroup V] [Module ℚ V]
    (b : Basis ι ℚ V) (η : V →ₗ[ℚ] ℚ)
    {H : ℕ} (hH : 1 ≤ H) (hheight : ∀ i, RationalHeightLE (η (b i)) H)
    (T : σ → ℕ) (hT : ∀ i, 0 < T i) (a : σ → ℝ ⊗[ℚ] V)
    {δ : ℝ} (hδ : 0 < δ)
    (hbias : δ ≤ ‖linearPhaseMean T (fun i => (realifyFunctional η (a i) : CircleFourier.Circle))‖) :
    ∃ (m : ℕ) (e p r : σ → ℝ ⊗[ℚ] V),
      0 < m ∧ m ≤ H ∧ (∀ i, e i + p i + r i = a i) ∧
      (∀ i, realifyFunctional η (p i) = 0) ∧
      (∀ i j, |(b.baseChange ℝ).repr (e i) j| ≤ (H : ℝ) / (2 * T i * δ)) ∧
      (fun z : σ × ι => (b.baseChange ℝ).repr (r z.1) z.2) ∈ realDenominatorGrid m := by
  by_cases hη : η = 0
  · subst η
    refine ⟨1, 0, a, 0, Nat.zero_lt_one, hH, ?_, ?_, ?_, ?_⟩
    · intro i
      simp
    · intro i
      exact realifyFunctional_zero (a i)
    · intro i j
      simp only [Pi.zero_apply, map_zero, Finsupp.zero_apply, abs_zero]
      positivity
    · refine ⟨0, ?_⟩
      ext z
      simp
  · exact exists_biased_linear_coefficient_splitting b η hη hH hheight T hT a hδ hbias

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealProductInclusion
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem productSpaceEquiv_symm_mk (g : ∀ i, (D i).RealGroup) :
    (productSpaceEquiv D).symm (fun i => QuotientGroup.mk (g i)) =
      QuotientGroup.mk ((realBCHPiEquiv (fun i => (D i).filtration)).symm g) := by
  apply (productSpaceEquiv D).injective
  rw [Equiv.apply_symm_apply]
  funext i
  change QuotientGroup.mk (g i) = QuotientGroup.mk
    (realBCHPiEquiv (fun i => (D i).filtration)
      ((realBCHPiEquiv (fun i => (D i).filtration)).symm g) i)
  rw [MulEquiv.apply_symm_apply]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]

theorem realification_piRight_symm_single (i : ι) (x : ℝ ⊗[ℚ] L i) :
    (TensorProduct.piRight ℚ ℝ ℝ L).symm (Pi.single i x) =
      realificationLieHom (liePiSingle i) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [TensorProduct.piRight_symm_single]
    rfl
  | add x y hx hy => simp only [Pi.single_add, map_add, hx, hy]

namespace RationalFilteredNilmanifold

variable {s : ℕ} {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

noncomputable def productInclusionHom (i : ι) : (D i).RealGroup →* (pi D).RealGroup :=
  realificationMap (hnil := (D i).filtration.lowerCentralSeries_eq_bot)
    (hM := (pi D).filtration.lowerCentralSeries_eq_bot) (liePiSingle i)

theorem realBCHPiEquiv_symm_single (i : ι) (g : (D i).RealGroup) :
    (realBCHPiEquiv (fun i => (D i).filtration)).symm (Pi.mulSingle i g) = productInclusionHom D i g := by
  apply NilpotentLieBCHGroup.ext
  change (TensorProduct.piRight ℚ ℝ ℝ L).symm
    (fun j => ((Pi.mulSingle i g : ∀ j, (D j).RealGroup) j).coord) =
    realificationLieHom (liePiSingle i) g.coord
  have h : (fun j => ((Pi.mulSingle i g : ∀ j, (D j).RealGroup) j).coord) = Pi.single i g.coord := by
    funext j
    by_cases hji : j = i
    · subst j
      simp only [Pi.mulSingle_eq_same, Pi.single_eq_same]
    · simp only [Pi.mulSingle_eq_of_ne hji, Pi.single_eq_of_ne hji, coord_one]
  rw [h, realification_piRight_symm_single]

theorem productInclusion_matrix_height (i : ι) (j : Fin (d i))
    (k : Fin (Fintype.card (Σ i, Fin (d i)))) :
    RationalHeightLE ((pi D).basis.repr (liePiSingle i ((D i).basis j)) k) 1 := by
  change RationalHeightLE ((pi D).basis.repr (Pi.single i ((D i).basis j)) k) 1
  rw [productFinBasis_repr]
  generalize hz : (Fintype.equivFin (Σ i, Fin (d i))).symm k = z
  rcases z with ⟨a, l⟩
  by_cases hai : a = i
  · subst a
    rw [Pi.single_eq_same, Module.Basis.repr_self]
    by_cases hjl : j = l <;> simp [hjl, RationalHeightLE]
  · rw [Pi.single_eq_of_ne hai, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero le_rfl

theorem productSpaceEquiv_symm_update_mk (g : ∀ i, (D i).RealGroup) (i : ι) (a : (D i).RealGroup) :
    (productSpaceEquiv D).symm (Function.update (fun j => QuotientGroup.mk (g j)) i (QuotientGroup.mk a)) =
      QuotientGroup.mk ((realBCHPiEquiv (fun j => (D j).filtration)).symm (Function.update g i a)) := by
  have h : Function.update (fun j => (QuotientGroup.mk (g j) : (D j).Space)) i (QuotientGroup.mk a) =
      (fun j => QuotientGroup.mk (Function.update g i a j)) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hji]
  rw [h, productSpaceEquiv_symm_mk]

end RationalFilteredNilmanifold
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NativeProductOrbitMetric
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {s : ℕ} {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]

theorem productInclusionHom_lipschitz (i : ι) :
    letI := rightMetricSpace (hnil := (D i).filtration.realification.lowerCentralSeries_eq_bot)
      ((D i).basis.baseChange ℝ)
    letI := rightMetricSpace (hnil := (pi D).filtration.realification.lowerCentralSeries_eq_bot)
      ((pi D).basis.baseChange ℝ)
    LipschitzWith (coordinateLipschitzBound (Fintype.card (Σ i, Fin (d i))) (d i) 1)
      (productInclusionHom D i) := by
  unfold productInclusionHom
  simpa only [Fintype.card_fin, Nat.cast_one] using
    (lipschitz_realificationMap (hnil := (D i).filtration.lowerCentralSeries_eq_bot)
      (hM := (pi D).filtration.lowerCentralSeries_eq_bot)
      (D i).basis (pi D).basis (liePiSingle i) 1 (fun k j => productInclusion_matrix_height D i j k))

theorem productSpaceEquiv_symm_coordinate_lipschitz (i : ι) (y : ∀ j, (D j).Space) :
    letI := (D i).metricSpace
    letI := (pi D).metricSpace
    LipschitzWith (coordinateLipschitzBound (Fintype.card (Σ j, Fin (d j))) (d i) 1)
      (fun a => (productSpaceEquiv D).symm (Function.update y i a)) := by
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L i) := ((D i).basis.baseChange ℝ).finiteDimensional_of_finite
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] (∀ j, L j)) := ((pi D).basis.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := (D i).filtration.realification.lowerCentralSeries_eq_bot)
    ((D i).basis.baseChange ℝ)
  let := rightMetricSpace (hnil := (pi D).filtration.realification.lowerCentralSeries_eq_bot)
    ((pi D).basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := (D i).filtration.realification.lowerCentralSeries_eq_bot)
    ((D i).basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := (pi D).filtration.realification.lowerCentralSeries_eq_bot)
    ((pi D).basis.baseChange ℝ)
  let := (pi D).metricSpace
  let g : ∀ j, (D j).RealGroup := fun j => (y j).out
  let e := realBCHPiEquiv (fun j => (D j).filtration)
  let u : (pi D).RealGroup := e.symm (Function.update g i 1)
  have hbase : (fun j => (QuotientGroup.mk (g j) : (D j).Space)) = y :=
    funext (fun j => Quotient.out_eq (y j))
  have heval (a : (D i).RealGroup) :
      (productSpaceEquiv D).symm (Function.update y i (QuotientGroup.mk a)) =
        QuotientGroup.mk (productInclusionHom D i a * u) := by
    rw [← hbase, productSpaceEquiv_symm_update_mk]
    have hup : Function.update g i a = Pi.mulSingle i a * Function.update g i 1 := by
      funext j
      by_cases hji : j = i
      · subst j
        simp only [Function.update_self, Pi.mul_apply, Pi.mulSingle_eq_same, mul_one]
      · simp only [Function.update_of_ne hji, Pi.mul_apply, Pi.mulSingle_eq_of_ne hji, one_mul]
    rw [hup, map_mul, realBCHPiEquiv_symm_single]
  have hm : LipschitzWith 1 (QuotientGroup.mk : (pi D).RealGroup → (pi D).Space) :=
    quotientMetricSpace_lipschitz_mk ((pi D).basis.baseChange ℝ) (pi D).realLattice
      (pi D).realLattice_closed_discrete.1
  have hf := hm.comp ((isometry_mul_right u).lipschitz.comp (productInclusionHom_lipschitz D i))
  have hf' : LipschitzWith (coordinateLipschitzBound (Fintype.card (Σ j, Fin (d j))) (d i) 1)
      (fun a : (D i).RealGroup => (productSpaceEquiv D).symm (Function.update y i (QuotientGroup.mk a))) := by
    simpa only [Function.comp_def, one_mul, heval] using hf
  exact rightCosetMetricSpace_lipschitz_lift (D i).realLattice (D i).realLattice_closed_discrete.1 _ hf'

theorem productSpaceEquiv_symm_lipschitz :
    letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
    letI := (pi D).metricSpace
    LipschitzWith (productMetricBound d) (productSpaceEquiv D).symm := by
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  let := (pi D).metricSpace
  exact lipschitzWith_of_coordinatewise _ _ (fun i y => productSpaceEquiv_symm_coordinate_lipschitz D i y)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComparisonAmbient
namespace OAI

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

variable {ι : Type v} [Fintype ι] {L₀ H : Type u} {L : ι → Type u}
  [LieRing L₀] [LieAlgebra ℚ L₀] [LieRing H] [LieAlgebra ℚ H]
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {s d₀ : ℕ} {d : ι → ℕ}
  (D₀ : RationalFilteredNilmanifold L₀ s d₀)
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

theorem optionProductMap_point_logHeight
    (φ₀ : H →ₗ⁅ℚ⁆ L₀) (φ : ∀ i, H →ₗ⁅ℚ⁆ L i) (x : H) {p : ℝ}
    (h₀ : ∀ i, rationalLogHeight (D₀.basis.repr (φ₀ x) i) ≤ p)
    (hφ : ∀ a i, rationalLogHeight ((D a).basis.repr (φ a x) i) ≤ p) :
    ∀ i, rationalLogHeight
      ((optionProduct D₀ D).basis.repr (optionProductMap φ₀ φ x) i) ≤ p := by
  intro i
  dsimp only [optionProduct]
  rw [productFinBasis_repr]
  generalize hz : (Fintype.equivFin (Σ i : Option ι, Fin (optionDimension d₀ d i))).symm i = z
  rcases z with ⟨a, k⟩
  cases a with
  | none => exact h₀ k
  | some a => exact hφ a k

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledComparisonModel
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {L K : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing K] [LieAlgebra ℚ K]
  {s t d r : ℕ} (D : RationalFilteredNilmanifold L s d)

include D in
theorem embedding_basis_card_le (b : Basis (Fin r) ℚ K)
    (φ : K →ₗ⁅ℚ⁆ L) (hφ : Function.Injective φ) : r ≤ d := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  have h := LinearMap.finrank_le_finrank_of_injective (f := φ.toLinearMap) hφ
  simpa only [finrank_eq_card_basis b, finrank_eq_card_basis D.basis, Fintype.card_fin] using h

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ComparisonEquivalenceBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem comparisonProductLip_le_exp (c : ℕ) (K L A : ℝ≥0) {p : ℝ} (hp : 0 ≤ p)
    (hc : (c : ℝ) ≤ Real.exp p) (hK : (K : ℝ) ≤ Real.exp p)
    (hL : (L : ℝ) ≤ Real.exp p) (hA : (A : ℝ) ≤ Real.exp p) :
    (comparisonProductLip c K L A p : ℝ) ≤ Real.exp ((p + 3) ^ 2 + 3 * p + 1) := by
  have hleft : (c : ℝ) * K * A ≤ Real.exp (3 * p) := by
    calc
      _ ≤ Real.exp p * Real.exp p * Real.exp p :=
        mul_le_mul (mul_le_mul hc hK K.coe_nonneg (Real.exp_pos _).le) hA
          A.coe_nonneg (by positivity)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hright : (L : ℝ) ≤ Real.exp (3 * p) :=
    hL.trans (Real.exp_le_exp.mpr (by linarith))
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  change (c : ℝ) * K * (A * Real.exp ((p + 3) ^ 2)) + L * Real.exp ((p + 3) ^ 2) ≤ _
  calc
    _ = ((c : ℝ) * K * A + L) * Real.exp ((p + 3) ^ 2) := by ring
    _ ≤ (2 * Real.exp (3 * p)) * Real.exp ((p + 3) ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ ≤ (Real.exp 1 * Real.exp (3 * p)) * Real.exp ((p + 3) ^ 2) := by gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.UniformInvariantBudget
namespace OAI

section

namespace Erdos3

theorem exists_uniform_invariantVertical_cost (M : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (m : ℕ), m ≤ M → ∀ p : ℝ, 0 ≤ p →
      invariantVerticalBudget m p ≤ (p + C) ^ C := by
  let B := (Finset.range (M + 1)).sup symmetricUnitConstant
  let X : Polynomial ℕ := Polynomial.X
  let P := Polynomial.C (2 * M + 2) * (2 * X + 1) + Polynomial.C B + X + Polynomial.C M + 1
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro m hm p hp
  have hb : symmetricUnitConstant m ≤ B := Finset.le_sup (f := symmetricUnitConstant)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
  have hmr : (m : ℝ) ≤ M := by exact_mod_cast hm
  have hbr : (symmetricUnitConstant m : ℝ) ≤ B := by exact_mod_cast hb
  have hle : invariantVerticalBudget m p ≤
      (2 * M + 2 : ℝ) * (2 * p + 1) + B + p + M + 1 := by
    dsimp [invariantVerticalBudget, symmetricUnitBudget]
    nlinarith
  apply hle.trans
  simpa [P, X] using hbound p hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeDilationObservable
namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped BigOperators NNReal

theorem signedTensorProduct_phase (m : ℤ) (v : Fin m.natAbs → ℂ)
    (θ : CircleFourier.Circle) :
    signedTensorProduct m (fun i => character θ * v i) =
      character (m • θ) * signedTensorProduct m v := by
  cases m with
  | ofNat n =>
    have hn : ¬Int.ofNat n < 0 := not_lt.mpr (Int.natCast_nonneg n)
    simp only [signedTensorProduct, if_neg hn, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    change character θ ^ n * (∏ i, v i) = character ((n : ℤ) • θ) * (∏ i, v i)
    rw [natCast_zsmul, character_nsmul]
  | negSucc n =>
    have hn : Int.negSucc n < 0 := by omega
    simp only [signedTensorProduct, if_pos hn, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    change star (character θ ^ (n + 1) * (∏ i, v i)) =
      character (-((n + 1 : ℕ) : ℤ) • θ) * star (∏ i, v i)
    rw [neg_smul, character_neg, natCast_zsmul, character_nsmul, star_mul]
    exact mul_comm _ _

theorem signed_power_phase_cancellation (m : ℤ) (v : ℂ) (w : Fin m.natAbs → ℂ)
    (θ₀ θ₁ : CircleFourier.Circle) (hθ : θ₀ = m • θ₁) :
    (character θ₀ * v) * star (signedTensorProduct m (fun i => character θ₁ * w i)) =
      v * star (signedTensorProduct m w) := by
  rw [signedTensorProduct_phase, hθ, star_mul]
  calc
    _ = (character (m • θ₁) * star (character (m • θ₁))) *
        (v * star (signedTensorProduct m w)) := by ring
    _ = _ := by rw [circle_character_mul_star, one_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymmetricSquarefreeMonotonicity
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def rootTensorEquiv (q t : ℕ) (ht : 1 ≤ t) :
    (Fin q × Fin (q ^ (t - 1))) ≃ Fin (((q : ℤ) ^ t).natAbs) :=
  finProdFinEquiv.trans (finCongr (by
    have h : q * q ^ (t - 1) = q ^ t := by rw [← pow_succ', Nat.sub_add_cancel ht]
    simpa only [Int.natAbs_pow, Int.natAbs_natCast] using h))

noncomputable def rootTensorIndex (d q t : ℕ) (ht : 1 ≤ t)
    (a : Fin q → Fin (d ^ (q ^ (t - 1)))) : Fin (((q : ℤ) ^ t).natAbs) → Fin d :=
  fun k => (tensorIndexEquiv d (q ^ (t - 1))).symm
    (a ((rootTensorEquiv q t ht).symm k).1) ((rootTensorEquiv q t ht).symm k).2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalTagConstraintChartBasis
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {B I : Type*} [Fintype B]
  (U : Submodule ℚ (B → ℚ)) (b : Basis I ℚ U)

theorem realRationalCoordinateSpan_basis :
    Submodule.span ℝ (Set.range (fun i j => ((b i : B → ℚ) j : ℝ))) =
      realRationalCoordinateSpan U := by
  have hb : Submodule.span ℚ (Set.range (fun i => (b i : B → ℚ))) = U := by
    change Submodule.span ℚ (Set.range (U.subtype ∘ b)) = U
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq,
      Submodule.map_top, Submodule.range_subtype]
  exact (realRationalCoordinateSpan_span (fun i => (b i : B → ℚ))).symm.trans
    (congrArg realRationalCoordinateSpan hb)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module

variable {m : ℕ} {J : Fin m → Type*}

theorem RationalTaggedConstraintCertificate.exists_bounded_chart_tag_basis {X : Type*}
    [∀ j, Fintype (J j)]
    {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {p : ℝ} {Cblocks : ℕ}
    (hcert : RationalTaggedConstraintCertificate J Set.univ K p Cblocks)
    (hp : 0 ≤ p) (hdim : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hblocks : (Cblocks : ℝ) ≤ p) :
    ∃ (n : Fin m → ℕ) (Ktag : Submodule ℝ ((Σ j, J j) → ℝ))
      (b : Basis (Σ j, Fin (n j)) ℝ Ktag)
      (matrix : (Σ j, Fin (n j)) → (Σ j, J j) → ℚ),
      (∀ j, n j ≤ Fintype.card (J j)) ∧
      (∀ a x, (b a : (Σ j, J j) → ℝ) x = (matrix a x : ℝ)) ∧
      (∀ a x, x.1 ≠ a.1 → matrix a x = 0) ∧
      (∀ a x, rationalLogHeight (matrix a x) ≤ ((p + 2) ^ 2 + 2) ^ 63) ∧
      K = {point | (fun x => point (Sum.inr x)) ∈ Ktag} ∧
      ∀ (U : ∀ j, Submodule ℝ (J j → ℝ)),
        (∀ point, (∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈ U j) → point ∈ K) →
        ∀ v : (Σ j, J j) → ℝ, (∀ j, (fun i => v ⟨j, i⟩) ∈ U j) → v ∈ Ktag := by
  classical
  obtain ⟨W, n, b, hn, hb, hK⟩ := hcert.exists_bounded_tag_bases_univ hp hdim hblocks
  let R := fun j => realRationalCoordinateSpan (W j)
  let br := fun j => rationalCoordinateRealBasis (W j) (b j)
  let Ktag := taggedSubmodule R
  let basis : Basis (Σ j, Fin (n j)) ℝ Ktag := taggedSubmoduleBasis R br
  let matrix := rationalTagChartMatrix W n b
  have hentry (a : Σ j, Fin (n j)) (x : Σ j, J j) :
      (basis a : (Σ j, J j) → ℝ) x = (matrix a x : ℝ) := by
    rcases a with ⟨j, a⟩
    rcases x with ⟨k, i⟩
    by_cases h : k = j
    · subst k
      change ((taggedSubmoduleBasis R br ⟨j, a⟩ : (Σ j, J j) → ℝ) ⟨j, i⟩) = _
      rw [taggedSubmoduleBasis_same]
      dsimp only [matrix]
      rw [rationalTagChartMatrix_same]
      exact rationalCoordinateRealBasis_apply (W j) (b j) a i
    · rw [show (basis ⟨j, a⟩ : (Σ j, J j) → ℝ) ⟨k, i⟩ = 0 from
        taggedSubmoduleBasis_of_ne R br j a k i h]
      rw [show matrix ⟨j, a⟩ ⟨k, i⟩ = 0 from
        rationalTagChartMatrix_of_ne W n b ⟨j, a⟩ ⟨k, i⟩ h, Rat.cast_zero]
  have htag : K = {point | (fun x => point (Sum.inr x)) ∈ Ktag} := by
    rw [hK]
    ext point
    change (∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈
      Submodule.span ℝ (Set.range (fun a i => ((b j a : J j → ℚ) i : ℝ)))) ↔
      ∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈ realRationalCoordinateSpan (W j)
    simp_rw [realRationalCoordinateSpan_basis]
  refine ⟨n, Ktag, basis, matrix, hn, hentry,
    rationalTagChartMatrix_of_ne W n b,
    rationalTagChartMatrix_height W n b (by positivity) hb, htag, ?_⟩
  intro U hret v hv
  have hpoint := hret (Sum.elim (fun _ : X => (0 : ℝ)) v) (by simpa using hv)
  simpa only [htag, Set.mem_ofPred_eq, Sum.elim_inr] using hpoint

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowTaggedGradedSpace
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

noncomputable def lowTaggedSubspaceFamily (d : ℕ)
    (K : Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ))
    (j : Fin m) : Submodule ℝ (J j → ℝ) :=
  if hj : j.val + 1 ≤ d then K.comap (lowTaggedEmbedding J d j hj) else ⊤

theorem mem_lowTaggedSubspaceFamily_iff (d : ℕ)
    (K : Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ))
    (j : Fin m) (hj : j.val + 1 ≤ d) (x : J j → ℝ) :
    x ∈ lowTaggedSubspaceFamily J d K j ↔ lowTaggedEmbedding J d j hj x ∈ K := by
  simp only [lowTaggedSubspaceFamily, dif_pos hj, Submodule.mem_comap]

theorem lowTaggedCoordinates_mem_iff (d : ℕ)
    (K : Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ))
    (hK : BasisGradedSubmodule (Pi.basisFun ℝ _) (lowTaggedWeight J d) K)
    (x : ∀ j, J j → ℝ) :
    lowTaggedCoordinates J d x ∈ K ↔ ∀ j, x j ∈ lowTaggedSubspaceFamily J d K j := by
  constructor
  · intro hx j
    by_cases hj : j.val + 1 ≤ d
    · rw [mem_lowTaggedSubspaceFamily_iff J d K j hj]
      rw [← lowTaggedCoordinates_projection J d x j hj]
      exact hK (j.val + 1) _ hx
    · simp only [lowTaggedSubspaceFamily, dif_neg hj, Submodule.mem_top]
  · intro hx
    rw [← sum_positive_coordinate_grades (lowTaggedWeight J d) d
      (lowTaggedWeight_pos J d) (lowTaggedWeight_le J d) (lowTaggedCoordinates J d x)]
    apply Submodule.sum_mem
    intro h _
    by_cases hm : h.val < m
    · let j : Fin m := ⟨h.val, hm⟩
      have hj : j.val + 1 ≤ d := by exact Nat.succ_le_of_lt h.isLt
      have hjmem := (mem_lowTaggedSubspaceFamily_iff J d K j hj (x j)).mp (hx j)
      rw [lowTaggedCoordinates_projection J d x j hj]
      exact hjmem
    · rw [lowTaggedCoordinates_projection_eq_zero J d x h.val (Nat.le_of_not_gt hm)]
      exact K.zero_mem

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMeanRowCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

theorem exists_mean_row_weighted_term {H X I : Type*} [Fintype H] [Fintype X] [Fintype I]
    (c : I → ℂ) (F : I → H → X → ℂ) {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 < M)
    (hcost : ∑ i, ‖c i‖ ≤ M) (hmass : ρ ≤ 𝔼 h, ‖𝔼 x, ∑ i, c i * F i h x‖) :
    ∃ i, ρ / M ≤ 𝔼 h, ‖𝔼 x, F i h x‖ :=
  exists_large_nonnegative_weighted_term (fun i => ‖c i‖) (fun i => 𝔼 h, ‖𝔼 x, F i h x‖)
    (fun _ => norm_nonneg _) (fun _ => Finset.expect_nonneg (fun _ _ => norm_nonneg _))
    hρ hM hcost (hmass.trans (mean_row_weighted_sum_norm_le c F))

namespace NativeIntegerExpansion

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem select_mean_row_correlation {σ H X : Type*} [Fintype H] [Fintype X]
    {w : σ → ℕ} {s : ℕ} {p : ℝ} {g : (σ → ℤ) → ℂ}
    (E : NativeIntegerExpansion w s p g) (sample : H → X → σ → ℤ) (f : H → X → ℂ)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hmass : ρ ≤ 𝔼 h, ‖𝔼 x, f h x * star (g (sample h x))‖) :
    ∃ i : Fin E.count, ρ / Real.exp p ≤
      𝔼 h, ‖𝔼 x, f h x * star ((E.test i).eval (sample h x))‖ := by
  let F (i : Fin E.count) (h : H) (x : X) := f h x * star ((E.test i).eval (sample h x))
  have heq (h : H) (x : X) : f h x * star (g (sample h x)) =
      ∑ i, star (E.coefficient i) * F i h x := by
    rw [E.eval, star_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [F, star_mul]
    ring
  simp only [heq] at hmass
  exact exists_mean_row_weighted_term (fun i => star (E.coefficient i)) F hρ (Real.exp_pos _)
    (by simpa only [norm_star] using E.cost) hmass

end NativeIntegerExpansion
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_large_value_of_mean_row_correlation {H X : Type*}
    [Fintype H] [Nonempty H] [Fintype X] [Nonempty X]
    (f g : H → X → ℂ) (hf : ∀ h x, ‖f h x‖ ≤ 1) {ρ : ℝ}
    (hcorr : ρ ≤ 𝔼 h, ‖𝔼 x, f h x * star (g h x)‖) :
    ∃ h x, ρ ≤ ‖g h x‖ := by
  have hb : ρ ≤ 𝔼 h, 𝔼 x, ‖g h x‖ := by
    apply hcorr.trans
    apply Finset.expect_le_expect
    intro h _
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le_expect
    intro x _
    rw [norm_mul, norm_star]
    exact mul_le_of_le_one_left (norm_nonneg _) (hf h x)
  obtain ⟨h, _, hh⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hb
  obtain ⟨x, _, hx⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hh
  exact ⟨h, x, hx⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeMeanRowCorrelation.lie NativeMeanRowCorrelation.algebra
  NativeMeanRowCorrelation.topology NativeMeanRowCorrelation.topologicalAdd
  NativeMeanRowCorrelation.continuousSMul NativeMeanRowCorrelation.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeMeanRowCorrelation

variable {σ H X : Type*} [Fintype H] [Fintype X] {w : σ → ℕ} {s : ℕ} {p q : ℝ}
  {sample : H → X → σ → ℤ} {f : H → X → ℂ}

noncomputable def mono (V : NativeMeanRowCorrelation w s p sample f) (hpq : p ≤ q) :
    NativeMeanRowCorrelation w s q sample f :=
  { V with
    complexity := V.complexity.mono hpq
    correlation := (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans V.correlation }

theorem exists_of_expansion {g : (σ → ℤ) → ℂ}
    (E : NativeIntegerExpansion w s p g) (hq : 0 ≤ q)
    (hcorr : Real.exp (-q) ≤ 𝔼 h, ‖𝔼 x, f h x * star (g (sample h x))‖) :
    Nonempty (NativeMeanRowCorrelation w s (q + p) sample f) := by
  obtain ⟨i, hi⟩ := E.select_mean_row_correlation sample f (Real.exp_pos _) hcorr
  refine ⟨{
    L := E.L i
    dim := E.dim i
    model := E.model i
    test := E.test i
    complexity := (E.complexity i).mono (le_add_of_nonneg_left hq)
    correlation := ?_ }⟩
  have heq : Real.exp (-q) / Real.exp p = Real.exp (-(q + p)) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  rwa [heq] at hi

end NativeMeanRowCorrelation
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeIntegerEquivalenceFiniteFamily
namespace OAI

section

namespace Erdos3.NativeIntegerVectorEquivalence

open scoped BigOperators

theorem conjugationPower {σ I J : Type*} [Fintype I] [Fintype J] {s : ℕ} {p : ℝ}
    {f : I → (σ → ℤ) → ℂ} {g : J → (σ → ℤ) → ℂ}
    (E : NativeIntegerVectorEquivalence s p f g) (n : ℕ) :
    NativeIntegerVectorEquivalence s p
      (fun i x => Erdos3.conjugationPower n (f i x))
      (fun j x => Erdos3.conjugationPower n (g j x)) := by
  induction n with
  | zero => exact E
  | succ n ih => exact ih.conjugate

end Erdos3.NativeIntegerVectorEquivalence

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitVerticalMeanRowCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem cyclicDivision_with_residue_injective (d : ℕ) [NeZero d] {N : ℕ} [NeZero N] :
    Function.Injective (fun x : ZMod N => (cyclicDivision d x, (x.val : ZMod d))) := by
  intro x y h
  have hq := congrArg (fun z : ZMod N × ZMod d => z.1.val) h
  have hr := congrArg (fun z : ZMod N × ZMod d => z.2.val) h
  simp only [cyclicDivision_val] at hq
  simp only [ZMod.val_natCast] at hr
  apply ZMod.val_injective
  have hx := Nat.mod_add_div x.val d
  have hy := Nat.mod_add_div y.val d
  rw [hq, hr] at hx
  exact hx.symm.trans hy

theorem expect_cyclicDivision_le (d : ℕ) [NeZero d] {N : ℕ} [NeZero N] (f : ZMod N → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    (𝔼 x : ZMod N, f (cyclicDivision d x)) ≤ d * (𝔼 x : ZMod N, f x) := by
  classical
  have hs : (∑ x : ZMod N, f (cyclicDivision d x)) ≤ ∑ z : ZMod N × ZMod d, f z.1 := by
    apply Finset.sum_le_sum_of_injOn (fun x : ZMod N => (cyclicDivision d x, (x.val : ZMod d)))
      (cyclicDivision_with_residue_injective d).injOn
    · exact Finset.subset_univ _
    · intro x _
      exact le_rfl
    · intro a _ _
      exact hf a.1
  have ht : (∑ z : ZMod N × ZMod d, f z.1) = d * ∑ x : ZMod N, f x := by
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul, ← Finset.mul_sum]
  rw [ht] at hs
  simp only [Fintype.expect_eq_sum_div_card, ZMod.card]
  calc
    _ ≤ (d * ∑ x : ZMod N, f x) / N := div_le_div_of_nonneg_right hs (Nat.cast_nonneg _)
    _ = _ := by ring

theorem expect_pair_cyclicDivision_le (d : ℕ) [NeZero d] {N : ℕ} [NeZero N]
    (f : (Fin 2 → ZMod N) → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (𝔼 x : Fin 2 → ZMod N, f (fun i => cyclicDivision d (x i))) ≤
      (d : ℝ) ^ 2 * (𝔼 x : Fin 2 → ZMod N, f x) := by
  rw [expect_fin_two, expect_fin_two]
  have heq (h n : ZMod N) : (fun i => cyclicDivision d (![h, n] i)) =
      ![cyclicDivision d h, cyclicDivision d n] := by
    funext i
    fin_cases i <;> rfl
  simp only [heq]
  calc
    _ ≤ 𝔼 h : ZMod N, d * (𝔼 n : ZMod N, f ![cyclicDivision d h, n]) := by
      apply Finset.expect_le_expect
      intro h _
      exact expect_cyclicDivision_le d (fun n => f ![cyclicDivision d h, n]) (fun n => hf _)
    _ = d * (𝔼 h : ZMod N, 𝔼 n : ZMod N, f ![cyclicDivision d h, n]) := by
      rw [← Finset.mul_expect]
    _ ≤ d * (d * (𝔼 h : ZMod N, 𝔼 n : ZMod N, f ![h, n])) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
      exact expect_cyclicDivision_le d (fun h => 𝔼 n : ZMod N, f ![h, n])
        (fun h => Finset.expect_nonneg (fun n _ => hf _))
    _ = _ := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestOrbitOne
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def oneOnOrbit (T : D.Niltest w) : D.Niltest w where
  orbit := T.orbit
  observable := fun _ => 1
  normBound := 1
  lipBound := 0
  norm_le _ := by simp
  lipschitz := by
    let := D.metricSpace
    exact LipschitzWith.const 1

theorem oneOnOrbit_eval (T : D.Niltest w) (x : σ → ℤ) : T.oneOnOrbit.eval x = 1 := rfl

theorem oneOnOrbit_complexity (T : D.Niltest w) {p : ℝ} (hp : 2 ≤ p)
    (hD : D.GeometryComplexityLE p) : T.oneOnOrbit.ComplexityLE p := by
  refine ⟨hD, ?_⟩
  change Real.log (2 + 1 + 0) ≤ p
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
  norm_num at h ⊢
  linarith

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSubspaceFreeModel
namespace OAI

section

namespace Erdos3.SubspaceFreeLift

open Module VectorPolynomial
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (S : Fin s → Submodule ℚ L)

noncomputable def generator (r : ℕ) (x : Alphabet S) : Algebra S r :=
  FreeDegreeRankLieAlgebra.of (Alphabet S) s r (weight S) (weight_pos S) x

variable (B : ∀ d, Basis (Fin (finrank ℚ (S d))) ℚ (S d))

noncomputable def coefficientLift (r : ℕ) (d : Fin s) : S d →ₗ[ℚ] Algebra S r :=
  (B d).constr ℚ (fun i => generator S r ⟨d, i⟩)

variable (F : DegreeRankLieFiltration L s r)
  (hS : ∀ d, S d ≤ F.layer (d.val + 1) 0)

noncomputable def realCoefficientLift (d : Fin s) :
    (S d).baseChange ℝ →ₗ[ℝ] ℝ ⊗[ℚ] Algebra S r :=
  ((coefficientLift S B r d).baseChange ℝ).comp
    (realificationSubmoduleEquiv (S d)).symm.toLinearMap

theorem realCoefficientLift_baseChange (d : Fin s) (x : ℝ ⊗[ℚ] S d) :
    realCoefficientLift S B (r := r) d (realificationSubmoduleEquiv _ x) =
      (coefficientLift S B r d).baseChange ℝ x :=
  congrArg ((coefficientLift S B r d).baseChange ℝ)
    ((realificationSubmoduleEquiv _).symm_apply_apply x)

end Erdos3.SubspaceFreeLift

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SharedFreeAffineBudget
namespace OAI

section

namespace Erdos3

open CyclicCrootSisask

theorem sharedFreeAffineConstant_two_le (s : ℕ) : 2 ≤ sharedFreeAffineConstant s := by
  have h := (exists_sharedFreeAffineUniform_bound s).choose_spec.1
  unfold sharedFreeAffineConstant
  omega

theorem sharedFreeAffineConstant_shift_bound (s : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (c : ℕ) (hc : c ≤ sharedFreeAffineConstant s) :
    (p + c) ^ c ≤ (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s := by
  have hcR : (c : ℝ) ≤ sharedFreeAffineConstant s := by exact_mod_cast hc
  have hCR : (2 : ℝ) ≤ sharedFreeAffineConstant s := by
    exact_mod_cast sharedFreeAffineConstant_two_le s
  exact (pow_le_pow_left₀ (by positivity)
    (by linarith : p + c ≤ p + sharedFreeAffineConstant s) c).trans
    (pow_le_pow_right₀ (by linarith : 1 ≤ p + sharedFreeAffineConstant s) hc)

theorem sharedFreeAffineConstant_spec (s : ℕ) :
    2 ≤ sharedFreeAffineConstant s ∧
      ∀ q p : ℝ, 0 ≤ q → q ≤ p → 0 ≤ p →
        ∀ n : ℕ, (n : ℝ) ≤ 4 * (s : ℝ) * p →
          sharedFreeRecoveryThreshold s q p ≤ (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s ∧
          affineRecoveryLogLoss ((p + 2) ^ 3 + 2 * p) n ≤
            (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s ∧
          2 + quarticBogolyubovConstant *
            (roundedModelLogBudget ((p + 2) ^ 3 + 2 * p) n + 1) ^ 4 ≤
              (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s := by
  refine ⟨sharedFreeAffineConstant_two_le s, ?_⟩
  intro q p hq hqp hp n hn
  have h := (exists_sharedFreeAffineUniform_bound s).choose_spec.2 q p hq hqp hp n hn
  have hb := sharedFreeAffineConstant_shift_bound s hp
    (exists_sharedFreeAffineUniform_bound s).choose (by unfold sharedFreeAffineConstant; omega)
  exact ⟨h.1.trans hb, h.2.1.trans hb, h.2.2.trans hb⟩

theorem sharedFreeAffineConstant_proper_spec (s : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (n : ℕ) (hn : (n : ℝ) ≤ 4 * (s : ℝ) * p) :
    properAffineRecoveryLogLoss ((p + 2) ^ 3 + 2 * p) n ≤
      (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s ∧
    properAffineScaleLog ((p + 2) ^ 3 + 2 * p) n ≤
      (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s ∧
    properAffineRankBound ((p + 2) ^ 3 + 2 * p) n ≤
      (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s := by
  have h := (exists_sharedFreeProperAffineSelection_bound s).choose_spec.2 p hp n hn
  have hb := sharedFreeAffineConstant_shift_bound s hp
    (exists_sharedFreeProperAffineSelection_bound s).choose (by unfold sharedFreeAffineConstant; omega)
  exact ⟨h.1.trans hb, h.2.1.trans hb, h.2.2.trans hb⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteForwardFixedCenterThreshold
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

@[simp] theorem candidateNestedForwardSeed_zero (A : ℕ) (constants : ℕ → ℕ)
    (innerDepth : ℕ) (x : ℝ) : candidateNestedForwardSeed A constants innerDepth 0 x = x := by
  simp [candidateNestedForwardSeed, candidateNestedForwardSeedPolynomial]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CertifiedChartBasisBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module

theorem RationalTaggedConstraintCertificate.exists_certified_chart_basis_budget
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)] {X : Type*}
    {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {p : ℝ} {Cblocks : ℕ}
    (hcert : RationalTaggedConstraintCertificate J Set.univ K p Cblocks)
    (hp : 0 ≤ p) (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hblocks : (Cblocks : ℝ) ≤ p) :
    ∃ (n : Fin m → ℕ) (Ktag : Submodule ℝ ((Σ j, J j) → ℝ))
      (b : Basis (Σ j, Fin (n j)) ℝ Ktag)
      (matrix : (Σ j, Fin (n j)) → (Σ j, J j) → ℚ) (d : ℕ),
      (∀ j, n j ≤ Fintype.card (J j)) ∧
      Fintype.card (Σ j, Fin (n j)) ≤ Fintype.card (Σ j, J j) ∧
      (∀ a x, (b a : (Σ j, J j) → ℝ) x = (matrix a x : ℝ)) ∧
      (∀ a x, x.1 ≠ a.1 → matrix a x = 0) ∧
      (∀ a x, rationalLogHeight (matrix a x) ≤ ((p + 2) ^ 2 + 2) ^ 63) ∧
      (∀ a x, RationalHeightLE (matrix a x) ⌈Real.exp (((p + 2) ^ 2 + 2) ^ 63)⌉₊) ∧
      (∀ a x, |(b a : (Σ j, J j) → ℝ) x| ≤ Real.exp (((p + 2) ^ 2 + 2) ^ 63)) ∧
      d = matrixDenominator matrix ∧ 0 < d ∧
      (d : ℝ) ≤ Real.exp ((p + 2) ^ 254) ∧
      (∀ a x, ∃ z : ℤ, (z : ℝ) = (d : ℝ) * (b a : (Σ j, J j) → ℝ) x) ∧
      K = {point | (fun x => point (Sum.inr x)) ∈ Ktag} ∧
      ∀ (U : ∀ j, Submodule ℝ (J j → ℝ)),
        (∀ point, (∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈ U j) → point ∈ K) →
        ∀ v : (Σ j, J j) → ℝ, (∀ j, (fun i => v ⟨j, i⟩) ∈ U j) → v ∈ Ktag := by
  classical
  have hdimTag (j : Fin m) : (Fintype.card (J j) : ℝ) ≤ p := by
    have hcard : Fintype.card (J j) ≤ Fintype.card (Σ j, J j) :=
      Fintype.card_le_of_injective (fun i => (⟨j, i⟩ : Σ j, J j)) sigma_mk_injective
    exact (Nat.cast_le.mpr hcard).trans hdim
  obtain ⟨n, Ktag, b, matrix, hn, hentry, hofftag, hheight, hK, hret⟩ :=
    hcert.exists_bounded_chart_tag_basis hp hdimTag hblocks
  have hcard : Fintype.card (Σ j, Fin (n j)) ≤ Fintype.card (Σ j, J j) := by
    simp only [Fintype.card_sigma, Fintype.card_fin]
    exact Finset.sum_le_sum (fun j _ => hn j)
  obtain ⟨habs, hdpos, hdbound, hgrid⟩ := certifiedChartMatrix_budget matrix hp
    ((Nat.cast_le.mpr hcard).trans hdim) hdim hheight
  refine ⟨n, Ktag, b, matrix, matrixDenominator matrix, hn, hcard, hentry,
    hofftag, hheight, fun a x => rationalHeightLE_ceil_exp (hheight a x),
    ?_, rfl, hdpos, hdbound, ?_, hK, hret⟩
  · intro a x
    rw [hentry]
    exact habs a x
  · intro a x
    rw [hentry]
    exact hgrid a x

end Erdos3.VectorPolynomial

end

end OAI
end


