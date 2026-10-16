-- Prove2me | Definitions.Def_OAIErdos3B1333
-- name    : OAIErdos3B1333
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-15T18:49:23.4855+00:00
-- url     : https://prove2.me/theorems/22914009-a466-4bd1-86be-538df36dfffb
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1334 of 1340
-- statement:
--   Definitions bundle 1334 of 1340 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1332`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1334 available.
--
--   Modules: `OAI.Erdos3.NilpotentLieBCHGroup.realPolynomialChartSubstitution_truncate_of_degreeLE`, `OAI.Erdos3.NilpotentLieFiltration.FullChartControlledFactors`, `OAI.Erdos3.NilpotentLieFiltration.FullChartControlledFactors.exists_degree_bounded_chart`, `OAI.Erdos3.NilpotentLieFiltration.FullChartControlledFactors.exists_graded_degree_bounded_chart`, `OAI.Erdos3.NilpotentLieFiltration.FullChartControlledFactors.exists_inhomogeneous_left_lift`, `OAI.Erdos3.NilpotentLieFiltration.FullChartControlledFactors.mono`, `OAI.Erdos3.NilpotentLieFiltration.FullChartMajorCorrelation`, `OAI.Erdos3.NilpotentLieFiltration.coefficientBound_gradedBasisSplitting`, `OAI.Erdos3.NilpotentLieFiltration.coefficients_gradedPolynomialProjection`, `OAI.Erdos3.NilpotentLieFiltration.exists_inhomogeneous_chart_lift_algebraic`, `OAI.Erdos3.NilpotentLieFiltration.gradedPolynomialProjection`, `OAI.Erdos3.NilpotentLieFiltration.gradedPolynomialProjection_coefficientBound`, `OAI.Erdos3.NilpotentLieFiltration.gradedPolynomialProjection_degreeLE`, `OAI.Erdos3.NilpotentLieFiltration.gradedPolynomialProjection_eq_self`, `OAI.Erdos3.NilpotentLieFiltration.gradedPolynomialProjection_mem`, `OAI.Erdos3.NilpotentLieFiltration.gradedPolynomialProjection_realChartSubstitute`, `OAI.Erdos3.NilpotentLieFiltration.polynomialSlowBound_inhomogeneous_chart_lift`, `OAI.Erdos3.NilpotentLieFiltration.realGradedSymbolPolynomialHom_degreeLE`, `OAI.Erdos3.NilpotentLieFiltration.realSymbolOfGradedPolynomial_homogeneousChart`, `OAI.Erdos3.VectorPolynomial.CoefficientBound.realChartSubstitute_sharp`, `OAI.Erdos3.VectorPolynomial.CoefficientBound.weightedDegreeTruncate`, `OAI.Erdos3.VectorPolynomial.coefficients_weightedDegreeTruncate`, `OAI.Erdos3.VectorPolynomial.degreeLE_one_weightedDegreeTruncate`, `OAI.Erdos3.VectorPolynomial.degreeLE_weightedDegreeTruncate`, `OAI.Erdos3.VectorPolynomial.realChartSubstitute_weightedDegreeTruncate`, `OAI.Erdos3.VectorPolynomial.weightedDegreeTruncate`, `OAI.Erdos3.VectorPolynomial.weightedDegreeTruncate_eq_self`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B210

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CertifiedFullChartDecompositionSource
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators

def FullChartMajorCorrelation
    {m : ℕ} {X L M ι η : Type} [Fintype X] [DecidableEq X] [Fintype η]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s t e : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (D : RationalFilteredNilmanifold M t e)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (p Rrank : ℝ) (C : ℕ) : Prop :=
  ∃ (periodCap coverCap : ℝ) (Lip : ℝ≥0)
    (W : η → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    (R : η → D.Niltest (fun _ : X => 1))
    (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J k)))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J k)) → ℤ),
    (∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j)) ∧
    (∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j) ∧
    (∀ u ∈ integerBox N, ∀ i,
      |MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J k poly i) -
        c i - (β u i : ℝ)| ≤ 1 / 2) ∧
    0 ≤ p ∧ (∀ j, (R j).ComplexityLE p) ∧
    (∀ j, ((R j).normBound : ℝ) ≤ 1) ∧
    ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ p ∧
    (∀ j, ((W j).modulus : ℝ) ≤ Real.exp p) ∧
    (∀ j, ((W j).cover : ℝ) ≤ Real.exp p) ∧
    (Lip : ℝ) ≤ Real.exp p ∧ (Ψ.lip : ℝ) ≤ Real.exp p ∧
    (∀ i, Real.exp ((p + C) ^ C) ≤ (N i : ℝ)) ∧
    Real.exp ((p + C) ^ C) ≤ Rrank ∧
    (∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j)) ∧
    (∀ j, Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N,
      (W j).eval N poly u * majorPhaseSample J k poly Ψ c
        (coordinate (basis.coord j).toAddMonoidHom
          (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
            (fullTaggedVariableWeight (X := X) J) fast k (left⁻¹ * Z * right⁻¹).coord))) β (R j).eval u‖)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

def FullChartControlledFactors
    {m : ℕ} {X L ι : Type} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
    (left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (budget : ℝ) : Prop :=
  ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp budget ∧
    ∃ Echart : PolynomialGroup (X ⊕ (Σ j, J j))
        F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot,
      F.realGradedSymbolPolynomialHom b ω hF (fullTaggedVariableWeight (X := X) J) left =
        realPolynomialChartSubstitution
          F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot
          (normalizedRealPolynomialChart (fun i => (N i : ℝ))
            (fullTaggedMajorTopCoordinates J poly)) Echart ∧
      CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) (fun _ => 1)
        (Real.exp budget) Echart.coord ∧
      CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ) q
        (F.realGradedSymbolPolynomialHom b ω hF
          (fullTaggedVariableWeight (X := X) J) right).coord

theorem FullChartControlledFactors.mono
    {m : ℕ} {X L ι : Type} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
    (left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    {budget budget' : ℝ} (h : FullChartControlledFactors F b ω hF J poly N left right budget)
    (hle : budget ≤ budget') :
    FullChartControlledFactors F b ω hF J poly N left right budget' := by
  obtain ⟨q, hq, hqB, Echart, hchart, hslow, hgrid⟩ := h
  refine ⟨q, hq, hqB.trans (Real.exp_le_exp.mpr hle), Echart, hchart, ?_, hgrid⟩
  exact CoefficientBound.mono _ _ (fun _ => zero_lt_one) hslow (Real.exp_le_exp.mpr hle)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FullChartPolynomialLiftControl
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module

variable {σ τ ι V : Type*}

theorem CoefficientBound.realChartSubstitute_sharp [Fintype σ]
    [LieRing V] [LieAlgebra ℚ V] [LieAlgebra ℝ V] [IsScalarTower ℚ ℝ V]
    (b : Basis ι ℝ V) (T : τ → ℝ) (hT : ∀ i, 0 < T i)
    (f : σ → MvPolynomial τ ℝ) {A B : ℝ} {s : ℕ} {P : VectorPolynomial σ ℚ V}
    (hP : CoefficientBound b (fun _ => 1) A P) (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hdegree : DegreeLE (fun _ : σ => 1) s P)
    (hf : ∀ i, realPolynomialMass (scaleMvPolynomialAxes T (f i)) ≤ B) :
    CoefficientBound b T
      (((Fintype.card σ : ℝ) + 1) ^ s * A * B ^ s)
      (Erdos3.VectorPolynomial.realChartSubstitute f P) := by
  intro α i
  let Q := coordinate (b.coord i).toAddMonoidHom P
  have hQdeg : Q.totalDegree ≤ s :=
    (degreeLE_one_iff_basis_totalDegree b s P).mp hdegree i
  have hQcoeff (β) : |Q.coeff β| ≤ A := by
    change |b.repr (coefficients P β) i| ≤ A
    simpa [monomialScale] using hP β i
  have hcard : (Q.support.card : ℝ) ≤ ((Fintype.card σ : ℝ) + 1) ^ s := by
    exact_mod_cast mvPolynomial_support_card_le_totalDegree Q hQdeg
  have hbound := scaled_substitution_coeff_bound T hT f Q hB hf hQcoeff hQdeg α
  have heq := congrArg (fun q : MvPolynomial τ ℝ => q.coeff α)
    (coordinate_realChartSubstitute (b.coord i) f P)
  rw [coeff_coordinate] at heq
  change (b.coord i)
    (coefficients (Erdos3.VectorPolynomial.realChartSubstitute f P) α) = _ at heq
  change |(b.coord i)
    (coefficients (Erdos3.VectorPolynomial.realChartSubstitute f P) α)| ≤ _
  rw [heq]
  apply hbound.trans
  apply div_le_div_of_nonneg_right _ (monomialScale_pos T hT α).le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hA)
    (pow_nonneg (zero_le_one.trans hB) s)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators

variable {σ τ R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

noncomputable def weightedDegreeTruncate (w : σ → ℕ) (d : ℕ)
    (p : VectorPolynomial σ R V) : VectorPolynomial σ R V :=
  ∑ j ∈ Finset.range (d + 1), weightedHomogeneousPart w j p

theorem coefficients_weightedDegreeTruncate (w : σ → ℕ) (d : ℕ)
    (p : VectorPolynomial σ R V) (α : σ →₀ ℕ) :
    coefficients (weightedDegreeTruncate w d p) α =
      if Finsupp.weight w α ≤ d then coefficients p α else 0 := by
  classical
  simp [weightedDegreeTruncate, coefficients_weightedHomogeneousPart]

theorem degreeLE_weightedDegreeTruncate (w : σ → ℕ) (d : ℕ)
    (p : VectorPolynomial σ R V) : DegreeLE w d (weightedDegreeTruncate w d p) := by
  intro α hα
  rw [coefficients_weightedDegreeTruncate, if_neg (not_le_of_gt hα)]

theorem weightedDegreeTruncate_eq_self (w : σ → ℕ) (d : ℕ)
    (p : VectorPolynomial σ R V) (hp : DegreeLE w d p) :
    weightedDegreeTruncate w d p = p := by
  classical
  apply coefficients.injective
  ext α
  rw [coefficients_weightedDegreeTruncate]
  split_ifs with h
  · rfl
  · exact (hp α (lt_of_not_ge h)).symm

theorem degreeLE_one_weightedDegreeTruncate (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (d : ℕ) (p : VectorPolynomial σ R V) :
    DegreeLE (fun _ => 1) d (weightedDegreeTruncate w d p) := by
  intro α hα
  apply degreeLE_weightedDegreeTruncate w d p α
  have h := exponentSum_le_positive_weight w hw α
  have he : Finsupp.weight (fun _ : σ => 1) α = α.sum (fun _ n => n) := by
    simp [Finsupp.weight_apply]
  rw [he] at hα
  exact hα.trans_le h

section Real
variable {W : Type*} [AddCommGroup W] [Module ℚ W] [Module ℝ W] [IsScalarTower ℚ ℝ W]

theorem realChartSubstitute_weightedDegreeTruncate (w : σ → ℕ) (v : τ → ℕ)
    (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ i, (f i).IsWeightedHomogeneous v (w i))
    (d : ℕ) (p : VectorPolynomial σ ℚ W) :
    realChartSubstitute f (weightedDegreeTruncate w d p) =
      weightedDegreeTruncate v d (realChartSubstitute f p) := by
  simp only [weightedDegreeTruncate, map_sum,
    realChartSubstitute_weightedHomogeneousPart w v f hf]
end Real

section Bounds
variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]

theorem CoefficientBound.weightedDegreeTruncate (b : Basis ι ℝ L)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    {p : VectorPolynomial σ ℚ L} (hp : CoefficientBound b T M p)
    (w : σ → ℕ) (d : ℕ) : CoefficientBound b T M (weightedDegreeTruncate w d p) := by
  intro α i
  rw [coefficients_weightedDegreeTruncate]
  split_ifs
  · exact hp α i
  · simp only [map_zero, Finsupp.zero_apply, abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT α).le
end Bounds

end Erdos3.VectorPolynomial

namespace Erdos3.NilpotentLieBCHGroup

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] {s : ℕ}

attribute [local irreducible] realChartSubstitute

theorem realPolynomialChartSubstitution_truncate_of_degreeLE
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (w : σ → ℕ)
    (f : σ → MvPolynomial σ ℝ) (hf : ∀ i, (f i).IsWeightedHomogeneous w (w i))
    (d : ℕ) (g E : PolynomialGroup σ hnil)
    (heq : g = realPolynomialChartSubstitution hnil f E) (hg : DegreeLE w d g.coord) :
    g = realPolynomialChartSubstitution hnil f ⟨weightedDegreeTruncate w d E.coord⟩ := by
  apply NilpotentLieBCHGroup.ext
  rw [realPolynomialChartSubstitution_coord]
  have he := congrArg NilpotentLieBCHGroup.coord heq
  rw [realPolynomialChartSubstitution_coord] at he
  have ht := weightedDegreeTruncate_eq_self w d g.coord hg
  have hc := realChartSubstitute_weightedDegreeTruncate w w f hf d E.coord
  exact ht.symm.trans ((congrArg (weightedDegreeTruncate w d) he).trans hc.symm)

end Erdos3.NilpotentLieBCHGroup

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

theorem realGradedSymbolPolynomialHom_degreeLE
    {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (left : F.RealPolynomialSymbolGroup w) :
    DegreeLE w s (F.realGradedSymbolPolynomialHom b ω hF w left).coord := by
  intro α hα
  apply ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr.injective
  ext i
  rw [map_zero, Finsupp.zero_apply]
  exact F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w left.coord α i (by
    have hi := F.adaptedBasis_weight_le_step b ω hF i
    omega)

attribute [local irreducible] realChartSubstitute

theorem FullChartControlledFactors.exists_degree_bounded_chart
    {m : ℕ} {X L ι : Type} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
    (left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    {budget : ℝ} (h : FullChartControlledFactors F b ω hF J poly N left right budget) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp budget ∧
      ∃ Echart : PolynomialGroup (X ⊕ (Σ j, J j))
          F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot,
        F.realGradedSymbolPolynomialHom b ω hF (fullTaggedVariableWeight (X := X) J) left =
          realPolynomialChartSubstitution
            F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot
            (normalizedRealPolynomialChart (fun i => (N i : ℝ))
              (fullTaggedMajorTopCoordinates J poly)) Echart ∧
        CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) (fun _ => 1)
          (Real.exp budget) Echart.coord ∧
        DegreeLE (fullTaggedVariableWeight (X := X) J) s Echart.coord ∧
        DegreeLE (fun _ => 1) s Echart.coord ∧
        CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ) q
          (F.realGradedSymbolPolynomialHom b ω hF
            (fullTaggedVariableWeight (X := X) J) right).coord := by
  obtain ⟨q, hq, hqB, E, hchart, hbound, hgrid⟩ := h
  let w := fullTaggedVariableWeight (X := X) J
  let E' : PolynomialGroup (X ⊕ (Σ j, J j))
      F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot :=
    ⟨weightedDegreeTruncate w s E.coord⟩
  refine ⟨q, hq, hqB, E', ?_, ?_, degreeLE_weightedDegreeTruncate w s E.coord,
    degreeLE_one_weightedDegreeTruncate w (fullTaggedVariableWeight_pos J) s E.coord, hgrid⟩
  · have hd := F.realGradedSymbolPolynomialHom_degreeLE b ω hF
      (fullTaggedVariableWeight (X := X) J) left
    have he := realPolynomialChartSubstitution_truncate_of_degreeLE
      F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot
      (fullTaggedVariableWeight (X := X) J)
      (normalizedRealPolynomialChart (fun i => (N i : ℝ)) (fullTaggedMajorTopCoordinates J poly))
      (fullTaggedMajorChart_homogeneous J poly (fun i => (N i : ℝ))) s
      (F.realGradedSymbolPolynomialHom b ω hF (fullTaggedVariableWeight (X := X) J) left)
      E hchart hd
    exact he
  · exact CoefficientBound.weightedDegreeTruncate _ _ (fun _ => zero_lt_one)
      (Real.exp_pos budget).le hbound w s

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

variable {σ : Type*} {ι L : Type} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem coefficientBound_gradedBasisSplitting
    (T : σ → ℝ) (M : ℝ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded)) :
    CoefficientBound (b.baseChange ℝ) T M
      (VectorPolynomial.map
        (((F.gradedBasisSplitting b ω hF).toLinearMap.baseChange ℝ).restrictScalars ℚ) P) ↔
      CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) T M P := by
  unfold CoefficientBound
  simp only [coefficients_map, LinearMap.restrictScalars_apply,
    F.gradedBasisSplitting_real_coordinate]

attribute [local irreducible] realChartSubstitute

end Erdos3.NilpotentLieFiltration

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.InhomogeneousFullChartLift
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def gradedPolynomialProjection (w : σ → ℕ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded)) :
    VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded) :=
  F.realGradedSymbolPolynomial b ω hF w (F.realSymbolOfGradedPolynomial b ω hF w P)

attribute [local irreducible] realChartSubstitute realGradedSymbolPolynomial realSymbolOfGradedPolynomial realSymbolHomogeneousPullback gradedPolynomialProjection

theorem coefficients_gradedPolynomialProjection (w : σ → ℕ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded)) (α : σ →₀ ℕ) :
    coefficients (F.gradedPolynomialProjection b ω hF w P) α =
      basisGradeProjection ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω
        (Finsupp.weight w α) (coefficients P α) := by
  apply ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr.injective
  ext i
  rw [basisGradeProjection_repr, gradedPolynomialProjection]
  by_cases hi : Finsupp.weight w α = ω i
  · rw [if_pos hi.symm,
      F.realGradedSymbolPolynomial_coordinate b ω hF w _ ⟨(α, i), hi⟩,
      F.realSymbolOfGradedPolynomial_coordinate]
  · rw [if_neg (Ne.symm hi),
      F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w _ α i hi]

theorem gradedPolynomialProjection_mem (w : σ → ℕ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded)) :
    F.gradedPolynomialProjection b ω hF w P ∈
      gradedPolynomialSubmodule ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω w := by
  rw [gradedPolynomialProjection]
  exact F.realGradedSymbolPolynomial_mem_gradedPolynomialSubmodule b ω hF w _

theorem gradedPolynomialProjection_eq_self (w : σ → ℕ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded))
    (hP : P ∈ gradedPolynomialSubmodule
      ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω w) :
    F.gradedPolynomialProjection b ω hF w P = P := by
  rw [gradedPolynomialProjection]
  exact F.realGradedSymbolPolynomial_ofGradedPolynomial b ω hF w P hP

theorem gradedPolynomialProjection_degreeLE (w u : σ → ℕ) (d : ℕ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded))
    (hP : DegreeLE u d P) :
    DegreeLE u d (F.gradedPolynomialProjection b ω hF w P) := by
  intro α hα
  rw [F.coefficients_gradedPolynomialProjection, hP α hα, map_zero]

theorem gradedPolynomialProjection_coefficientBound (w : σ → ℕ)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded))
    (hP : CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) T M P) :
    CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) T M
      (F.gradedPolynomialProjection b ω hF w P) := by
  intro α i
  rw [F.coefficients_gradedPolynomialProjection, basisGradeProjection_repr]
  split_ifs
  · exact hP α i
  · rw [abs_zero]
    exact div_nonneg hM (monomialScale_pos T hT α).le

theorem realSymbolOfGradedPolynomial_homogeneousChart
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded)) :
    F.realSymbolOfGradedPolynomial b ω hF v (realChartSubstitute β p) =
      F.realSymbolHomogeneousPullback b ω hF w v β
        (F.realSymbolOfGradedPolynomial b ω hF w p) := by
  classical
  apply ((F.polynomialSymbolBasis b ω hF v).baseChange ℝ).repr.injective
  ext z
  rw [F.realSymbolOfGradedPolynomial_coordinate, realSymbolHomogeneousPullback,
    F.realSymbolOfGradedPolynomial_coordinate]
  rw [coefficients_realChartSubstitute, coefficients_realChartSubstitute]
  simp only [map_sum, Finsupp.finsetSum_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr_of_eq_on_inter
  · intro γ hγ hγ'
    have hz : coefficients (F.realGradedSymbolPolynomial b ω hF w
        (F.realSymbolOfGradedPolynomial b ω hF w p)) γ = 0 := Finsupp.notMem_support_iff.mp hγ'
    by_cases h : Finsupp.weight w γ = ω z.val.2
    · have he := F.realGradedSymbolPolynomial_coordinate b ω hF w
        (F.realSymbolOfGradedPolynomial b ω hF w p) ⟨(γ, z.val.2), h⟩
      rw [hz, map_zero, Finsupp.zero_apply, F.realSymbolOfGradedPolynomial_coordinate] at he
      rw [← he, mul_zero]
    · rw [(isWeightedHomogeneous_aeval_monomial w v β hβ γ (1 : ℝ)).coeff_eq_zero _
        (fun he => h (he.symm.trans z.property)), zero_mul]
  · intro γ hγ hγ'
    have hz : coefficients p γ = 0 := Finsupp.notMem_support_iff.mp hγ'
    by_cases h : Finsupp.weight w γ = ω z.val.2
    · rw [F.realGradedSymbolPolynomial_coordinate b ω hF w _ ⟨(γ, z.val.2), h⟩,
        F.realSymbolOfGradedPolynomial_coordinate, hz, map_zero, Finsupp.zero_apply, mul_zero]
    · rw [F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w _ γ z.val.2 h, mul_zero]
  · intro γ hγ hγ'
    have hz := z.property
    by_cases h : Finsupp.weight w γ = ω z.val.2
    · rw [F.realGradedSymbolPolynomial_coordinate b ω hF w _ ⟨(γ, z.val.2), h⟩,
        F.realSymbolOfGradedPolynomial_coordinate]
    · have ha : Finsupp.weight v z.val.1 ≠ Finsupp.weight w γ :=
        fun he => h (he.symm.trans hz)
      rw [(isWeightedHomogeneous_aeval_monomial w v β hβ γ (1 : ℝ)).coeff_eq_zero _ ha]
      simp only [zero_mul]

theorem gradedPolynomialProjection_realChartSubstitute
    (w : σ → ℕ) (v : τ → ℕ) (β : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded)) :
    F.gradedPolynomialProjection b ω hF v (realChartSubstitute β P) =
      realChartSubstitute β (F.gradedPolynomialProjection b ω hF w P) := by
  rw [gradedPolynomialProjection, gradedPolynomialProjection,
    F.realSymbolOfGradedPolynomial_homogeneousChart b ω hF w v β hβ]
  exact F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v β hβ _

theorem FullChartControlledFactors.exists_graded_degree_bounded_chart
    {m : ℕ} {X L ι : Type} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
    (left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    {budget : ℝ} (h : FullChartControlledFactors F b ω hF J poly N left right budget) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp budget ∧
      ∃ Echart : PolynomialGroup (X ⊕ (Σ j, J j))
          F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot,
        F.realGradedSymbolPolynomialHom b ω hF (fullTaggedVariableWeight (X := X) J) left =
          realPolynomialChartSubstitution
            F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot
            (normalizedRealPolynomialChart (fun i => (N i : ℝ))
              (fullTaggedMajorTopCoordinates J poly)) Echart ∧
        CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) (fun _ => 1)
          (Real.exp budget) Echart.coord ∧
        Echart.coord ∈ gradedPolynomialSubmodule
          ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω
          (fullTaggedVariableWeight (X := X) J) ∧
        DegreeLE (fullTaggedVariableWeight (X := X) J) s Echart.coord ∧
        DegreeLE (fun _ => 1) s Echart.coord ∧
        CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ) q
          (F.realGradedSymbolPolynomialHom b ω hF
            (fullTaggedVariableWeight (X := X) J) right).coord := by
  obtain ⟨q, hq, hqB, E, hchart, hbound, hweighted, hdegree, hgrid⟩ :=
    FullChartControlledFactors.exists_degree_bounded_chart F b ω hF J poly N left right h
  let w := fullTaggedVariableWeight (X := X) J
  let E' : PolynomialGroup (X ⊕ (Σ j, J j))
      F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot :=
    ⟨F.gradedPolynomialProjection b ω hF w E.coord⟩
  refine ⟨q, hq, hqB, E', ?_, ?_, F.gradedPolynomialProjection_mem b ω hF w E.coord,
    F.gradedPolynomialProjection_degreeLE b ω hF w w s E.coord hweighted,
    F.gradedPolynomialProjection_degreeLE b ω hF w (fun _ => 1) s E.coord hdegree, hgrid⟩
  · apply NilpotentLieBCHGroup.ext
    have he := congrArg NilpotentLieBCHGroup.coord hchart
    rw [realPolynomialChartSubstitution_coord] at he
    change F.realGradedSymbolPolynomial b ω hF w left.coord =
      realChartSubstitute
        (normalizedRealPolynomialChart (fun i => (N i : ℝ))
          (fullTaggedMajorTopCoordinates J poly))
        (F.gradedPolynomialProjection b ω hF w E.coord)
    have hgraded := F.realGradedSymbolPolynomial_mem_gradedPolynomialSubmodule
      b ω hF w left.coord
    rw [← F.gradedPolynomialProjection_realChartSubstitute b ω hF w w _
      (fullTaggedMajorChart_homogeneous J poly (fun i => (N i : ℝ))) E.coord,
      ← he]
    exact (F.gradedPolynomialProjection_eq_self b ω hF w _ hgraded).symm
  · exact F.gradedPolynomialProjection_coefficientBound b ω hF w _
      (fun _ => zero_lt_one) (Real.exp_pos budget).le E.coord hbound

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

variable {σ τ : Type*} {ι L : Type} [Fintype σ]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

attribute [local irreducible] realChartSubstitute realSymbolOfGradedPolynomial realGradedSymbolPolynomial realSymbolHomogeneousPullback

omit [Fintype σ] in

theorem exists_inhomogeneous_chart_lift_algebraic
    (w : σ → ℕ) (v : τ → ℕ) (E : F.RealPolynomialSymbolGroup w)
    (f : σ → MvPolynomial σ ℝ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded))
    (hgraded : P ∈ gradedPolynomialSubmodule
      ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω w)
    (hchart : (F.realGradedSymbolPolynomialHom b ω hF w E).coord =
      realChartSubstitute f P)
    (β δ : σ → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (w i))
    (hδ : ∀ i, δ i ∈ weightedSupportLE v (w i))
    (htop : ∀ i, MvPolynomial.weightedHomogeneousComponent v (w i) (δ i) =
      MvPolynomial.aeval β (f i)) :
    ∃ e : (F.realification.adaptedPolynomialFiltration v).Group,
      e.coord.val = realChartSubstitute δ (VectorPolynomial.map
        (((F.gradedBasisSplitting b ω hF).toLinearMap.baseChange ℝ).restrictScalars ℚ) P) ∧
      F.realPolynomialSymbolHom b ω hF v e =
        F.realSymbolHomogeneousPullbackHom b ω hF w v β hβ E := by
  let Y : F.RealPolynomialSymbolGroup w := ⟨F.realSymbolOfGradedPolynomial b ω hF w P⟩
  have hY : F.realGradedSymbolPolynomial b ω hF w Y.coord = P :=
    F.realGradedSymbolPolynomial_ofGradedPolynomial b ω hF w P hgraded
  let S := (F.gradedBasisSplitting b ω hF).toLinearMap.baseChange ℝ
  have hlog : (F.realPolynomialSymbolLift b ω hF w Y).coord.val =
      VectorPolynomial.map (S.restrictScalars ℚ) P := by
    rw [F.realPolynomialSymbolLift_log, F.realSymbolRepresentative_eq_map, hY]
  let e := F.weightedAdaptedRealChartHom w v δ hδ
    (F.realPolynomialSymbolLift b ω hF w Y)
  have he : e.coord.val = realChartSubstitute δ
      (VectorPolynomial.map (S.restrictScalars ℚ) P) := by
    change realChartSubstitute δ (F.realPolynomialSymbolLift b ω hF w Y).coord.val = _
    rw [hlog]
  refine ⟨e, he, ?_⟩
  rw [F.realPolynomialSymbolHom_weightedAdaptedRealChart,
      F.realPolynomialSymbolHom_lift]
  apply F.realGradedSymbolPolynomialHom_injective b ω hF v
  apply NilpotentLieBCHGroup.ext
  change F.realGradedSymbolPolynomial b ω hF v
      (F.realSymbolHomogeneousPullback b ω hF w v _ Y.coord) =
      F.realGradedSymbolPolynomial b ω hF v
        (F.realSymbolHomogeneousPullback b ω hF w v β E.coord)
  rw [F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v _
      (fun _ => MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _),
      F.realGradedSymbolPolynomial_homogeneousPullback b ω hF w v β hβ, hY]
  change realChartSubstitute _ P =
      realChartSubstitute β (F.realGradedSymbolPolynomialHom b ω hF w E).coord
  rw [hchart, realChartSubstitute_comp]
  exact congrArg (fun z => realChartSubstitute z P) (funext htop)

theorem polynomialSlowBound_inhomogeneous_chart_lift
    {υ : Type*} (v : τ → ℕ) (u : υ → ℕ)
    (e : (F.realification.adaptedPolynomialFiltration v).Group)
    (δ : σ → MvPolynomial τ ℝ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded))
    (he : e.coord.val = realChartSubstitute δ (VectorPolynomial.map
      (((F.gradedBasisSplitting b ω hF).toLinearMap.baseChange ℝ).restrictScalars ℚ) P))
    (γ : τ → MvPolynomial υ ℝ) (hγ : ∀ i, γ i ∈ weightedSupportLE u (v i))
    (T : υ → ℝ) (hT : ∀ i, 0 < T i) {A B : ℝ} {d : ℕ}
    (hbound : CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ)
      (fun _ => 1) A P) (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hdegree : DegreeLE (fun _ : σ => 1) d P)
    (hmass : ∀ i, realPolynomialMass
      (scaleMvPolynomialAxes T (MvPolynomial.aeval γ (δ i))) ≤ B) :
    F.PolynomialSlowBound b u T
      (((Fintype.card σ : ℝ) + 1) ^ d * A * B ^ d)
      (F.weightedAdaptedRealChartHom v u γ hγ e) := by
  change CoefficientBound (b.baseChange ℝ) T _ (realChartSubstitute γ e.coord.val)
  rw [he, realChartSubstitute_comp]
  exact CoefficientBound.realChartSubstitute_sharp (b.baseChange ℝ) T hT _
    ((F.coefficientBound_gradedBasisSplitting b ω hF _ _ P).mpr hbound)
    hA hB (hdegree.map _) hmass

theorem FullChartControlledFactors.exists_inhomogeneous_left_lift
    {m : ℕ} {X : Type} [Fintype X]
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
    (left right : F.RealPolynomialSymbolGroup
      (fullTaggedVariableWeight (X := X) J))
    {budget : ℝ} (h : FullChartControlledFactors F b ω hF J poly N left right budget)
    (v : τ → ℕ) (β δ : (X ⊕ (Σ j, J j)) → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v
      (fullTaggedVariableWeight (X := X) J i))
    (hδ : ∀ i, δ i ∈ weightedSupportLE v
      (fullTaggedVariableWeight (X := X) J i))
    (htop : ∀ i, MvPolynomial.weightedHomogeneousComponent v
      (fullTaggedVariableWeight (X := X) J i) (δ i) =
      MvPolynomial.aeval β (normalizedRealPolynomialChart (fun i => (N i : ℝ))
        (fullTaggedMajorTopCoordinates J poly) i)) :
    ∃ (P : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] F.AssociatedGraded))
      (e : (F.realification.adaptedPolynomialFiltration v).Group),
      CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ)
        (fun _ => 1) (Real.exp budget) P ∧
      P ∈ gradedPolynomialSubmodule ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω
        (fullTaggedVariableWeight (X := X) J) ∧
      DegreeLE (fullTaggedVariableWeight (X := X) J) s P ∧
      DegreeLE (fun _ => 1) s P ∧
      e.coord.val = realChartSubstitute δ (VectorPolynomial.map
        (((F.gradedBasisSplitting b ω hF).toLinearMap.baseChange ℝ).restrictScalars ℚ) P) ∧
      F.realPolynomialSymbolHom b ω hF v e = F.realSymbolHomogeneousPullbackHom b ω hF
        (fullTaggedVariableWeight (X := X) J) v β hβ left := by
  obtain ⟨q, hq, hqB, E, hchart, hbound, hgraded, hweighted, hdegree, hgrid⟩ :=
    FullChartControlledFactors.exists_graded_degree_bounded_chart
      F b ω hF J poly N left right h
  have hc := congrArg NilpotentLieBCHGroup.coord hchart
  rw [realPolynomialChartSubstitution_coord] at hc
  obtain ⟨e, he, hsymbol⟩ := F.exists_inhomogeneous_chart_lift_algebraic b ω hF
    _ v left _ E.coord hgraded hc β δ hβ hδ htop
  exact ⟨E.coord, e, hbound, hgraded, hweighted, hdegree, he, hsymbol⟩

end Erdos3.NilpotentLieFiltration

end

end OAI

end


