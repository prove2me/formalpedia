-- Prove2me | Definitions.Def_OAIE3v2B290
-- name    : OAIE3v2B290
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T08:14:36.543392+00:00
-- url     : https://prove2.me/theorems/b08630cc-dc07-4d25-b8a5-270449283afb
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 303 of 311
-- statement:
--   Definitions bundle 303 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B309`, `OAIE3v2B280`, `OAIE3v2B281`, `OAIE3v2B282`, `OAIE3v2B283`, `OAIE3v2B284`, `OAIE3v2B286` of this split.
--
--   Modules: `Dynamics/AllocatedCandidateNestedTerminalUniformLayersBudget.lean`, `Dynamics/AllocatedExternalCandidateSourcePhysicalBudgetBounds.lean`, `Dynamics/PreparedFiniteNestedCanonicalEarlyPrimitiveBudget.lean`, `Estimates/AllocatedCandidateGeneratedFastTerminal.lean`, `Estimates/AllocatedCandidateInnerSourceGain.lean`, `Estimates/AllocatedExternalCandidatePrimitiveFrontDescentData.lean`, `Estimates/AllocatedZeroLayerForwardFrontSourceProfile.lean`, `Estimates/PreparedFiniteNestedSourceArrays.lean`, `Estimates/PreparedRelativePositiveNativeRuleCanonical.lean`, `Lattices/AllocatedAffineCanonicalBackendBudget.lean`, `Lattices/AllocatedAffinePhysicalTerminalReset.lean`, `Polynomial/PreparedUniformDegreeProductiveSource.lean`, `Sampling/PreparedShortForecastRawSourceBounds.lean`, `Sampling/SharedWidthPreparedShortForecastProductiveModelAttachment.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B309
import Definitions.Def_OAIE3v2B280
import Definitions.Def_OAIE3v2B281
import Definitions.Def_OAIE3v2B282
import Definitions.Def_OAIE3v2B283
import Definitions.Def_OAIE3v2B284
import Definitions.Def_OAIE3v2B286

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCandidateGeneratedFastTerminal
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

noncomputable def allocatedCandidateForwardScheduleExponent
    (s m Cprimitive Csource extra : ℕ) : ℕ :=
  max extra (max (allocatedCandidateStageBaseExponent s m Cprimitive)
    (max (allocatedCandidateStageSliceExponent s m Cprimitive + 1)
      ((Finset.range s).sup fun r => allocatedCandidateCompositePhaseConstant s m 1
        (allocatedCandidatePromotedMajorConstant Csource) r)))

theorem allocatedCandidateForwardScheduleExponent_bounds
    (s m Cprimitive Csource extra : ℕ) :
    extra ≤ allocatedCandidateForwardScheduleExponent s m Cprimitive Csource extra ∧
    allocatedCandidateStageBaseExponent s m Cprimitive ≤
      allocatedCandidateForwardScheduleExponent s m Cprimitive Csource extra ∧
    allocatedCandidateStageSliceExponent s m Cprimitive + 1 ≤
      allocatedCandidateForwardScheduleExponent s m Cprimitive Csource extra ∧
    ∀ r < s, allocatedCandidateCompositePhaseConstant s m 1
      (allocatedCandidatePromotedMajorConstant Csource) r ≤
        allocatedCandidateForwardScheduleExponent s m Cprimitive Csource extra := by
  unfold allocatedCandidateForwardScheduleExponent
  refine ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _), ?_⟩
  intro r hr
  exact (Finset.le_sup (f := fun r => allocatedCandidateCompositePhaseConstant s m 1
    (allocatedCandidatePromotedMajorConstant Csource) r) (Finset.mem_range.mpr hr)).trans
      (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _))

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffinePhysicalTerminalReset
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped Classical TensorProduct BigOperators
attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I Deck J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {Rad σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U btag Rad σ}
    {hb : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hRad : ∀ j, 0 < Rad j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U btag S hb o hRad hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (keep : ℕ → LayerSamplerVariables G I n B → Prop)
    {ι κ η : Type} {χ : ℕ → Type} [Fintype ι] [Fintype κ] [∀ r, Fintype (χ r)] [Fintype η]
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (bD '' {i | j ≤ ω i}))
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)

local notation "fast" => W.map (D.filtration.associatedGradedMap Fmark φ hφ)
local notation "gmark" => Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked
local notation "Z" => Fmark.realPolynomialSymbolHom bF ν hF (fullTaggedVariableWeight J) gmark

theorem exists_affinePhysicalTerminalData
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (Fmark.AssociatedGraded ⧸ (fast).toSubmodule)))
    (lift : (Fmark.AssociatedGraded ⧸ (fast).toSubmodule) →ₗ[ℚ] Fmark.AssociatedGraded)
    (Bphase budget pAffine : ℝ)
    (history : CertifiedFullChartFiniteHistory Fmark bF ν hF J (fast).toSubmodule
      basis lift Z Set.univ U poly N Bphase s)
    (hfast : BasisGradedSubmodule (Fmark.associatedGradedBasis bF ν hF) ν (fast).toSubmodule)
    (hcontrol : FullChartControlledFactors Fmark bF ν hF J poly N
      history.outer.1 history.outer.2 budget)
    {blocks : ℕ}
    (hcertificate : RationalTaggedConstraintCertificate J Set.univ history.K pAffine blocks)
    (hpAffine : 0 ≤ pAffine) (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ pAffine)
    (hblocks : (blocks : ℝ) ≤ pAffine)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hτ : τ ≤ 1) (hξ : ξ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1)
    (hmass : 0 < massThreshold) (H : ℕ) (a : ℕ) (pFull : ℝ)
    (hH : 1 ≤ H) (hpFull : 0 ≤ pFull)
    (hκ : (Fintype.card κ : ℝ) ≤ pFull)
    (htags : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ pFull)
    (hHExp : (H : ℝ) ≤ Real.exp pFull)
    (hden : Real.exp budget * (Real.exp ((m : ℝ) * certifiedAffineCenterBudget pAffine)) ^ s ≤
      Real.exp pFull)
    (hbracket : ∀ i j k, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ k) H)
    (hsampler : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pFull)
    (hmassFull : (((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ s * Real.exp budget *
      (actualCandidateSlowProjectionMassBudget m (Fintype.card (LayerSamplerVariables G I n B)) pFull
        (((pAffine + ((pAffine+2)^2+2)^63)+2)^8)) ^ s ≤ Real.exp ((pFull + 2) ^ a)))
    (separation : ℝ) (hseparation : certifiedAffineLongSideBound pAffine ≤ separation) :
    Nonempty (P.AffinePhysicalTerminalData bF ν hF hφ W basis lift
      Bphase budget pAffine pFull a history separation) := by
  classical
  have hretained (point) (hpoint : ∀ j, (fun i => point (Sum.inr ⟨j,i⟩)) ∈ U j) :
      point ∈ history.K := history.retained point (Set.mem_univ _) hpoint
  have hcap (j : Fin m) :
      Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ Real.exp pAffine :=
    (hsmall j).trans (Real.one_le_exp_iff.mpr hpAffine)
  obtain ⟨selected⟩ := P.exists_certifiedThresholdAffineRefinement hσone history.K
    (p := pAffine) (blocks := blocks) hcertificate hretained hpAffine hdim hblocks
    Cgeo hCgeo hchart hpoly hcap separation hseparation hmass
  obtain ⟨hDpos, hDbound, q, nFinal, hq, hqB, hn, hnB, hdiv, factors,
      hgrid, hlocal, hphysicalLeft, hphysicalRight, _⟩ :=
    ((Classical.choose_spec
      (Classical.choose_spec (exists_allocatedCertifiedAffineGlobalPhysicalTerminal s a))).2.2)
      selected.freezing.problem bF ν hF fast basis lift Z Bphase budget pAffine
      history selected.affine hfast hcontrol hpoly rfl hτ hξ hσone Cgeo hCgeo hchart hsmall
      H pFull hH hpFull hκ htags hHExp hden hbracket hsampler hmassFull
  exact ⟨{
    selected := selected
    denominator_pos := hDpos
    denominator_bound := hDbound
    q := q
    nFinal := nFinal
    q_pos := hq
    q_bound := hqB
    nFinal_pos := hn
    nFinal_bound := hnB
    denominator_dvd := hdiv
    factors := factors
    right_grid := hgrid
    local_left := hlocal
    physical_left := hphysicalLeft
    physical_right := hphysicalRight
  }⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineCanonicalBackendBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open NilpotentLieFiltration

theorem allocatedAffineCanonicalBudget_le_diagonal (s : ℕ) {p0 pFull B : ℝ}
    (hp0 : 0 ≤ p0) (hFull : 0 ≤ pFull) (hp0B : p0 ≤ B) (hFullB : pFull ≤ B) :
    allocatedAffineCanonicalBudget s p0 pFull ≤ allocatedAffineCanonicalBudget s B B := by
  have hB : 0 ≤ B := hp0.trans hp0B
  have hmap0 := (allocatedAffineResetMapBudget_bounds s hp0 hFull).nonnegative
  have hnative0 := (allocatedAffineCanonicalBudget_bounds s hp0 hFull).native_nonnegative
  have hpoint : ordinaryImagePointwiseBudget (s + 1) (s + 1) p0 ≤
      ordinaryImagePointwiseBudget (s + 1) (s + 1) B := by
    unfold ordinaryImagePointwiseBudget pointwiseFastSectionInput
    gcongr
  have hmap : allocatedAffineResetMapBudget s p0 pFull ≤
      allocatedAffineResetMapBudget s B B := by
    unfold allocatedAffineResetMapBudget allocatedAffineResetHeightLog allocatedAffineResetRightLog
    gcongr
  have hnative : allocatedAffineCanonicalNativeBudget s p0 pFull ≤
      allocatedAffineCanonicalNativeBudget s B B := by
    unfold allocatedAffineCanonicalNativeBudget allocatedAffineResetNativeBudget affineResetNativeBudget
    gcongr
  have hreset : allocatedAffineResetLogBudget s (allocatedAffineCanonicalNativeBudget s p0 pFull) ≤
      allocatedAffineResetLogBudget s (allocatedAffineCanonicalNativeBudget s B B) := by
    unfold allocatedAffineResetLogBudget markedNativeLiftInput fullMarkedNativeInput
      pointwiseFastSectionInput
    gcongr
  have hcompare : allocatedAffineResetCompareLog s (allocatedAffineCanonicalNativeBudget s p0 pFull) ≤
      allocatedAffineResetCompareLog s (allocatedAffineCanonicalNativeBudget s B B) := by
    unfold allocatedAffineResetCompareLog
    gcongr
  have hleft : allocatedAffineResetLeftLog s pFull ≤ allocatedAffineResetLeftLog s B := by
    unfold allocatedAffineResetLeftLog
    gcongr
  unfold allocatedAffineCanonicalBudget
  linarith

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open NilpotentLieFiltration

noncomputable def allocatedAffineCanonicalBudgetPolynomial (s : ℕ) : Polynomial ℕ :=
  let X := Polynomial.X
  let sectionPoly := canonicalSectionPolynomial (s + 1) X
  let right := (X + Polynomial.C (allocatedEarlyAffineRightExponent (s + 1) 4)) ^
    allocatedEarlyAffineRightExponent (s + 1) 4
  let left := (X + Polynomial.C (allocatedEarlyAffineLeftExponent (s + 1) 4)) ^
    allocatedEarlyAffineLeftExponent (s + 1) 4
  let map := sectionPoly + sectionPoly + (X + 2) ^ 5 + (X + 4) ^ 12 + 1 + X + right
  let native := X + map + X + left + (map + 2) ^ 4
  let nativeSection := canonicalSectionPolynomial (s + 1) native
  let full := (nativeSection + Polynomial.C (allocatedAffineResetFactorExponent s)) ^
      allocatedAffineResetFactorExponent s + (native + 2) ^ 1 + nativeSection
  let reset := ((full + 2) ^ 11 + full + Polynomial.C (allocatedAffineResetLiftExponent s)) ^
    allocatedAffineResetLiftExponent s
  X + X + map + native + reset +
    (native + Polynomial.C (allocatedAffineResetCompareExponent s)) ^
      allocatedAffineResetCompareExponent s + left + Polynomial.C (s + 2)

theorem allocatedAffineCanonicalBudgetPolynomial_eval (s : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    (allocatedAffineCanonicalBudgetPolynomial s).eval₂ (Nat.castRingHom ℝ) B =
      allocatedAffineCanonicalBudget s B B := by
  simp only [allocatedAffineCanonicalBudgetPolynomial, canonicalSectionPolynomial,
    allocatedAffineCanonicalBudget, allocatedAffineResetMapBudget,
    allocatedAffineCanonicalNativeBudget, allocatedAffineResetNativeBudget,
    affineResetNativeBudget, allocatedAffineResetRightLog, allocatedAffineResetLeftLog,
    allocatedAffineResetCompareLog, allocatedAffineResetLogBudget,
    ordinaryImagePointwiseBudget, allocatedAffineResetHeightLog,
    markedNativeLiftInput, fullMarkedNativeInput, pointwiseFastSectionInput,
    max_eq_left hB, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
    Polynomial.eval₂_ofNat, Polynomial.eval₂_one, Nat.coe_castRingHom,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]

noncomputable def allocatedAffineCanonicalBackendPolynomial (s : ℕ) : Polynomial ℕ :=
  let P := allocatedAffineCanonicalBudgetPolynomial s
  P + 12 * (P + Polynomial.C (candidatePrimitivePhysicalBudgetExponent s 1)) ^
    candidatePrimitivePhysicalBudgetExponent s 1 + 32

theorem allocatedAffineCanonicalBackendPolynomial_eval (s : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    (allocatedAffineCanonicalBackendPolynomial s).eval₂ (Nat.castRingHom ℝ) B =
      allocatedAffineCanonicalBudget s B B +
        finiteFreezingRecursiveParameter (candidatePrimitivePhysicalBudgetExponent s 1)
          (allocatedAffineCanonicalBudget s B B) := by
  simp only [allocatedAffineCanonicalBackendPolynomial, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C,
    Polynomial.eval₂_ofNat, Nat.coe_castRingHom, allocatedAffineCanonicalBudgetPolynomial_eval s hB,
    finiteFreezingRecursiveParameter]
  ring

theorem allocatedAffineCanonicalBackendPolynomial_bounds (s : ℕ) {p0 pFull B : ℝ}
    (hp0 : 0 ≤ p0) (hFull : 0 ≤ pFull) (hp0B : p0 ≤ B) (hFullB : pFull ≤ B) :
    AllocatedAffineCanonicalBackendBounds s p0 pFull
      ((allocatedAffineCanonicalBackendPolynomial s).eval₂ (Nat.castRingHom ℝ) B) := by
  have hB := hp0.trans hp0B
  have hp := (allocatedAffineCanonicalBudget_bounds s hp0 hFull).nonnegative
  have hd := (allocatedAffineCanonicalBudget_bounds s hB hB).nonnegative
  have hdiag := allocatedAffineCanonicalBudget_le_diagonal s hp0 hFull hp0B hFullB
  have hrec :
      finiteFreezingRecursiveParameter (candidatePrimitivePhysicalBudgetExponent s 1)
        (allocatedAffineCanonicalBudget s p0 pFull) ≤
      finiteFreezingRecursiveParameter (candidatePrimitivePhysicalBudgetExponent s 1)
        (allocatedAffineCanonicalBudget s B B) := by
    unfold finiteFreezingRecursiveParameter
    gcongr
  have hrec0 : 0 ≤
      finiteFreezingRecursiveParameter (candidatePrimitivePhysicalBudgetExponent s 1)
        (allocatedAffineCanonicalBudget s B B) := by
    unfold finiteFreezingRecursiveParameter
    positivity
  have hrecUpper :
      finiteFreezingRecursiveParameter (candidatePrimitivePhysicalBudgetExponent s 1)
        (allocatedAffineCanonicalBudget s p0 pFull) ≤
      (allocatedAffineCanonicalBackendPolynomial s).eval₂ (Nat.castRingHom ℝ) B := by
    rw [allocatedAffineCanonicalBackendPolynomial_eval s hB]
    linarith only [hrec, hd]
  constructor
  · rw [allocatedAffineCanonicalBackendPolynomial_eval s hB]
    linarith only [hdiag, hrec0]
  · exact hrecUpper
  · exact ((candidatePrimitiveFreezingCutoff_le_budget s 1 hp).trans
      (power_le_recursiveParameter _ hp)).trans hrecUpper
  · exact (allocatedAffineCanonical_cutoffCost_le_recursive s hp0 hFull).trans hrecUpper

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedCandidateNestedTerminalUniformLayersBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem uniformLayersTerminalPolynomial_eval (s Cprimitive : ℕ) (x : ℝ) :
    (uniformLayersTerminalPolynomial s Cprimitive).eval₂ (Nat.castRingHom ℝ) x =
      (x + Cprimitive) ^ Cprimitive + x + x +
        s * x * certifiedAffineCenterBudget x + certifiedAffineCenterBudget x + s + x + 10 := by
  simp only [uniformLayersTerminalPolynomial, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_ofNat,
    Nat.coe_castRingHom, uniformLayersAffinePolynomial_eval]

attribute [local irreducible] certifiedAffineCenterBudget
  preparedFiniteForwardParameter preparedFiniteForwardWork preparedFiniteForwardCap
  preparedFiniteForwardBranch preparedFiniteForwardCumulative

theorem terminalFullInput_le_uniformLayers (s m Cprimitive : ℕ)
    {x work cumulative u : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ cumulative)
    (hmx : (m : ℝ) ≤ x) (hxu : x ≤ u) (hwu : work ≤ u) (hcu : cumulative ≤ u) :
    allocatedCandidateTerminalFullInput s m Cprimitive x work cumulative ≤
      (uniformLayersTerminalPolynomial s Cprimitive).eval₂ (Nat.castRingHom ℝ) u := by
  have hmu : (m : ℝ) ≤ u := hmx.trans hxu
  have hu : 0 ≤ u := hx.trans hxu
  have hB : certifiedAffineCenterBudget cumulative ≤ certifiedAffineCenterBudget u := by
    simpa only [uniformLayersAffinePolynomial_eval] using
      natPolynomial_eval_mono_nonneg uniformLayersAffinePolynomial hc hcu
  have hB0 : 0 ≤ certifiedAffineCenterBudget cumulative := by
    simpa only [uniformLayersAffinePolynomial_eval] using
      natPolynomial_eval_nonneg uniformLayersAffinePolynomial hc
  have hBu0 : 0 ≤ certifiedAffineCenterBudget u := hB0.trans hB
  rw [uniformLayersTerminalPolynomial_eval]
  unfold allocatedCandidateTerminalFullInput
  gcongr

theorem exists_terminalFullInput_uniformLayers_polynomial_next_work
    (s Cprimitive : ℕ) (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (m A : ℕ) (constants : ℕ → ℕ) {x : ℝ},
      C ≤ A → 0 ≤ x → (m : ℝ) ≤ x →
      P.eval₂ (Nat.castRingHom ℝ)
        (allocatedCandidateTerminalFullInput s m Cprimitive x
          (preparedFiniteForwardWork A constants s x)
          (preparedFiniteForwardCumulative A constants s x)) ≤
        preparedFiniteForwardWork A constants (s + 1) x := by
  obtain ⟨C, hC, hcap⟩ := exists_preparedFiniteForward_polynomial_cap
    (P.comp (uniformLayersTerminalPolynomial s Cprimitive))
  refine ⟨C, hC, ?_⟩
  intro m A constants x hCA hx hmx
  have hA : 2 ≤ A := hC.trans hCA
  have hzero : (0 : ℝ) ∈ Set.Icc 0 x := ⟨le_rfl, hx⟩
  have hprec := preparedFiniteForward_model_precision_bounds A constants s hx hzero hzero
  have hprefix := preparedFiniteForward_prefix_bounds A constants s hx
  have hwork := preparedFiniteForward_model_scalar_bounds A constants s 0 hA hx
    (by simpa only [Nat.cast_zero] using hx)
  let u := preparedFiniteForwardSourcePrecision A constants s x 0 0 +
    preparedFiniteForwardWork A constants s x
  have hwu : preparedFiniteForwardWork A constants s x ≤ u :=
    le_add_of_nonneg_left hprec.2.1
  have hxu : x ≤ u :=
    (le_preparedFiniteForwardParameter A constants s hx).trans (hwork.2.1.trans hwu)
  have hcu : preparedFiniteForwardCumulative A constants s x ≤ u :=
    hprefix.1.2.trans (hwork.2.1.trans hwu)
  have hinput := terminalFullInput_le_uniformLayers s m Cprimitive hx hprefix.1.1
    hmx hxu hwu hcu
  have hinput0 :=
    (allocatedCandidateTerminalFullInput_bounds s m Cprimitive hx hwork.1 hprefix.1.1).1
  have hP := natPolynomial_eval_mono_nonneg P hinput0 hinput
  have hcapP : P.eval₂ (Nat.castRingHom ℝ)
      ((uniformLayersTerminalPolynomial s Cprimitive).eval₂ (Nat.castRingHom ℝ) u) ≤
        preparedFiniteForwardCap A constants s x := by
    simpa only [Polynomial.eval₂_comp, u] using hcap A constants s hCA hx hzero hzero
  have hnext := preparedFiniteForward_model_scalar_bounds A constants (s + 1) 0 hA hx
    (by simpa only [Nat.cast_zero] using hx)
  have hcapNext : preparedFiniteForwardCap A constants s x ≤
      preparedFiniteForwardParameter A constants (s + 1) x := by
    rw [preparedFiniteForwardParameter_succ]
    have hb := preparedFiniteForwardParameter_nonneg A constants s hx
    have hbranch := preparedFiniteForwardBranch_nonneg A constants s hx
    linarith only [hb, hbranch]
  exact (hP.trans hcapP).trans (hcapNext.trans hnext.2.1)

theorem exists_allocatedCandidateNestedTerminal_uniformLayers_polynomial_budget
    (s Cprimitive : ℕ) (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ (m A : ℕ) (constants : ℕ → ℕ) (innerDepth outer : ℕ) {x : ℝ},
        C ≤ A → s + 1 ≤ innerDepth → 0 ≤ x →
        (m : ℝ) ≤ candidateNestedForwardSeed A constants innerDepth outer x →
        let seed := candidateNestedForwardSeed A constants innerDepth outer x
        P.eval₂ (Nat.castRingHom ℝ)
          (allocatedCandidateTerminalFullInput s m Cprimitive seed
            (preparedFiniteForwardWork A constants s seed)
            (preparedFiniteForwardCumulative A constants s seed)) ≤
          candidateNestedForwardSeed A constants innerDepth (outer + 1) x := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_terminalFullInput_uniformLayers_polynomial_next_work s Cprimitive P
  refine ⟨C, hC, ?_⟩
  intro m A constants innerDepth outer x hCA hdepth hx hm seed
  have hseed : 0 ≤ seed := candidateNestedForwardSeed_nonneg A constants innerDepth outer hx
  exact (hbound m A constants hCA hseed hm).trans
    (candidateNestedForwardWork_le_next_seed A constants innerDepth outer (s + 1) hx hdepth)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedShortForecastRawSourceBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m nX M : ℕ} {X₀ J₀ : Type}
variable (prep : RankPreparationFamily X₀ J₀ m)
local notation "kernel" => EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))
local notation "blocks" => EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))
local notation "axes" => PreparedSamplerContinuous prep
local notation "transverse" => preparedSamplerTransverse prep
local notation "coords" => (fun j : Fin m => RankPreparationLayer.Coord (prep j))
variable (U : ∀ j, Submodule ℝ (coords j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (transverse j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := kernel) (I := axes) (n := transverse) (J := coords) blocks U b R σ)
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
variable (selection : Fin (0 + 1) ↪ kernel) (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
variable (τ u p forecastCap : ℝ)
variable {P : ℝ}

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (axes j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (coords j)) (euclideanSubspace (U j))))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (coords j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (coords j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables kernel axes transverse blocks) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables kernel axes transverse blocks) U)]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables kernel axes transverse blocks) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables kernel axes transverse blocks) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

structure PreparedCenteredShortForecastGoodBounds
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale
      (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j => RankPreparationLayer.Coord (prep j))
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    (selection : Fin (0 + 1) ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ)
    (Vtail : Fin m → ℝ≥0) (u p forecastCap : ℝ)
    (Pchart Qstride Pmaster Plate Pphysical coarseTarget : ℝ)
    (B0 Vlog gainLog gain Pwidth P₀ Pgood : ℝ) (Qgood : ℕ) (D : ℝ) : Prop where
  hcert : PreparedShortCertifiedSameScaleBadProductInterface (nX := nX) (M := M) prep U b S B0 (gainLog + 8) Vlog Qgood
  hnX : 0 < nX
  hσ1 : ∀ j, σ j ≤ 1
  hsmall : ∀ C : Fin m → ℝ, (∀ j, 0 ≤ C j) →
      (∀ j, C j ≤ Real.exp Pchart) →
      ∀ j, C j * ((Fintype.card ((PreparedSamplerContinuous prep) j) : ℝ) + 1) * R j ≤ 1/4
  hMaster : 0 ≤ Pmaster
  hLate : Pmaster ≤ Plate
  hd : AllocatedComparisonDimensions (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (Fin (0 + 1)) (fun j : Fin m => (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1) : Type)) D
  hD : D ≤ Pmaster
  hnMaster : (nX : ℝ) ≤ Pmaster
  hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pmaster
  hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Plate
  hS : (S.value : ℝ) ≤ Real.exp Plate
  hchartB : Pchart ≤ B0
  hprojection : (preparedModularGeneralDetectorResources
      (preparedModularGeneralDetectorConstants m 0) (0 + 1) Pmaster Plate).Pproj ≤ Pwidth
  hphysical : jointPhysicalBaseLog Pwidth (gainLog + 8) Vlog ≤ B0
  hVlog : 0 ≤ Vlog
  hQexp : (Qgood : ℝ) ≤ Real.exp Vlog
  hP₀ : 0 ≤ P₀
  hnP₀ : (nX : ℝ) ≤ P₀
  hgP₀ : gainLog ≤ P₀
  hcutoffP : (P₀ + preparedCenteredShortForecastSpatialExponent m) ^
      preparedCenteredShortForecastSpatialExponent m ≤ Pgood
  hBP : B0 ≤ Pgood
  hwidthP : Pwidth ≤ Pgood
  hg : 0 ≤ gainLog
  hgP : gainLog + 8 ≤ Pgood
  hgain : Real.exp (-gainLog) ≤ gain
  hstrideWidth : Qstride ≤ Pwidth
  hτWidth : Pphysical ≤ Pwidth
  hξWidth : (normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) (layerSamplerDegree (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))) selection
      (allocatedDetectedKernelCutoff 0 (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
        (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
        Pdetect (allocatedModelTestLog uSource pModel) (allocatedModelTestLog uSource pModel) ((forecastAugmentedUnitThreshold u p (Real.exp (pSlice * Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))) (max 1 (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous prep) j)) ((preparedSamplerTransverse prep) j) (R j) (Vtail j))) forecastCap) / 2)) Pphysical coarseTarget)⁻¹ ≤ Real.exp Pwidth

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidateSourcePhysicalBudgetBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module
open scoped TensorProduct

noncomputable def candidateSourceBackendPolynomial (s : ℕ) : Polynomial ℕ :=
  (allocatedAffineCanonicalBackendPolynomial s).comp ((Polynomial.X + 4) ^ 10)

theorem candidateSourceBackendPolynomial_eval (s : ℕ) (pFull : ℝ) :
    (candidateSourceBackendPolynomial s).eval₂ (Nat.castRingHom ℝ) pFull =
      (allocatedAffineCanonicalBackendPolynomial s).eval₂ (Nat.castRingHom ℝ)
        (candidatePhysicalOrdinaryBudget pFull) := by
  simp only [candidateSourceBackendPolynomial, Polynomial.eval₂_comp,
    Polynomial.eval₂_pow, Polynomial.eval₂_add, Polynomial.eval₂_X,
    Polynomial.eval₂_ofNat, candidatePhysicalOrdinaryBudget]

theorem candidateSourceBackendPolynomial_bounds (s : ℕ) {pFull : ℝ} (hp : 0 ≤ pFull) :
    AllocatedAffineCanonicalBackendBounds s (candidatePhysicalOrdinaryBudget pFull) pFull
      ((candidateSourceBackendPolynomial s).eval₂ (Nat.castRingHom ℝ) pFull) := by
  rw [candidateSourceBackendPolynomial_eval]
  have hb := candidatePhysicalOrdinaryBudget_bounds hp
  exact allocatedAffineCanonicalBackendPolynomial_bounds s hb.1 hp le_rfl hb.2.1

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedZeroLayerForwardFrontSourceProfile
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

attribute [local instance] OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.preparedFrontSourceProfileSiteNonempty
noncomputable def preparedFixedCenterFrontSourceProfile
    {degree e : ℕ} {p u pModel sliceBudget testBudget nativeBudget projectionPrecision
      E rawCap α : ℝ}
    (hξone : ξ ≤ 1)
    (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    (hu : 0 ≤ u) (hpModel : 0 ≤ pModel) (hInputModel : 2 * p + 3 ≤ pModel)
    (hNative : 0 ≤ nativeBudget)
    (hSliceNonneg : 0 ≤ sliceBudget) (hTestNontrivial : 2 ≤ testBudget)
    (hSliceLog : sliceBudget * Fintype.card (LayerSamplerVariables G I n B) ≤ pModel)
    (hRawCap : rawCap ≤ Real.exp pModel)
    (hPrecision : u + 2 * pModel + max (max nativeBudget 3)
      (2 * u + 4 * pModel + 20) + 32 ≤ projectionPrecision)
    (hProjection : projectionPrecision ≤ E)
    (hdirect : A.NativeDetection degree sliceBudget testBudget nativeBudget α)
    (hThreshold : α ≤ Real.exp (-(2 * u + 4 * pModel + 8)))
    (hexcess :
      (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
        (A.law.siteLaw (A.physicalBox hξone hmargin)) rawCap ≤
          6 * positiveProjectionAccuracy E)
    (hInputSlice : p ≤ sliceBudget)
    (hProjectionTest :
      AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p) ≤ testBudget)
    (hMarkovPrecision :
      AllocatedExternalCandidateProblem.positiveKernelMarkovPrecisionParameter (2 * p) e ≤ u) :
    A.FrontSourceProfile degree p e := by
  have hcap := marginalCap_max_one_exp_bound hpModel hRawCap
  have haccuracy : positiveProjectionAccuracy E ≤ positiveProjectionAccuracy projectionPrecision := by
    unfold positiveProjectionAccuracy
    apply Real.exp_le_exp.mpr
    linarith only [hProjection]
  have hexcess' :
      (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
        (A.law.siteLaw (A.physicalBox hξone (fun x => (A.trimMargin_proper x).le)))
        (max 1 rawCap) ≤ 6 * positiveProjectionAccuracy projectionPrecision :=
    ((FiniteProbabilityWeights.excessMass_max_one_le
      (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty)
      (A.law.siteLaw (A.physicalBox hξone hmargin)) rawCap).trans hexcess).trans
      (mul_le_mul_of_nonneg_left haccuracy (by norm_num))
  exact {
    u := u
    pModel := pModel
    sliceBudget := sliceBudget
    testBudget := testBudget
    nativeBudget := nativeBudget
    projectionPrecision := projectionPrecision
    marginalCap := max 1 rawCap
    narrow := hξone
    u_nonneg := hu
    model_nonneg := hpModel
    input_model := hInputModel
    native_nonneg := hNative
    slice_nonneg := hSliceNonneg
    test_nontrivial := hTestNontrivial
    slice_log := hSliceLog
    marginal_one := hcap.1
    marginal_bound := hcap.2
    projection_precision := hPrecision
    detection := hdirect.mono_tests A le_rfl le_rfl hThreshold
    physical_excess := hexcess'
    input_slice := hInputSlice
    projection_test := hProjectionTest
    markov_precision := hMarkovPrecision }

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.SharedWidthPreparedShortForecastProductiveModelAttachment
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m nX M : ℕ} {X₀ J₀ : Type}
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite

def SharedWidthPreparedCenteredShortForecastProductiveGoodModelInterface
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale
      (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j => RankPreparationLayer.Coord (prep j))
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    (selection : Fin (0 + 1) ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ) (uSource pModel pSlice : ℝ)
    (Vtail : Fin m → ℝ≥0) (τ u p forecastCap : ℝ)
    {Q : Fin m → Type} [∀ j, Fintype (Q j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection
      (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [IsProbabilityMeasure μ]
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget : ℝ)
    (B0 gainLog gain Pgood : ℝ) (Qgood : ℕ)
    (spatialEmbedding : Fin 2 × Fin nX ↪ (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (Pprod : ℝ) : Prop :=
  SharedWidthPreparedCenteredForecastModelExtensionInterface
    (G := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (I := (PreparedSamplerContinuous prep)) (n := (preparedSamplerTransverse prep)) (J := (fun j : Fin m => RankPreparationLayer.Coord (prep j)))
      (B := (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (U := U) (basis := b) (S := S) (hR := hR) (hσ := hσ)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (uSource := uSource) (pModel := pModel) (pSlice := pSlice)
    (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
    (hb := hb) (o := o) (μ := μ)
    (Good := fun (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
      (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
      (V : Option (LayerSamplerVariables
        (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
        (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
        (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ)
      (bases : Finset (Fin nX → ℤ))
      (law : CoefficientTorus (K := LayerSamplerVariables
        (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
        (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
        (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U →
        FiniteProbabilityWeights (bases × rectangularWeightIndices 0 V 1)) =>
      PreparedCenteredShortForecastGoodConclusion (m := m) (nX := nX) (M := M) prep U b S bW hb o hR hσ μ poly hmem
        stride V bases gainLog gain Qgood spatialEmbedding law ∧
      PreparedCenteredForecastProductiveConclusion (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S hb o hR hσ μ poly hmem
        N V bases gainLog law)
    Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
    (max (preparedCenteredShortForecastGoodRequired m B0 Pgood)
      ((Pprod + preparedModularGeneralProductivityExponent m) ^ preparedModularGeneralProductivityExponent m))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedUniformDegreeProductiveSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

def PreparedUniformDegreeProductiveSourceConclusion
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale
      (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j => RankPreparationLayer.Coord (prep j))
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ) (pModel pSlice : ℝ)
    (Vtail : Fin m → ℝ≥0) (τ u p forecastCap : ℝ)
    {Q : Fin m → Type} [∀ j, Fintype (Q j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection
      (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables
      (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
      (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [IsProbabilityMeasure μ]
    (Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius Pscale
      Pseed Qw gainLog gain Vlog : ℝ) (Qgood : ℕ) : Prop :=
    let baseB0 := preparedUniformDegreeProductiveCertificateBudget
      M nX pRadius Pscale Pseed Qw (gainLog + 8) Vlog
    let Pwidth := 4 * (Plate + 8) ^ 2
    let Bcert := preparedForecastGoodCertificateBudget baseB0 Pchart Pwidth gainLog Vlog
    let Pgood := preparedForecastGoodAnalyticBudget
      (preparedCenteredShortForecastSpatialExponent m) baseB0 Pchart Pwidth gainLog Vlog
    SharedWidthPreparedCenteredShortForecastProductiveGoodModelInterface
      (m := m) (nX := nX) (M := M) (X₀ := X₀) (J₀ := J₀) (Q := Q) (R := R) (σ := σ) prep U b hR hσ S (enlargedPreparedCommonCanonicalSelection m (modularInitialBlockCount m (nX + m * M)) 0 (Nat.zero_le m)) stride N Pdetect
      (u + 2 * p + 1) pModel pSlice Vtail τ u p forecastCap hb o bW μ
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget
      Bcert gainLog gain Pgood Qgood (preparedSpatialKernelBlocks m M nX) Pwidth

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteNestedSourceArrays
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (sampler : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

local notation "countConstants" => AllocatedExternalCandidateSampler.degreeSourceCountConstants
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

noncomputable def preparedFiniteForwardInnerSourceProfile
    (degree cutoff exponent Cprimitive Cslice Cdirect Cresource : ℕ)
    (x gainLog stageLog : ℝ) (Pmaster : ℕ → ℝ) (Plate rankThreshold : ℝ)
    (hx : 0 ≤ x) (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x)
    (hprimitive : 1 ≤ Cprimitive) (hdegree : degree ≤ cutoff)
    (hExponent : allocatedCandidateForwardScheduleExponent degree m Cprimitive
      (preparedFiniteForwardInnerSourceExponent Cdirect Cresource) 2 ≤ exponent)
    (hCslice : allocatedCandidateStageSliceExponent degree m Cprimitive ≤ Cslice)
    (hresource : ∀ r < degree,
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m r)
        (r + 1) (Pmaster r) Plate).nativeBudget ∈ Set.Icc 0
        ((preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants r true
            x gainLog stageLog + preparedFiniteForwardWork exponent countConstants r x + Cresource) ^ Cresource))
    (hNative : ∀ r < degree, sampler.NativeDetection r
      ((preparedFiniteForwardParameter exponent countConstants r x + Cslice) ^ Cslice)
      ((preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants r true x gainLog stageLog)
          (preparedFiniteForwardWork exponent countConstants r x)))
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m r)
        (r + 1) (Pmaster r) Plate).nativeBudget
      (Real.exp (-(2 * preparedFiniteForwardModelPrecision exponent countConstants r x gainLog stageLog +
        4 * preparedFiniteForwardWork exponent countConstants r x + 8))))
    (htags : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ x)
    (hlayers : (m : ℝ) ≤ x)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ x)
    (hsize : ∀ i, Real.exp (preparedFiniteForwardCumulative exponent countConstants degree x) ≤ (N i : ℝ))
    (hrank : Real.exp (preparedFiniteForwardCumulative exponent countConstants degree x) ≤ rankThreshold)
    (hsampling : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) rankThreshold (U j) (poly j)) :
    sampler.InnerSourceProfile degree := by
  have hschedule := allocatedCandidateForwardScheduleExponent_bounds degree m Cprimitive
    (preparedFiniteForwardInnerSourceExponent Cdirect Cresource) 2
  refine {
    x := x
    scheduleExponent := exponent
    Cprimitive := Cprimitive
    Csource := preparedFiniteForwardInnerSourceExponent Cdirect Cresource
    gainLog := gainLog
    stageLog := stageLog
    sourceNative := fun r =>
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m r)
        (r + 1) (Pmaster r) Plate).nativeBudget
    pTest := fun r => (preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
      (allocatedModelTestLog
        (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants r true x gainLog stageLog)
        (preparedFiniteForwardWork exponent countConstants r x))
    detectionLoss := fun _ => Real.exp (-gainLog) / 2
    rankThreshold := rankThreshold
    x_nonneg := hx
    gain_range := hg
    stage_range := hs
    primitive_pos := hprimitive
    base_exponent := hschedule.2.1.trans hExponent
    slice_exponent := hschedule.2.2.1.trans hExponent
    phase_exponent := fun r hr => (hschedule.2.2.2 r hr).trans hExponent
    source_nonneg := fun r hr => (hresource r hr).1
    source_bound := ?_
    test_floor := ?_
    loss_nonneg := fun _ _ => div_nonneg (Real.exp_nonneg _) (by norm_num)
    loss_bound := fun _ _ => le_rfl
    detection := ?_
    tags_input := htags
    layers_input := hlayers
    variables_input := hvariables
    size_floor := hsize
    rank_floor := hrank
    sampling_rank := hsampling }
  · intro r hr
    exact (hresource r hr).2.trans
      ((Classical.choose_spec (exists_preparedFiniteForwardPairedResource_budget Cdirect Cresource)).2
        exponent countConstants r hx hg hs)
  · intro r hr
    exact (preparedFiniteForwardDetectorPolynomial_stage_bounds cutoff exponent Cdirect
      countConstants r true hx hg hs).2 r (hr.le.trans hdegree)
  · intro r hr
    have hb : 0 ≤ preparedFiniteForwardParameter exponent countConstants r x :=
      preparedFiniteForwardParameter_nonneg exponent countConstants r hx
    have hCtwo : 2 ≤ Cslice :=
      (allocatedCandidateStageSlice_bounds degree m Cprimitive hb).1.trans hCslice
    have hslice : allocatedCandidateStageSlice degree m Cprimitive
        (preparedFiniteForwardParameter exponent countConstants r x) ≤
        (preparedFiniteForwardParameter exponent countConstants r x + Cslice) ^ Cslice := by
      unfold allocatedCandidateStageSlice
      apply (pow_le_pow_left₀ (add_nonneg hb (Nat.cast_nonneg _))
        (add_le_add le_rfl (Nat.cast_le.mpr hCslice)) _).trans
      exact pow_le_pow_right₀ (by
        have hC : (2 : ℝ) ≤ Cslice := Nat.cast_le.mpr hCtwo
        linarith only [hb, hC]) hCslice
    exact AllocatedExternalCandidateSampler.NativeDetection.mono_tests sampler
      (hNative r hr) hslice le_rfl
      (preparedFiniteForwardInnerDetectionThreshold_bound exponent countConstants r hx hg hs)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (sampler : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

local notation "countConstants" => AllocatedExternalCandidateSampler.degreeSourceCountConstants
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

noncomputable def preparedFiniteForwardResourceLayerInnerSourceProfile
    (q degree cutoff exponent Cprimitive Cslice Cdirect Cresource : ℕ)
    (x gainLog stageLog : ℝ) (Pmaster : ℕ → ℝ) (Plate rankThreshold : ℝ)
    (hx : 0 ≤ x) (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x)
    (hprimitive : 1 ≤ Cprimitive) (hdegree : degree ≤ cutoff)
    (hExponent : allocatedCandidateForwardScheduleExponent degree m Cprimitive
      (preparedFiniteForwardInnerSourceExponent Cdirect Cresource) 2 ≤ exponent)
    (hCslice : allocatedCandidateStageSliceExponent degree m Cprimitive ≤ Cslice)
    (hresource : ∀ r < degree,
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants q r)
        (r + 1) (Pmaster r) Plate).nativeBudget ∈ Set.Icc 0
        ((preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants r true
            x gainLog stageLog + preparedFiniteForwardWork exponent countConstants r x + Cresource) ^ Cresource))
    (hNative : ∀ r < degree, sampler.NativeDetection r
      ((preparedFiniteForwardParameter exponent countConstants r x + Cslice) ^ Cslice)
      ((preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants r true x gainLog stageLog)
          (preparedFiniteForwardWork exponent countConstants r x)))
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants q r)
        (r + 1) (Pmaster r) Plate).nativeBudget
      (Real.exp (-(2 * preparedFiniteForwardModelPrecision exponent countConstants r x gainLog stageLog +
        4 * preparedFiniteForwardWork exponent countConstants r x + 8))))
    (htags : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ x)
    (hlayers : (m : ℝ) ≤ x)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ x)
    (hsize : ∀ i, Real.exp (preparedFiniteForwardCumulative exponent countConstants degree x) ≤ (N i : ℝ))
    (hrank : Real.exp (preparedFiniteForwardCumulative exponent countConstants degree x) ≤ rankThreshold)
    (hsampling : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) rankThreshold (U j) (poly j)) :
    sampler.InnerSourceProfile degree := by
  have hschedule := allocatedCandidateForwardScheduleExponent_bounds degree m Cprimitive
    (preparedFiniteForwardInnerSourceExponent Cdirect Cresource) 2
  refine {
    x := x
    scheduleExponent := exponent
    Cprimitive := Cprimitive
    Csource := preparedFiniteForwardInnerSourceExponent Cdirect Cresource
    gainLog := gainLog
    stageLog := stageLog
    sourceNative := fun r =>
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants q r)
        (r + 1) (Pmaster r) Plate).nativeBudget
    pTest := fun r => (preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
      (allocatedModelTestLog
        (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants r true x gainLog stageLog)
        (preparedFiniteForwardWork exponent countConstants r x))
    detectionLoss := fun _ => Real.exp (-gainLog) / 2
    rankThreshold := rankThreshold
    x_nonneg := hx
    gain_range := hg
    stage_range := hs
    primitive_pos := hprimitive
    base_exponent := hschedule.2.1.trans hExponent
    slice_exponent := hschedule.2.2.1.trans hExponent
    phase_exponent := fun r hr => (hschedule.2.2.2 r hr).trans hExponent
    source_nonneg := fun r hr => (hresource r hr).1
    source_bound := ?_
    test_floor := ?_
    loss_nonneg := fun _ _ => div_nonneg (Real.exp_nonneg _) (by norm_num)
    loss_bound := fun _ _ => le_rfl
    detection := ?_
    tags_input := htags
    layers_input := hlayers
    variables_input := hvariables
    size_floor := hsize
    rank_floor := hrank
    sampling_rank := hsampling }
  · intro r hr
    exact (hresource r hr).2.trans
      ((Classical.choose_spec (exists_preparedFiniteForwardPairedResource_budget Cdirect Cresource)).2
        exponent countConstants r hx hg hs)
  · intro r hr
    exact (preparedFiniteForwardDetectorPolynomial_stage_bounds cutoff exponent Cdirect
      countConstants r true hx hg hs).2 r (hr.le.trans hdegree)
  · intro r hr
    have hb : 0 ≤ preparedFiniteForwardParameter exponent countConstants r x :=
      preparedFiniteForwardParameter_nonneg exponent countConstants r hx
    have hCtwo : 2 ≤ Cslice :=
      (allocatedCandidateStageSlice_bounds degree m Cprimitive hb).1.trans hCslice
    have hslice : allocatedCandidateStageSlice degree m Cprimitive
        (preparedFiniteForwardParameter exponent countConstants r x) ≤
        (preparedFiniteForwardParameter exponent countConstants r x + Cslice) ^ Cslice := by
      unfold allocatedCandidateStageSlice
      apply (pow_le_pow_left₀ (add_nonneg hb (Nat.cast_nonneg _))
        (add_le_add le_rfl (Nat.cast_le.mpr hCslice)) _).trans
      exact pow_le_pow_right₀ (by
        have hC : (2 : ℝ) ≤ Cslice := Nat.cast_le.mpr hCtwo
        linarith only [hb, hC]) hCslice
    exact AllocatedExternalCandidateSampler.NativeDetection.mono_tests sampler
      (hNative r hr) hslice le_rfl
      (preparedFiniteForwardInnerDetectionThreshold_bound exponent countConstants r hx hg hs)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (sampler : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

local notation "countConstants" => AllocatedExternalCandidateSampler.degreeSourceCountConstants
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

noncomputable def preparedFiniteForwardActualInnerSourceProfile
    (degree cutoff exponent Cprimitive Cslice Cdirect : ℕ)
    (x gainLog stageLog Bstruct pnum Pchart Qstride Plate rankThreshold : ℝ)
    (hx : 0 ≤ x) (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x)
    (hprimitive : 1 ≤ Cprimitive) (hdegree : degree ≤ cutoff) (hcutoff : cutoff ≤ m)
    (hBstruct : Bstruct ∈ Set.Icc 0 x) (hpnum : pnum ∈ Set.Icc 0 x)
    (hPchart : Pchart ∈ Set.Icc 0 x) (hQstride : Qstride ∈ Set.Icc 0 x)
    (hG : (Fintype.card G : ℝ) ≤ x)
    (hExponent : allocatedCandidateForwardScheduleExponent degree m Cprimitive
      (preparedFiniteForwardInnerSourceExponent Cdirect
        (preparedFiniteForwardActualNativeBudgetExponent m
          (preparedFiniteForwardDetectorPolynomial cutoff))) 2 ≤ exponent)
    (hCslice : allocatedCandidateStageSliceExponent degree m Cprimitive ≤ Cslice)
    (hNative : ∀ r < degree, sampler.NativeDetection r
      ((preparedFiniteForwardParameter exponent countConstants r x + Cslice) ^ Cslice)
      ((preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants r true x gainLog stageLog)
          (preparedFiniteForwardWork exponent countConstants r x)))
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m r)
        (r + 1)
        (preparedFiniteForwardActualLocalMaster m G
          (Fintype.card (LayerSamplerVariables G I n B)) (Fintype.card X)
          (preparedFiniteForwardDetectorPolynomial cutoff) exponent Cdirect countConstants r
          x gainLog stageLog Bstruct pnum Pchart Qstride) Plate).nativeBudget
      (Real.exp (-(2 * preparedFiniteForwardModelPrecision exponent countConstants r x gainLog stageLog +
        4 * preparedFiniteForwardWork exponent countConstants r x + 8))))
    (htags : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ x)
    (hlayers : (m : ℝ) ≤ x)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ x)
    (hsize : ∀ i, Real.exp (preparedFiniteForwardCumulative exponent countConstants degree x) ≤ (N i : ℝ))
    (hrank : Real.exp (preparedFiniteForwardCumulative exponent countConstants degree x) ≤ rankThreshold)
    (hsampling : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) rankThreshold (U j) (poly j)) :
    sampler.InnerSourceProfile degree := by
  let Pdetect := preparedFiniteForwardDetectorPolynomial cutoff
  let Cresource := preparedFiniteForwardActualNativeBudgetExponent m Pdetect
  let Pmaster := fun r => preparedFiniteForwardActualLocalMaster m G
    (Fintype.card (LayerSamplerVariables G I n B)) (Fintype.card X)
    Pdetect exponent Cdirect countConstants r x gainLog stageLog Bstruct pnum Pchart Qstride
  have hExponentTwo : 2 ≤ exponent :=
    (allocatedCandidateForwardScheduleExponent_bounds degree m Cprimitive
      (preparedFiniteForwardInnerSourceExponent Cdirect Cresource) 2).1.trans hExponent
  have hX : (Fintype.card X : ℝ) ≤ x := by
    have hXtags : Fintype.card X ≤ Fintype.card (X ⊕ (Σ j, J j)) := by
      rw [Fintype.card_sum]
      exact Nat.le_add_right _ _
    exact (Nat.cast_le.mpr hXtags).trans htags
  have hresource (r : ℕ) (hr : r < degree) :
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m r)
        (r + 1) (Pmaster r) Plate).nativeBudget ∈ Set.Icc 0
        ((preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants r true
            x gainLog stageLog + preparedFiniteForwardWork exponent countConstants r x + Cresource) ^ Cresource) := by
    have hrm : r < m + 1 := Nat.lt_succ_of_le ((Nat.le_of_lt hr).trans (hdegree.trans hcutoff))
    have h := (Classical.choose_spec (exists_preparedFiniteForwardActualNativeBudget m Pdetect)).2
      ⟨r, hrm⟩ exponent Cdirect countConstants r true
      (G := G) hExponentTwo hx hg hs hBstruct hpnum hPchart hQstride
      hvariables hX hG Plate
    exact h.2.2.1
  exact preparedFiniteForwardInnerSourceProfile sampler degree cutoff exponent Cprimitive Cslice
    Cdirect Cresource x gainLog stageLog Pmaster Plate rankThreshold
    hx hg hs hprimitive hdegree hExponent hCslice hresource hNative htags hlayers
    hvariables hsize hrank hsampling

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (sampler : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

local notation "countConstants" => AllocatedExternalCandidateSampler.degreeSourceCountConstants
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

noncomputable def preparedFiniteForwardActualResourceLayerInnerSourceProfile
    (q degree cutoff exponent Cprimitive Cslice Cdirect : ℕ)
    (x gainLog stageLog Bstruct pnum Pchart Qstride Plate rankThreshold : ℝ)
    (hx : 0 ≤ x) (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x)
    (hprimitive : 1 ≤ Cprimitive) (hdegree : degree ≤ cutoff) (hcutoff : cutoff ≤ q)
    (hBstruct : Bstruct ∈ Set.Icc 0 x) (hpnum : pnum ∈ Set.Icc 0 x)
    (hPchart : Pchart ∈ Set.Icc 0 x) (hQstride : Qstride ∈ Set.Icc 0 x)
    (hG : (Fintype.card G : ℝ) ≤ x)
    (hExponent : allocatedCandidateForwardScheduleExponent degree m Cprimitive
      (preparedFiniteForwardInnerSourceExponent Cdirect
        (preparedFiniteForwardActualNativeBudgetExponent q
          (preparedFiniteForwardDetectorPolynomial cutoff))) 2 ≤ exponent)
    (hCslice : allocatedCandidateStageSliceExponent degree m Cprimitive ≤ Cslice)
    (hNative : ∀ r < degree, sampler.NativeDetection r
      ((preparedFiniteForwardParameter exponent countConstants r x + Cslice) ^ Cslice)
      ((preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog
          (preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants r true x gainLog stageLog)
          (preparedFiniteForwardWork exponent countConstants r x)))
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants q r)
        (r + 1)
        (preparedFiniteForwardActualLocalMaster q G
          (Fintype.card (LayerSamplerVariables G I n B)) (Fintype.card X)
          (preparedFiniteForwardDetectorPolynomial cutoff) exponent Cdirect countConstants r
          x gainLog stageLog Bstruct pnum Pchart Qstride) Plate).nativeBudget
      (Real.exp (-(2 * preparedFiniteForwardModelPrecision exponent countConstants r x gainLog stageLog +
        4 * preparedFiniteForwardWork exponent countConstants r x + 8))))
    (htags : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ x)
    (hlayers : (m : ℝ) ≤ x)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ x)
    (hsize : ∀ i, Real.exp (preparedFiniteForwardCumulative exponent countConstants degree x) ≤ (N i : ℝ))
    (hrank : Real.exp (preparedFiniteForwardCumulative exponent countConstants degree x) ≤ rankThreshold)
    (hsampling : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) rankThreshold (U j) (poly j)) :
    sampler.InnerSourceProfile degree := by
  let Pdetect := preparedFiniteForwardDetectorPolynomial cutoff
  let Cresource := preparedFiniteForwardActualNativeBudgetExponent q Pdetect
  let Pmaster := fun r => preparedFiniteForwardActualLocalMaster q G
    (Fintype.card (LayerSamplerVariables G I n B)) (Fintype.card X)
    Pdetect exponent Cdirect countConstants r x gainLog stageLog Bstruct pnum Pchart Qstride
  have hExponentTwo : 2 ≤ exponent :=
    (allocatedCandidateForwardScheduleExponent_bounds degree m Cprimitive
      (preparedFiniteForwardInnerSourceExponent Cdirect Cresource) 2).1.trans hExponent
  have hX : (Fintype.card X : ℝ) ≤ x := by
    have hXtags : Fintype.card X ≤ Fintype.card (X ⊕ (Σ j, J j)) := by
      rw [Fintype.card_sum]
      exact Nat.le_add_right _ _
    exact (Nat.cast_le.mpr hXtags).trans htags
  have hresource (r : ℕ) (hr : r < degree) :
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants q r)
        (r + 1) (Pmaster r) Plate).nativeBudget ∈ Set.Icc 0
        ((preparedFiniteForwardPairedSourcePrecision exponent Cdirect countConstants r true
            x gainLog stageLog + preparedFiniteForwardWork exponent countConstants r x + Cresource) ^ Cresource) := by
    have hrq : r < q + 1 := Nat.lt_succ_of_le ((Nat.le_of_lt hr).trans (hdegree.trans hcutoff))
    have h := (Classical.choose_spec (exists_preparedFiniteForwardActualNativeBudget q Pdetect)).2
      ⟨r, hrq⟩ exponent Cdirect countConstants r true
      (G := G) hExponentTwo hx hg hs hBstruct hpnum hPchart hQstride
      hvariables hX hG Plate
    exact h.2.2.1
  exact preparedFiniteForwardResourceLayerInnerSourceProfile sampler q degree cutoff exponent Cprimitive Cslice
    Cdirect Cresource x gainLog stageLog Pmaster Plate rankThreshold
    hx hg hs hprimitive hdegree hExponent hCslice hresource hNative htags hlayers
    hvariables hsize hrank hsampling

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteNestedCanonicalEarlyPrimitiveBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedFiniteNestedEarlyPrimitive_budget
    (m cutoff A Cdirect outerDepth innerDepth : ℕ) (constants : ℕ → ℕ)
    (hA : 2 ≤ A) (hcutoff : cutoff ≤ m) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (G : Type) [Fintype G] (count nX M : ℕ)
      {Bstruct pnum Qstride gainLog stageLog : ℝ},
      0 ≤ Bstruct → pnum ∈ Set.Icc 0 Bstruct → Qstride ∈ Set.Icc 0 Bstruct →
      gainLog ∈ Set.Icc 0 Bstruct → stageLog ∈ Set.Icc 0 Bstruct →
      (count : ℝ) ≤ Bstruct → (nX : ℝ) ≤ Bstruct →
      (Fintype.card G : ℝ) ≤ Bstruct → (M : ℝ) ≤ Bstruct →
      allocatedCommonProductRadiusLog m Bstruct Bstruct ∈ Set.Icc 0 ((Bstruct + 2) ^ C) ∧
      allocatedComparisonDimension m pnum ∈ Set.Icc 0 ((Bstruct + 2) ^ C) ∧
      ((nX + m * M : ℕ) : ℝ) ∈ Set.Icc 0 ((Bstruct + 2) ^ C) ∧
      preparedFiniteForwardParameter A constants innerDepth
        (candidateNestedForwardSeed A constants innerDepth outerDepth Bstruct) ∈
          Set.Icc 0 ((Bstruct + 2) ^ C) ∧
      ∀ k : PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff,
      let seed := preparedFiniteNestedForwardAllDegreeSeed A constants Bstruct k
      let stage := (preparedFiniteNestedForwardAllDegreeStage k).val
      let sourceU := preparedFiniteForwardPairedSourcePrecision A Cdirect constants stage
        (preparedFiniteNestedForwardAllDegreeIsDirect k) seed gainLog stageLog
      let work := preparedFiniteForwardWork A constants stage seed
      preparedFiniteForwardParameter A constants stage seed ∈ Set.Icc 0 ((Bstruct + 2) ^ C) ∧
      sourceU ∈ Set.Icc 0 ((Bstruct + 2) ^ C) ∧
      preparedFiniteForwardModelPrecision A constants stage seed gainLog stageLog ∈
        Set.Icc 0 ((Bstruct + 2) ^ C) ∧
      work ∈ Set.Icc 0 ((Bstruct + 2) ^ C) ∧
      preparedFiniteNestedSourceNative m G count nX (preparedFiniteForwardDetectorPolynomial cutoff)
        A Cdirect constants Bstruct pnum Qstride gainLog stageLog 0 k ∈
          Set.Icc 0 ((Bstruct + 2) ^ C) ∧
      (preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog sourceU work) ∈ Set.Icc 0 ((Bstruct + 2) ^ C) := by
  obtain ⟨D, _, hlocal⟩ :=
    exists_candidateNestedForwardLocal_budget A Cdirect constants innerDepth outerDepth hA
  let Cnative := preparedFiniteNestedSourceNativeExponent m cutoff Cdirect
  let Cradius := preparedCommonRadiusPrimitiveExponent m
  let X : Polynomial ℕ := Polynomial.X
  let T : Polynomial ℕ := (X + 2) ^ D
  let N : Polynomial ℕ := (2 * T + Polynomial.C Cnative) ^ Cnative
  let Radius : Polynomial ℕ := (X + Polynomial.C Cradius) ^ Cradius
  let Dimension : Polynomial ℕ := allocatedComparisonDimension m X
  let ModelDimension : Polynomial ℕ := Polynomial.C (m + 1) * X
  let Detector : Polynomial ℕ := 7 * T + 12 + Polynomial.C (preparedFiniteForwardDetectorOffset cutoff)
  let Q : Polynomial ℕ := T + N + Radius + Dimension + ModelDimension + Detector
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_fixed_power_budget Q
  refine ⟨C, hC, ?_⟩
  intro G _ count nX M Bstruct pnum Qstride gainLog stageLog
    hB hnum hstride hg hs hcount hnX hG hM
  let Treal : ℝ := (Bstruct + 2) ^ D
  let Nreal : ℝ := (2 * Treal + Cnative) ^ Cnative
  let RadiusReal : ℝ := (Bstruct + Cradius) ^ Cradius
  let DimensionReal : ℝ := allocatedComparisonDimension m Bstruct
  let ModelDimensionReal : ℝ := (m + 1 : ℕ) * Bstruct
  let DetectorReal : ℝ := 7 * Treal + 12 + preparedFiniteForwardDetectorOffset cutoff
  have hT0 : 0 ≤ Treal := by dsimp only [Treal]; positivity
  have hN0 : 0 ≤ Nreal := by dsimp only [Nreal]; positivity
  have hR0 : 0 ≤ RadiusReal := by dsimp only [RadiusReal]; positivity
  have hD0 : 0 ≤ DimensionReal := (allocatedComparisonDimension_bounds m hB).1
  have hMD0 : 0 ≤ ModelDimensionReal := by dsimp only [ModelDimensionReal]; positivity
  have hDet0 : 0 ≤ DetectorReal := by dsimp only [DetectorReal]; positivity
  have htotal : Treal + Nreal + RadiusReal + DimensionReal + ModelDimensionReal + DetectorReal ≤
      (Bstruct + 2) ^ C := by
    simpa [Q, T, N, Radius, Dimension, ModelDimension, Detector, X,
      Treal, Nreal, RadiusReal, DimensionReal, ModelDimensionReal, DetectorReal,
      allocatedComparisonDimension, Polynomial.eval₂_pow] using hpoly Bstruct hB
  have hT : Treal ≤ (Bstruct + 2) ^ C := by
    linarith only [htotal, hN0, hR0, hD0, hMD0, hDet0]
  have hN : Nreal ≤ (Bstruct + 2) ^ C := by
    linarith only [htotal, hT0, hR0, hD0, hMD0, hDet0]
  have hR : RadiusReal ≤ (Bstruct + 2) ^ C := by
    linarith only [htotal, hT0, hN0, hD0, hMD0, hDet0]
  have hD : DimensionReal ≤ (Bstruct + 2) ^ C := by
    linarith only [htotal, hT0, hN0, hR0, hMD0, hDet0]
  have hMD : ModelDimensionReal ≤ (Bstruct + 2) ^ C := by
    linarith only [htotal, hT0, hN0, hR0, hD0, hDet0]
  have hDet : DetectorReal ≤ (Bstruct + 2) ^ C := by
    linarith only [htotal, hT0, hN0, hR0, hD0, hMD0]
  have hradius := preparedCommonRadiusPrimitive_bound m m le_rfl hB
  have hdim : allocatedComparisonDimension m pnum ≤ DimensionReal :=
    allocatedComparisonDimension_mono m hnum.1 hnum.2
  have hmodeldim : ((nX + m * M : ℕ) : ℝ) ≤ ModelDimensionReal := by
    have hmul := mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    dsimp only [ModelDimensionReal]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    nlinarith only [hnX, hmul]
  have hend := (hlocal hB hg hs outerDepth le_rfl innerDepth le_rfl).2.1
  refine ⟨⟨hradius.1, hradius.2.trans hR⟩,
    ⟨(allocatedComparisonDimension_bounds m hnum.1).1, hdim.trans hD⟩,
    ⟨Nat.cast_nonneg _, hmodeldim.trans hMD⟩, ⟨hend.1, hend.2.trans hT⟩, ?_⟩
  intro k seed stage sourceU work
  have hloc := hlocal hB hg hs k.1.val (Nat.le_of_lt_succ k.1.isLt)
    k.2.1.val (Nat.le_of_lt_succ k.2.1.isLt)
  have hparam := hloc.2.1
  have hwork := hloc.2.2.1
  have hmodel := hloc.2.2.2.2.1
  have hsource := hloc.2.2.2.2.2 (preparedFiniteNestedForwardAllDegreeIsDirect k)
  have hsourceFalse := hloc.2.2.2.2.2 false
  simp only [preparedFiniteForwardPairedSourcePrecision_model] at hsourceFalse
  have hnative := preparedFiniteNestedSourceNative_budget m G count nX A Cdirect constants
    hcutoff hA hB hnum hstride hg hs hcount hnX hG 0 k
  have hnativeBound : preparedFiniteNestedSourceNative m G count nX
      (preparedFiniteForwardDetectorPolynomial cutoff) A Cdirect constants
      Bstruct pnum Qstride gainLog stageLog 0 k ≤ Nreal := by
    apply hnative.2.trans
    apply pow_le_pow_left₀
      (add_nonneg (add_nonneg hsourceFalse.1 hwork.1) (Nat.cast_nonneg Cnative))
    dsimp only [Treal, Nreal]
    linarith only [hsourceFalse.2, hwork.2]
  have hdetector : (preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
      (allocatedModelTestLog sourceU work) ∈ Set.Icc 0 DetectorReal := by
    have hs0 : 0 ≤ sourceU := hsource.1
    have hsT : sourceU ≤ Treal := hsource.2
    have hw0 : 0 ≤ work := hwork.1
    have hwT : work ≤ Treal := hwork.2
    rw [preparedFiniteForwardDetectorPolynomial_eval]
    dsimp only [allocatedModelTestLog, DetectorReal]
    have hoffset : (0 : ℝ) ≤ preparedFiniteForwardDetectorOffset cutoff := Nat.cast_nonneg _
    exact ⟨by linarith only [hs0, hw0, hoffset], by linarith only [hsT, hwT]⟩
  exact ⟨⟨hparam.1, hparam.2.trans hT⟩, ⟨hsource.1, hsource.2.trans hT⟩,
    ⟨hmodel.1, hmodel.2.trans hT⟩, ⟨hwork.1, hwork.2.trans hT⟩,
    ⟨hnative.1, hnativeBound.trans hN⟩, ⟨hdetector.1, hdetector.2.trans hDet⟩⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCandidateInnerSourceGain
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {sampler : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateSampler.InnerSourceProfile

noncomputable def raise_gain {degree : ℕ} (P : sampler.InnerSourceProfile degree)
    (gain : ℝ) (hgain : P.gainLog ≤ gain) (hgainx : gain ≤ P.x)
    (hloss : ∀ r < degree, P.detectionLoss r ≤ Real.exp (-gain) / 2) :
    sampler.InnerSourceProfile degree := by
  refine { P with
    gainLog := gain
    gain_range := ⟨P.gain_range.1.trans hgain, hgainx⟩
    source_bound := ?_
    loss_bound := hloss
  }
  intro r hr
  apply (P.source_bound r hr).trans
  have hsource0 := (preparedFiniteForward_model_precision_bounds
    P.scheduleExponent AllocatedExternalCandidateSampler.degreeSourceCountConstants r
    P.x_nonneg P.gain_range P.stage_range).2.1
  have hwork0 := preparedFiniteForwardWork_nonneg P.scheduleExponent
    AllocatedExternalCandidateSampler.degreeSourceCountConstants r P.x_nonneg
  apply pow_le_pow_left₀ (add_nonneg (add_nonneg hsource0 hwork0) (Nat.cast_nonneg _))
  unfold preparedFiniteForwardSourcePrecision preparedFiniteForwardModelPrecision
  linarith only [hgain]

noncomputable def with_gain_detection {degree : ℕ} (P : sampler.InnerSourceProfile degree)
    (gain : ℝ) (hgain : P.gainLog ≤ gain) (hgainx : gain ≤ P.x)
    (loss : ℕ → ℝ) (hzero : ∀ r < degree, 0 ≤ loss r)
    (hloss : ∀ r < degree, loss r ≤ Real.exp (-gain) / 2)
    (hdetect : ∀ r < degree, sampler.NativeDetection r
      (allocatedCandidateStageSlice degree m P.Cprimitive
        (preparedFiniteForwardParameter P.scheduleExponent
          AllocatedExternalCandidateSampler.degreeSourceCountConstants r P.x))
      (P.pTest r) (P.sourceNative r) (loss r)) :
    sampler.InnerSourceProfile degree := by
  have hweaken : Real.exp (-gain) / 2 ≤ Real.exp (-P.gainLog) / 2 :=
    div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hgain)) (by norm_num)
  let Q : sampler.InnerSourceProfile degree := { P with
    detectionLoss := loss
    loss_nonneg := hzero
    loss_bound := fun r hr => (hloss r hr).trans hweaken
    detection := hdetect
  }
  exact Q.raise_gain gain hgain hgainx hloss

end AllocatedExternalCandidateSampler.InnerSourceProfile
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidatePrimitiveFrontDescentData
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {f : ℕ} (FmarkNative : RationalFilteredNilmanifold M t f) {φ : L →ₗ⁅ℚ⁆ M}
    {marked : FmarkNative.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem.PositiveKernelPreparation

variable {cost massThreshold scoreThreshold p : ℝ} {e : ℕ}
    {P : AllocatedExternalCandidateProblem (E := E) A D FmarkNative.filtration φ marked observable weight
      cost massThreshold scoreThreshold}
    (prep : P.PositiveKernelPreparation p e)

theorem exists_native_marked_descended_quotient
    (pBudget : ℝ) (hs : 1 ≤ s) (hpBudget : 0 ≤ pBudget)
    (hD : D.GeometryComplexityLE pBudget) (hFmark : FmarkNative.GeometryComplexityLE pBudget)
    (hmark : ∀ i j, rationalLogHeight (FmarkNative.basis.repr (φ (D.basis j)) i) ≤ pBudget)
    (hqBudget : positiveKernelPreparationParameter p ≤ pBudget) :
    ∃ hker : ∀ x ∈ prep.nativeQuotientIdeal, φ x = 0,
    ∃ dQ : ℕ, dQ ≤ d ∧ ∃ Q : RationalFilteredNilmanifold (L ⧸ prep.nativeQuotientIdeal) s dQ,
      Q.filtration = D.filtration.quotientLie prep.nativeQuotientIdeal prep.nativeQuotientIdeal_terminal ∧
      Q.lattice = D.lattice.map (D.filtration.quotientStepHom prep.nativeQuotientIdeal prep.nativeQuotientIdeal_terminal) ∧
      Q.GeometryComplexityLE
        ((pBudget + 2) ^ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s) ∧
      (∀ i j, rationalLogHeight (Q.basis.repr (lieQuotientMap prep.nativeQuotientIdeal (D.basis j)) i) ≤
        (pBudget + 2) ^ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s) ∧
      (∀ i j, rationalLogHeight
        (FmarkNative.basis.repr
          (quotientInducedMark prep.nativeQuotientIdeal φ hker (Q.basis j)) i) ≤
        quotientInducedMarkHeightBudget
          ((pBudget + 2) ^ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s)) ∧
      (letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ prep.nativeQuotientIdeal))
       letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ prep.nativeQuotientIdeal)) :=
         IsModuleTopology.topologicalAddGroup ℝ _
       letI := realification_moduleTopology_t2 Q.basis
       ∃ descended : (X → ℤ) → Q.Niltest (fullTaggedVariableWeight (X := X) J),
         (∀ x, (descended x).UnitIntervalValued) ∧
         (∀ x y, ‖(descended x).observable y‖ ≤ 1) ∧
         (∀ x, (descended x).ComplexityLE
           ((pBudget + 2) ^ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s)) ∧
         (∀ x, letI := Q.metricSpace;
           LipschitzWith
             ⟨Real.exp ((pBudget + 2) ^ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s),
               Real.exp_nonneg _⟩ (descended x).observable) ∧
         (∀ x (g : D.RealGroup), (descended x).observable (QuotientGroup.mk
           (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
             (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap prep.nativeQuotientIdeal) g)) =
             (prep.selected.tests x).observable (QuotientGroup.mk g)) ∧
         (∀ x y η, (∀ z, ‖observable x z - observable y z‖ ≤ η) →
           ∀ z, ‖(descended x).observable z - (descended y).observable z‖ ≤ η) ∧
         ∀ entropy : ℝ → ℝ,
           (∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ, (n : ℝ) ≤ entropy η ∧
             ∃ rep : Fin n → {x : X → ℤ // x ∈ integerBox N},
               ∀ x ∈ integerBox N, ∃ i, ∀ y,
                 ‖observable x y - observable (rep i).val y‖ ≤ η) →
           ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ, (n : ℝ) ≤ entropy η ∧
             ∃ rep : Fin n → {x : X → ℤ // x ∈ integerBox N},
               ∀ x ∈ integerBox N, ∃ i, ∀ y,
                 ‖(descended x).observable y - (descended (rep i).val).observable y‖ ≤ η) := by
  classical
  obtain ⟨hker, dQ, hdQ, Q, hQF, hQL, hQ, hprojection, hdescended⟩ :=
    prep.exists_native_descended_quotient FmarkNative.basis pBudget hs hpBudget hD
      hFmark.1 hmark hqBudget
  have hdegree : 1 ≤ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s :=
    (by omega : 1 ≤ 2).trans
      (RationalFilteredNilmanifold.positiveKernelNativeDescentExponent_ge_two s)
  have hinflate : pBudget ≤
      (pBudget + 2) ^ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s :=
    le_power_budget hpBudget hdegree
  have hnonneg : 0 ≤
      (pBudget + 2) ^ RationalFilteredNilmanifold.positiveKernelNativeDescentExponent s :=
    hpBudget.trans hinflate
  have hinduced := D.quotientInducedMark_native_logHeight FmarkNative
    prep.nativeQuotientIdeal Q φ hker hnonneg (hD.mono D hinflate) hQ hprojection
    (fun i j => (hmark i j).trans hinflate)
  exact ⟨hker, dQ, hdQ, Q, hQF, hQL, hQ, hprojection, hinduced, hdescended⟩

end AllocatedExternalCandidateProblem.PositiveKernelPreparation
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativePositiveNativeRuleCanonical
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module
open scoped BigOperators TensorProduct

noncomputable def candidateSourceRecursiveNextSeedExponent (s Cprimitive : ℕ) : ℕ :=
  (exists_allocatedCandidateNestedTerminal_uniformLayers_polynomial_budget
    (s + 1) Cprimitive (candidateSourceBackendPolynomial s)).choose

theorem candidateSourceBackendPolynomial_le_next_seed
    (s Cprimitive m exponent innerDepth outer : ℕ) {x : ℝ}
    (hExponent : candidateSourceRecursiveNextSeedExponent s Cprimitive ≤ exponent)
    (hdepth : s + 2 ≤ innerDepth) (hx : 0 ≤ x)
    (hm : (m : ℝ) ≤ candidateNestedForwardSeed exponent
      AllocatedExternalCandidateSampler.degreeSourceCountConstants innerDepth outer x) :
    (candidateSourceBackendPolynomial s).eval₂ (Nat.castRingHom ℝ)
      (nativePhysicalTerminalFullBudget (s + 1) m Cprimitive exponent
        (candidateNestedForwardSeed exponent
          AllocatedExternalCandidateSampler.degreeSourceCountConstants innerDepth outer x)) ≤
      candidateNestedForwardSeed exponent
        AllocatedExternalCandidateSampler.degreeSourceCountConstants innerDepth (outer + 1) x := by
  exact (exists_allocatedCandidateNestedTerminal_uniformLayers_polynomial_budget
    (s + 1) Cprimitive (candidateSourceBackendPolynomial s)).choose_spec.2
      m exponent AllocatedExternalCandidateSampler.degreeSourceCountConstants innerDepth outer
      hExponent hdepth hx hm

noncomputable def candidateSourceRecursiveUniformExponent (cutoff Cprimitive : ℕ) : ℕ :=
  2 + ∑ s ∈ Finset.range cutoff, candidateSourceRecursiveNextSeedExponent s Cprimitive

theorem candidateSourceRecursiveNextSeedExponent_le_uniform (Cprimitive : ℕ)
    {s cutoff : ℕ} (hs : s < cutoff) :
    candidateSourceRecursiveNextSeedExponent s Cprimitive ≤
      candidateSourceRecursiveUniformExponent cutoff Cprimitive := by
  have hsingle : candidateSourceRecursiveNextSeedExponent s Cprimitive ≤
      ∑ r ∈ Finset.range cutoff, candidateSourceRecursiveNextSeedExponent r Cprimitive :=
    Finset.single_le_sum
      (fun r _ => Nat.zero_le (candidateSourceRecursiveNextSeedExponent r Cprimitive))
      (Finset.mem_range.mpr hs)
  unfold candidateSourceRecursiveUniformExponent
  omega

end Erdos3.VectorPolynomial

end

end OAI
end


