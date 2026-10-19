-- Prove2me | Definitions.Def_OAIE3v2B289
-- name    : OAIE3v2B289
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T08:11:41.860697+00:00
-- url     : https://prove2.me/theorems/599e5a48-95a5-4c79-bcd4-06f4bfa0bef6
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 302 of 311
-- statement:
--   Definitions bundle 302 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B309`, `OAIE3v2B280`, `OAIE3v2B281`, `OAIE3v2B282` of this split.
--
--   Modules: `Dynamics/AllocatedExternalCandidateSourcePhysicalBudgetBounds.lean`, `Dynamics/CandidatePhysicalOrdinaryBudget.lean`, `Dynamics/PreparedFiniteNestedFrontNativeBudget.lean`, `Estimates/AllocatedExternalCandidateLocalFixedCenterFront.lean`, `Estimates/AllocatedFrozenPrefixStageData.lean`, `Estimates/AllocatedOrdinaryLongPhysicalTerminalConclusion.lean`, `Lattices/AllocatedAffineCanonicalBackendBudget.lean`, `Lattices/AllocatedAffinePhysicalBoundsSuccessor.lean`, `Lattices/AllocatedAffinePhysicalTerminalReset.lean`, `Linear/AllocatedExternalCandidateCommonKeepPositiveKernelPreparation.lean`, `Polynomial/AllocatedNestedDegreeInduction.lean`.
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

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFrozenPrefixStageData
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

theorem allocatedCandidateStage_cost_lt_slice (s m Cprimitive : ℕ)
    {x b cost : ℝ} (hx : 0 ≤ x) (hxb : x ≤ b)
    (hcost : cost ≤ (x + Cprimitive) ^ Cprimitive) :
    cost < allocatedCandidateStageSlice s m Cprimitive b := by
  have hb : 0 ≤ b := hx.trans hxb
  have hv := (allocatedCandidateStageBase_bounds s m Cprimitive hb).1
  have hcostBase := hcost.trans
    (allocatedCandidateStage_primitive_le_base s m Cprimitive hx hxb)
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hstrict : allocatedCandidateStageBase s m Cprimitive b <
      allocatedCandidateStageBase s m Cprimitive b + (s : ℝ) + 1 := by
    linarith only [hs0]
  have hraw := (allocatedCandidateStage_slice_bounds s m hv).2.2.1
  have hcanonical := (allocatedCandidateStageSlice_bounds s m Cprimitive hb).2
  exact hcostBase.trans_lt (hstrict.trans_le (hraw.trans hcanonical))

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d t : ℕ}
    {D : RationalFilteredNilmanifold L s d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

local notation "countConstants" => (fun n => fullChartStageCountConstant (n + 1) 254)

theorem exists_forward_axisFreezing
    (keep : LayerSamplerVariables G I n B → Prop)
    (Cprimitive scheduleExponent r : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (hcost : cost ≤ (x + Cprimitive) ^ Cprimitive)
    (hkept : ∀ i, keep i →
      Real.exp (allocatedCandidateStageSlice s m Cprimitive
        (preparedFiniteForwardParameter scheduleExponent countConstants r x)) ≤ (A.sides i : ℝ))
    (hfrozen : ∀ i, ¬keep i → (A.sides i : ℝ) ≤
      Real.exp (allocatedCandidateStageSlice s m Cprimitive
        (preparedFiniteForwardParameter scheduleExponent countConstants r x))) :
    Nonempty (P.AxisFreezing (fun _ => keep)
      (allocatedCandidateStageSlice s m Cprimitive
        (preparedFiniteForwardParameter scheduleExponent countConstants r x))) := by
  exact P.exists_axisFreezing_of_side_bounds keep _
    (allocatedCandidateStage_cost_lt_slice s m Cprimitive hx
      (le_preparedFiniteForwardParameter scheduleExponent countConstants r hx) hcost)
    hkept hfrozen

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffinePhysicalTerminalReset
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct
attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  symbolPointwiseSubalgebra realificationLieSubalgebra PolynomialRationalGrid PolynomialSlowBound
  HasCommonRefilteredOrbitFactors polynomialOrbitCoordinates associatedGradedMap realPolynomialGroupMap
  AllocatedExternalCandidateProblem.Refinement.problem
  realSymbolHomogeneousPullbackHom CertifiedFullChartFiniteHistory.outer

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

namespace AllocatedExternalCandidateProblem

variable {L M : Type} {nMarkedBasis : ℕ} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF : ℕ}
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (c : Basis (Fin nMarkedBasis) ℚ M)
    (ν : Fin nMarkedBasis → ℕ)
    (hF : ∀ j, Fmark.filtration.layer j = span ℚ (c '' {i | j ≤ ν i}))
    {η : Type} [Fintype η]
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (Fmark.filtration.AssociatedGraded ⧸
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)).toSubmodule)))
    (lift : (Fmark.filtration.AssociatedGraded ⧸
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)).toSubmodule) →ₗ[ℚ]
        Fmark.filtration.AssociatedGraded)
    (Bphase budget pAffine pFull separation : ℝ)
    (history : CertifiedFullChartFiniteHistory Fmark.filtration c ν hF J
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)).toSubmodule
      basis lift
      (Fmark.filtration.realPolynomialSymbolHom c ν hF (fullTaggedVariableWeight J)
        (Fmark.filtration.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked))
      Set.univ U poly N Bphase (s + 1))
    (data : P.AffinePhysicalTerminalData c ν hF hφ W basis lift
      Bphase budget pAffine pFull 4 history separation)
    (hcost : Real.exp cost ≤ separation)

local notation "kept" => (fun i : LayerSamplerVariables G I n B =>
  candidateSideCutoff separation ≤ A.sides i)

theorem exists_affinePhysicalTerminal_nativeReset_of_zero_restriction
    {κK μ χ : Type} [Fintype κK] [Fintype μ] [Fintype χ]
    (ω : Fin d → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (D.basis '' {i | j ≤ ω i}))
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (bk : Basis κK ℚ (LinearMap.ker φ.toLinearMap))
    (v : μ → D.filtration.AssociatedGraded)
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hD) ω W.toSubmodule)
    (hvspan : span ℚ (Set.range v) = W.toSubmodule)
    (vg : χ → Fmark.filtration.PolynomialSymbol (fun _ : {i // kept i} => 1))
    (hvgspan : span ℚ (Set.range vg) =
      (Fmark.filtration.symbolPointwiseSubalgebra c ν hF (fun _ : {i // kept i} => 1)
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))).toSubmodule)
    [Fintype (SymbolBasisIndex (fun _ : {i // kept i} => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : {i // kept i} => 1) ν)]
    (H l : ℕ) (pMap pNative : ℝ)
    (hH : 1 ≤ H) (hl : 0 < l) (hpMap : 0 ≤ pMap) (hpNative : 0 ≤ pNative)
    (hsrc : (Fintype.card (SymbolBasisIndex (fun _ : {i // kept i} => 1) ω) : ℝ) ≤ pMap)
    (htgt : (Fintype.card (SymbolBasisIndex (fun _ : {i // kept i} => 1) ν) : ℝ) ≤ pMap)
    (hHmap : (H : ℝ) ≤ Real.exp pMap)
    (hlmap : ((l * data.nFinal : ℕ) : ℝ) ≤ Real.exp pMap)
    (hmabsorb : Real.exp ((pMap + 2) ^ 4) ≤ Real.exp pNative)
    (hd : (d : ℝ) ≤ pNative) (hc : (nMarkedBasis : ℝ) ≤ pNative)
    (hk : (Fintype.card κK : ℝ) ≤ pNative)
    (hμ : (Fintype.card μ : ℝ) ≤ pNative)
    (hχ : (Fintype.card χ : ℝ) ≤ pNative)
    (hvars : (Fintype.card {i // kept i} : ℝ) ≤ pNative)
    (hHp : (H : ℝ) ≤ Real.exp pNative)
    (hbracketD : ∀ i j k, RationalHeightLE (D.basis.repr ⁅D.basis i, D.basis j⁆ k) H)
    (hbracketF : ∀ i j k, RationalHeightLE (c.repr ⁅c i, c j⁆ k) H)
    (hkernel : ∀ i j, RationalHeightLE (D.basis.repr (bk j : L) i) H)
    (hentries : ∀ k i, RationalHeightLE (c.repr (φ (D.basis i)) k) H)
    (hv : ∀ j i, RationalHeightLE
      ((D.filtration.associatedGradedBasis D.basis ω hD).repr (v j) i) H)
    (hvg : ∀ i z, RationalHeightLE
      ((Fmark.filtration.polynomialSymbolBasis c ν hF (fun _ : {i // kept i} => 1)).repr (vg i) z) H)
    (hslow : Real.exp ((pFull + allocatedEarlyAffineLeftExponent (s + 1) 4) ^
      allocatedEarlyAffineLeftExponent (s + 1) 4) ≤ Real.exp ((pNative + 2) ^ (1 : ℕ)))
    (hsideBound : Real.exp ((pNative + allocatedAffineResetCompareExponent s) ^
      allocatedAffineResetCompareExponent s) ≤ separation)
    (q : ℝ)
    (hq : Real.exp q ≤ Real.exp ((pNative + 2) ^ (1 : ℕ)))
    (hqmap : Real.exp ((pMap + 2) ^ 3 + q) ≤ Real.exp ((pNative + 2) ^ (1 : ℕ)))
    (hcutoff : Real.exp cost * ((s + 1 + 1 : ℕ) : ℝ) ≤ separation)
    (initialLong : LayerSamplerVariables G I n B → Prop)
    (hsub : ∀ i, kept i → initialLong i)
    (hzero : ∀ z : P.productive,
      D.filtration.HasCommonRefilteredOrbitFactors D.basis ω hD
        (fun i : {i // initialLong i} => (A.sides i.val : ℝ)) q l W
        (D.filtration.weightedAdaptedRealChartHom (fun _ : (P.chart z).Variables => 1)
          (fun _ : {i // initialLong i} => 1) ((P.chart z).axisPolynomial initialLong (fun _ => 0))
          ((P.chart z).axisPolynomial_support initialLong (fun _ => 0))
          (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1) (P.candidate z).orbit))) :
    ∃ denominator : ℕ, 0 < denominator ∧
      (denominator : ℝ) ≤ Real.exp (allocatedAffineResetLogBudget s pNative) ∧
      data.nFinal ∣ denominator ∧
      Nonempty (AllocatedExternalGlobalNativeResetFamily Fmark φ hφ
        data.selected.problem kept (data.selected.common_keep hcost) W data.factors
        (Real.exp (allocatedAffineResetLogBudget s pNative)) denominator) := by
  classical
  have hreset := Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (exists_allocatedCertifiedAffineFamilyReset s 1)))
  obtain ⟨mMap, denominator, hmMap, hmMapBound, hdiv, hden, hdenBound, hmMapDen, hrun⟩ :=
    hreset.2.2.2 (sampler := A) (E := E) D Fmark φ hφ ω hD c ν hF hsurj kept
      bk W v hW hvspan vg hvgspan H l data.nFinal pMap pNative hH hl data.nFinal_pos
      hpMap hpNative hsrc htgt hHmap hlmap hmabsorb hd (by simpa using hc) hk hμ hχ
      (by convert hvars using 1; simp only [Fintype.card_eq_nat_card]) hHp
      hbracketD hbracketF hkernel hentries hv hvg
  refine ⟨denominator, hden, hdenBound, (dvd_mul_left data.nFinal l).trans (hdiv.trans hmMapDen), ?_⟩
  have hside (i : {i // kept i}) :
      Real.exp ((pNative + allocatedAffineResetCompareExponent s) ^
        allocatedAffineResetCompareExponent s) ≤ (A.sides i.val : ℝ) :=
    hsideBound.trans ((lt_candidateSideCutoff separation).le.trans (Nat.cast_le.mpr i.property))
  have hlong (i : LayerSamplerVariables G I n B) (hi : kept i) :
      separation ≤ layerSamplerBox B U b S i := by
    rw [allocatedParameterBox_side_eq B U b S i]
    exact (lt_candidateSideCutoff separation).le.trans (Nat.cast_le.mpr hi)
  apply hrun marked observable weight data.selected.freezing.problem data.selected.affine
    (data.selected.common_keep hcost) _ _ data.factors data.right_grid
  · intro z
    exact Fmark.filtration.polynomialSlowBound_mono c
      (fun _ : (data.selected.problem.chart z).Variables => 1)
      (fun i => (A.sides i.val : ℝ)) (fun i => Nat.cast_pos.mpr (A.sides_pos i.val))
      hslow _ (data.local_left z)
  · exact hside
  · exact hq
  · exact hqmap
  · exact data.selected.original_dense
  · exact hcutoff
  · exact hlong
  · exact data.selected.withKeep_nativeFactors_of_zero_restriction
      kept (data.selected.common_keep hcost) initialLong
      (fun z i hi => hsub i hi.2) D.basis ω hD q l W hzero

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem allocatedAffineResetNativeBudget_exp_bounds (s : ℕ) {pFull pMap q : ℝ}
    (hFull : 0 ≤ pFull) (hMap : 0 ≤ pMap) :
    let pNative := allocatedAffineResetNativeBudget s pFull pMap q
    let Ce := allocatedEarlyAffineLeftExponent (s + 1) 4
    0 ≤ pNative ∧ pFull ≤ pNative ∧ pMap ≤ pNative ∧
      Real.exp ((pMap + 2) ^ 4) ≤ Real.exp pNative ∧
      Real.exp ((pFull + Ce) ^ Ce) ≤ Real.exp ((pNative + 2) ^ (1 : ℕ)) ∧
      Real.exp q ≤ Real.exp ((pNative + 2) ^ (1 : ℕ)) ∧
      Real.exp ((pMap + 2) ^ 3 + q) ≤ Real.exp ((pNative + 2) ^ (1 : ℕ)) :=
  affineResetNativeBudget_exp_bounds (allocatedEarlyAffineLeftExponent (s + 1) 4) hFull hMap

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

theorem allocatedAffineCanonicalBudget_exp_bounds (s : ℕ) {p0 pFull : ℝ}
    (hp0 : 0 ≤ p0) (hFull : 0 ≤ pFull) :
    AllocatedAffineCanonicalExpBounds s p0 pFull := by
  have hb := allocatedAffineCanonicalBudget_bounds s hp0 hFull
  obtain ⟨_, _, _, hm, hf, hq, hmq⟩ :=
    allocatedAffineResetNativeBudget_exp_bounds s hFull hb.map_nonnegative (q := p0)
  have hcut := candidatePrimitiveFreezingCutoff_ge_input s 1 hb.nonnegative
  refine ⟨hm, hf, hq, hmq, Real.exp_le_exp.mpr (hb.compare.trans hcut), ?_, ?_⟩
  · intro cost hcost
    exact Real.exp_le_exp.mpr ((hcost.trans hb.input).trans hcut)
  · intro cost hcost
    have hs : ((s + 2 : ℕ) : ℝ) ≤ Real.exp (s + 2 : ℕ) := by
      linarith [Real.add_one_le_exp ((s + 2 : ℕ) : ℝ)]
    calc
      Real.exp cost * (s + 2 : ℕ) ≤ Real.exp cost * Real.exp (s + 2 : ℕ) :=
        mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
      _ = Real.exp (cost + (s + 2 : ℕ)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr
        ((add_le_add hcost le_rfl).trans (hb.interpolation_log.trans hcut))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CandidatePhysicalOrdinaryBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem candidatePhysicalOrdinaryBudget_separation (s : ℕ) {pFull pAffine : ℝ}
    (hp : 0 ≤ pFull) (ha : 0 ≤ pAffine)
    (hcenter : certifiedAffineCenterBudget pAffine ≤ pFull) :
    certifiedAffineLongSideBound pAffine ≤ Real.exp (candidatePrimitiveFreezingCutoff s 1
      (allocatedAffineCanonicalBudget s (candidatePhysicalOrdinaryBudget pFull) pFull)) := by
  have hbase := certifiedAffineCenterBudget_primitive_bounds ha
  have hlog : 2 * (pAffine + 2) ^ 9 + pAffine ≤ candidatePhysicalOrdinaryBudget pFull := by
    have hpA := hbase.1.trans hcenter
    have hpN := hbase.2.trans hcenter
    linarith only [hpA, hpN, (candidatePhysicalOrdinaryBudget_bounds hp).2.2.2.2]
  have hordinary := (candidatePhysicalOrdinaryBudget_bounds hp).1
  have hcanonical := allocatedAffineCanonicalBudget_bounds s hordinary hp
  have hcut := candidatePrimitiveFreezingCutoff_ge_input s 1 hcanonical.nonnegative
  unfold certifiedAffineLongSideBound
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  norm_num only [Nat.cast_ofNat]
  exact hlog.trans (hcanonical.input.trans hcut)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffinePhysicalBoundsSuccessor
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal
attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  symbolPointwiseSubalgebra realificationLieSubalgebra PolynomialRationalGrid PolynomialSlowBound
  HasCommonRefilteredOrbitFactors polynomialOrbitCoordinates associatedGradedMap realPolynomialGroupMap
  AllocatedExternalCandidateProblem.Refinement.problem
  realSymbolHomogeneousPullbackHom CertifiedFullChartFiniteHistory.outer

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

namespace AllocatedExternalCandidateProblem

variable {L M : Type} {nMarkedBasis : ℕ} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (c : Basis (Fin nMarkedBasis) ℚ M)
    (ν : Fin nMarkedBasis → ℕ)
    (hF : ∀ j, Fmark.filtration.layer j = span ℚ (c '' {i | j ≤ ν i}))
    {η : Type} [Fintype η]
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (Fmark.filtration.AssociatedGraded ⧸
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)).toSubmodule)))
    (lift : (Fmark.filtration.AssociatedGraded ⧸
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)).toSubmodule) →ₗ[ℚ]
        Fmark.filtration.AssociatedGraded)
    (Bphase budget pAffine pFull separation : ℝ)
    (history : CertifiedFullChartFiniteHistory Fmark.filtration c ν hF J
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)).toSubmodule
      basis lift
      (Fmark.filtration.realPolynomialSymbolHom c ν hF (fullTaggedVariableWeight J)
        (Fmark.filtration.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked))
      Set.univ U poly N Bphase (s + 1))
    (data : P.AffinePhysicalTerminalData c ν hF hφ W basis lift
      Bphase budget pAffine pFull 4 history separation)
    (hcost : Real.exp cost ≤ separation)

local notation "kept" => (fun i : LayerSamplerVariables G I n B =>
  candidateSideCutoff separation ≤ A.sides i)

theorem conclusion_of_affinePhysicalTerminal_zeroRestricted_degreeRule
    {κK μ χ : Type} [Fintype κK] [Fintype μ] [Fintype χ]
    (ω : Fin d → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (D.basis '' {i | j ≤ ω i}))
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (bk : Basis κK ℚ (LinearMap.ker φ.toLinearMap))
    (v : μ → D.filtration.AssociatedGraded)
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hD) ω W.toSubmodule)
    (hvspan : span ℚ (Set.range v) = W.toSubmodule)
    (vg : χ → Fmark.filtration.PolynomialSymbol (fun _ : {i // kept i} => 1))
    (hvgspan : span ℚ (Set.range vg) =
      (Fmark.filtration.symbolPointwiseSubalgebra c ν hF (fun _ : {i // kept i} => 1)
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))).toSubmodule)
    [Fintype (SymbolBasisIndex (fun _ : {i // kept i} => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : {i // kept i} => 1) ν)]
    (H l : ℕ) (pMap pNative : ℝ)
    (hH : 1 ≤ H) (hl : 0 < l) (hpMap : 0 ≤ pMap) (hpNative : 0 ≤ pNative)
    (hsrc : (Fintype.card (SymbolBasisIndex (fun _ : {i // kept i} => 1) ω) : ℝ) ≤ pMap)
    (htgt : (Fintype.card (SymbolBasisIndex (fun _ : {i // kept i} => 1) ν) : ℝ) ≤ pMap)
    (hHmap : (H : ℝ) ≤ Real.exp pMap)
    (hlmap : ((l * data.nFinal : ℕ) : ℝ) ≤ Real.exp pMap)
    (hmabsorb : Real.exp ((pMap + 2) ^ 4) ≤ Real.exp pNative)
    (hd : (d : ℝ) ≤ pNative) (hc : (nMarkedBasis : ℝ) ≤ pNative)
    (hk : (Fintype.card κK : ℝ) ≤ pNative)
    (hμ : (Fintype.card μ : ℝ) ≤ pNative)
    (hχ : (Fintype.card χ : ℝ) ≤ pNative)
    (hvars : (Fintype.card {i // kept i} : ℝ) ≤ pNative)
    (hHp : (H : ℝ) ≤ Real.exp pNative)
    (hbracketD : ∀ i j k, RationalHeightLE (D.basis.repr ⁅D.basis i, D.basis j⁆ k) H)
    (hbracketF : ∀ i j k, RationalHeightLE (c.repr ⁅c i, c j⁆ k) H)
    (hkernel : ∀ i j, RationalHeightLE (D.basis.repr (bk j : L) i) H)
    (hentries : ∀ k i, RationalHeightLE (c.repr (φ (D.basis i)) k) H)
    (hv : ∀ j i, RationalHeightLE
      ((D.filtration.associatedGradedBasis D.basis ω hD).repr (v j) i) H)
    (hvg : ∀ i z, RationalHeightLE
      ((Fmark.filtration.polynomialSymbolBasis c ν hF (fun _ : {i // kept i} => 1)).repr (vg i) z) H)
    (hslow : Real.exp ((pFull + allocatedEarlyAffineLeftExponent (s + 1) 4) ^
      allocatedEarlyAffineLeftExponent (s + 1) 4) ≤ Real.exp ((pNative + 2) ^ (1 : ℕ)))
    (hsideBound : Real.exp ((pNative + allocatedAffineResetCompareExponent s) ^
      allocatedAffineResetCompareExponent s) ≤ separation)
    (q : ℝ)
    (hq : Real.exp q ≤ Real.exp ((pNative + 2) ^ (1 : ℕ)))
    (hqmap : Real.exp ((pMap + 2) ^ 3 + q) ≤ Real.exp ((pNative + 2) ^ (1 : ℕ)))
    (hcutoff : Real.exp cost * ((s + 1 + 1 : ℕ) : ℝ) ≤ separation)
    (initialLong : LayerSamplerVariables G I n B → Prop)
    (hsub : ∀ i, kept i → initialLong i)
    (hzero : ∀ z : P.productive,
      D.filtration.HasCommonRefilteredOrbitFactors D.basis ω hD
        (fun i : {i // initialLong i} => (A.sides i.val : ℝ)) q l W
        (D.filtration.weightedAdaptedRealChartHom (fun _ : (P.chart z).Variables => 1)
          (fun _ : {i // initialLong i} => 1) ((P.chart z).axisPolynomial initialLong (fun _ => 0))
          ((P.chart z).axisPolynomial_support initialLong (fun _ => 0))
          (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1) (P.candidate z).orbit)))
    {p outputCost : ℝ} {e : ℕ}
    (input : data.SuccessorInputs p e outputCost)
    (hresetBudget : allocatedAffineResetLogBudget s pNative ≤ p) :
    Nonempty (P.Conclusion (max outputCost (candidateSideCutoffCost separation))
      (Real.exp (-outputCost)) (Real.exp (-outputCost))) := by
  have hcost : Real.exp cost ≤ separation := by
    rw [input.separation_eq]
    exact Real.exp_le_exp.mpr
      (input.cost_bound.trans (candidatePrimitiveFreezingCutoff_ge_input s 1 input.nonnegative))
  obtain ⟨denominator, hden, hdenBound, hdenDvd, ⟨reset⟩⟩ :=
    P.exists_affinePhysicalTerminal_nativeReset_of_zero_restriction Fmark φ hφ W c ν hF
      basis lift Bphase budget pAffine pFull separation history data hcost
      ω hD hsurj bk v hW hvspan vg hvgspan H l pMap pNative hH hl hpMap hpNative
      hsrc htgt hHmap hlmap hmabsorb hd hc hk hμ hχ hvars hHp
      hbracketD hbracketF hkernel hentries hv hvg hslow hsideBound q hq hqmap hcutoff
      initialLong hsub hzero
  exact input.conclusion_of_reset (hcost := hcost) reset hresetBudget hden
    (hdenBound.trans (Real.exp_le_exp.mpr hresetBudget)) hdenDvd

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal
attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  symbolPointwiseSubalgebra realificationLieSubalgebra PolynomialRationalGrid PolynomialSlowBound
  HasCommonRefilteredOrbitFactors polynomialOrbitCoordinates associatedGradedMap realPolynomialGroupMap
  AllocatedExternalCandidateProblem.Refinement.problem
  realSymbolHomogeneousPullbackHom CertifiedFullChartFiniteHistory.outer

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

namespace AllocatedExternalCandidateProblem

variable {L M : Type} {nMarkedBasis : ℕ} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (c : Basis (Fin nMarkedBasis) ℚ M)
    (ν : Fin nMarkedBasis → ℕ)
    (hF : ∀ j, Fmark.filtration.layer j = span ℚ (c '' {i | j ≤ ν i}))
    {η : Type} [Fintype η]
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (Fmark.filtration.AssociatedGraded ⧸
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)).toSubmodule)))
    (lift : (Fmark.filtration.AssociatedGraded ⧸
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)).toSubmodule) →ₗ[ℚ]
        Fmark.filtration.AssociatedGraded)
    (Bphase budget pAffine pFull separation : ℝ)
    (history : CertifiedFullChartFiniteHistory Fmark.filtration c ν hF J
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)).toSubmodule
      basis lift
      (Fmark.filtration.realPolynomialSymbolHom c ν hF (fullTaggedVariableWeight J)
        (Fmark.filtration.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked))
      Set.univ U poly N Bphase (s + 1))
    (data : P.AffinePhysicalTerminalData c ν hF hφ W basis lift
      Bphase budget pAffine pFull 4 history separation)
    (hcost : Real.exp cost ≤ separation)

local notation "kept" => (fun i : LayerSamplerVariables G I n B =>
  candidateSideCutoff separation ≤ A.sides i)

theorem conclusion_of_normalized_affinePhysicalTerminal_zeroRestricted_degreeRule
    {γ : Type} [Fintype γ]
    (p0 : ℝ) (hp0 : 0 ≤ p0) (hpFull : 0 ≤ pFull)
    (hDgeo : D.GeometryComplexityLE p0) (hFgeo : Fmark.GeometryComplexityLE p0)
    (hcForward : ∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ p0)
    (hMap : ∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p0)
    (ω : Fin d → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (D.basis '' {i | j ≤ ω i}))
    (v : γ → D.filtration.AssociatedGraded)
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hD) ω W.toSubmodule)
    (hvspan : span ℚ (Set.range v) = W.toSubmodule)
    (hγ : (Fintype.card γ : ℝ) ≤ p0)
    (hvHeight : ∀ j i, rationalLogHeight
      ((D.filtration.associatedGradedBasis D.basis ω hD).repr (v j) i) ≤ p0)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p0)
    (q : ℝ) (l : ℕ) (hq0 : q ≤ p0) (hl : 0 < l) (hlBound : (l : ℝ) ≤ Real.exp p0)
    (hcost0 : cost ≤ p0)
    (initialLong : LayerSamplerVariables G I n B → Prop)
    (hshort : ∀ i, ¬initialLong i → (A.sides i : ℝ) ≤ Real.exp p0)
    (hzero : ∀ z : P.productive,
      D.filtration.HasCommonRefilteredOrbitFactors D.basis ω hD
        (fun i : {i // initialLong i} => (A.sides i.val : ℝ)) q l W
        (D.filtration.weightedAdaptedRealChartHom (fun _ : (P.chart z).Variables => 1)
          (fun _ : {i // initialLong i} => 1) ((P.chart z).axisPolynomial initialLong (fun _ => 0))
          ((P.chart z).axisPolynomial_support initialLong (fun _ => 0))
          (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1) (P.candidate z).orbit)))
    {outputCost : ℝ} {e : ℕ}
    (input : data.SuccessorInputs (allocatedAffineCanonicalBudget s p0 pFull) e outputCost) :
    Nonempty (P.Conclusion (max outputCost (candidateSideCutoffCost separation))
      (Real.exp (-outputCost)) (Real.exp (-outputCost))) := by
  classical
  let Vars := {i : LayerSamplerVariables G I n B // kept i}
  have hvars : (Fintype.card Vars : ℝ) ≤ p0 :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le kept)).trans hvariables
  obtain ⟨hHeight0, hHeightInput, hHeightBracket, hHeightKernel, hHeightPoint⟩ :=
    allocatedAffineResetHeightLog_bounds hp0
  let H := ⌈Real.exp (allocatedAffineResetHeightLog p0)⌉₊
  obtain ⟨hH, hHBound, hd, hc, hbracketD, hbracketF⟩ :=
    D.nativeResetBracketGeometry_of_logBudget Fmark c hp0 hDgeo hFgeo hcForward hHeightBracket
  obtain ⟨r, hr, hrp, bk, hbk⟩ := exists_marked_kernel_basis_commonHeight_of_dim
    D.basis c φ hp0 (by simpa using hd) hc hMap
  let : Fintype (SymbolBasisIndex (fun _ : Vars => 1) ω) :=
    D.filtration.ordinarySymbolBasisFintype D.basis ω hD
  let : Fintype (SymbolBasisIndex (fun _ : Vars => 1) ν) :=
    Fmark.filtration.ordinarySymbolBasisFintype c ν hF
  let vg := D.filtration.gradedImagePointwiseSpanningFamily Fmark.filtration φ hφ
    c ν hF (fun _ : Vars => 1) v
  obtain ⟨hvgspan, _, hvgHeight, hsrcCount, htgtCount, hvgCount, _, _⟩ :=
    D.filtration.ordinaryGradedImagePointwiseSpanning_controlled Fmark.filtration φ hφ
      D.basis ω hD c ν hF W v hW hvspan hp0 (by simpa using hd) hc hγ hvars hvHeight
      (fun i j => hMap j i)
  have mapBounds := allocatedAffineResetMapBudget_bounds s hp0 hpFull
  have bounds := allocatedAffineCanonicalBudget_bounds s hp0 hpFull
  have expBounds := allocatedAffineCanonicalBudget_exp_bounds s hp0 hpFull
  have hsrc : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ω) : ℝ) ≤
      allocatedAffineResetMapBudget s p0 pFull := by
    simpa only [Nat.card_eq_fintype_card] using hsrcCount.trans mapBounds.pointwise
  have htgt : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ν) : ℝ) ≤
      allocatedAffineResetMapBudget s p0 pFull := by
    simpa only [Nat.card_eq_fintype_card] using htgtCount.trans mapBounds.pointwise
  have hχ : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ν × γ) : ℝ) ≤
      allocatedAffineCanonicalNativeBudget s p0 pFull := by
    simpa only [Nat.card_eq_fintype_card] using
      (hvgCount.trans mapBounds.pointwise).trans bounds.native_map
  have hHmap : (H : ℝ) ≤ Real.exp (allocatedAffineResetMapBudget s p0 pFull) :=
    hHBound.trans (Real.exp_le_exp.mpr mapBounds.height)
  have hlmap : ((l * data.nFinal : ℕ) : ℝ) ≤
      Real.exp (allocatedAffineResetMapBudget s p0 pFull) :=
    allocatedAffineResetMapBudget_denominator s hp0 hpFull hlBound data.nFinal_bound
  have hkernel : ∀ i j, RationalHeightLE (D.basis.repr (bk j : L) i) H := by
    intro i j
    exact (hbk j i).mono (Nat.ceil_mono (Real.exp_le_exp.mpr hHeightKernel))
  have hentries : ∀ i j, RationalHeightLE (c.repr (φ (D.basis j)) i) H :=
    fun i j => rationalHeightLE_ceil_exp ((hMap i j).trans hHeightInput)
  have hv : ∀ j i, RationalHeightLE
      ((D.filtration.associatedGradedBasis D.basis ω hD).repr (v j) i) H :=
    fun j i => rationalHeightLE_ceil_exp ((hvHeight j i).trans hHeightInput)
  have hvg : ∀ i z, RationalHeightLE
      ((Fmark.filtration.polynomialSymbolBasis c ν hF (fun _ : Vars => 1)).repr (vg i) z) H := by
    intro i z
    exact (hvgHeight i z).mono (Nat.ceil_mono (Real.exp_le_exp.mpr hHeightPoint))
  have hside : Real.exp ((allocatedAffineCanonicalNativeBudget s p0 pFull +
      allocatedAffineResetCompareExponent s) ^ allocatedAffineResetCompareExponent s) ≤ separation := by
    rw [input.separation_eq]
    exact expBounds.compare_cutoff
  have hcutoff : Real.exp cost * ((s + 1 + 1 : ℕ) : ℝ) ≤ separation := by
    rw [input.separation_eq]
    simpa only [Nat.add_assoc] using expBounds.interpolation cost hcost0
  have hsub : ∀ i, kept i → initialLong i := by
    intro i hi
    by_contra hn
    have hside0 : Real.exp p0 ≤ separation := by
      rw [input.separation_eq]
      exact expBounds.cost_cutoff p0 le_rfl
    have hlong : separation < (A.sides i : ℝ) :=
      (lt_candidateSideCutoff separation).trans_le (Nat.cast_le.mpr hi)
    exact (not_lt_of_ge ((hshort i hn).trans hside0)) hlong
  exact P.conclusion_of_affinePhysicalTerminal_zeroRestricted_degreeRule Fmark φ hφ W c ν hF
    basis lift Bphase budget pAffine pFull separation history data
    ω hD input.surjective bk v hW hvspan vg hvgspan H l
    (allocatedAffineResetMapBudget s p0 pFull) (allocatedAffineCanonicalNativeBudget s p0 pFull)
    hH hl bounds.map_nonnegative bounds.native_nonnegative hsrc htgt hHmap hlmap
    expBounds.map_absorption (hd.trans bounds.native_input)
    (by simpa only [Fintype.card_fin] using hc.trans bounds.native_input)
    (by simpa only [Fintype.card_fin] using hrp.trans bounds.native_input)
    (hγ.trans bounds.native_input) hχ (hvars.trans bounds.native_input)
    (hHmap.trans (Real.exp_le_exp.mpr bounds.native_map)) hbracketD hbracketF
    hkernel hentries hv hvg expBounds.physical_absorption hside q
    ((Real.exp_le_exp.mpr hq0).trans expBounds.original_absorption)
    ((Real.exp_le_exp.mpr (add_le_add le_rfl hq0)).trans expBounds.mapped_absorption)
    hcutoff initialLong hsub hzero input bounds.reset

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOrdinaryLongPhysicalTerminalConclusion
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

attribute [local irreducible] realPolynomialSymbolHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer
  CertifiedFullChartFiniteHistory.earlyForwardBranchTree
  polynomialOrbitCoordinates realGradedSymbolPolynomial

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
    {κ : Type} [Fintype κ]
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (scheduleExponent Cprimitive : ℕ) (x separation : ℝ)

local notation "fast" => W.map (D.filtration.associatedGradedMap Fmark φ hφ)
local notation "gmark" => Fmark.realification.polynomialOrbitCoordinates
  (fullTaggedVariableWeight J) marked
local notation "Z" => Fmark.realPolynomialSymbolHom bF ν hF (fullTaggedVariableWeight J) gmark
local notation "countConstants" => (fun n => fullChartStageCountConstant (n + 1) 254)

def NativeCommonPhysicalTerminal : Prop :=
  let pFull := allocatedCandidateTerminalFullInput s m Cprimitive x
    (preparedFiniteForwardWork scheduleExponent countConstants s x)
    (preparedFiniteForwardCumulative scheduleExponent countConstants s x)
  ∃ (qDim : ℕ) (_hdim : qDim ≤ Fintype.card κ)
    (eQ : Basis (Fin qDim) ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
    (lift : (Fmark.AssociatedGraded ⧸ (fast).toSubmodule) →ₗ[ℚ] Fmark.AssociatedGraded),
  BasisGradedSubmodule (Fmark.associatedGradedBasis bF ν hF) ν (fast).toSubmodule ∧
  Function.RightInverse lift (fast).toSubmodule.mkQ ∧
  ∃ (hx : 0 ≤ x)
    (hXEarly : (Fintype.card X : ℝ) ≤ x) (hmEarly : (m : ℝ) ≤ x)
    (hJEarly : (Fintype.card (Σ j, J j) : ℝ) ≤ x)
    (hηBase : (Fintype.card (Fin qDim) : ℝ) ≤ x)
    (hblocks : ((s * (Fintype.card (Fin qDim) * m) : ℕ) : ℝ) ≤ x)
    (hNEarly : ∀ i, 1 ≤ N i),
  let T := CertifiedFullChartFiniteHistory.earlyForwardBranchTree
    Fmark bF ν hF J (fast).toSubmodule (eQ.baseChange ℝ) lift Z U poly N
    s scheduleExponent x hx hXEarly hmEarly hJEarly hηBase hblocks
    (fun j ex _ => hm j ex) hNEarly
  let pAffine := preparedFiniteForwardCumulative scheduleExponent countConstants s x
  let budget := preparedFiniteForwardWork scheduleExponent countConstants s x
  ∃ history ∈ T.level s,
    FullChartControlledFactors Fmark bF ν hF J poly N history.outer.1 history.outer.2
      (preparedFiniteForwardWork scheduleExponent countConstants s x) ∧
    RationalTaggedConstraintCertificate J Set.univ history.K
      (preparedFiniteForwardCumulative scheduleExponent countConstants s x)
      (s * (Fintype.card (Fin qDim) * m)) ∧
    (∀ point ∈ history.K,
      eval₂ point (Fmark.realGradedSymbolPolynomial bF ν hF (fullTaggedVariableWeight J)
        (history.outer.1⁻¹ * Z * history.outer.2⁻¹).coord) ∈ (fast).toSubmodule.baseChange ℝ) ∧
    Nonempty (P.AffinePhysicalTerminalData bF ν hF hφ W (eQ.baseChange ℝ) lift
      pAffine budget pAffine pFull 4 history separation)

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

attribute [local irreducible] realPolynomialSymbolHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer
  CertifiedFullChartFiniteHistory.earlyForwardBranchTree
  polynomialOrbitCoordinates realGradedSymbolPolynomial

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
    {κ : Type} [Fintype κ]
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (scheduleExponent Cprimitive : ℕ) (x separation : ℝ)

local notation "fast" => W.map (D.filtration.associatedGradedMap Fmark φ hφ)
local notation "gmark" => Fmark.realification.polynomialOrbitCoordinates
  (fullTaggedVariableWeight J) marked
local notation "Z" => Fmark.realPolynomialSymbolHom bF ν hF (fullTaggedVariableWeight J) gmark

variable {P bF ν hF hφ W scheduleExponent Cprimitive x separation}

theorem NativeCommonPhysicalTerminal.exists_physicalData
    (hterminal : P.NativeCommonPhysicalTerminal bF ν hF hφ W
      scheduleExponent Cprimitive x separation) :
    0 ≤ nativePhysicalTerminalFullBudget s m Cprimitive scheduleExponent x ∧
    ∃ (qDim : ℕ)
      (eQ : Basis (Fin qDim) ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
      (lift : (Fmark.AssociatedGraded ⧸ (fast).toSubmodule) →ₗ[ℚ] Fmark.AssociatedGraded)
      (history : CertifiedFullChartFiniteHistory Fmark bF ν hF J (fast).toSubmodule
        (eQ.baseChange ℝ) lift Z Set.univ U poly N
        (nativePhysicalTerminalAffineBudget s scheduleExponent x) s),
      Nonempty (P.AffinePhysicalTerminalData bF ν hF hφ W (eQ.baseChange ℝ) lift
        (nativePhysicalTerminalAffineBudget s scheduleExponent x)
        (nativePhysicalTerminalWorkBudget s scheduleExponent x)
        (nativePhysicalTerminalAffineBudget s scheduleExponent x)
        (nativePhysicalTerminalFullBudget s m Cprimitive scheduleExponent x)
        4 history separation) := by
  obtain ⟨qDim, _hdim, eQ, lift, _hfast, _hsection, hx, _hXEarly, _hmEarly, _hJEarly,
    _hηBase, _hblocks, _hNEarly, history, _hmem, _hcontrol, _hcertificate, _hpointwise, hdata⟩ :=
      hterminal
  exact ⟨(nativePhysicalTerminalBudgets_nonneg s m Cprimitive scheduleExponent hx).2.2,
    qDim, eQ, lift, history, hdata⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

attribute [local irreducible] realPolynomialSymbolHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer
  CertifiedFullChartFiniteHistory.earlyForwardBranchTree
  polynomialOrbitCoordinates realGradedSymbolPolynomial

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
    {s d f : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (Mmodel : RationalFilteredNilmanifold M s f)
    (ω : Fin d → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (D.basis '' {i | j ≤ ω i}))
    (ν : Fin f → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (Mmodel.basis '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ z ∈ D.filtration.layer j, φ z ∈ Fmark.layer j)

structure OrdinaryLongPhysicalTerminalData
    (p0 : ℝ) (nGenerators : ℕ)
    (initialLong : LayerSamplerVariables G I n B → Prop)
    (scheduleExponent Cprimitive : ℕ) (x separation : ℝ) where
  model_filtration : Mmodel.filtration = Fmark
  nonnegative : 0 ≤ p0
  source_geometry : D.GeometryComplexityLE p0
  marked_geometry : Mmodel.GeometryComplexityLE p0
  marked_basis_height : ∀ i j,
    rationalLogHeight (Mmodel.basis.repr (Mmodel.basis i) j) ≤ p0
  mark_height : ∀ i j, rationalLogHeight (Mmodel.basis.repr (φ (D.basis j)) i) ≤ p0
  generator_count : (nGenerators : ℝ) ≤ p0
  variable_count : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p0
  cost_bound : cost ≤ p0
  short : ∀ i, ¬initialLong i → (A.sides i : ℝ) ≤ Real.exp p0
  W : LieSubalgebra ℚ D.filtration.AssociatedGraded
  generators : Fin nGenerators → D.filtration.AssociatedGraded
  span : Submodule.span ℚ (Set.range generators) = W.toSubmodule
  graded : BasisGradedSubmodule
    (D.filtration.associatedGradedBasis D.basis ω hD) ω W.toSubmodule
  generator_height : ∀ a i, rationalLogHeight
    ((D.filtration.associatedGradedBasis D.basis ω hD).repr (generators a) i) ≤ p0
  q : ℝ
  q_bound : q ≤ p0
  denominator : ℕ
  denominator_pos : 0 < denominator
  denominator_bound : (denominator : ℝ) ≤ Real.exp p0
  zero_factors : ∀ z : P.productive,
    D.filtration.HasCommonRefilteredOrbitFactors D.basis ω hD
      (fun i : {i // initialLong i} => (A.sides i.val : ℝ)) q denominator W
      (D.filtration.weightedAdaptedRealChartHom (fun _ : (P.chart z).Variables => 1)
        (fun _ : {i // initialLong i} => 1)
        ((P.chart z).axisPolynomial initialLong (fun _ => 0))
        ((P.chart z).axisPolynomial_support initialLong (fun _ => 0))
        (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
          (P.candidate z).orbit))
  top_kernel : ∀ z ∈ D.filtration.gradedRefiltrationLayer W s, φ z = 0 → z = 0
  surjective : ∀ j, ∀ y ∈ Fmark.layer j,
    ∃ z ∈ D.filtration.layer j, φ z = y
  terminal : P.NativeCommonPhysicalTerminal Mmodel.basis ν hF hφ W
    scheduleExponent Cprimitive x separation

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedExternalCandidateCommonKeepPositiveKernelPreparation
namespace OAI

section

namespace Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem

theorem exists_positiveKernelPreparationParameters_bound (e : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      p + 3 ≤ (p + C) ^ C ∧
      positiveKernelPreparationParameter p ≤ (p + C) ^ C ∧
      positiveKernelPreparationBinLog p e ≤ (p + C) ^ C ∧
      positiveKernelResidualPrecisionParameter p e ≤ (p + C) ^ C ∧
      positiveKernelMarkovPrecisionParameter p e ≤ (p + C) ^ C := by
  let q : Polynomial ℕ := (Polynomial.X + 5) ^ positiveKernelPreparationExponent
  let bin : Polynomial ℕ := (2 * Polynomial.X + q + 5 + Polynomial.C e) ^ e
  let residual : Polynomial ℕ := q + q + bin + 4
  let markov : Polynomial ℕ := (q + bin) + (2 * q + bin + 4) + (Polynomial.X + q) + 2
  let total : Polynomial ℕ := Polynomial.X + 3 + q + bin + residual + markov
  obtain ⟨C, hC, hbound⟩ := Erdos3.exists_natPolynomial_eval_budget total
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hq := positiveKernelPreparationParameter_nonneg hp
  have hbin := positiveKernelPreparationBinLog_nonneg hp e
  have hresidual : 0 ≤ positiveKernelResidualPrecisionParameter p e := by
    unfold positiveKernelResidualPrecisionParameter
    positivity
  have hmarkov : 0 ≤ positiveKernelMarkovPrecisionParameter p e := by
    unfold positiveKernelMarkovPrecisionParameter
    positivity
  have htotal : p + 3 + positiveKernelPreparationParameter p +
      positiveKernelPreparationBinLog p e + positiveKernelResidualPrecisionParameter p e +
      positiveKernelMarkovPrecisionParameter p e ≤ (p + C) ^ C := by
    simpa [total, markov, residual, bin, q, positiveKernelPreparationParameter,
      positiveKernelPreparationBinLog, positiveKernelResidualPrecisionParameter,
      positiveKernelMarkovPrecisionParameter, Polynomial.eval₂_pow] using hbound p hp
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateLocalFixedCenterFront
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
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
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

namespace PrecenterKernelSelection
variable {P} {p q : ℝ}
    {T : (X → ℤ) → D.Niltest (fullTaggedVariableWeight (X := X) J)}
    {early : ExternalFamilyPrecenterProjectionData T p q}
    {top : Submodule ℚ L} {htop : top ≤ D.filtration.layer s}
    {hpos : 0 < A.law.mass P.productive}
    (selected : P.PrecenterKernelSelection early top htop hpos)

attribute [local instance] OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.PrecenterKernelSelection.actualFixedCenterFrontSiteNonempty
theorem exists_actualFixedCenter_spatialNativeFamily
    {Bin : Type} [Fintype Bin] [Nonempty Bin]
    (representative : Bin → integerBox N)
    (hnet : ∀ x : integerBox N, ∃ i, ∀ y,
      ‖(T x.val).observable y - (T (representative i).val).observable y‖ ≤
        Real.exp (-(p + q + 2)))
    {u pModel sliceBudget testBudget localBudget forecastNative forecastMassLog capLog
      Edata projectionPrecision marginalCap binLog dimensionLog Eres sourceMassLog : ℝ}
    (hξ1 : ξ ≤ 1)
    (hu : 0 ≤ u) (hpModel : 0 ≤ pModel) (hinputBudget : p ≤ pModel)
    (hlocalBudget : 0 ≤ localBudget) (hforecastNative : 0 ≤ forecastNative)
    (hSliceNonneg : 0 ≤ sliceBudget) (hTestNontrivial : 2 ≤ testBudget)
    (hSliceLog : sliceBudget * Fintype.card (LayerSamplerVariables G I n B) ≤ pModel)
    (hMarginalCap : 1 ≤ marginalCap) (hMarginalBound : marginalCap ≤ Real.exp pModel)
    (hCap : capLog ≤ pModel)
    (hAccuracy : 2 * u + 4 * pModel + 12 ≤ Edata)
    (hPrecision : u + 2 * pModel + max (max localBudget (3 * forecastNative + 3))
      (2 * u + 4 * pModel + max 0 forecastMassLog + 20) + 32 ≤ projectionPrecision)
    (hdirect : A.NativeDetection s sliceBudget testBudget localBudget
      (Real.exp (-(2 * u + 4 * pModel + 8))))
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξ1 (fun x => (A.trimMargin_proper x).le))) marginalCap ≤
        6 * positiveProjectionAccuracy projectionPrecision)
    {Forecast : Type} [Nonempty Forecast]
    (data : Forecast → ActualForecastData N poly forecastNative forecastMassLog capLog Edata)
    (hq : 0 ≤ q) (hbin : 0 ≤ binLog)
    (hcard : (Fintype.card Bin : ℝ) ≤ Real.exp binLog)
    (hdim : (finrank ℚ top : ℝ) ≤ dimensionLog)
    (hweight : ∀ x ∈ integerBox N, ‖weight x‖ ≤ Real.exp p)
    (hcost0 : 0 ≤ cost) (hSliceBudget : cost ≤ sliceBudget) (hTestBudget : q ≤ testBudget)
    (hsourceMass : Real.exp (-sourceMassLog) ≤ A.law.mass P.productive)
    (hMarkovPrecision : (q + binLog) + Eres + (sourceMassLog + q) + 2 ≤ u)
    (hresBudget : q + q + binLog + 4 ≤ Eres)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ a, (P.chart a).keep = keep)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hτ1 : τ ≤ 1) (hσ1 : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    {pFamily : ℝ} (hpFamily : 0 ≤ pFamily)
    (hcost : cost ≤ pFamily) (hlocal : q ≤ pFamily)
    (hperiod : 2 * max localBudget (3 * forecastNative + 3) ≤ pFamily)
    (hvariation : Real.exp (max localBudget (3 * forecastNative + 3)) *
      (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp pFamily)
    (hK : (Fintype.card {i // keep i} : ℝ) ≤ pFamily) :
    let commonBudget := max localBudget (3 * forecastNative + 3)
    let Qmodel := max commonBudget (2 * u + 4 * pModel + max 0 forecastMassLog + 20)
    let coefficientLog := Qmodel + 2
    let termLog := 2 * Qmodel + 2 * u + 4 * pModel + 34
    ∃ (retained : Finset A.Path), retained ⊆ selected.retained ∧
      0 < A.law.mass retained ∧
      Real.exp (-(dimensionLog * (binLog + termLog))) * (A.law.mass selected.retained / 2) ≤
        A.law.mass retained ∧
      Real.exp (-(q + dimensionLog * (binLog + termLog) + 2)) * A.law.mass P.productive ≤
        A.law.mass retained ∧
      ∃ F : AllocatedExternalCandidateSpatialNativeFamily A E A.Path
          (KernelProjectionPresentPivot selected.code) D Fmark φ marked keep cost pFamily q commonBudget
          (q + binLog + coefficientLog + 4) (Real.exp commonBudget) (Real.exp commonBudget)
          ⟨Real.exp commonBudget, Real.exp_nonneg _⟩,
        F.sourceChart = P.precenterChart hpos ∧
        (∀ a, HEq (F.sourceCandidate a) (P.precenterCandidate hpos a)) ∧
        F.η = (fun k => early.eta (kernelProjectionSelectedPivot selected.code k)) ∧
        (∀ a ∈ retained, ∀ k,
          Real.exp (-(q + binLog + coefficientLog + 4)) ≤ ‖F.correlation a k‖) ∧
        (∀ a ∈ retained, (F.sourceChart a).path = a) ∧
        (∀ a, (F.sourceChart a).centerLift = P.centerLift) ∧
        (∀ a ∈ retained, Real.exp (-q) ≤
          (F.sourceCandidate a).score (fun x => (selected.tests x).observable) weight) := by
  intro commonBudget Qmodel coefficientLog termLog
  have hcommon : 0 ≤ commonBudget := hlocalBudget.trans (le_max_left _ _)
  have hQ : 0 ≤ Qmodel := hcommon.trans (le_max_left _ _)
  have hnative : commonBudget ≤ pFamily := by
    have := hperiod
    change 2 * commonBudget ≤ pFamily at this
    linarith only [this, hcommon]
  have hperiod' : Real.exp commonBudget * Real.exp commonBudget ≤ Real.exp pFamily := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith only [hperiod]
  have hweightModel (x : integerBox N) : ‖weight x.val‖ ≤ Real.exp pModel :=
    (hweight x.val x.property).trans (Real.exp_le_exp.mpr hinputBudget)
  have hthreshold := (forecastAugmentedUnitThreshold_bounds hu hpModel (Real.exp_nonneg _)
    (zero_le_one.trans hMarginalCap) (Real.exp_le_exp.mpr hSliceLog) hMarginalBound
    (Real.exp_le_exp.mpr hCap)).2.2
  have hdirect' : A.NativeDetection s sliceBudget testBudget localBudget
      (forecastAugmentedUnitThreshold u pModel
        (Real.exp (sliceBudget * Fintype.card (LayerSamplerVariables G I n B)))
        marginalCap (Real.exp capLog)) :=
    AllocatedExternalCandidateSampler.NativeDetection.mono_tests
      A hdirect le_rfl le_rfl hthreshold
  obtain ⟨models, hmodels⟩ := A.exists_fixedCenter_mask_models s hξ1
    (fun x => (A.trimMargin_proper x).le) hu hpModel hlocalBudget hforecastNative
    hSliceNonneg hTestNontrivial hSliceLog hMarginalCap hMarginalBound hCap hAccuracy
    hPrecision hdirect' hexcess data (fun f (x : integerBox N) => (early.U f x.val).observable)
    (fun f i => (early.U f (representative i).val).observable)
    (contracted_member_net (early := early) representative hnet) (fun x => weight x.val) hweightModel
  obtain ⟨retained, hsub, hpos', hmass, F, hFC, hFcandidate, hFeta, hcorr, hpath, hcenter, hscore⟩ :=
    selected.exists_fixedCenter_spatialNativeFamily representative hnet models
      (Real.exp commonBudget) (Real.exp commonBudget) ⟨Real.exp commonBudget, Real.exp_nonneg _⟩
      (fun branch => (hmodels branch).1) (fun branch => (hmodels branch).2.1)
      (fun branch => (hmodels branch).2.2.1) (fun branch => (hmodels branch).2.2.2.2.2)
      hq (by positivity) (by positivity)
      hbin hcard hdim hξ1 hweight hcost0 hSliceBudget hTestBudget
      (fun branch => (hmodels branch).2.2.2.1)
      (selected.fixedCenter_residual_budget hsourceMass hcard hMarkovPrecision) hresBudget
      keep hkeep hpoly hτ1 hσ1 Cgeo hCgeo hchart hsmall hpFamily hcost hlocal hnative
      hperiod' hvariation hK
  exact ⟨retained, hsub, hpos', hmass, selected.fixedCenter_mass_after_native_selection hmass,
    F, hFC, hFcandidate, hFeta, hcorr, hpath, hcenter, hscore⟩

end PrecenterKernelSelection
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
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
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

namespace PrecenterKernelSelection
variable {P} {p q : ℝ}
    {T : (X → ℤ) → D.Niltest (fullTaggedVariableWeight (X := X) J)}
    {early : ExternalFamilyPrecenterProjectionData T p q}
    {top : Submodule ℚ L} {htop : top ≤ D.filtration.layer s}
    {hpos : 0 < A.law.mass P.productive}
    (selected : P.PrecenterKernelSelection early top htop hpos)

attribute [local instance] OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.PrecenterKernelSelection.localFixedCenterFrontSiteNonempty
theorem exists_localFixedCenter_spatialNativeFamily
    {Bin : Type} [Fintype Bin] [Nonempty Bin]
    (representative : Bin → integerBox N)
    (hnet : ∀ x : integerBox N, ∃ i, ∀ y,
      ‖(T x.val).observable y - (T (representative i).val).observable y‖ ≤
        Real.exp (-(p + q + 2)))
    {u pModel sliceBudget testBudget localBudget projectionPrecision marginalCap binLog dimensionLog Eres sourceMassLog : ℝ}
    (hξ1 : ξ ≤ 1)
    (hu : 0 ≤ u) (hpModel : 0 ≤ pModel) (hinputBudget : p ≤ pModel)
    (hlocalBudget : 0 ≤ localBudget)
    (hSliceNonneg : 0 ≤ sliceBudget) (hTestNontrivial : 2 ≤ testBudget)
    (hSliceLog : sliceBudget * Fintype.card (LayerSamplerVariables G I n B) ≤ pModel)
    (hMarginalCap : 1 ≤ marginalCap) (hMarginalBound : marginalCap ≤ Real.exp pModel)
    (hPrecision : u + 2 * pModel + max (max localBudget 3)
      (2 * u + 4 * pModel + 20) + 32 ≤ projectionPrecision)
    (hdirect : A.NativeDetection s sliceBudget testBudget localBudget
      (Real.exp (-(2 * u + 4 * pModel + 8))))
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξ1 (fun x => (A.trimMargin_proper x).le))) marginalCap ≤
        6 * positiveProjectionAccuracy projectionPrecision)
    (hq : 0 ≤ q) (hbin : 0 ≤ binLog)
    (hcard : (Fintype.card Bin : ℝ) ≤ Real.exp binLog)
    (hdim : (finrank ℚ top : ℝ) ≤ dimensionLog)
    (hweight : ∀ x ∈ integerBox N, ‖weight x‖ ≤ Real.exp p)
    (hcost0 : 0 ≤ cost) (hSliceBudget : cost ≤ sliceBudget) (hTestBudget : q ≤ testBudget)
    (hsourceMass : Real.exp (-sourceMassLog) ≤ A.law.mass P.productive)
    (hMarkovPrecision : (q + binLog) + Eres + (sourceMassLog + q) + 2 ≤ u)
    (hresBudget : q + q + binLog + 4 ≤ Eres)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ a, (P.chart a).keep = keep)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hτ1 : τ ≤ 1) (hσ1 : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    {pFamily : ℝ} (hpFamily : 0 ≤ pFamily)
    (hcost : cost ≤ pFamily) (hlocal : q ≤ pFamily)
    (hperiod : 2 * max localBudget 3 ≤ pFamily)
    (hvariation : Real.exp (max localBudget 3) *
      (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp pFamily)
    (hK : (Fintype.card {i // keep i} : ℝ) ≤ pFamily) :
    let commonBudget := max localBudget 3
    let Qmodel := max commonBudget (2 * u + 4 * pModel + 20)
    let coefficientLog := Qmodel + 2
    let termLog := 2 * Qmodel + 2 * u + 4 * pModel + 34
    ∃ (retained : Finset A.Path), retained ⊆ selected.retained ∧
      0 < A.law.mass retained ∧
      Real.exp (-(dimensionLog * (binLog + termLog))) * (A.law.mass selected.retained / 2) ≤
        A.law.mass retained ∧
      Real.exp (-(q + dimensionLog * (binLog + termLog) + 2)) * A.law.mass P.productive ≤
        A.law.mass retained ∧
      ∃ F : AllocatedExternalCandidateSpatialNativeFamily A E A.Path
          (KernelProjectionPresentPivot selected.code) D Fmark φ marked keep cost pFamily q commonBudget
          (q + binLog + coefficientLog + 4) (Real.exp commonBudget) (Real.exp commonBudget)
          ⟨Real.exp commonBudget, Real.exp_nonneg _⟩,
        F.sourceChart = P.precenterChart hpos ∧
        (∀ a, HEq (F.sourceCandidate a) (P.precenterCandidate hpos a)) ∧
        F.η = (fun k => early.eta (kernelProjectionSelectedPivot selected.code k)) ∧
        (∀ a ∈ retained, ∀ k,
          Real.exp (-(q + binLog + coefficientLog + 4)) ≤ ‖F.correlation a k‖) ∧
        (∀ a ∈ retained, (F.sourceChart a).path = a) ∧
        (∀ a, (F.sourceChart a).centerLift = P.centerLift) ∧
        (∀ a ∈ retained, Real.exp (-q) ≤
          (F.sourceCandidate a).score (fun x => (selected.tests x).observable) weight) := by
  let data : PUnit → ActualForecastData N poly 0 0 0 (2 * u + 4 * pModel + 12) :=
    fun _ => ActualForecastData.zero N poly 0 0 0 (2 * u + 4 * pModel + 12)
  have hprecision' : u + 2 * pModel + max (max localBudget (3 * (0 : ℝ) + 3))
      (2 * u + 4 * pModel + max 0 0 + 20) + 32 ≤ projectionPrecision := by
    simpa only [mul_zero, zero_add, max_self, add_zero] using hPrecision
  have hperiod' : 2 * max localBudget (3 * (0 : ℝ) + 3) ≤ pFamily := by
    simpa only [mul_zero, zero_add] using hperiod
  have hvariation' : Real.exp (max localBudget (3 * (0 : ℝ) + 3)) *
      (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp pFamily := by
    simpa only [mul_zero, zero_add] using hvariation
  have result := selected.exists_actualFixedCenter_spatialNativeFamily representative hnet hξ1
      hu hpModel hinputBudget hlocalBudget (le_refl 0) hSliceNonneg hTestNontrivial hSliceLog
      hMarginalCap hMarginalBound hpModel le_rfl hprecision' hdirect hexcess data hq hbin
      hcard hdim hweight hcost0 hSliceBudget hTestBudget hsourceMass hMarkovPrecision hresBudget
      keep hkeep hpoly hτ1 hσ1 Cgeo hCgeo hchart hsmall hpFamily hcost hlocal hperiod'
      hvariation' hK
  rw [show (3 : ℝ) * 0 + 3 = 3 by ring] at result
  rw [show max (0 : ℝ) 0 = 0 from max_self 0, add_zero] at result
  exact result

end PrecenterKernelSelection
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AllocatedNestedDegreeInduction
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

namespace AllocatedExternalCandidateProblem

theorem positiveKernelMarkovPrecisionParameter_mono_netExponent {p : ℝ}
    (hp : 0 ≤ p) {e f : ℕ} (hef : e ≤ f) :
    positiveKernelMarkovPrecisionParameter p e ≤ positiveKernelMarkovPrecisionParameter p f := by
  have hbin := positiveKernelPreparationBinLog_mono_netExponent hp hef
  unfold positiveKernelMarkovPrecisionParameter
  linarith only [hbin]

end AllocatedExternalCandidateProblem

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
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateSampler

def FrontSourceProfile.mono_netExponent {degree e f : ℕ} {p : ℝ}
    (source : A.FrontSourceProfile degree p f) (hp : 0 ≤ p) (hef : e ≤ f) :
    A.FrontSourceProfile degree p e :=
  { source with
    markov_precision :=
      (AllocatedExternalCandidateProblem.positiveKernelMarkovPrecisionParameter_mono_netExponent
        (by positivity : 0 ≤ 2 * p) hef).trans source.markov_precision }

end AllocatedExternalCandidateSampler
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

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateSampler.InnerSourceProfile
variable {s : ℕ} (source : A.InnerSourceProfile (s + 1))

noncomputable def recursiveParameter : ℝ :=
  finiteFreezingRecursiveParameter (candidatePrimitivePhysicalBudgetExponent s 1)
    (allocatedAffineCanonicalBudget s source.ordinaryBudget source.physicalBudget)

noncomputable def separation : ℝ :=
  Real.exp (candidatePrimitiveFreezingCutoff s 1
    (allocatedAffineCanonicalBudget s source.ordinaryBudget source.physicalBudget))

theorem physicalBudget_nonneg : 0 ≤ source.physicalBudget :=
  (nativePhysicalTerminalBudgets_nonneg (s + 1) m source.Cprimitive source.scheduleExponent
    source.x_nonneg).2.2

theorem ordinaryBudget_nonneg : 0 ≤ source.ordinaryBudget :=
  (candidatePhysicalOrdinaryBudget_bounds source.physicalBudget_nonneg).1

theorem recursiveParameter_nonneg : 0 ≤ source.recursiveParameter := by
  have h := (allocatedAffineCanonicalBudget_bounds s source.ordinaryBudget_nonneg
    source.physicalBudget_nonneg).nonnegative
  unfold recursiveParameter finiteFreezingRecursiveParameter
  positivity

theorem physicalBudget_le_recursiveParameter : source.physicalBudget ≤ source.recursiveParameter := by
  have hb := candidatePhysicalOrdinaryBudget_bounds source.physicalBudget_nonneg
  have hc := allocatedAffineCanonicalBudget_bounds s hb.1 source.physicalBudget_nonneg
  change AllocatedAffineCanonicalBudgetBounds s source.ordinaryBudget source.physicalBudget at hc
  have hi := candidatePrimitivePhysical_input_budget s 1 hc.nonnegative
  have hpower : 0 ≤ (allocatedAffineCanonicalBudget s source.ordinaryBudget source.physicalBudget +
      candidatePrimitivePhysicalBudgetExponent s 1) ^ candidatePrimitivePhysicalBudgetExponent s 1 := by
    exact pow_nonneg (add_nonneg hc.nonnegative (Nat.cast_nonneg _)) _
  apply hc.full.trans
  unfold recursiveParameter finiteFreezingRecursiveParameter
  linarith only [hi, hpower]

theorem input_le_recursiveParameter : source.x ≤ source.recursiveParameter :=
  source.input_le_physicalBudget.trans source.physicalBudget_le_recursiveParameter

end AllocatedExternalCandidateSampler.InnerSourceProfile
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteNestedFrontNativeBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct

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
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateSampler.FrontSourceProfile

variable {degree e : ℕ} {p : ℝ} (source : A.FrontSourceProfile degree p e)

theorem familyCap_bounds (hp : 0 ≤ p) :
    0 ≤ source.familyCap ∧ p ≤ source.familyCap ∧
    AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p) ≤
      source.familyCap ∧
    source.u ≤ source.familyCap ∧ source.pModel ≤ source.familyCap ∧
    source.nativeBudget ≤ source.familyCap ∧ (m : ℝ) ≤ source.familyCap ∧
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ source.familyCap ∧
    3 ≤ source.familyCap := by
  have hq := AllocatedExternalCandidateProblem.positiveKernelPreparationParameter_nonneg
    (show 0 ≤ 2 * p by positivity)
  have hu := source.u_nonneg
  have hmodel := source.model_nonneg
  have hnative := source.native_nonneg
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hvariables : (0 : ℝ) ≤ Fintype.card (LayerSamplerVariables G I n B) :=
    Nat.cast_nonneg _
  dsimp only [familyCap]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    linarith only [hp, hq, hu, hmodel, hnative, hm, hvariables]

structure FamilyBudget : Prop where
  hpFamily : 0 ≤ source.familyParameter
  cost : p ≤ source.familyParameter
  projection : AllocatedExternalCandidateProblem.positiveKernelPreparationParameter (2 * p) ≤
    source.familyParameter
  native : max source.nativeBudget 3 ≤ source.familyParameter
  period : 2 * max source.nativeBudget 3 ≤ source.familyParameter
  variation : Real.exp (max source.nativeBudget 3) *
    (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
      ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤
        Real.exp source.familyParameter
  keepCard : ∀ keep : LayerSamplerVariables G I n B → Prop,
    (Fintype.card {i // keep i} : ℝ) ≤ source.familyParameter

theorem familyBudget (hp : 0 ≤ p) : source.FamilyBudget := by
  obtain ⟨hcap, hpCap, hqCap, _, _, hnCap, hmCap, hvCap, _⟩ := source.familyCap_bounds hp
  obtain ⟨hf0, hcf, hperiod, hvariation⟩ := candidateFrontFamilyBounds source.familyCap
    source.nativeBudget m (Fintype.card (LayerSamplerVariables G I n B))
    hcap hnCap hmCap hvCap
  refine ⟨hf0, hpCap.trans hcf, hqCap.trans hcf, ?_, hperiod, hvariation, ?_⟩
  · exact (by linarith [le_max_right source.nativeBudget (3 : ℝ)] :
      max source.nativeBudget 3 ≤ 2 * max source.nativeBudget 3).trans hperiod
  · intro keep
    have hcard : Fintype.card {i // keep i} ≤
        Fintype.card (LayerSamplerVariables G I n B) := Fintype.card_subtype_le _
    exact (Nat.cast_le.mpr hcard).trans (hvCap.trans hcf)

end AllocatedExternalCandidateSampler.FrontSourceProfile
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open AllocatedExternalCandidateProblem

theorem exists_preparedFiniteForwardFrontFamilyScalar_budget (Cnative : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (m cardVars : ℕ) {t p u pModel native : ℝ},
      0 ≤ t → p ∈ Set.Icc 0 t → u ∈ Set.Icc 0 t → pModel ∈ Set.Icc 0 t →
      (m : ℝ) ≤ t → (cardVars : ℝ) ≤ t →
      native ∈ Set.Icc 0 ((t + Cnative) ^ Cnative) →
      candidateFrontFamilyParameter
        (p + positiveKernelPreparationParameter (2 * p) + u + pModel + native + m + cardVars + 3) ∈
          Set.Icc 0 ((t + C) ^ C) := by
  let X : Polynomial ℕ := Polynomial.X
  let Q : Polynomial ℕ :=
    (5 * X + (2 * X + 5) ^ positiveKernelPreparationExponent +
      (X + Polynomial.C Cnative) ^ Cnative + 6) ^ 4
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro m cardVars t p u pModel native ht hp hu hmodel hm hvars hn
  have hp2 : 0 ≤ 2 * p := by linarith only [hp.1]
  have hq0 := positiveKernelPreparationParameter_nonneg hp2
  have hq : positiveKernelPreparationParameter (2 * p) ≤
      (2 * t + 5) ^ positiveKernelPreparationExponent := by
    unfold positiveKernelPreparationParameter
    exact pow_le_pow_left₀ (by linarith only [hp.1])
      (by linarith only [hp.2]) _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hv0 : (0 : ℝ) ≤ cardVars := Nat.cast_nonneg _
  have hbase0 : 0 ≤ p + positiveKernelPreparationParameter (2 * p) + u + pModel +
      native + m + cardVars + 3 + 3 := by
    linarith only [hp.1, hq0, hu.1, hmodel.1, hn.1, hm0, hv0]
  have hbase : p + positiveKernelPreparationParameter (2 * p) + u + pModel +
      native + m + cardVars + 3 + 3 ≤
      5 * t + (2 * t + 5) ^ positiveKernelPreparationExponent +
        (t + Cnative) ^ Cnative + 6 := by
    linarith only [hp.2, hq, hu.2, hmodel.2, hn.2, hm, hvars]
  have hbudget : (5 * t + (2 * t + 5) ^ positiveKernelPreparationExponent +
      (t + Cnative) ^ Cnative + 6) ^ 4 ≤ (t + C) ^ C := by
    simpa [Q, X, Polynomial.eval₂_pow] using hpoly t ht
  exact ⟨pow_nonneg hbase0 4, (pow_le_pow_left₀ hbase0 hbase 4).trans hbudget⟩

end Erdos3.VectorPolynomial

end

end OAI
end


