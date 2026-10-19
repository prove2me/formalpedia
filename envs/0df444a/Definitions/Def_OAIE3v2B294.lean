-- Prove2me | Definitions.Def_OAIE3v2B294
-- name    : OAIE3v2B294
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T09:09:33.665292+00:00
-- url     : https://prove2.me/theorems/18a038dc-d51b-428b-a951-3b0a601851c2
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 308 of 311
-- statement:
--   Definitions bundle 308 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B285`, `OAIE3v2B288`, `OAIE3v2B289`, `OAIE3v2B290`, `OAIE3v2B291` of this split.
--
--   Modules: `Dynamics/PreparedFiniteForwardFrontProfileBudget.lean`, `Dynamics/PreparedFiniteNestedCanonicalEarlyPrimitiveBudget.lean`, `Estimates/AllocatedZeroLayerForwardFrontSourceProfile.lean`, `Estimates/PreparedCanonicalInitializedRelativeSource.lean`, `Estimates/PreparedCanonicalInitializedRelativeSourceConclusion.lean`, `Estimates/PreparedCanonicalRelativeEndpointBounds.lean`, `Estimates/PreparedFiniteNestedSourceArrays.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B285
import Definitions.Def_OAIE3v2B288
import Definitions.Def_OAIE3v2B289
import Definitions.Def_OAIE3v2B290
import Definitions.Def_OAIE3v2B291

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteForwardFrontProfileBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open AllocatedExternalCandidateProblem

theorem exists_preparedFiniteForwardFrontProfile_budget (e : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (A : ℕ), C ≤ A →
      ∀ (stageCountConstant : ℕ → ℕ) {x p gainLog stageLog : ℝ},
      0 ≤ x → p ∈ Set.Icc 0 x → gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x →
      2 * p + 3 ≤ preparedFiniteForwardWork A stageCountConstant 0 x ∧
      positiveKernelPreparationParameter (2 * p) ≤
        preparedFiniteForwardWork A stageCountConstant 0 x ∧
      positiveKernelMarkovPrecisionParameter (2 * p) e ≤
        preparedFiniteForwardModelPrecision A stageCountConstant 0 x gainLog stageLog := by
  obtain ⟨K, _, hparameters⟩ := exists_positiveKernelPreparationParameters_bound e
  let Q : Polynomial ℕ := (2 * Polynomial.X + Polynomial.C K) ^ K
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro A hCA stageCountConstant x p gainLog stageLog hx hp hg hs
  have hp2 : 0 ≤ 2 * p := mul_nonneg (by norm_num) hp.1
  have hparameters' := hparameters (2 * p) hp2
  have hscaled : (2 * p + K) ^ K ≤ (2 * x + K) ^ K :=
    pow_le_pow_left₀ (add_nonneg hp2 (Nat.cast_nonneg K))
      (add_le_add (mul_le_mul_of_nonneg_left hp.2 (by norm_num)) le_rfl) K
  have hpoly : (2 * x + K) ^ K ≤ (x + C) ^ C := by
    simpa [Q, Polynomial.eval₂_pow] using hbudget x hx
  have hwork : (2 * p + K) ^ K ≤ preparedFiniteForwardWork A stageCountConstant 0 x :=
    hscaled.trans (hpoly.trans
      (preparedFiniteForward_shiftedPower_le_work A C stageCountConstant 0
        (hC.trans hCA) hCA hx))
  have hmodel : preparedFiniteForwardWork A stageCountConstant 0 x ≤
      preparedFiniteForwardModelPrecision A stageCountConstant 0 x gainLog stageLog := by
    simp only [preparedFiniteForwardModelPrecision, preparedFiniteForwardPrefixLog,
      Finset.range_zero, Finset.sum_empty, zero_add]
    linarith only [hg.1, hs.1]
  exact ⟨hparameters'.1.trans hwork, hparameters'.2.1.trans hwork,
    hparameters'.2.2.2.2.trans (hwork.trans hmodel)⟩

noncomputable def preparedFiniteForwardFrontProfileExponent (e : ℕ) : ℕ :=
  Classical.choose (exists_preparedFiniteForwardFrontProfile_budget e)

theorem preparedFiniteForwardFrontProfileExponent_two_le (e : ℕ) :
    2 ≤ preparedFiniteForwardFrontProfileExponent e :=
  (Classical.choose_spec (exists_preparedFiniteForwardFrontProfile_budget e)).1

theorem preparedFiniteForwardFrontProfile_bounds (e A : ℕ)
    (stageCountConstant : ℕ → ℕ) {x p gainLog stageLog : ℝ}
    (hA : preparedFiniteForwardFrontProfileExponent e ≤ A)
    (hx : 0 ≤ x) (hp : p ∈ Set.Icc 0 x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    2 * p + 3 ≤ preparedFiniteForwardWork A stageCountConstant 0 x ∧
    positiveKernelPreparationParameter (2 * p) ≤
      preparedFiniteForwardWork A stageCountConstant 0 x ∧
    positiveKernelMarkovPrecisionParameter (2 * p) e ≤
      preparedFiniteForwardModelPrecision A stageCountConstant 0 x gainLog stageLog :=
  (Classical.choose_spec (exists_preparedFiniteForwardFrontProfile_budget e)).2
    A hA stageCountConstant hx hp hg hs

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
    (sampler : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

variable (cutoff A Cslice : ℕ) (constants : ℕ → ℕ)
    {x p gainLog stageLog native E rawCap : ℝ} {degree e : ℕ}

local notation "work" => preparedFiniteForwardWork A constants 0 x
local notation "modelPrecision" => preparedFiniteForwardModelPrecision A constants 0 x gainLog stageLog
local notation "sourcePrecision" => preparedFiniteForwardSourcePrecision A constants 0 x gainLog stageLog
local notation "slice" => (x + Cslice) ^ Cslice
local notation "test" => Polynomial.eval₂ (Nat.castRingHom ℝ)
    (allocatedModelTestLog sourcePrecision work) (preparedFiniteForwardDetectorPolynomial cutoff)

attribute [local instance] OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.forwardFrontSourceSiteNonempty
noncomputable def preparedFiniteForwardFrontSourceProfile
    (hA : preparedFiniteForwardFrontProfileExponent e ≤ A)
    (hCslice : 1 ≤ Cslice) (hSliceExponent : Cslice + 1 ≤ A)
    (hx : 0 ≤ x) (hp : p ∈ Set.Icc 0 x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ x)
    (hξ : ξ ≤ 1) (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i)
    (hnative : 0 ≤ native) (hcap : rawCap ≤ Real.exp work)
    (hprojection : modelPrecision + 2 * work + max (max native 3)
      (2 * modelPrecision + 4 * work + 20) + 32 ≤ E)
    (hdetection : sampler.NativeDetection degree slice test native
      (Real.exp (-(2 * modelPrecision + 4 * work + 8))))
    (hexcess :
      (FiniteProbabilityWeights.uniformFinset (integerBox N) sampler.integerBox_nonempty).excessMass
        (sampler.law.siteLaw (sampler.physicalBox hξ hmargin)) rawCap ≤
          6 * positiveProjectionAccuracy E) : sampler.FrontSourceProfile degree p e := by
  have hAtwo : 2 ≤ A := (preparedFiniteForwardFrontProfileExponent_two_le e).trans hA
  have hw : 0 ≤ work := preparedFiniteForwardWork_nonneg A constants 0 hx
  have hprecision := preparedFiniteForward_model_precision_bounds A constants 0 hx hg hs
  have hfront := preparedFiniteForwardFrontProfile_bounds e A constants hA hx hp hg hs
  have hslice := preparedFiniteForward_controlled_slice_bounds A Cslice constants 0
    (Fintype.card (LayerSamplerVariables G I n B)) hAtwo hSliceExponent hx hvariables
  have htest := (preparedFiniteForwardDetectorPolynomial_bounds cutoff hprecision.2.1 hw).1
  have hslice0 : 0 ≤ slice := by
    simpa only [preparedFiniteForwardParameter_zero] using hslice.1
  have hsliceLoss : slice * Fintype.card (LayerSamplerVariables G I n B) ≤ work := by
    simpa only [preparedFiniteForwardParameter_zero] using hslice.2.2
  have htwo : 2 ≤ test := by linarith only [hp.1, hfront.1, htest]
  exact sampler.preparedFixedCenterFrontSourceProfile
    hξ hmargin hprecision.1 hw hfront.1 hnative hslice0 htwo hsliceLoss
    hcap hprojection le_rfl hdetection le_rfl hexcess
    (preparedFiniteForwardFrontProfile_slice_bound Cslice hCslice hx hp.2)
    (hfront.2.1.trans htest) hfront.2.2

end AllocatedExternalCandidateSampler
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

namespace AllocatedExternalCandidateSampler

variable (cutoff exponent Cslice Cdirect : ℕ) (constants : ℕ → ℕ)
    {x p gainLog stageLog Bstruct pnum Pchart Qstride Plate E rawCap : ℝ} {degree e : ℕ}

local notation "work" => preparedFiniteForwardWork exponent constants 0 x
local notation "modelPrecision" => preparedFiniteForwardModelPrecision exponent constants 0 x gainLog stageLog
local notation "sourcePrecision" => preparedFiniteForwardSourcePrecision exponent constants 0 x gainLog stageLog
local notation "slice" => (x + Cslice) ^ Cslice
local notation "test" => Polynomial.eval₂ (Nat.castRingHom ℝ)
    (allocatedModelTestLog sourcePrecision work) (preparedFiniteForwardDetectorPolynomial cutoff)
local notation "master" => preparedFiniteForwardActualFrontLocalMaster m G
    (Fintype.card (LayerSamplerVariables G I n B)) (Fintype.card X)
    (preparedFiniteForwardDetectorPolynomial cutoff) exponent Cdirect constants degree
    x gainLog stageLog Bstruct pnum Pchart Qstride
local notation "native" => PreparedModularCanonicalDetectorResources.nativeBudget
    (preparedModularGeneralDetectorResources
      (preparedModularGeneralDetectorConstants m degree) (degree + 1) master Plate)
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

attribute [local instance] OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.actualForwardFrontSourceSiteNonempty
noncomputable def preparedFiniteForwardActualFrontSourceProfile
    (hExponent : preparedFiniteForwardFrontProfileExponent e ≤ exponent)
    (hCslice : 1 ≤ Cslice) (hSliceExponent : Cslice + 1 ≤ exponent)
    (hdegree : degree ≤ m)
    (hx : 0 ≤ x) (hp : p ∈ Set.Icc 0 x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x)
    (hBstruct : Bstruct ∈ Set.Icc 0 x) (hpnum : pnum ∈ Set.Icc 0 x)
    (hPchart : Pchart ∈ Set.Icc 0 x) (hQstride : Qstride ∈ Set.Icc 0 x)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ x)
    (hX : (Fintype.card X : ℝ) ≤ x) (hG : (Fintype.card G : ℝ) ≤ x)
    (hξ : ξ ≤ 1) (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i)
    (hcap : rawCap ≤ Real.exp work)
    (hprojection : modelPrecision + 2 * work + max (max native 3)
      (2 * modelPrecision + 4 * work + 20) + 32 ≤ E)
    (hdetection : sampler.NativeDetection degree slice test native
      (Real.exp (-(2 * modelPrecision + 4 * work + 8))))
    (hexcess :
      (FiniteProbabilityWeights.uniformFinset (integerBox N) sampler.integerBox_nonempty).excessMass
        (sampler.law.siteLaw (sampler.physicalBox hξ hmargin)) rawCap ≤
          6 * positiveProjectionAccuracy E) : sampler.FrontSourceProfile degree p e := by
  have hExponentTwo : 2 ≤ exponent :=
    (preparedFiniteForwardFrontProfileExponent_two_le e).trans hExponent
  have hresource := (Classical.choose_spec
      (exists_preparedFiniteForwardActualNativeBudget m (preparedFiniteForwardDetectorPolynomial cutoff))).2
    ⟨degree, Nat.lt_succ_of_le hdegree⟩ exponent Cdirect constants 0 false
    (G := G) hExponentTwo hx hg hs hBstruct hpnum hPchart hQstride
    hvariables hX hG Plate
  have hnative : 0 ≤ native := hresource.2.2.1.1
  exact sampler.preparedFiniteForwardFrontSourceProfile cutoff exponent Cslice constants
    hExponent hCslice hSliceExponent hx hp hg hs hvariables hξ hmargin
    hnative hcap hprojection hdetection hexcess

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin 0 → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin 0 → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSampler

variable (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection

variable (q cutoff exponent Cslice Cdirect : ℕ) (constants : ℕ → ℕ)
    {x p gainLog stageLog Bstruct pnum Pchart Qstride Plate : ℝ} {degree e : ℕ}
local notation "work" => preparedFiniteForwardWork exponent constants 0 x
local notation "modelPrecision" => preparedFiniteForwardModelPrecision exponent constants 0 x gainLog stageLog
local notation "sourcePrecision" => preparedFiniteForwardSourcePrecision exponent constants 0 x gainLog stageLog
local notation "test" => Polynomial.eval₂ (Nat.castRingHom ℝ)
    (allocatedModelTestLog sourcePrecision work) (preparedFiniteForwardDetectorPolynomial cutoff)
local notation "master" => preparedFiniteForwardActualFrontLocalMaster q G
    (Fintype.card (LayerSamplerVariables G I n B)) (Fintype.card X)
    (preparedFiniteForwardDetectorPolynomial cutoff) exponent Cdirect constants degree
    x gainLog stageLog Bstruct pnum Pchart Qstride
local notation "native" => PreparedModularCanonicalDetectorResources.nativeBudget
    (preparedModularGeneralDetectorResources
      (preparedModularGeneralDetectorConstants q degree) (degree + 1) master Plate)

attribute [local instance] OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.zeroLayerForwardFrontSiteNonempty
noncomputable def zeroLayerForwardFrontSourceProfile
    (hExponent : preparedFiniteForwardFrontProfileExponent e ≤ exponent)
    (hCslice : 1 ≤ Cslice) (hSliceExponent : Cslice + 1 ≤ exponent)
    (hdegree : degree ≤ q)
    (hx : 0 ≤ x) (hp : p ∈ Set.Icc 0 x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x)
    (hBstruct : Bstruct ∈ Set.Icc 0 x) (hpnum : pnum ∈ Set.Icc 0 x)
    (hPchart : Pchart ∈ Set.Icc 0 x) (hQstride : Qstride ∈ Set.Icc 0 x)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ x)
    (hX : (Fintype.card X : ℝ) ≤ x) (hG : (Fintype.card G : ℝ) ≤ x)
    (hξ : ξ ≤ 1)
    {surplus L : ℝ} (hsurplus : 0 < surplus) (hsurplus1 : surplus ≤ 1)
    (htrim : τ = unconditionedSpatialTrimFraction (Fintype.card X) surplus)
    (hN : ∀ i, unconditionedSpatialWidthCutoff
      (allocatedExternalCandidateRootBudget B U b S) τ L ≤ (N i : ℝ))
    (hdetection : A.NativeDetection degree ((x + Cslice) ^ Cslice) test native
      (Real.exp (-(2 * modelPrecision + 4 * work + 8)))) :
    A.FrontSourceProfile degree p e := by
  have hExponentTwo : 2 ≤ exponent :=
    (preparedFiniteForwardFrontProfileExponent_two_le e).trans hExponent
  have hresource := (Classical.choose_spec
      (exists_preparedFiniteForwardActualNativeBudget q (preparedFiniteForwardDetectorPolynomial cutoff))).2
    ⟨degree, Nat.lt_succ_of_le hdegree⟩ exponent Cdirect constants 0 false
    (G := G) hExponentTwo hx hg hs hBstruct hpnum hPchart hQstride
    hvariables hX hG Plate
  have hnative : 0 ≤ native := hresource.2.2.1.1
  have hfront := preparedFiniteForwardFrontProfile_bounds e exponent constants hExponent hx hp hg hs
  have hwork : 1 ≤ work := by linarith only [hfront.1, hp.1]
  have hcap : (2 : ℝ) ≤ Real.exp work :=
    (by linarith : (2 : ℝ) ≤ work + 1).trans (Real.add_one_le_exp work)
  let precision := modelPrecision + 2 * work + max (max native 3)
    (2 * modelPrecision + 4 * work + 20) + 32
  have hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i := fun i => (A.trimMargin_proper i).le
  have hexcess :
      (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
        (A.law.siteLaw (A.physicalBox hξ hmargin)) 2 ≤
          6 * positiveProjectionAccuracy precision := by
    rw [A.fixedCenter_excess_zero_layers_of_spatial_cutoff hξ hmargin
      hsurplus hsurplus1 htrim hN]
    exact mul_nonneg (by norm_num) (Real.exp_nonneg _)
  exact A.preparedFiniteForwardFrontSourceProfile cutoff exponent Cslice constants
    hExponent hCslice hSliceExponent hx hp hg hs hvariables hξ hmargin
    hnative hcap (le_refl precision) hdetection hexcess

noncomputable def zeroLayerDegreeSourceProfile
    {degree e : ℕ} {p : ℝ}
    (front : A.FrontSourceProfile degree p e)
    (inner : A.InnerSourceProfile degree)
    (hinput : p ≤ inner.x) (htrim : τ ≤ 1) :
    A.DegreeSourceProfile degree p e where
  front := front
  inner := inner
  input_inner := hinput
  trim_le_one := htrim
  width_le_one := fun j => Fin.elim0 j
  polynomial_degree := fun j => Fin.elim0 j
  chartConstant := fun j => Fin.elim0 j
  chartConstant_nonneg := fun j => Fin.elim0 j
  chart_bound := fun j => Fin.elim0 j
  chart_small := fun j => Fin.elim0 j

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteNestedSourceArrays
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

noncomputable def preparedFiniteNestedSourceExponent
    (m cutoff e Cprimitive Cdirect extra : ℕ) : ℕ :=
  2 + extra + preparedFiniteForwardFrontProfileExponent e +
    preparedCommonRadiusDensityCapNestedExponent m +
    preparedFiniteNestedSourceSliceExponent m cutoff Cprimitive + 1 +
    ∑ d : Fin (cutoff + 1), allocatedCandidateForwardScheduleExponent d.val m Cprimitive
      (preparedFiniteNestedSourceNativeExponent m cutoff Cdirect) 2

theorem preparedFiniteNestedSourceExponent_bounds
    (m cutoff e Cprimitive Cdirect extra A : ℕ)
    (hA : preparedFiniteNestedSourceExponent m cutoff e Cprimitive Cdirect extra ≤ A) :
    2 ≤ A ∧ extra ≤ A ∧ preparedFiniteForwardFrontProfileExponent e ≤ A ∧
    preparedCommonRadiusDensityCapNestedExponent m ≤ A ∧
    preparedFiniteNestedSourceSliceExponent m cutoff Cprimitive + 1 ≤ A ∧
    ∀ d ≤ cutoff, allocatedCandidateForwardScheduleExponent d m Cprimitive
      (preparedFiniteNestedSourceNativeExponent m cutoff Cdirect) 2 ≤ A := by
  have hfields : 2 ≤ A ∧ extra ≤ A ∧ preparedFiniteForwardFrontProfileExponent e ≤ A ∧
      preparedCommonRadiusDensityCapNestedExponent m ≤ A ∧
      preparedFiniteNestedSourceSliceExponent m cutoff Cprimitive + 1 ≤ A := by
    unfold preparedFiniteNestedSourceExponent at hA
    omega
  refine ⟨hfields.1, hfields.2.1, hfields.2.2.1, hfields.2.2.2.1,
    hfields.2.2.2.2, ?_⟩
  intro d hd
  have hsum := Finset.single_le_sum
    (f := fun i : Fin (cutoff + 1) => allocatedCandidateForwardScheduleExponent i.val m Cprimitive
      (preparedFiniteNestedSourceNativeExponent m cutoff Cdirect) 2)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨d, Nat.lt_succ_of_le hd⟩ : Fin (cutoff + 1)))
  change allocatedCandidateForwardScheduleExponent d m Cprimitive
    (preparedFiniteNestedSourceNativeExponent m cutoff Cdirect) 2 ≤ _ at hsum
  unfold preparedFiniteNestedSourceExponent at hA
  omega

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def preparedFiniteNestedResourceLayerSourceExponent
    (m q cutoff e Cprimitive Cdirect extra : ℕ) : ℕ :=
  2 + extra + preparedFiniteForwardFrontProfileExponent e +
    preparedFiniteNestedSourceSliceExponent m cutoff Cprimitive + 1 +
    ∑ d : Fin (cutoff + 1), allocatedCandidateForwardScheduleExponent d.val m Cprimitive
      (preparedFiniteNestedSourceNativeExponent q cutoff Cdirect) 2

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteNestedCanonicalEarlyPrimitiveBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

theorem exists_preparedFiniteNestedCanonicalEarlyPrimitive_budget
    (s outerDepth innerDepth cutoff e Cprimitive Cdirect extra : ℕ)
    (constants : ℕ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ m ≤ s, ∀ (G : Type) [Fintype G] (count nX M : ℕ)
      {Bstruct pnum Qstride gainLog stageLog : ℝ},
      let q := max m cutoff
      let A := preparedFiniteNestedSourceExponent q cutoff e Cprimitive Cdirect extra
      0 ≤ Bstruct → pnum ∈ Set.Icc 0 Bstruct → Qstride ∈ Set.Icc 0 Bstruct →
      gainLog ∈ Set.Icc 0 Bstruct → stageLog ∈ Set.Icc 0 Bstruct →
      (count : ℝ) ≤ Bstruct → (nX : ℝ) ≤ Bstruct →
      (Fintype.card G : ℝ) ≤ Bstruct → (M : ℝ) ≤ Bstruct →
      allocatedCommonProductRadiusLog q Bstruct Bstruct ∈ Set.Icc 0 ((Bstruct + 2) ^ C) ∧
      allocatedComparisonDimension q pnum ∈ Set.Icc 0 ((Bstruct + 2) ^ C) ∧
      ((nX + q * M : ℕ) : ℝ) ∈ Set.Icc 0 ((Bstruct + 2) ^ C) ∧
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
      preparedFiniteNestedSourceNative q G count nX (preparedFiniteForwardDetectorPolynomial cutoff)
        A Cdirect constants Bstruct pnum Qstride gainLog stageLog 0 k ∈
          Set.Icc 0 ((Bstruct + 2) ^ C) ∧
      (preparedFiniteForwardDetectorPolynomial cutoff).eval₂ (Nat.castRingHom ℝ)
        (allocatedModelTestLog sourceU work) ∈ Set.Icc 0 ((Bstruct + 2) ^ C) := by
  let q := fun i : Fin (s + 1) => max i.val cutoff
  let A := fun i : Fin (s + 1) =>
    preparedFiniteNestedSourceExponent (q i) cutoff e Cprimitive Cdirect extra
  have hA (i : Fin (s + 1)) : 2 ≤ A i :=
    (preparedFiniteNestedSourceExponent_bounds (q i) cutoff e Cprimitive Cdirect extra
      (A i) le_rfl).1
  let exponent := fun i : Fin (s + 1) => Classical.choose
    (exists_preparedFiniteNestedEarlyPrimitive_budget (q i) cutoff (A i) Cdirect
      outerDepth innerDepth constants (hA i) (Nat.le_max_right _ _))
  let C := max 2 (Finset.univ.sup exponent)
  refine ⟨C, le_max_left _ _, ?_⟩
  intro m hm G _ count nX M Bstruct pnum Qstride gainLog stageLog q' A'
    hB hnum hstride hg hs hcount hnX hG hM
  let i : Fin (s + 1) := ⟨m, Nat.lt_succ_of_le hm⟩
  have hlocal := (Classical.choose_spec
    (exists_preparedFiniteNestedEarlyPrimitive_budget (q i) cutoff (A i) Cdirect
      outerDepth innerDepth constants (hA i) (Nat.le_max_right _ _))).2
    G count nX M hB hnum hstride hg hs hcount hnX hG hM
  have hexponent : exponent i ≤ C :=
    (Finset.le_sup (Finset.mem_univ i)).trans (le_max_right _ _)
  have hentry : (Bstruct + 2) ^ exponent i ≤ (Bstruct + 2) ^ C :=
    pow_le_pow_right₀ (by linarith only [hB]) hexponent
  have lift {z : ℝ} (hz : z ∈ Set.Icc 0 ((Bstruct + 2) ^ exponent i)) :
      z ∈ Set.Icc 0 ((Bstruct + 2) ^ C) := ⟨hz.1, hz.2.trans hentry⟩
  obtain ⟨hradius, hdimension, hmodelDimension, hendpoint, hslots⟩ := hlocal
  refine ⟨lift hradius, lift hdimension, lift hmodelDimension, lift hendpoint, ?_⟩
  intro k seed stage sourceU work
  obtain ⟨hparameter, hsource, hmodel, hwork, hnative, hdetector⟩ := hslots k
  exact ⟨lift hparameter, lift hsource, lift hmodel, lift hwork, lift hnative, lift hdetector⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedCanonicalRelativeEndpointBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

noncomputable def preparedCanonicalRelativeSourceRequired
    {nX D m : ℕ} (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    (s outerDepth innerDepth e Cprimitive Cdirect extra : ℕ)
    (Bstruct p knob : ℝ) : ℝ :=
  let q := max m s
  let M := preparationCoordinateCap q D (s * D)
  let Jalloc := modularInitialBlockCount q (nX + q * M)
  let G := EnlargedPreparedCommonKernel q Jalloc
  let count := Fintype.card (LayerSamplerVariables G
    (PreparedSamplerContinuous (prep.pad q)) (preparedSamplerTransverse (prep.pad q))
    (EnlargedPreparedCommonSamplerBlock (prep.pad q) Jalloc))
  preparedFiniteNestedSourceRequiredLog q s
    (preparedFiniteNestedSourceExponent q s e Cprimitive Cdirect extra) Cdirect outerDepth innerDepth
    AllocatedExternalCandidateSampler.degreeSourceCountConstants G M count nX Bstruct
    (enlargedPreparedCommonSamplerDimension q M Jalloc) 0 p 0 knob knob knob knob knob

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedCanonicalInitializedRelativeSourceConclusion
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection integerBox
  RankPreparationFamily.PreparedHeights.canonicalPaddedSamplerData

noncomputable def preparedCanonicalInitializedRelativeSourceConclusion
    {nX m s D Erest : ℕ} (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    (oldPatch : PolynomialPatch (Fin nX) s (D + Erest)) (F : oldPatch.LowestLayerModel m)
    (outerDepth innerDepth e Cprimitive Cdirect extra : ℕ)
    {p pRelative Bstruct knob pPrep pLate precisionBudget : ℝ} {Rrank : ℕ}
    (hheight : prep.PreparedHeights pPrep Rrank) (hsize : prep.Sized D (m * D))
    (hms : m ≤ s) (_hs : 1 ≤ s) (_hnX : 0 < nX)
    (_hp : 2 ≤ p) (hpPrep : 0 ≤ pPrep) (hRank : 1 ≤ Rrank)
    (hPrepLate : pPrep ≤ pLate) (hRankLate : (Rrank : ℝ) ≤ Real.exp pLate)
    (hCapLate : (preparationCoordinateCap (max m s) D (s * D) : ℝ) ≤ pLate)
    (_hprimitive : 1 ≤ Cprimitive) (_hknob : 0 ≤ knob)
    (_hstructure :
      let M := preparationCoordinateCap s D (s * D)
      let Jalloc := modularInitialBlockCount s (nX + s * M)
      let dim := enlargedPreparedCommonSamplerDimension s M Jalloc
      p ≤ pRelative ∧ (s : ℝ) + 3 ≤ pRelative ∧
        (M : ℝ) ≤ pRelative ∧ (Jalloc : ℝ) ≤ pRelative ∧
        (dim : ℝ) ≤ pRelative ∧ allocatedUniformChartLog (M : ℝ) + 1 ≤ pRelative)
    (_hBrelative : 6 * pRelative + 35 ≤ Bstruct)
    (_hprecision : 3 * pRelative + 130 ≤ precisionBudget)
    (_hnXp : (nX : ℝ) ≤ p)
    (_hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Bstruct)
    (_hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Bstruct)
    (N : Fin nX → ℕ)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ))
      (Rrank : ℝ) (prep j).space (prep j).poly)
    (_hN : ∀ i, Real.exp (preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (N i : ℝ))
    (_hSourceRank : Real.exp (preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (Rrank : ℝ))
    (ip : Fin D → MvPolynomial (Fin nX) ℤ) (_hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial (Fin nX) ℝ (Fin D → ℝ))
    (_hprepare : ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      prep.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (_herr : ∀ x ∈ integerBox N, ∀ i,
      |eval (fun z => (x z : ℝ)) err i| ≤ Real.exp (-precisionBudget))
    {n₀ stage d₀ : ℕ} {discount : ℝ} {childCutoff childCost : ℝ → ℝ}
    (_ih : RelativePatchInductionRule s n₀ stage discount childCutoff childCost)
    {a Λ initialCost : ℝ}
    (_ha : Real.exp (-p) ≤ a) (_haΛ : a ≤ Λ) (_hΛ : Λ ≤ 1)
    (_habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (_hOldComplexity : relativePatchComplexity oldPatch ≤ p)
    (_hDpos : 0 < D) (_hrest : ∀ i : Fin Erest, m < oldPatch.weight (i.natAdd D))
    (_hOldStage : relativePatchDistinctWeights oldPatch ≤ stage + 1)
    (f : (Fin nX → ℤ) → ℝ)
    (_hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (_hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (_hscore : Real.exp (-p) ≤ relativePatchBoxScore N f a oldPatch)
    (_hdiscount : discount ∈ Set.Icc (0 : ℝ) 1)
    (_hchildCost : 0 ≤ childCost (pRelative + 2))
    (_hCost : childCost (pRelative + 2) ≤ initialCost)
    (H Lmin Qgood : ℕ) (_hHLmin : H ≤ Lmin)
    (_hHcut : Real.exp (childCutoff (pRelative + 2)) ≤ (H : ℝ))
    (_hHcost : (H : ℝ) ≤ Real.exp initialCost)
    (_hLmin : (Lmin : ℝ) ≤ Real.exp knob)
    (_hQgood : 1 ≤ Qgood) (_hQexp : (Qgood : ℝ) ≤ Real.exp knob) : Prop :=
    let q := max m s
    let M := preparationCoordinateCap q D (s * D)
    let Jalloc := modularInitialBlockCount q (nX + q * M)
    let G := EnlargedPreparedCommonKernel q Jalloc
    let Vars := LayerSamplerVariables G (PreparedSamplerContinuous (prep.pad q))
      (preparedSamplerTransverse (prep.pad q)) (EnlargedPreparedCommonSamplerBlock (prep.pad q) Jalloc)
    let data := hheight.canonicalPaddedSamplerData prep Vars (Nat.le_max_left m s)
      hpPrep hRank hPrepLate hRankLate hsize (Nat.mul_le_mul_right D hms) hCapLate
    let U := fun j => (prep.pad q j).space
    letI : ∀ j, DecidableEq (prep.pad q j).Coord := fun _ => Classical.decEq _
    letI := data.measures.lattice
    letI := data.measures.coefficientCompact
    letI := data.measures.coefficientBorel
    letI := data.measures.rowCompact
    letI := data.measures.rowBorel
    letI := data.measures.siteBorel
    letI := data.measures.layerInvariant
    letI := data.measures.layerProbability
    letI := data.measures.coefficientInvariant
    letI := data.measures.coefficientProbability
    letI := data.measures.rowInvariant
    letI := data.measures.rowProbability
    let b := data.b
    let hb := data.span_eq
    let o := data.o
    let bW := data.bW
    let _ν := data.measures.layer
    let μ := data.measures.coefficient
    let _μrows := data.measures.row
    let cutoff := s
    let Q := PreparedSamplerContinuous (prep.pad q)
    let Qstride : ℝ := 0
    let stageLog : ℝ := 0
    let endpoint := knob
    let Qσ := knob
    let Pmin := knob
    let requestedCoarse := knob
    let gainLog := p
    let gain := Real.exp (-p)
    let Vlog := knob
    let pchild := pRelative + 2
    let chartLog := allocatedUniformChartLog (M : ℝ)
    let Vtail : Fin q → ℝ≥0 := fun _ => ⟨Real.exp chartLog, (Real.exp_pos _).le⟩
    let stride : Fin nX → ℕ := fun _ => 1
    let cells : Finset (ColumnResiduePattern (Option Vars) (Fin nX) stride) := {0}
    let hmem := prep.pad_coefficients_mem (q := q) (fun j => (hheight j).2.1)
    let stageCountConstant := AllocatedExternalCandidateSampler.degreeSourceCountConstants
    let A := preparedFiniteNestedSourceExponent (max m cutoff) cutoff e Cprimitive Cdirect extra
    let Cslice := preparedFiniteNestedSourceSliceExponent (max m cutoff) cutoff Cprimitive
    let forecastCap : ℝ := 1
    let Qw := 2 * Bstruct + 2 * Vlog + 5 * (gainLog + 8) + 24
    let Pdetect := preparedFiniteForwardDetectorPolynomial cutoff
    let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
    let degree : K → ℕ := preparedFiniteNestedForwardAllDegreeDegree
    let Cdetect := fun k : K => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
    let kModel : K := preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth cutoff
    let sourceU := fun k : K =>
      preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant
        (preparedFiniteNestedForwardAllDegreeStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
        (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k) gainLog stageLog
    let modelLog := fun k : K => preparedFiniteForwardWork A stageCountConstant
      (preparedFiniteNestedForwardAllDegreeStage k).val
      (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k)
    let sliceLog := fun k : K =>
      (preparedFiniteForwardParameter A stageCountConstant (preparedFiniteNestedForwardAllDegreeStage k).val
        (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k) + Cslice) ^ Cslice
    let u := preparedFiniteForwardModelPrecision A stageCountConstant innerDepth
      (candidateNestedForwardSeed A stageCountConstant innerDepth outerDepth Bstruct) gainLog stageLog
    let p := preparedFiniteForwardWork A stageCountConstant innerDepth
      (candidateNestedForwardSeed A stageCountConstant innerDepth outerDepth Bstruct)
    let pnum : ℝ := enlargedPreparedCommonSamplerDimension (max m cutoff) M (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))
    let R : Fin (max m cutoff) → ℝ := fun _ => allocatedCommonProductRadius (max m cutoff) Bstruct Bstruct
    let pRadius := allocatedCommonProductRadiusLog (max m cutoff) Bstruct Bstruct
    let D := allocatedComparisonDimension (max m cutoff) pnum
    let pDetect := fun k => allocatedModelTestLog (sourceU k) (modelLog k)
    let aDetect := fun k => 2 * sourceU k + 4 * modelLog k + 7
    let detectionGain := fun s : K => slicedDetectionGainLog (degree s) (Cdetect s)
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))))) (pDetect s) (pDetect s) (aDetect s)
    let Pk := fun s : K => scalarKernelLogarithmicBudget (Fin ((degree s) + 1)) (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
      (detectionGain s + pDetect s + 4)
    let Pphysical := fun k : K => preparedFiniteScheduleLocalPhysical (max m cutoff) nX
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))))) Qstride (Pk k)
    let target := fun k => detectionGain k + 40 + coefficientErrorSpatialLog (Pphysical k)
    let E := fun s : K => target s + D * (((max m cutoff) * 2 ^ ((max m cutoff) + 1) : ℕ) * Pk s) + 5
    let Prho := fun s : K => 2 * affineProfileInputEnvelope D
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2) + 2
    let Ptail := fun s : K => affineProfileToleranceEnvelope (max m cutoff) D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2)
    let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
    let Tmod := fun s : K => (((max m cutoff) + 1 : ℕ) : ℝ) * Pk s + nX * Qstride
    let lengthLogs := fun s : K => allocatedAffineLengthLog (max m cutoff) D Pscale (Prho s) (Pk s)
      (target s) (pDetect s + 2) (Tmod s)
    let Pseed := allocatedScaleLog (Pscale + ∑ s, lengthLogs s + Pmin + 1)
    let W := physicalBadProductGap ((modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)) * (nX + (max m cutoff) * M)) (gainLog + 8) Vlog Qgood
    let Pmaster := fun k : K => preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride
      (Pphysical k) (sourceU k) (modelLog k) (Prho k) (target k) (detectionGain k)
    let coarseTarget := preparedFiniteScheduleDirectCoarse detectionGain requestedCoarse
    let Plate := ∑ k : K, preparedUniformDegreeDirectLate (Pmaster k) Pscale
      (Pphysical k) coarseTarget (allocatedWitnessScaleLog Pseed Qw)
    let native : K → ℝ := fun k =>
      (preparedModularGeneralDetectorResources
        (preparedModularGeneralDetectorConstants (max m cutoff) (degree k))
        (degree k + 1) (Pmaster k) Plate).nativeBudget
    let Econditional := preparedNestedFrontProjectionEnvelope A stageCountConstant innerDepth
      (fun k : K => k.1.val) (fun k : K => k.2.1.val) native
      Bstruct gainLog stageLog endpoint
    let τ := Real.exp (-(gainLog + (nX : ℝ) + 8))
    let α := fun k : K => Real.exp (-(2 * preparedFiniteForwardModelPrecision A stageCountConstant
      (preparedFiniteNestedForwardAllDegreeStage k).val
      (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k) gainLog stageLog +
      4 * modelLog k + 8))
    let baseB0 := preparedUniformDegreeProductiveCertificateBudget M nX pRadius Pscale Pseed Qw (gainLog + 8) Vlog
    let Pwidth := 4 * (Plate + 8) ^ 2
    let Bcert := preparedForecastGoodCertificateBudget baseB0 Bstruct Pwidth gainLog Vlog
    let Pgood := preparedForecastGoodAnalyticBudget (preparedCenteredShortForecastSpatialExponent (max m cutoff))
      baseB0 Bstruct Pwidth gainLog Vlog
    let anchorRequired := preparedFiniteScheduleAnchorGoodRequired (max m cutoff) (Pmaster kModel) Plate Econditional Bcert Pgood Pwidth
    let conditionalRequired := preparedConditionalExcessRequired (max m cutoff) Plate Econditional
    let detectorRequired := fun k : K => (preparedModularGeneralDetectorResources
      (preparedModularGeneralDetectorConstants (max m cutoff) (degree k)) (degree k + 1) (Pmaster k) Plate).required
    let _Rreq := preparedFiniteNestedSourceRequired A stageCountConstant innerDepth outerDepth cutoff Bstruct
      anchorRequired conditionalRequired detectorRequired
    ∃ (hR : ∀ j, 0 < R j) (σ : ℝ) (hσ : 0 < σ)
      (S : LayerSamplerScale («G» := (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) («I» := (PreparedSamplerContinuous (prep.pad (max m cutoff)))) («n» := (preparedSamplerTransverse (prep.pad (max m cutoff)))) («J» := (fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b R (fun _ => σ)),
      0 ≤ pRadius ∧ (∀ j, R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      σ ≤ 1 ∧ σ ≤ Real.exp (-Qσ) ∧ σ⁻¹ ≤ Real.exp Pscale ∧
      Lmin ≤ S.value ∧ (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog Pseed Qw) ∧
      (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
        8 * (probabilityProfileLipschitz : ℝ) * W ≤
          (layerSamplerGapWidth («G» := (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) R ⟨j, i⟩ / 2) *
            ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
      (∀ s : K, PreparedUniformDegreeGeometryAt («G» := (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b S (degree s) (Cdetect s) nX
        Bstruct Pscale D (target s) (Pk s) (Prho s) Qstride (pDetect s) pRadius (aDetect s) (detectionGain s)) ∧
      (∀ k, PreparedUniformDegreeDirectScalarBounds (max m cutoff) (degree k) nX
        (Fintype.card (LayerSamplerVariables
          (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
          (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff)))
          (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))))
        (Cdetect k) Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride (Pmaster k) Plate
        (detectionGain k) (Pphysical k) coarseTarget pRadius (sourceU k) (modelLog k) (sliceLog k)) ∧
      (∀ k, PreparedScheduledDirectSourceAvailability
          (B := EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection (max m cutoff)
            (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)) (degree k) (preparedFiniteNestedForwardAllDegreeDegree_le (Nat.le_max_right m cutoff) k))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) ∧
      (∀ k, PreparedScheduledDegreeModelAvailability
          (B := EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection (max m cutoff)
            (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)) (degree k)
              (preparedFiniteNestedForwardAllDegreeDegree_le (Nat.le_max_right m cutoff) k))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o) (μ := μ)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) ∧
      PreparedUniformDegreeProductiveSourceConclusion
        (m := (max m cutoff)) (nX := nX) (M := M) (prep := (prep.pad (max m cutoff))) (U := U) (b := b) (S := S)
        (hR := hR) (hσ := fun _ => hσ) (stride := stride) (N := N)
        (Pdetect := Pdetect) (pModel := modelLog kModel) (pSlice := sliceLog kModel)
        (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
        (hb := hb) (o := o) (bW := bW) (μ := μ)
        Bstruct Qstride (Pmaster kModel) Plate (detectionGain kModel) (Pphysical kModel) coarseTarget
        pRadius Pscale Pseed Qw gainLog gain Vlog Qgood ∧
      ∃ (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i)
        (Acandidate : AllocatedExternalCandidateSamplerFamily (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b S hb o hR (fun _ => hσ)
          N (fun j => (prep.pad (max m cutoff) j).poly) hmem τ (Real.exp (-Plate)) stride cells)
        (hξone : Real.exp (-Plate) ≤ 1),
      PreparedCenteredProductiveGoodCenterEnhancedConclusion (m := (max m cutoff)) (nX := nX) (M := M)
        (prep.pad (max m cutoff)) U b S bW hb o hR (fun _ => hσ) μ (fun j => (prep.pad (max m cutoff) j).poly) hmem stride
        (allocatedExternalCandidateWidths (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b S N τ (Real.exp (-Plate))) (Acandidate 0).bases
        gainLog gain Qgood (preparedSpatialKernelBlocks (max m cutoff) M nX) Acandidate.law N (relativePatchSourceTest N f a oldPatch)
        (fun center =>
          let _ : DecidableEq (Fin nX) := Classical.decEq _
          ((∀ k : K, (Acandidate center).NativeDetection (degree k) (sliceLog k)
            (Pdetect.eval₂ (Nat.castRingHom ℝ) (pDetect k))
            (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants (max m cutoff) (degree k))
              (degree k + 1) (Pmaster k) Plate).nativeBudget (α k)) ∧
          letI : Nonempty (Acandidate center).Site := (Acandidate center).site_nonempty
          (FiniteProbabilityWeights.uniformFinset (integerBox N) (Acandidate center).integerBox_nonempty).excessMass
            ((Acandidate center).law.siteLaw ((Acandidate center).physicalBox hξone hmargin))
            (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous (prep.pad (max m cutoff))) j)) ((preparedSamplerTransverse (prep.pad (max m cutoff))) j) (R j) (Vtail j)) ≤
              6 * positiveProjectionAccuracy Econditional) ∧
          ∀ (outerFront outerInner : Fin (outerDepth + 1)) (d : ℕ),
            ∀ (hd : d ≤ cutoff), d ≤ innerDepth → ∀ (pInput : ℝ),
            pInput ∈ Set.Icc 0 (candidateNestedForwardSeed A stageCountConstant innerDepth outerFront.val Bstruct) →
            pInput ≤ candidateNestedForwardSeed A stageCountConstant innerDepth outerInner.val Bstruct →
            ∃ profile : (Acandidate center).DegreeSourceProfile d pInput e,
              profile.inner.x = candidateNestedForwardSeed A stageCountConstant innerDepth outerInner.val Bstruct ∧
              profile.inner.gainLog = candidateNestedForwardSeed A stageCountConstant innerDepth outerInner.val Bstruct ∧
              profile.front.u = preparedFiniteForwardModelPrecision A stageCountConstant 0
                (candidateNestedForwardSeed A stageCountConstant innerDepth outerFront.val Bstruct) gainLog stageLog ∧
              profile.front.pModel = preparedFiniteForwardWork A stageCountConstant 0
                (candidateNestedForwardSeed A stageCountConstant innerDepth outerFront.val Bstruct) ∧
              profile.front.nativeBudget = native (outerFront, 0, ⟨d, Nat.lt_succ_of_le hd⟩, false) ∧
              profile.inner.Cprimitive = Cprimitive ∧
              profile.inner.scheduleExponent = A ∧
              profile.inner.Csource = preparedFiniteNestedSourceNativeExponent (max m cutoff) cutoff Cdirect)
        (fun center centerLift productive =>
          AllocatedNormalizedCandidateConclusion (E := Q) (A := Acandidate center)
            s (fun k => H ≤ (Acandidate center).sides k) centerLift productive
            (childCost pchild) initialCost (d₀ + s * Erest) f
            ((1 - discount) ^ (stage + 1) * Λ))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedCanonicalInitializedRelativeSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct
attribute [local irreducible] AllocatedExternalCandidateSampler.NativeDetection integerBox
  RankPreparationFamily.PreparedHeights.canonicalPaddedSamplerData

noncomputable def preparedCanonicalInitializedRelativeSourceDataConclusion
    {nX m s D Erest : ℕ} (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    (oldPatch : PolynomialPatch (Fin nX) s (D + Erest)) (F : oldPatch.LowestLayerModel m)
    (outerDepth innerDepth e Cprimitive Cdirect extra : ℕ)
    {p pRelative Bstruct knob pPrep pLate precisionBudget : ℝ} {Rrank : ℕ}
    (hheight : prep.PreparedHeights pPrep Rrank) (_hsize : prep.Sized D (m * D))
    (_hms : m ≤ s) (_hs : 1 ≤ s) (_hnX : 0 < nX)
    (_hp : 2 ≤ p) (_hpPrep : 0 ≤ pPrep) (_hRank : 1 ≤ Rrank)
    (_hPrepLate : pPrep ≤ pLate) (_hRankLate : (Rrank : ℝ) ≤ Real.exp pLate)
    (_hCapLate : (preparationCoordinateCap (max m s) D (s * D) : ℝ) ≤ pLate)
    (_hprimitive : 1 ≤ Cprimitive) (_hknob : 0 ≤ knob)
    (_hstructure :
      let M := preparationCoordinateCap s D (s * D)
      let Jalloc := modularInitialBlockCount s (nX + s * M)
      let dim := enlargedPreparedCommonSamplerDimension s M Jalloc
      p ≤ pRelative ∧ (s : ℝ) + 3 ≤ pRelative ∧
        (M : ℝ) ≤ pRelative ∧ (Jalloc : ℝ) ≤ pRelative ∧
        (dim : ℝ) ≤ pRelative ∧ allocatedUniformChartLog (M : ℝ) + 1 ≤ pRelative)
    (_hBrelative : 6 * pRelative + 35 ≤ Bstruct)
    (_hprecision : 3 * pRelative + 130 ≤ precisionBudget)
    (_hnXp : (nX : ℝ) ≤ p)
    (_hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Bstruct)
    (_hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Bstruct)
    (N : Fin nX → ℕ)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ))
      (Rrank : ℝ) (prep j).space (prep j).poly)
    (_hN : ∀ i, Real.exp (preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (N i : ℝ))
    (_hSourceRank : Real.exp (preparedCanonicalRelativeSourceRequired prep s outerDepth innerDepth
      e Cprimitive Cdirect extra Bstruct p knob) ≤ (Rrank : ℝ))
    (ip : Fin D → MvPolynomial (Fin nX) ℤ) (_hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial (Fin nX) ℝ (Fin D → ℝ))
    (_hprepare : ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      prep.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (_herr : ∀ x ∈ integerBox N, ∀ i,
      |eval (fun z => (x z : ℝ)) err i| ≤ Real.exp (-precisionBudget))
    {n₀ stage d₀ : ℕ} {discount : ℝ} {childCutoff childCost : ℝ → ℝ}
    (_ih : RelativePatchInductionRule s n₀ stage discount childCutoff childCost)
    {a Λ initialCost : ℝ}
    (_ha : Real.exp (-p) ≤ a) (_haΛ : a ≤ Λ) (_hΛ : Λ ≤ 1)
    (_habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (_hOldComplexity : relativePatchComplexity oldPatch ≤ p)
    (_hDpos : 0 < D) (_hrest : ∀ i : Fin Erest, m < oldPatch.weight (i.natAdd D))
    (_hOldStage : relativePatchDistinctWeights oldPatch ≤ stage + 1)
    (f : (Fin nX → ℤ) → ℝ)
    (_hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (_hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (_hscore : Real.exp (-p) ≤ relativePatchBoxScore N f a oldPatch)
    (_hdiscount : discount ∈ Set.Icc (0 : ℝ) 1)
    (_hchildCost : 0 ≤ childCost (pRelative + 2))
    (_hCost : childCost (pRelative + 2) ≤ initialCost)
    (H Lmin Qgood : ℕ) (_hHLmin : H ≤ Lmin)
    (_hHcut : Real.exp (childCutoff (pRelative + 2)) ≤ (H : ℝ))
    (_hHcost : (H : ℝ) ≤ Real.exp initialCost)
    (_hLmin : (Lmin : ℝ) ≤ Real.exp knob)
    (_hQgood : 1 ≤ Qgood) (_hQexp : (Qgood : ℝ) ≤ Real.exp knob)
    (data :
      let q := max m s
      let M := preparationCoordinateCap q D (s * D)
      let Jalloc := modularInitialBlockCount q (nX + q * M)
      let G := EnlargedPreparedCommonKernel q Jalloc
      let Vars := LayerSamplerVariables G (PreparedSamplerContinuous (prep.pad q))
        (preparedSamplerTransverse (prep.pad q)) (EnlargedPreparedCommonSamplerBlock (prep.pad q) Jalloc)
      (prep.pad q).CanonicalSamplerData Vars M pLate) : Prop :=
    let q := max m s
    let M := preparationCoordinateCap q D (s * D)
    let Jalloc := modularInitialBlockCount q (nX + q * M)
    let G := EnlargedPreparedCommonKernel q Jalloc
    let Vars := LayerSamplerVariables G (PreparedSamplerContinuous (prep.pad q))
      (preparedSamplerTransverse (prep.pad q)) (EnlargedPreparedCommonSamplerBlock (prep.pad q) Jalloc)
    let U := fun j => (prep.pad q j).space
    letI : ∀ j, DecidableEq (prep.pad q j).Coord := fun _ => Classical.decEq _
    letI := data.measures.lattice
    letI := data.measures.coefficientCompact
    letI := data.measures.coefficientBorel
    letI := data.measures.rowCompact
    letI := data.measures.rowBorel
    letI := data.measures.siteBorel
    letI := data.measures.layerInvariant
    letI := data.measures.layerProbability
    letI := data.measures.coefficientInvariant
    letI := data.measures.coefficientProbability
    letI := data.measures.rowInvariant
    letI := data.measures.rowProbability
    let b := data.b
    let hb := data.span_eq
    let o := data.o
    let bW := data.bW
    let _ν := data.measures.layer
    let μ := data.measures.coefficient
    let _μrows := data.measures.row
    let cutoff := s
    let Q := PreparedSamplerContinuous (prep.pad q)
    let Qstride : ℝ := 0
    let stageLog : ℝ := 0
    let endpoint := knob
    let Qσ := knob
    let Pmin := knob
    let requestedCoarse := knob
    let gainLog := p
    let gain := Real.exp (-p)
    let Vlog := knob
    let pchild := pRelative + 2
    let chartLog := allocatedUniformChartLog (M : ℝ)
    let Vtail : Fin q → ℝ≥0 := fun _ => ⟨Real.exp chartLog, (Real.exp_pos _).le⟩
    let stride : Fin nX → ℕ := fun _ => 1
    let cells : Finset (ColumnResiduePattern (Option Vars) (Fin nX) stride) := {0}
    let hmem := prep.pad_coefficients_mem (q := q) (fun j => (hheight j).2.1)
    let stageCountConstant := AllocatedExternalCandidateSampler.degreeSourceCountConstants
    let A := preparedFiniteNestedSourceExponent (max m cutoff) cutoff e Cprimitive Cdirect extra
    let Cslice := preparedFiniteNestedSourceSliceExponent (max m cutoff) cutoff Cprimitive
    let forecastCap : ℝ := 1
    let Qw := 2 * Bstruct + 2 * Vlog + 5 * (gainLog + 8) + 24
    let Pdetect := preparedFiniteForwardDetectorPolynomial cutoff
    let K := PreparedFiniteNestedForwardAllDegreeSlot outerDepth innerDepth cutoff
    let degree : K → ℕ := preparedFiniteNestedForwardAllDegreeDegree
    let Cdetect := fun k : K => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
    let kModel : K := preparedFiniteNestedForwardAllDegreeAnchor outerDepth innerDepth cutoff
    let sourceU := fun k : K =>
      preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant
        (preparedFiniteNestedForwardAllDegreeStage k).val (preparedFiniteNestedForwardAllDegreeIsDirect k)
        (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k) gainLog stageLog
    let modelLog := fun k : K => preparedFiniteForwardWork A stageCountConstant
      (preparedFiniteNestedForwardAllDegreeStage k).val
      (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k)
    let sliceLog := fun k : K =>
      (preparedFiniteForwardParameter A stageCountConstant (preparedFiniteNestedForwardAllDegreeStage k).val
        (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k) + Cslice) ^ Cslice
    let u := preparedFiniteForwardModelPrecision A stageCountConstant innerDepth
      (candidateNestedForwardSeed A stageCountConstant innerDepth outerDepth Bstruct) gainLog stageLog
    let p := preparedFiniteForwardWork A stageCountConstant innerDepth
      (candidateNestedForwardSeed A stageCountConstant innerDepth outerDepth Bstruct)
    let pnum : ℝ := enlargedPreparedCommonSamplerDimension (max m cutoff) M (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))
    let R : Fin (max m cutoff) → ℝ := fun _ => allocatedCommonProductRadius (max m cutoff) Bstruct Bstruct
    let pRadius := allocatedCommonProductRadiusLog (max m cutoff) Bstruct Bstruct
    let D := allocatedComparisonDimension (max m cutoff) pnum
    let pDetect := fun k => allocatedModelTestLog (sourceU k) (modelLog k)
    let aDetect := fun k => 2 * sourceU k + 4 * modelLog k + 7
    let detectionGain := fun s : K => slicedDetectionGainLog (degree s) (Cdetect s)
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))))) (pDetect s) (pDetect s) (aDetect s)
    let Pk := fun s : K => scalarKernelLogarithmicBudget (Fin ((degree s) + 1)) (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
      (detectionGain s + pDetect s + 4)
    let Pphysical := fun k : K => preparedFiniteScheduleLocalPhysical (max m cutoff) nX
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))))) Qstride (Pk k)
    let target := fun k => detectionGain k + 40 + coefficientErrorSpatialLog (Pphysical k)
    let E := fun s : K => target s + D * (((max m cutoff) * 2 ^ ((max m cutoff) + 1) : ℕ) * Pk s) + 5
    let Prho := fun s : K => 2 * affineProfileInputEnvelope D
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2) + 2
    let Ptail := fun s : K => affineProfileToleranceEnvelope (max m cutoff) D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2)
    let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
    let Tmod := fun s : K => (((max m cutoff) + 1 : ℕ) : ℝ) * Pk s + nX * Qstride
    let lengthLogs := fun s : K => allocatedAffineLengthLog (max m cutoff) D Pscale (Prho s) (Pk s)
      (target s) (pDetect s + 2) (Tmod s)
    let Pseed := allocatedScaleLog (Pscale + ∑ s, lengthLogs s + Pmin + 1)
    let W := physicalBadProductGap ((modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)) * (nX + (max m cutoff) * M)) (gainLog + 8) Vlog Qgood
    let Pmaster := fun k : K => preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride
      (Pphysical k) (sourceU k) (modelLog k) (Prho k) (target k) (detectionGain k)
    let coarseTarget := preparedFiniteScheduleDirectCoarse detectionGain requestedCoarse
    let Plate := ∑ k : K, preparedUniformDegreeDirectLate (Pmaster k) Pscale
      (Pphysical k) coarseTarget (allocatedWitnessScaleLog Pseed Qw)
    let native : K → ℝ := fun k =>
      (preparedModularGeneralDetectorResources
        (preparedModularGeneralDetectorConstants (max m cutoff) (degree k))
        (degree k + 1) (Pmaster k) Plate).nativeBudget
    let Econditional := preparedNestedFrontProjectionEnvelope A stageCountConstant innerDepth
      (fun k : K => k.1.val) (fun k : K => k.2.1.val) native
      Bstruct gainLog stageLog endpoint
    let τ := Real.exp (-(gainLog + (nX : ℝ) + 8))
    let α := fun k : K => Real.exp (-(2 * preparedFiniteForwardModelPrecision A stageCountConstant
      (preparedFiniteNestedForwardAllDegreeStage k).val
      (preparedFiniteNestedForwardAllDegreeSeed A stageCountConstant Bstruct k) gainLog stageLog +
      4 * modelLog k + 8))
    let baseB0 := preparedUniformDegreeProductiveCertificateBudget M nX pRadius Pscale Pseed Qw (gainLog + 8) Vlog
    let Pwidth := 4 * (Plate + 8) ^ 2
    let Bcert := preparedForecastGoodCertificateBudget baseB0 Bstruct Pwidth gainLog Vlog
    let Pgood := preparedForecastGoodAnalyticBudget (preparedCenteredShortForecastSpatialExponent (max m cutoff))
      baseB0 Bstruct Pwidth gainLog Vlog
    let anchorRequired := preparedFiniteScheduleAnchorGoodRequired (max m cutoff) (Pmaster kModel) Plate Econditional Bcert Pgood Pwidth
    let conditionalRequired := preparedConditionalExcessRequired (max m cutoff) Plate Econditional
    let detectorRequired := fun k : K => (preparedModularGeneralDetectorResources
      (preparedModularGeneralDetectorConstants (max m cutoff) (degree k)) (degree k + 1) (Pmaster k) Plate).required
    let _Rreq := preparedFiniteNestedSourceRequired A stageCountConstant innerDepth outerDepth cutoff Bstruct
      anchorRequired conditionalRequired detectorRequired
    ∃ (hR : ∀ j, 0 < R j) (σ : ℝ) (hσ : 0 < σ)
      (S : LayerSamplerScale («G» := (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) («I» := (PreparedSamplerContinuous (prep.pad (max m cutoff)))) («n» := (preparedSamplerTransverse (prep.pad (max m cutoff)))) («J» := (fun j : Fin (max m cutoff) => RankPreparationLayer.Coord ((prep.pad (max m cutoff)) j))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b R (fun _ => σ)),
      0 ≤ pRadius ∧ (∀ j, R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      σ ≤ 1 ∧ σ ≤ Real.exp (-Qσ) ∧ σ⁻¹ ≤ Real.exp Pscale ∧
      Lmin ≤ S.value ∧ (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog Pseed Qw) ∧
      (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
        8 * (probabilityProfileLipschitz : ℝ) * W ≤
          (layerSamplerGapWidth («G» := (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) R ⟨j, i⟩ / 2) *
            ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
      (∀ s : K, PreparedUniformDegreeGeometryAt («G» := (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))) (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b S (degree s) (Cdetect s) nX
        Bstruct Pscale D (target s) (Pk s) (Prho s) Qstride (pDetect s) pRadius (aDetect s) (detectionGain s)) ∧
      (∀ k, PreparedUniformDegreeDirectScalarBounds (max m cutoff) (degree k) nX
        (Fintype.card (LayerSamplerVariables
          (EnlargedPreparedCommonKernel (max m cutoff) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
          (PreparedSamplerContinuous (prep.pad (max m cutoff))) (preparedSamplerTransverse (prep.pad (max m cutoff)))
          (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))))
        (Cdetect k) Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride (Pmaster k) Plate
        (detectionGain k) (Pphysical k) coarseTarget pRadius (sourceU k) (modelLog k) (sliceLog k)) ∧
      (∀ k, PreparedScheduledDirectSourceAvailability
          (B := EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection (max m cutoff)
            (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)) (degree k) (preparedFiniteNestedForwardAllDegreeDegree_le (Nat.le_max_right m cutoff) k))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) ∧
      (∀ k, PreparedScheduledDegreeModelAvailability
          (B := EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection (max m cutoff)
            (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M)) (degree k)
              (preparedFiniteNestedForwardAllDegreeDegree_le (Nat.le_max_right m cutoff) k))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o) (μ := μ)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) ∧
      PreparedUniformDegreeProductiveSourceConclusion
        (m := (max m cutoff)) (nX := nX) (M := M) (prep := (prep.pad (max m cutoff))) (U := U) (b := b) (S := S)
        (hR := hR) (hσ := fun _ => hσ) (stride := stride) (N := N)
        (Pdetect := Pdetect) (pModel := modelLog kModel) (pSlice := sliceLog kModel)
        (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
        (hb := hb) (o := o) (bW := bW) (μ := μ)
        Bstruct Qstride (Pmaster kModel) Plate (detectionGain kModel) (Pphysical kModel) coarseTarget
        pRadius Pscale Pseed Qw gainLog gain Vlog Qgood ∧
      ∃ (hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i)
        (Acandidate : AllocatedExternalCandidateSamplerFamily (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b S hb o hR (fun _ => hσ)
          N (fun j => (prep.pad (max m cutoff) j).poly) hmem τ (Real.exp (-Plate)) stride cells)
        (hξone : Real.exp (-Plate) ≤ 1),
      PreparedCenteredProductiveGoodCenterEnhancedConclusion (m := (max m cutoff)) (nX := nX) (M := M)
        (prep.pad (max m cutoff)) U b S bW hb o hR (fun _ => hσ) μ (fun j => (prep.pad (max m cutoff) j).poly) hmem stride
        (allocatedExternalCandidateWidths (EnlargedPreparedCommonSamplerBlock (prep.pad (max m cutoff)) (modularInitialBlockCount (max m cutoff) (nX + (max m cutoff) * M))) U b S N τ (Real.exp (-Plate))) (Acandidate 0).bases
        gainLog gain Qgood (preparedSpatialKernelBlocks (max m cutoff) M nX) Acandidate.law N (relativePatchSourceTest N f a oldPatch)
        (fun center =>
          let _ : DecidableEq (Fin nX) := Classical.decEq _
          ((∀ k : K, (Acandidate center).NativeDetection (degree k) (sliceLog k)
            (Pdetect.eval₂ (Nat.castRingHom ℝ) (pDetect k))
            (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants (max m cutoff) (degree k))
              (degree k + 1) (Pmaster k) Plate).nativeBudget (α k)) ∧
          letI : Nonempty (Acandidate center).Site := (Acandidate center).site_nonempty
          (FiniteProbabilityWeights.uniformFinset (integerBox N) (Acandidate center).integerBox_nonempty).excessMass
            ((Acandidate center).law.siteLaw ((Acandidate center).physicalBox hξone hmargin))
            (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous (prep.pad (max m cutoff))) j)) ((preparedSamplerTransverse (prep.pad (max m cutoff))) j) (R j) (Vtail j)) ≤
              6 * positiveProjectionAccuracy Econditional) ∧
          ∀ (outerFront outerInner : Fin (outerDepth + 1)) (d : ℕ),
            ∀ (hd : d ≤ cutoff), d ≤ innerDepth → ∀ (pInput : ℝ),
            pInput ∈ Set.Icc 0 (candidateNestedForwardSeed A stageCountConstant innerDepth outerFront.val Bstruct) →
            pInput ≤ candidateNestedForwardSeed A stageCountConstant innerDepth outerInner.val Bstruct →
            ∃ profile : (Acandidate center).DegreeSourceProfile d pInput e,
              profile.inner.x = candidateNestedForwardSeed A stageCountConstant innerDepth outerInner.val Bstruct ∧
              profile.inner.gainLog = candidateNestedForwardSeed A stageCountConstant innerDepth outerInner.val Bstruct ∧
              profile.front.u = preparedFiniteForwardModelPrecision A stageCountConstant 0
                (candidateNestedForwardSeed A stageCountConstant innerDepth outerFront.val Bstruct) gainLog stageLog ∧
              profile.front.pModel = preparedFiniteForwardWork A stageCountConstant 0
                (candidateNestedForwardSeed A stageCountConstant innerDepth outerFront.val Bstruct) ∧
              profile.front.nativeBudget = native (outerFront, 0, ⟨d, Nat.lt_succ_of_le hd⟩, false) ∧
              profile.inner.Cprimitive = Cprimitive ∧
              profile.inner.scheduleExponent = A ∧
              profile.inner.Csource = preparedFiniteNestedSourceNativeExponent (max m cutoff) cutoff Cdirect)
        (fun center centerLift productive =>
          AllocatedNormalizedCandidateConclusion (E := Q) (A := Acandidate center)
            s (fun k => H ≤ (Acandidate center).sides k) centerLift productive
            (childCost pchild) initialCost (d₀ + s * Erest) f
            ((1 - discount) ^ (stage + 1) * Λ))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

noncomputable def preparedCanonicalRelativeLiteralRequired
    {nX D m : ℕ} (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    (s outerDepth innerDepth e Cprimitive Cdirect extra : ℕ)
    (Bstruct p knob : ℝ) : ℝ :=
  let q := max m s
  let M := preparationCoordinateCap q D (s * D)
  let Jalloc := modularInitialBlockCount q (nX + q * M)
  let G := EnlargedPreparedCommonKernel q Jalloc
  let count := Fintype.card (LayerSamplerVariables G
    (PreparedSamplerContinuous (prep.pad q)) (preparedSamplerTransverse (prep.pad q))
    (EnlargedPreparedCommonSamplerBlock (prep.pad q) Jalloc))
  preparedFiniteNestedSourceLiteralRequired q s
    (preparedFiniteNestedSourceExponent q s e Cprimitive Cdirect extra) Cdirect outerDepth innerDepth
    AllocatedExternalCandidateSampler.degreeSourceCountConstants G M count nX Bstruct
    (enlargedPreparedCommonSamplerDimension q M Jalloc) 0 p 0 knob knob knob knob knob

end Erdos3.VectorPolynomial

end

end OAI
end


