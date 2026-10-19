-- Prove2me | Definitions.Def_OAIE3v2B177
-- name    : OAIE3v2B177
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:37:34.916439+00:00
-- url     : https://prove2.me/theorems/2c110192-af0c-403f-8508-bc448f119ac7
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 179 of 311
-- statement:
--   Definitions bundle 179 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B151`, `OAIE3v2B152`, `OAIE3v2B159`, `OAIE3v2B160` of this split.
--
--   Modules: `Dynamics/CandidateFrontActualPowerBudget.lean`, `Dynamics/InitialBudgetJointReplacement.lean`, `Dynamics/PreparedFiniteForwardStageBudget.lean`, `Estimates/AllocatedEnormousProfiles.lean`, `Estimates/AllocatedFrozenBlockPMF.lean`, `Estimates/AllocatedTrimmedVectorSite.lean`, `Estimates/PreparedFiniteForwardFixedCenterThreshold.lean`, `Estimates/SmallWeightedPhysicalReplacement.lean`, `Fourier/NormalizedTwistSingleSiteFourierHaar.lean`, `Lattices/AffineSampleAlphabet.lean`, `Lattices/ConcreteAffineMeshBoundary.lean`, `Lattices/OriginalKernelResidueRetained.lean`, `Lattices/RetainedPhysicalCRT.lean`, `Polynomial/CandidateFrontFactorPolynomialBudget.lean`, `Probability/AdaptiveCouplingComparison.lean`, `Probability/RestrictedWeightedLawModeledTransfer.lean`, `Sampling/AllocatedProbabilityGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B151
import Definitions.Def_OAIE3v2B152
import Definitions.Def_OAIE3v2B159
import Definitions.Def_OAIE3v2B160

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
variable {G : Type*} [Fintype G] [∀ j, Fintype (I j)]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

theorem allocatedPrincipalSides_long (d : LayerSamplerAxis I n)
    (hd : ¬allocatedGridAxis U basis S.value d) (b : B d) (v : Fin (layerSamplerDegree I n d)) :
    allocatedPrincipalSides B U basis S ⟨d, b, v⟩ = S.value := by
  rcases d with ⟨j, d⟩
  cases d with
  | inl i => rfl
  | inr i =>
    change ¬basisAxisScale (basis j) i ≤ S.value^(layerTailDegree m+1) at hd
    have hactive : S.value^(j.val+1) < basisAxisScale (basis j) i :=
      (Nat.pow_le_pow_right S.positive
        ((layerDegree_le_tailDegree j).trans (Nat.le_succ _))).trans_lt (Nat.lt_of_not_ge hd)
    simp only [allocatedPrincipalSides, layerSamplerSides, heterogeneousSamplerSides,
      layerSamplerDenominators, Sum.elim_inr, layerSamplerDegree,
      integerAxisSideLength, hactive, ↓reduceIte]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFrozenBlockPMF
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value

noncomputable def allocatedFrozenBlockPMF :
    ∀ a : {a // grid a}, PMF (CoefficientJetAxisRow O a.val)
  | ⟨⟨_, .inl _⟩, ha⟩ => False.elim ha
  | ⟨⟨j, .inr i⟩, ha⟩ =>
      (independentProductPMF (allocatedLayerIntegerPMFs B U b hR hσ S j i)).map
        (fun c t => booleanCoefficient (fun _ => c (constantCoefficientSlot _ _)) (rows j t) +
          ∑ q : B ⟨j, Sum.inr i⟩,
            c (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ q) *
              integerBooleanBlockJet
                (fun v r => (u ⟨⟨⟨j, Sum.inr i⟩, ha⟩, q, v⟩ r : ℤ)) (rows j t))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedTrimmedVectorSite
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedPhysicalRootBudget_zero_ratio {p : ℝ} (hp : 0 ≤ p)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p) :
    (1 + allocatedPhysicalRootBudget B U b S (fun _ => 0)) / (S.value : ℝ) ≤
      allocatedPrimitiveRootRatio p := by
  have hS : (0 : ℝ) < S.value := Nat.cast_pos.mpr S.positive
  have hS1 : (1 : ℝ) ≤ S.value := by exact_mod_cast S.positive
  rw [allocatedPhysicalRootBudget_zero, (allocatedPrimitiveRootRatio_bounds hp).1,
    add_div, mul_div_cancel_right₀ _ hS.ne']
  have hinv : 1 / (S.value : ℝ) ≤ 1 := (div_le_one hS).mpr hS1
  linarith

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedProbabilityGrid
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value

noncomputable def allocatedNormalizedGridFactor :
    ∀ a : {a // grid a}, (O a.val.1 → ℝ) → ℝ
  | ⟨⟨_, .inl _⟩, ha⟩ => False.elim ha
  | ⟨⟨j, .inr i⟩, ha⟩ => normalizedIntegerRowInterpolation (basisAxisScale (b j) i)
      (allocatedFrozenBlockPMF B U b hR hσ S u rows ⟨⟨j, .inr i⟩, ha⟩)

noncomputable def allocatedNormalizedGridInterpolation
    (z : ∀ a : {a // grid a}, O a.val.1 → ℝ) : ℝ :=
  ∏ a, allocatedNormalizedGridFactor B U b hR hσ S u rows a (z a)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RestrictedWeightedLawModeledTransfer
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteProbabilityTest {Ω U : Type*} [Fintype U]
    (law : FiniteProbabilityWeights U) (ψ : U → Ω) : (Ω → ℂ) →ₗ[ℂ] ℂ where
  toFun v := law.complexMean (fun u => v (ψ u))
  map_add' v z := by
    simp only [FiniteProbabilityWeights.complexMean, Pi.add_apply, mul_add,
      Finset.sum_add_distrib]
  map_smul' c v := by
    change (∑ u, (law.weight u : ℂ) * (c * v (ψ u))) =
      c * ∑ u, (law.weight u : ℂ) * v (ψ u)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring

open _root_.MvPolynomial
open scoped NNReal

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteForwardStageBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedFiniteForwardStage_budget (depth A : ℕ)
    (stageCountConstant : ℕ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ x gainLog stageLog : ℝ, 0 ≤ x →
      gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x → ∀ n : ℕ, n ≤ depth →
      preparedFiniteForwardParameter A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardWork A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardCap A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardCount A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardBranch A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardCumulative A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardPrefixLog A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardModelPrecision A stageCountConstant n x gainLog stageLog ∈
        Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog ∈
        Set.Icc 0 ((x + C) ^ C) := by
  obtain ⟨B, hB, hschedule⟩ :=
    exists_preparedFiniteForwardSchedule_budget depth A stageCountConstant
  let Q : Polynomial ℕ := 8 * (Polynomial.X + Polynomial.C B) ^ B + 32
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro x gainLog stageLog hx hg hstage n hn
  have hbound : 8 * (x + B) ^ B + 32 ≤ (x + C) ^ C := by
    simpa [Q, Polynomial.eval₂_pow] using hbudget x hx
  have hT : 0 ≤ (x + B) ^ B := pow_nonneg (add_nonneg hx (Nat.cast_nonneg B)) _
  have hraise : (x + B) ^ B ≤ (x + C) ^ C := by linarith only [hbound, hT]
  obtain ⟨hp, hw, hcap, hcount, hbranch⟩ := hschedule x hx n hn
  have hprefix := preparedFiniteForward_prefix_bounds A stageCountConstant n hx
  have hprecision :=
    preparedFiniteForward_model_precision_bounds A stageCountConstant n hx hg hstage
  have hsource :
      preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog ≤
        (x + C) ^ C := by
    linarith only [hprecision.2.2.2.2, hp.2, hw.1, hw.2, hbound]
  have hmodel :
      preparedFiniteForwardModelPrecision A stageCountConstant n x gainLog stageLog ≤
        preparedFiniteForwardSourcePrecision A stageCountConstant n x gainLog stageLog := by
    linarith only [hprecision.2.2.1, hw.1]
  exact ⟨⟨hp.1, hp.2.trans hraise⟩, ⟨hw.1, hw.2.trans hraise⟩,
    ⟨hcap.1, hcap.2.trans hraise⟩, ⟨hcount.1, hcount.2.trans hraise⟩,
    ⟨hbranch.1, hbranch.2.trans hraise⟩,
    ⟨hprefix.1.1, hprefix.1.2.trans (hp.2.trans hraise)⟩,
    ⟨hprefix.2.1, hprefix.2.2.trans (hp.2.trans hraise)⟩,
    ⟨hprecision.1, hmodel.trans hsource⟩, ⟨hprecision.2.1, hsource⟩⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteForwardFixedCenterThreshold
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedFiniteForwardPairedSourcePrecision_budget
    (depth A Cdirect : ℕ) (stageCountConstant : ℕ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {x gainLog stageLog : ℝ}, 0 ≤ x →
      gainLog ∈ Set.Icc 0 x → stageLog ∈ Set.Icc 0 x →
      ∀ n ≤ depth, ∀ isDirect : Bool,
      preparedFiniteForwardPairedSourcePrecision A Cdirect stageCountConstant n isDirect x gainLog stageLog ∈
        Set.Icc 0 ((x + C) ^ C) := by
  obtain ⟨B, _, hb⟩ := exists_preparedFiniteForwardStage_budget depth A stageCountConstant
  let X : Polynomial ℕ := Polynomial.X
  let T : Polynomial ℕ := (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget
    (T + (2 * T + Polynomial.C Cdirect) ^ Cdirect)
  refine ⟨C, hC, ?_⟩
  intro x gainLog stageLog hx hg hs n hn isDirect
  have hstage := hb x gainLog stageLog hx hg hs n hn
  have hwork := hstage.2.1
  have hsource := hstage.2.2.2.2.2.2.2.2
  have hbound : (x + B) ^ B + (2 * (x + B) ^ B + Cdirect) ^ Cdirect ≤ (x + C) ^ C := by
    simpa [T, X, Polynomial.eval₂_pow] using hpoly x hx
  refine ⟨preparedFiniteForwardPairedSourcePrecision_nonneg A Cdirect stageCountConstant n isDirect hx hg hs, ?_⟩
  cases isDirect with
  | false =>
    rw [preparedFiniteForwardPairedSourcePrecision_model]
    apply hsource.2.trans
    apply le_trans _ hbound
    have hnonneg : 0 ≤ (2 * (x + B) ^ B + Cdirect) ^ Cdirect := by positivity
    linarith only [hnonneg]
  | true =>
    rw [preparedFiniteForwardPairedSourcePrecision_direct]
    apply le_trans _ hbound
    apply add_le_add hsource.2
    apply pow_le_pow_left₀ (add_nonneg (add_nonneg hsource.1 hwork.1) (Nat.cast_nonneg Cdirect))
    linarith only [hsource.2, hwork.2]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.OriginalKernelResidueRetained
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem integerScalarCubeWeights_empty_residue_mass_pos
    (L q : ℕ) (hL : 0 < L) (hq : 0 < q) (hqL : q ≤ L) (r : ZMod q) :
    0 < (integerScalarCubeWeights Empty L hL).mass
      (Finset.univ.filter (fun x => ((x none : ℤ) : ZMod q) = r)) := by
  rw [← scalarCubeResidueSet_empty_eq_filter]
  exact scalarCubeResidue_mass_pos Empty L q hL (fun _ => q) (fun _ => r)
    (fun _ => hq) (fun _ => le_rfl) (by simpa using hqL)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.CandidateFrontFactorPolynomialBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators
open RationalFilteredNilmanifold

theorem exists_candidateFrontFactor_power_budget
    (s Cdesc Cgeometry Cpair Cbasis K T Cmark : ℕ) :
    ∃ Ctotal : ℕ, 2 ≤ Ctotal ∧ ∀ p : ℝ, 0 ≤ p →
    let vertical := verticalDecompositionBudget (3 * p + 1)
    let factor := 2 * p + vertical + 2
    let desc := (p + 2) ^ Cdesc
    let geom := p + desc + 2
    let pairGeo := (geom + 2) ^ 2
    let jointGeo := (geom + 3) ^ 2
    let adapted := (jointGeo + 2) ^ Cgeometry
    let bnd := adapted + (pairGeo + 3) ^ 5 + pairGeo + jointGeo + geom + factor + 2
    let localCost := allocatedFrozenTaggedPairBudget s Cpair Cbasis pairGeo factor
    let jointCost := allocatedFrozenTaggedFamilyInputBudget bnd localCost
    let fullCost := jointCost + (jointCost + K) ^ K
    let common := (fullCost + 2) ^ T + (((fullCost + 2) ^ 2 + 2) ^ 63 + 1) + fullCost + 1
    let projected := common + adapted + 1
    let markHeight := quotientInducedMarkHeightBudget geom
    let markInput := jointGeo + markHeight + adapted + 2
    let markBudget := (markInput + 2) ^ Cmark
    let commonInput := p + geom + pairGeo + jointGeo + jointGeo ^ 2 + adapted + bnd + factor +
      common + projected + (projected + 2) ^ 4 + markHeight + markInput + markBudget + 2
    let fast := allocatedCandidateCommonFastBudget s commonInput
    let longThreshold := (factor + 2 + Cpair) ^ Cpair + 7 * factor + 22 +
      (fullCost + 2) ^ T + p + 1
    let massLog := p + vertical * p + ((common + 2) ^ 5 + common)
    commonInput ∈ Set.Icc 0 ((p + 2) ^ Ctotal) ∧
      fast ∈ Set.Icc 0 ((p + 2) ^ Ctotal) ∧
      longThreshold ∈ Set.Icc 0 ((p + 2) ^ Ctotal) ∧
      massLog ∈ Set.Icc 0 ((p + 2) ^ Ctotal) := by
  let X : Polynomial ℕ := Polynomial.X
  let ca := (3 * X + 1 + 3) ^ 9 + 2 * (3 * X + 1) + 2
  let vertical := 2 * ca * (2 * ca + 2) ^ 4 +
    ((2 * ca + 2) ^ 4 + ca + (3 * X + 1 + 3) ^ 5 + 2) ^ 4
  let factor := 2 * X + vertical + 2
  let desc := (X + 2) ^ Cdesc
  let geom := X + desc + 2
  let pairGeo := (geom + 2) ^ 2
  let jointGeo := (geom + 3) ^ 2
  let adapted := (jointGeo + 2) ^ Cgeometry
  let bnd := adapted + (pairGeo + 3) ^ 5 + pairGeo + jointGeo + geom + factor + 2
  let transfer := pairGeo + factor + ((factor + 2 + Polynomial.C Cpair) ^ Cpair +
    Polynomial.C s * (9 * factor + 23))
  let localCost := (((pairGeo + 3) ^ 5 + transfer + 1 + 2) ^ 4 + transfer + 1 +
    Polynomial.C Cbasis) ^ Cbasis
  let jointCost := bnd + localCost + (bnd + 3) ^ 4 + 1
  let fullCost := jointCost + (jointCost + Polynomial.C K) ^ K
  let common := (fullCost + 2) ^ T + (((fullCost + 2) ^ 2 + 2) ^ 63 + 1) + fullCost + 1
  let projected := common + adapted + 1
  let markHeight := (geom + (geom + 3) ^ 7 + 3) ^ 4
  let markInput := jointGeo + markHeight + adapted + 2
  let markBudget := (markInput + 2) ^ Cmark
  let commonInput := X + geom + pairGeo + jointGeo + jointGeo ^ 2 + adapted + bnd + factor +
    common + projected + (projected + 2) ^ 4 + markHeight + markInput + markBudget + 2
  let sec := (commonInput + 2) ^ 4 + 1
  let fast := (sec + 2) ^ 47 + 1 +
    (2 * (commonInput + Polynomial.C (s + 3)) ^ (s + 3) +
      ((commonInput + Polynomial.C (s + 3)) ^ (s + 3)) ^ 2 + commonInput)
  let longThreshold := (factor + 2 + Polynomial.C Cpair) ^ Cpair + 7 * factor + 22 +
    (fullCost + 2) ^ T + X + 1
  let massLog := X + vertical * X + ((common + 2) ^ 5 + common)
  obtain ⟨Ctotal, hCtotal, htotal⟩ :=
    exists_natPolynomial_fixed_power_budget (fast + longThreshold + massLog)
  refine ⟨Ctotal, hCtotal, ?_⟩
  intro p hp v f d g pg jg a b l j full c proj mh mi mb ci fa lt ml
  have hv : 0 ≤ v := verticalDecompositionBudget_nonneg (by positivity)
  have hf : 0 ≤ f := by dsimp only [f]; positivity
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have hg : 0 ≤ g := by dsimp only [g]; positivity
  have hpg : 0 ≤ pg := by dsimp only [pg]; positivity
  have hjg : 0 ≤ jg := by dsimp only [jg]; positivity
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hl : 0 ≤ l := by
    dsimp only [l, allocatedFrozenTaggedPairBudget, fixedAdaptedSymbolTransferInput]
    positivity
  have hj : 0 ≤ j := by dsimp only [j, allocatedFrozenTaggedFamilyInputBudget]; positivity
  have hfull : 0 ≤ full := by dsimp only [full]; positivity
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hproj : 0 ≤ proj := by dsimp only [proj]; positivity
  have hmh : 0 ≤ mh := by dsimp only [mh, quotientInducedMarkHeightBudget]; positivity
  have hmi : 0 ≤ mi := by dsimp only [mi]; positivity
  have hmb : 0 ≤ mb := by dsimp only [mb]; positivity
  have hci : 0 ≤ ci := by dsimp only [ci]; positivity
  have hciFast : ci ≤ fa := (allocatedCandidateCommonFastBudget_bounds s hci).2.2
  have hfa : 0 ≤ fa := hci.trans hciFast
  have hlt : 0 ≤ lt := by dsimp only [lt]; positivity
  have hml : 0 ≤ ml := by dsimp only [ml]; positivity
  have eval_ca : ca.eval₂ (Nat.castRingHom ℝ) p = centralActionBudget (3 * p + 1) := by
    simp only [ca, X, centralActionBudget, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_ofNat, Polynomial.eval₂_one]
  have eval_vertical : vertical.eval₂ (Nat.castRingHom ℝ) p = v := by
    simp only [vertical, v, verticalDecompositionBudget, X, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_ofNat, Polynomial.eval₂_one, eval_ca]
  have eval_factor : factor.eval₂ (Nat.castRingHom ℝ) p = f := by
    simp only [factor, f, X, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X,
      Polynomial.eval₂_ofNat, eval_vertical]
  have eval_desc : desc.eval₂ (Nat.castRingHom ℝ) p = d := by
    simp only [desc, d, X, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_ofNat]
  have eval_geom : geom.eval₂ (Nat.castRingHom ℝ) p = g := by
    simp only [geom, g, X, Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_ofNat, eval_desc]
  have eval_pairGeo : pairGeo.eval₂ (Nat.castRingHom ℝ) p = pg := by
    simp only [pairGeo, pg, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_ofNat, eval_geom]
  have eval_jointGeo : jointGeo.eval₂ (Nat.castRingHom ℝ) p = jg := by
    simp only [jointGeo, jg, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_ofNat, eval_geom]
  have eval_adapted : adapted.eval₂ (Nat.castRingHom ℝ) p = a := by
    simp only [adapted, a, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_ofNat, eval_jointGeo]
  have eval_bnd : bnd.eval₂ (Nat.castRingHom ℝ) p = b := by
    simp only [bnd, b, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_ofNat, eval_factor,
      eval_geom, eval_pairGeo, eval_jointGeo, eval_adapted]
  have eval_transfer : transfer.eval₂ (Nat.castRingHom ℝ) p = pg + f + ((f + 2 + Cpair) ^ Cpair + (s : ℝ) * (9 * f + 23)) := by
    simp only [transfer, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_C, Polynomial.eval₂_ofNat, Nat.coe_castRingHom, eval_factor, eval_pairGeo]
  have eval_localCost : localCost.eval₂ (Nat.castRingHom ℝ) p = l := by
    simp only [localCost, l, allocatedFrozenTaggedPairBudget, fixedAdaptedSymbolTransferInput,
      Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_ofNat,
      Polynomial.eval₂_one, Nat.coe_castRingHom, eval_pairGeo, eval_transfer]
  have eval_jointCost : jointCost.eval₂ (Nat.castRingHom ℝ) p = j := by
    simp only [jointCost, j, allocatedFrozenTaggedFamilyInputBudget, Polynomial.eval₂_add,
      Polynomial.eval₂_pow, Polynomial.eval₂_ofNat, Polynomial.eval₂_one, eval_bnd, eval_localCost]
  have eval_fullCost : fullCost.eval₂ (Nat.castRingHom ℝ) p = full := by
    simp only [fullCost, full, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_C,
      Nat.coe_castRingHom, eval_jointCost]
  have eval_common : common.eval₂ (Nat.castRingHom ℝ) p = c := by
    simp only [common, c, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_ofNat,
      Polynomial.eval₂_one, eval_fullCost]
  have eval_projected : projected.eval₂ (Nat.castRingHom ℝ) p = proj := by
    simp only [projected, proj, Polynomial.eval₂_add, Polynomial.eval₂_one, eval_adapted, eval_common]
  have eval_markHeight : markHeight.eval₂ (Nat.castRingHom ℝ) p = mh := by
    simp only [markHeight, mh, quotientInducedMarkHeightBudget, Polynomial.eval₂_add,
      Polynomial.eval₂_pow, Polynomial.eval₂_ofNat, eval_geom]
  have eval_markInput : markInput.eval₂ (Nat.castRingHom ℝ) p = mi := by
    simp only [markInput, mi, Polynomial.eval₂_add, Polynomial.eval₂_ofNat, eval_jointGeo, eval_adapted,
      eval_markHeight]
  have eval_markBudget : markBudget.eval₂ (Nat.castRingHom ℝ) p = mb := by
    simp only [markBudget, mb, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_ofNat,
      eval_markInput]
  have eval_commonInput : commonInput.eval₂ (Nat.castRingHom ℝ) p = ci := by
    simp only [commonInput, ci, X, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_ofNat, eval_factor, eval_geom, eval_pairGeo, eval_jointGeo, eval_adapted,
      eval_bnd, eval_common, eval_projected, eval_markHeight, eval_markInput, eval_markBudget]
  have eval_sec : sec.eval₂ (Nat.castRingHom ℝ) p = allocatedCandidateCommonFastSectionInput ci := by
    simp only [sec, allocatedCandidateCommonFastSectionInput, Polynomial.eval₂_add, Polynomial.eval₂_pow,
      Polynomial.eval₂_ofNat, Polynomial.eval₂_one, eval_commonInput]
  have eval_fast : fast.eval₂ (Nat.castRingHom ℝ) p = fa := by
    simp only [fast, fa, allocatedCandidateCommonFastBudget, allocatedCandidateCommonFastGeometryLog,
      NilpotentLieFiltration.pointwiseFastSectionInput, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_ofNat, Polynomial.eval₂_one,
      Nat.coe_castRingHom, Nat.cast_add, Nat.cast_ofNat, eval_commonInput, eval_sec]
  have eval_longThreshold : longThreshold.eval₂ (Nat.castRingHom ℝ) p = lt := by
    simp only [longThreshold, lt, X, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_ofNat, Polynomial.eval₂_one,
      Nat.coe_castRingHom, eval_factor, eval_fullCost]
  have eval_massLog : massLog.eval₂ (Nat.castRingHom ℝ) p = ml := by
    simp only [massLog, ml, X, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_ofNat, eval_vertical, eval_common]
  have hsum : fa + lt + ml ≤ (p + 2) ^ Ctotal := by
    simpa only [Polynomial.eval₂_add, eval_fast, eval_longThreshold, eval_massLog]
      using htotal p hp
  exact bounds_of_sum hci hfa hlt hml hciFast hsum

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CandidateFrontActualPowerBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open RationalFilteredNilmanifold

theorem exists_candidateFrontActual_power_budget
    (s Cdesc Cgeometry Cpair Cbasis K T Cmark : ℕ) :
    ∃ Ctotal : ℕ, 2 ≤ Ctotal ∧ ∀ m : ℕ, ∀ p : ℝ, 0 ≤ p → (m : ℝ) ≤ p →
    ∀ cost nVariables nPivot mass0 : ℝ,
    cost ≤ p → nVariables ∈ Set.Icc 0 p → nPivot ∈ Set.Icc 0 p → mass0 ≤ p →
    let vertical := verticalDecompositionBudget (3 * p + 1)
    let factor := 2 * p + vertical + 2
    let geometry := p + (p + 2) ^ Cdesc + 2
    let pairGeo := (geometry + 2) ^ 2
    let jointGeo := (geometry + 3) ^ 2
    let adapted := (jointGeo + 2) ^ Cgeometry
    let bnd := adapted + (pairGeo + 3) ^ 5 + pairGeo + jointGeo + geometry + factor + 2
    let localCost := allocatedFrozenTaggedPairBudget s Cpair Cbasis pairGeo factor
    let jointCost := allocatedFrozenTaggedFamilyInputBudget bnd localCost
    let fullCost := jointCost + (jointCost + K) ^ K
    let common := (fullCost + 2) ^ T + (((fullCost + 2) ^ 2 + 2) ^ 63 + 1) + fullCost + 1
    let projected := max common 0 + adapted + 1
    let markInput := nativeOptionFixedSourceQuotientMarkInput geometry
    let markBudget := (markInput + 2) ^ Cmark
    let terminal := (projected + 2) ^ 4 + markInput + markBudget + jointGeo + nVariables + 2
    let initialShort := max ((factor + 2 + Cpair) ^ Cpair + 7 * factor + 22)
      ((fullCost + 2) ^ T)
    let nativeInput := (projected + 2) ^ 3 + common
    let B := (p + 2) ^ Ctotal
    terminal ∈ Set.Icc 0 B ∧
      allocatedCandidateCommonFastBudget s terminal ≤ B ∧
      max cost initialShort ≤ B ∧
      nativeInput ≤ B ∧
      markInput ∈ Set.Icc 0 B ∧
      0 ≤ common ∧
      vertical * nPivot + ((common + 2) ^ 5 + common) + mass0 ≤ B ∧
      (s : ℝ) * (markInput * m) ≤ B ∧
      p ≤ B ∧ geometry ≤ B ∧ adapted ≤ B ∧ markBudget ≤ B ∧
      jointGeo ≤ B ∧ (projected + 2) ^ 4 ≤ B ∧ cost ≤ B := by
  obtain ⟨Cbase, hCbase, hpower⟩ := exists_candidateFrontFactor_power_budget
    s Cdesc Cgeometry Cpair Cbasis K T Cmark
  refine ⟨Cbase + s + 1, hCbase.trans (by omega), ?_⟩
  intro m p hp hm cost nVariables nPivot mass0 hcost hvariables hpivot hmass
    vertical factor geometry pairGeo jointGeo adapted bnd localCost jointCost
    fullCost common projected markInput markBudget terminal initialShort nativeInput B
  let envelopeProjected := common + adapted + 1
  let envelopeMarkHeight := quotientInducedMarkHeightBudget geometry
  let envelopeMarkInput := jointGeo + envelopeMarkHeight + adapted + 2
  let envelopeMarkBudget := (envelopeMarkInput + 2) ^ Cmark
  let commonInput := p + geometry + pairGeo + jointGeo + jointGeo ^ 2 + adapted + bnd + factor +
    common + envelopeProjected + (envelopeProjected + 2) ^ 4 + envelopeMarkHeight +
    envelopeMarkInput + envelopeMarkBudget + 2
  let fast := allocatedCandidateCommonFastBudget s commonInput
  let longThreshold := (factor + 2 + Cpair) ^ Cpair + 7 * factor + 22 +
    (fullCost + 2) ^ T + p + 1
  let massLog := p + vertical * p + ((common + 2) ^ 5 + common)
  have hpoly := hpower p hp
  change commonInput ∈ Set.Icc 0 ((p + 2) ^ Cbase) ∧
    fast ∈ Set.Icc 0 ((p + 2) ^ Cbase) ∧
    longThreshold ∈ Set.Icc 0 ((p + 2) ^ Cbase) ∧
    massLog ∈ Set.Icc 0 ((p + 2) ^ Cbase) at hpoly
  obtain ⟨hci, hfast, hlong, hmassLog⟩ := hpoly
  have hvertical : 0 ≤ vertical :=
    verticalDecompositionBudget_nonneg (by linarith only [hp])
  have hfactor : 0 ≤ factor := by dsimp only [factor]; positivity
  have hgeometry : 0 ≤ geometry := by dsimp only [geometry]; positivity
  have hactual := candidateFrontFactor_actual_bounds s Cgeometry Cpair Cbasis K T Cmark
    (factor := factor) (geom := geometry) hp hfactor hgeometry le_rfl le_rfl
    hcost hvariables.1 hvariables.2
  change terminal ∈ Set.Icc 0 commonInput ∧
    allocatedCandidateCommonFastBudget s terminal ≤ fast ∧
    max cost initialShort ≤ longThreshold ∧
    nativeInput ≤ commonInput ∧
    markInput ∈ Set.Icc 0 commonInput ∧
    common ∈ Set.Icc 0 common ∧
    p ≤ commonInput ∧ geometry ≤ commonInput ∧ adapted ≤ commonInput ∧
    markBudget ≤ commonInput ∧ jointGeo ≤ commonInput ∧
    (projected + 2) ^ 4 ≤ commonInput ∧ cost ≤ commonInput at hactual
  obtain ⟨hterminal, hfastActual, hshort, hnative, hmark, hcommon,
    hpci, hgeoci, hadapted, hmarkBudget, hjoint, hprojected, hcostci⟩ := hactual
  have hB : (p + 2) ^ Cbase ≤ B :=
    pow_le_pow_right₀ (by linarith only [hp]) (by omega)
  have hciB : commonInput ≤ B := hci.2.trans hB
  have hmassActual : vertical * nPivot + ((common + 2) ^ 5 + common) + mass0 ≤ massLog :=
    candidateFrontFactor_massLog_le hvertical le_rfl hpivot.1 hpivot.2
      hcommon.1 le_rfl hmass
  have hblock : (s : ℝ) * (markInput * m) ≤ B :=
    candidateFrontFactor_uniform_block_le_power s Cbase hp hm hmark.2 hci.2
  exact ⟨⟨hterminal.1, hterminal.2.trans hciB⟩,
    hfastActual.trans (hfast.2.trans hB), hshort.trans (hlong.2.trans hB),
    hnative.trans hciB, ⟨hmark.1, hmark.2.trans hciB⟩, hcommon.1,
    hmassActual.trans (hmassLog.2.trans hB), hblock,
    hpci.trans hciB, hgeoci.trans hciB, hadapted.trans hciB, hmarkBudget.trans hciB,
    hjoint.trans hciB, hprojected.trans hciB, hcostci.trans hciB⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineSampleAlphabet
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {q : ℕ} [NeZero q] {J G : Type*} [Fintype J]
  [AddCommGroup G] [Module (ZMod q) G] [Fintype G]

noncomputable def residueAffineSource : FiniteProbabilityWeights ((J → G) × G) :=
  (FiniteProbabilityWeights.uniform (J → G)).prod (FiniteProbabilityWeights.uniform G)

noncomputable def residueAffineKernel (z : (J → G) × G) : FiniteProbabilityWeights G :=
  (FiniteProbabilityWeights.uniform (J → ZMod q)).fiberLaw
    (fun t => z.2 + residueColumnMap (q := q) z.1 t)

theorem residueAffineKernel_mean (z : (J → G) × G) (f : G → ℝ) :
    (residueAffineKernel (q := q) z).mean f = residueColumnRealAverage (q := q) z.1 f z.2 := by
  rw [residueAffineKernel, FiniteProbabilityWeights.fiberLaw_mean, FiniteProbabilityWeights.uniform_mean]
  rfl

theorem residueAffineKernel_preserves_mean (f : G → ℝ) :
    (residueAffineSource (J := J) (G := G)).mean (fun z => (residueAffineKernel (q := q) z).mean f) =
      (FiniteProbabilityWeights.uniform G).mean f := by
  simp only [residueAffineSource, FiniteProbabilityWeights.mean_prod, residueAffineKernel_mean,
    FiniteProbabilityWeights.uniform_mean, residueColumnRealAverage_mean, Fintype.expect_const]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem affineSampleAlphabet_weight {J I R : Type*} [Fintype J] [Fintype I]
    [Fintype R] [AddCommGroup R] (z : Option J × I → R) :
    (residueAffineSource (J := J) (G := I → R)).weight (affineSampleAlphabetEquiv z) =
      (FiniteProbabilityWeights.uniform (Option J × I → R)).weight z := by
  change (Fintype.card (J → I → R) : ℝ)⁻¹ * (Fintype.card (I → R) : ℝ)⁻¹ =
    (Fintype.card (Option J × I → R) : ℝ)⁻¹
  rw [Fintype.card_congr (affineSampleAlphabetEquiv (J := J) (I := I) (R := R))]
  simp only [Fintype.card_prod, Nat.cast_mul, mul_inv_rev]
  ring

theorem affineSampleAlphabet_mean {J I R : Type*} [Fintype J] [Fintype I]
    [Fintype R] [AddCommGroup R] (f : ((J → I → R) × (I → R)) → ℝ) :
    (FiniteProbabilityWeights.uniform (Option J × I → R)).mean
      (fun z => f (affineSampleAlphabetEquiv z)) =
      (residueAffineSource (J := J) (G := I → R)).mean f :=
  FiniteProbabilityWeights.mean_equiv _ _ affineSampleAlphabetEquiv affineSampleAlphabet_weight f

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmallWeightedPhysicalReplacement
namespace OAI

section

namespace Erdos3

noncomputable def physicalMeanAccuracyLog {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ A : ℝ) (degree : ℕ) (epsilon : ℝ) : ℝ :=
  -Real.log (physicalPairMeanAccuracy n k Q C κ A degree epsilon)

noncomputable def physicalReplacementScaleThreshold {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ A epsilon : ℝ) (degree : ℕ) (modLog dimLog : ℝ) : ℝ :=
  replacementScaleThreshold C (physicalPairPointAccuracy n k Q C κ A epsilon)
    (physicalPairGridAccuracy n k C κ A epsilon)
    (Real.exp (modLog * (2 * degree : ℕ) + physicalMeanAccuracyLog n k Q C κ A degree epsilon + dimLog + 1))
    Q 2 (8 * probabilityProfileLipschitz)

theorem physicalReplacementScaleThreshold_conditions {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ : ℝ) (degree : ℕ) (modLog dimLog : ℝ)
    {A epsilon L H : ℝ} {N e : ℕ} (hC : 0 ≤ C) (hA : 0 ≤ A) (heps : 0 < epsilon)
    (hL : 1 ≤ L) (he : 2 ≤ e)
    (hscale : physicalReplacementScaleThreshold n k Q C κ A epsilon degree modLog dimLog * L ^ e ≤ H)
    (hupper : H ≤ 2 * (N : ℝ)) :
    let delta := physicalPairPointAccuracy n k Q C κ A epsilon
    let rho := physicalPairGridAccuracy n k C κ A epsilon
    let accLog := physicalMeanAccuracyLog n k Q C κ A degree epsilon
    0 < H ∧ 2 * C * L ^ 2 / H ≤ delta ∧ 4 ≤ rho * H ∧
      Real.exp (modLog * (2 * degree : ℕ) + accLog + dimLog + 1) ≤ rho * H / 4 ∧
      (Q : ℝ) ≤ N ∧ 8 * (probabilityProfileLipschitz : ℝ) ≤ H / L ∧ rho * H ≤ 2 * N := by
  have hd := physicalPairPointAccuracy_spec n k Q C κ hA heps
  have hr := physicalPairGridAccuracy_spec n k C κ hA heps
  exact replacementScaleThreshold_conditions hC hd.1 hr.1 (Real.exp_nonneg _) (Nat.cast_nonneg Q)
    (by norm_num) (by positivity) hL he hscale hupper (by nlinarith [hr.2.1])

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem physicalMeanAccuracyLog_le (n degree : ℕ) (k : J) (Q : ℕ)
    {C κ A epsilon P : ℝ} (hP : 0 ≤ P) (hC0 : 0 ≤ C) (hκ0 : 0 < κ)
    (hA0 : 0 ≤ A) (heps0 : 0 < epsilon) (hQ : (Q : ℝ) ≤ Real.exp P)
    (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P) (hA : A ≤ Real.exp P)
    (heps : epsilon⁻¹ ≤ Real.exp P)
    (hpow : (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp P) :
    physicalMeanAccuracyLog n k Q C κ A degree epsilon ≤ 2 * physicalPairMeanLog n degree P + 2 := by
  have hi := physicalPairMeanAccuracy_inverse_le_exp n degree k Q hP hC0 hκ0 hA0 heps0 hQ hC hκ hA heps hpow
  have hp := (physicalPairMeanAccuracy_spec n k Q C κ degree hA0 heps0).1
  have hl := Real.log_le_log (inv_pos.mpr hp) hi
  simpa only [physicalMeanAccuracyLog, Real.log_inv, Real.log_exp] using hl

theorem physicalReplacementScaleThreshold_le_exp (n degree : ℕ) (k : J) (Q : ℕ)
    {C κ A epsilon P : ℝ} (hP : 0 ≤ P) (hC0 : 0 ≤ C) (hκ0 : 0 < κ)
    (hA0 : 0 ≤ A) (heps0 : 0 < epsilon)
    (hn : (n : ℝ) ≤ Real.exp P) (hQ : (Q : ℝ) ≤ Real.exp P)
    (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P) (hA : A ≤ Real.exp P)
    (heps : epsilon⁻¹ ≤ Real.exp P) (hcard : (Fintype.card J : ℝ) ≤ Real.exp P)
    (hrow : (smoothPairRowLipschitz k : ℝ) ≤ Real.exp P)
    (hpow : (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) :
    physicalReplacementScaleThreshold n k Q C κ A epsilon degree P P ≤
      Real.exp (2 * physicalReplacementThresholdLog n (Fintype.card {j : J // j ≠ k}) degree P + 16) := by
  let d := Fintype.card {j : J // j ≠ k}
  have hb := physicalReplacementThresholdLog_bounds n d degree hP
  have hPR : P ≤ physicalReplacementThresholdLog n d degree P := by linarith [hb.2.1]
  have hexp := Real.exp_le_exp.mpr hPR
  have hpointgrid := physicalPairPointGridAccuracy_inverse_le_exp n k Q hP hC0 hκ0 hA0 heps0
    hn hQ hC hκ hA heps hcard hrow hpow
  have hmean := physicalMeanAccuracyLog_le n degree k Q hP hC0 hκ0 hA0 heps0 hQ hC hκ hA heps hpow
  have hd := (physicalPairPointAccuracy_spec n k Q C κ hA0 heps0).1
  have hr := (physicalPairGridAccuracy_spec n k C κ hA0 heps0).1
  unfold physicalReplacementScaleThreshold
  apply replacementScaleThreshold_le_exp hC0 hd hr (Nat.cast_nonneg Q) hb.1
  · exact hC.trans hexp
  · exact hpointgrid.1.trans (Real.exp_le_exp.mpr hb.2.2.1)
  · exact hpointgrid.2.trans (Real.exp_le_exp.mpr hb.2.2.1)
  · apply Real.exp_le_exp.mpr
    push_cast
    have hlast := hb.2.2.2
    nlinarith
  · exact hQ.trans hexp
  · have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    exact h2.trans (Real.exp_le_exp.mpr (by linarith [hb.2.1]))
  · have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
    calc
      _ ≤ Real.exp 8 * Real.exp P := mul_le_mul h8 hprofile (by positivity) (Real.exp_nonneg _)
      _ = Real.exp (P + 8) := by rw [← Real.exp_add, add_comm]
      _ ≤ _ := Real.exp_le_exp.mpr hb.2.1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RetainedPhysicalCRT
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {J I : Type*} [Fintype J] [Fintype I] {q : ℕ} [NeZero q]

noncomputable def affineSampleKernel (z : Option J × I → ZMod q) : FiniteProbabilityWeights (I → ZMod q) :=
  residueAffineKernel (q := q) (affineSampleAlphabetEquiv z)

theorem affineSampleKernel_preserves_mean (f : (I → ZMod q) → ℝ) :
    (FiniteProbabilityWeights.uniform (Option J × I → ZMod q)).mean
      (fun z => (affineSampleKernel z).mean f) = (FiniteProbabilityWeights.uniform (I → ZMod q)).mean f := by
  unfold affineSampleKernel
  rw [affineSampleAlphabet_mean
    (fun z : (J → I → ZMod q) × (I → ZMod q) => (residueAffineKernel (q := q) z).mean f)]
  exact residueAffineKernel_preserves_mean f

noncomputable def affineSampleCoupling :
    FiniteProbabilityCoupling (FiniteProbabilityWeights.uniform (Option J × I → ZMod q))
      (FiniteProbabilityWeights.uniform (I → ZMod q)) :=
  FiniteProbabilityCoupling.ofKernel _ _ affineSampleKernel affineSampleKernel_preserves_mean

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {J I : Type*} [Fintype J] [Fintype I] {q : ℕ} [NeZero q]

theorem affineSampleFixedParameter_mean (t : J → ZMod q) (f : (I → ZMod q) → ℝ) :
    (FiniteProbabilityWeights.uniform (Option J × I → ZMod q)).mean
      (fun z => f ((affineSampleAlphabetEquiv z).2 +
        residueColumnMap (q := q) (affineSampleAlphabetEquiv z).1 t)) =
      (FiniteProbabilityWeights.uniform (I → ZMod q)).mean f := by
  rw [affineSampleAlphabet_mean
    (fun z : (J → I → ZMod q) × (I → ZMod q) => f (z.2 + residueColumnMap (q := q) z.1 t))]
  rw [residueAffineSource, FiniteProbabilityWeights.mean_prod]
  have hs (V : J → I → ZMod q) :
      (FiniteProbabilityWeights.uniform (I → ZMod q)).mean
        (fun x => f (x + residueColumnMap (q := q) V t)) =
      (FiniteProbabilityWeights.uniform (I → ZMod q)).mean f :=
    FiniteProbabilityWeights.uniform_mean_equiv (Equiv.addRight (residueColumnMap (q := q) V t)) f
  simp only [hs, FiniteProbabilityWeights.mean_const]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.InitialBudgetJointReplacement
namespace OAI

section

namespace Erdos3

theorem selectedPhysicalReplacementThreshold_le_exp {J : Type*} [Fintype J] [DecidableEq J]
    (m n degree : ℕ) (k : J) (D : ℕ) {K A C Cwidth c epsilon P : ℝ}
    (hP : 0 ≤ P) (hK0 : 0 ≤ K) (hA0 : 0 ≤ A) (hC0 : 0 ≤ C) (hCwidth0 : 0 ≤ Cwidth)
    (hc0 : 0 < c) (heps0 : 0 < epsilon) (hD : 0 < D)
    (hn : (n : ℝ) ≤ Real.exp P) (hcard : (Fintype.card J : ℝ) ≤ Real.exp P)
    (hDlog : (D : ℝ) ≤ Real.exp P) (hK : K ≤ Real.exp P) (hA : A ≤ Real.exp P)
    (hC : C ≤ Real.exp P) (hCwidth : Cwidth ≤ Real.exp P)
    (hc : c⁻¹ ≤ Real.exp P) (heps : epsilon⁻¹ ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) :
    let tol := weightedReplacementTolerance ((3 * K) ^ m) ((2 : ℝ) ^ (n + 1) * A ^ n) epsilon
    let Q := D * integerBoxGcdCutoff (Fintype.card J) Cwidth tol
    let κ := integerBoxRetainedGap (Fintype.card J) D c tol
    let Z := replacementCommonInputLog m n (Fintype.card J) P
    physicalReplacementScaleThreshold n k Q C κ A tol degree Z Z ≤
      Real.exp (2 * physicalReplacementThresholdLog n (Fintype.card {j : J // j ≠ k}) degree Z + 16) := by
  intro tol Q κ Z
  obtain ⟨ht, hti, hk, hki, hq, _⟩ := replacement_selected_parameter_bounds m n (Fintype.card J) D
    hP hK0 hA0 hCwidth0 hc0 heps0 hD hDlog hK hA hCwidth hc heps
  obtain ⟨hn', hcard', hC', hA', hprofile', hrow', hpow'⟩ :=
    replacement_common_geometric_bounds m n k hP hn hcard hC hA hprofile
  exact physicalReplacementScaleThreshold_le_exp n degree k Q
    (replacementCommonInputLog_bounds m n (Fintype.card J) hP).1 hC0 hk hA0 ht
    hn' hq hC' hki hA' hti hcard' hrow' hpow' hprofile'

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.NormalizedTwistSingleSiteFourierHaar
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

noncomputable def ambientIntegerCharacter {J : Type*} [Fintype J] (frequency : J → ℤ)
    (x : J → UnitAddCircle) : ℂ :=
  ∏ j, CircleFourier.character (frequency j • x j)

theorem ambientIntegerCharacter_norm {J : Type*} [Fintype J]
    (frequency : J → ℤ) (x : J → UnitAddCircle) :
    ‖ambientIntegerCharacter frequency x‖ = 1 := by
  simp [ambientIntegerCharacter, norm_prod, CircleFourier.norm_character]

theorem ambientIntegerCharacter_lipschitz {J : Type*} [Fintype J]
    (frequency : J → ℤ) (C : ℝ≥0) (hC : ∀ j, |(frequency j : ℝ)| ≤ C) :
    LipschitzWith (Fintype.card J * (CircleFourier.characterLipConstant * C))
      (ambientIntegerCharacter frequency) := by
  have hcoord (j : J) : LipschitzWith C (fun x : J → UnitAddCircle => frequency j • x j) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, ← smul_sub]
    apply (norm_zsmul_le (frequency j) (x j - y j)).trans
    apply mul_le_mul
    · simpa only [Int.norm_eq_abs] using hC j
    · simpa only [dist_eq_norm] using dist_le_pi_dist x y j
    · exact norm_nonneg _
    · exact C.coe_nonneg
  have h := (bounded_lipschitz_fintype_prod
    (fun j (x : J → UnitAddCircle) => CircleFourier.character (frequency j • x j))
    (B := 1) le_rfl (fun j => CircleFourier.character_lipschitz.comp (hcoord j))
    (fun j x => (CircleFourier.norm_character _).le)).2
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [one_pow, mul_one, ambientIntegerCharacter] using h.dist_le_mul x y

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ConcreteAffineMeshBoundary
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def integerBoxMeshCellEquiv (lo hi : I → ℤ)
    (P : ∀ i, FiniteProgressionPartition (hi i - lo i).toNat)
    (hstep : ∀ i c, (P i).step c = 1) (hpos : ∀ i c, 0 < (P i).length c)
    (c : ∀ i, (P i).Label) :
    {z : (∀ i, Finset.Ico (lo i) (hi i)) // integerBoxMesh lo hi P z = c} ≃
      IntegerResidueBox (fun i => intervalCellLower (lo i) (P i) (c i))
        (fun i => intervalCellLower (lo i) (P i) (c i) + (P i).length (c i))
        (fun _ => 1) (fun _ => 0) := by
  let e : {z : (∀ i, Finset.Ico (lo i) (hi i)) // integerBoxMesh lo hi P z = c} ≃
      {x : translatedIntegerBox lo (fun i => (hi i - lo i).toNat) //
        physicalBoxCell lo (fun i => (hi i - lo i).toNat) P x = c} :=
    (integerBoxMeshPointEquiv lo hi).subtypeEquiv (fun _ => Iff.rfl)
  exact e.trans (physicalBoxCellEquiv lo (fun i => (hi i - lo i).toNat) P hstep hpos c)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AdaptiveCouplingComparison
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {μ : ∀ i, FiniteProbabilityWeights (X i)} {ν : ∀ i, FiniteProbabilityWeights (Y i)}
  (c : ∀ i, FiniteProbabilityCoupling (μ i) (ν i))

noncomputable def adaptiveLeafPairMass (baseX : ∀ i, X i) (baseY : ∀ i, Y i)
    (z : Σ leaf : ProductCylinder Y, ∀ i : leaf.1, X i.val) : ℝ :=
  productCouplingAtomMass c z.1.1 (productSubtypePoint z.1.1 z.2 baseX) (z.1.assignment baseY)

theorem adaptiveLeafPairMass_sum (tree : CoordinateDecisionTree ι Y) (I : Finset ι)
    (baseX : ∀ i, X i) (baseY : ∀ i, Y i) :
    (∑ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree I baseY,
      adaptiveLeafPairMass c baseX baseY z) =
      productFiberMass (FiniteProbabilityWeights.pi ν).weight I baseY := by
  simp only [CoordinateDecisionTree.leafSourceAssignments, Finset.sum_sigma, adaptiveLeafPairMass,
    productCouplingAtomMass_sum_left]
  exact CoordinateDecisionTree.leafCylinders_mass_sum tree I baseY (FiniteProbabilityWeights.pi ν).weight

theorem adaptiveLeafPairMass_sum_empty (tree : CoordinateDecisionTree ι Y)
    (baseX : ∀ i, X i) (baseY : ∀ i, Y i) :
    (∑ z ∈ CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY,
      adaptiveLeafPairMass c baseX baseY z) = 1 := by
  rw [adaptiveLeafPairMass_sum, productFiberMass_empty, (FiniteProbabilityWeights.pi ν).total]

noncomputable def adaptiveLeafCouplingWeights (tree : CoordinateDecisionTree ι Y)
    (baseX : ∀ i, X i) (baseY : ∀ i, Y i) :
    FiniteProbabilityWeights (CoordinateDecisionTree.leafSourceAssignments X tree ∅ baseY) where
  weight z := adaptiveLeafPairMass c baseX baseY z.val
  nonneg z := productCouplingAtomMass_nonneg c _ _ _
  total := by
    rw [Finset.sum_coe_sort]
    exact adaptiveLeafPairMass_sum_empty c tree baseX baseY

end Erdos3

end

end OAI
end


