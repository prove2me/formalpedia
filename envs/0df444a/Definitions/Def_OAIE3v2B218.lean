-- Prove2me | Definitions.Def_OAIE3v2B218
-- name    : OAIE3v2B218
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:31:37.031782+00:00
-- url     : https://prove2.me/theorems/a45095f3-3a37-448f-8be3-66e5088f973b
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 222 of 311
-- statement:
--   Definitions bundle 222 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B299`, `OAIE3v2B191`, `OAIE3v2B192`, `OAIE3v2B193`, `OAIE3v2B195`, `OAIE3v2B300`, `OAIE3v2B197` of this split.
--
--   Modules: `Dynamics/AllocatedFixedPathSlicedNativeAmbientComparison.lean`, `Dynamics/CanonicalZeroLayerBudgetedInitialization.lean`, `Dynamics/PreparedFiniteNestedSourceLatePowerBudget.lean`, `Estimates/PreparedScalarNestedPowerDetection.lean`, `Fourier/ForecastSpatialCharacterSplit.lean`, `Geometry/PhysicalBoxControl.lean`, `Lattices/AllocatedResidueInterpolationMixture.lean`, `Lattices/ForecastJointNativeResidue.lean`, `Lattices/ResiduePrimeDensityError.lean`, `Lattices/RetainedPhysicalCRT.lean`, `Linear/AllocatedShortRankWitnessWidth.lean`, `Polynomial/ScalarInitialPolynomialBudget.lean`, `Sampling/AllocatedFixedPathRecoveredJointGridComparison.lean`, `Sampling/PreparedActualForecastSetup.lean`, `Sampling/PreparedConcreteSlicedForecastModelLogs.lean`, `Sampling/PreparedConcreteSlicedForecastPrimitiveCapBudget.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B299
import Definitions.Def_OAIE3v2B191
import Definitions.Def_OAIE3v2B192
import Definitions.Def_OAIE3v2B193
import Definitions.Def_OAIE3v2B195
import Definitions.Def_OAIE3v2B300
import Definitions.Def_OAIE3v2B197

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedResidueInterpolationMixture
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h L hL).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "coord" => principalSupportedCoordinateWeights B h L hL q r hcell

noncomputable def principalSupportedAxisTuplePMF (a : D) :
    PMF (∀ b : B a, ∀ v : Fin (h a), IntegerScalarCubeBox α (L ⟨a, b, v⟩)) :=
  dependentProductPMF (fun b => dependentProductPMF (fun v => ((coord) ⟨a, b, v⟩).toPMF))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedShortRankWitnessWidth
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U basis R σ)

noncomputable local instance spatialReferenceSmoothFintype :
    Fintype (AllocatedFullSmoothCoefficientIndex G X I n B) := inferInstance
noncomputable local instance spatialReferenceDeckFintype :
    Fintype (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E) := inferInstance

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ForecastSpatialCharacterSplit
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
variable (inactive : LayerSamplerAxis I n → Prop)

def forecastSpatialOutputHom {R : Type*} [AddCommMonoid R] :
    (X → R) →+ (Sigma (AllocatedCongruenceRankOutput X E inactive) → R) where
  toFun u o := match o.2 with
    | .inl x => u x.val
    | .inr _ => 0
  map_zero' := by
    funext o
    rcases o with ⟨j, x | i | a⟩ <;> rfl
  map_add' u v := by
    funext o
    rcases o with ⟨j, x | i | a⟩ <;> simp

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ForecastJointNativeResidue
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)
local notation "short" => allocatedShortAxis (I := I) U basis L
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)

def forecastJointNativeResidue {A : Type*}
    (deck : ∀ j, E j → A) (r : X ⊕ AllocatedActiveIntegerAxis U basis L → A) : Out → A
  | ⟨_, .inl x⟩ => r (.inl x.val)
  | ⟨j, .inr (.inl e)⟩ => deck j e
  | ⟨j, .inr (.inr i)⟩ => r (.inr ⟨⟨j, i.val⟩, Nat.lt_of_not_ge i.property⟩)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedFixedPathRecoveredJointGridComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical
variable {X : Type*} {m : ℕ} {I E : Fin m → Type*} {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ) (hm : 0 < m)
local notation "short" => allocatedShortAxis (I := I) U basis L
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "Aux" => (Σ j : Fin m, E j)
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis L

def forecastCongruenceJointAxisEquiv : Out ≃ Aux ⊕ (X ⊕ IntAxis) where
  toFun a := match a with
    | ⟨_, .inl x⟩ => .inr (.inl x.val)
    | ⟨j, .inr (.inl e)⟩ => .inl ⟨j, e⟩
    | ⟨j, .inr (.inr i)⟩ => .inr (.inr ⟨⟨j, i.val⟩, Nat.lt_of_not_ge i.property⟩)
  invFun a := match a with
    | .inl ⟨j, e⟩ => ⟨j, .inr (.inl e)⟩
    | .inr (.inl x) => ⟨⟨0, hm⟩, .inl ⟨x, rfl⟩⟩
    | .inr (.inr a) => ⟨a.val.1, .inr (.inr ⟨a.val.2, Nat.not_le.mpr a.property⟩)⟩
  left_inv a := by
    rcases a with ⟨j, x | e | i⟩
    · rcases j with ⟨j, hj⟩
      rcases x with ⟨x, hx⟩
      change j = 0 at hx
      subst j
      rfl
    · rfl
    · rfl
  right_inv a := by
    rcases a with ⟨j, e⟩ | x | ⟨⟨j, i⟩, ha⟩ <;> rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped Classical BigOperators NNReal
variable {X : Type*} [Fintype X]
variable {m : ℕ} {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (Lsize : ℕ) (hm : 0 < m)
local notation "Aux" => (Σ j : Fin m, E j)
local notation "IntAxis" => AllocatedActiveIntegerAxis U basis Lsize
local notation "Joint" => X ⊕ IntAxis
local notation "Cont" => (Σ j : Fin m, I j)
local notation "axis" => forecastCongruenceJointAxisEquiv (X := X) (I := I) (E := E) U basis Lsize hm
local notation "join" => forecastJointCoordinateJoin (X := X) (I := I) U basis Lsize

variable {PIndex Ω Z : Type*} [Fintype PIndex] [Fintype Ω]
variable (inactive : FiniteProbabilityWeights PIndex) (active : PIndex → FiniteProbabilityWeights Ω)
variable (gridPoint : PIndex → Z) (Y : PIndex → Ω → Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ℤ)
variable (N q : ℕ) [NeZero N] (hq : q ∣ N) (gridVolume : ℝ)
variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℝ)
variable (test : Z → (Sigma (AllocatedCongruenceRankOutput X E
  (allocatedShortAxis (I := I) U basis Lsize)) → ZMod q) →
  (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis Lsize a}, Unit) → ℝ)) → ℂ)
variable (center scale : X ⊕ AllocatedActiveIntegerAxis U basis Lsize → ℝ)

noncomputable def forecastJointOriginalGridMean : ℂ :=
  𝔼 aux : Aux → ZMod N, ∫ c : Cont → ℝ,
    (∑' z, ∑' k : Joint → ℤ,
      (density (join c (fun j => ((k j : ℝ) - center j) / scale j)) : ℂ) *
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z
        (fun a => Sum.elim aux (fun j => (k j : ZMod N)) (axis a)) / gridVolume : ℝ) : ℂ) *
      test z (fun a => Sum.elim (zmodPiReduction hq aux)
        (fun j => (k j : ZMod q)) (axis a))
        (join c (fun j => ((k j : ℝ) - center j) / scale j))) /
      ((∏ j, scale j : ℝ) : ℂ)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedFixedPathSlicedNativeAmbientComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G T : Type*} {X : Type} [Fintype T] [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
local notation "Ncrt" => (∏ l, primes l ^ exponent l)
local instance slicedAmbientNativeCRTNeZero : NeZero Ncrt :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (primes l)))⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G T : Type*} {X : Type} [Fintype T] [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
local notation "Ncrt" => (∏ l, primes l ^ exponent l)
local instance slicedCompleteNativeCRTNeZero : NeZero Ncrt :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (primes l)))⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedActualForecastSetup
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem preparedActualForecast_radius_bounds
    {m : ℕ} (hm : 0 < m) {Vars : Type} [Fintype Vars]
    (T : Fin m → ℝ) (radius : ℝ≥0)
    (hT : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent Vars (j.val + 1)) : ℝ) *
      (2 * 2 ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j : Fin m, (boundedBooleanJetRows (Fin 1) (j.val + 1)).card * T j ≤ (radius : ℝ)) :
    (3 : ℝ) ≤ radius ∧
      ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent Vars (j.val + 1)) : ℝ) ≤ radius := by
  have hcount (j : Fin m) :
      (1 : ℝ) ≤ Fintype.card (BoundedCoefficientExponent Vars (j.val + 1)) := by
    have : Nonempty (BoundedCoefficientExponent Vars (j.val + 1)) := ⟨⟨0, by simp⟩⟩
    exact_mod_cast Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr this)
  have hT0 (j : Fin m) : 0 ≤ T j :=
    (mul_nonneg (Nat.cast_nonneg _) (by positivity)).trans (hT j)
  have hTradius (j : Fin m) : T j ≤ (radius : ℝ) :=
    (le_mul_of_one_le_left (hT0 j) (by exact_mod_cast forecastRows_one_le j.val)).trans (hradius j)
  constructor
  · let j : Fin m := ⟨0, hm⟩
    have hj := (hT j).trans (hTradius j)
    have hc := hcount j
    norm_num only [j, Nat.zero_add, pow_one] at hj
    linarith
  · intro j
    have hf : (1 : ℝ) ≤ 2 * 2 ^ (j.val + 1) := by
      have := (one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) : (1 : ℝ) ≤ 2 ^ (j.val + 1))
      linarith
    exact (le_mul_of_one_le_right (Nat.cast_nonneg _) hf).trans ((hT j).trans (hTradius j))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedConcreteSlicedForecastModelLogs
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

noncomputable def preparedConcreteSlicedForecastTailSiteLog (m M nX Jalloc : ℕ)
    (Pdim cost pRadius childLog : ℝ) : ℝ :=
  let P := preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost
  let D := P + (layerTailDegree m + 1 : ℕ) + 1
  let v := P + (allocatedComparisonDimension m
    (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + pRadius + 1)
  slicedFixedUniformSiteLog m
    (preparedSlicedForecastTailLog cost + slicedFixedZeroGeometryLog D v cost 0 (childLog + 1)) 0

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResiduePrimeDensityError
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def normalizedResiduePrimeDensity {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [DecidableEq σ] (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ)
    (hne : Nonempty (IntegerResidueBox lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a))
    (q : ι → ℕ) [∀ i, NeZero (q i)] (f : (σ → ℤ) → ℝ) (scale : ℝ)
    (x : ∀ i, σ → ZMod (q i)) : ℝ :=
  scale⁻¹ * residuePrimeCoordinateDensity lo N M a hne q f x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalBoxControl
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {I ι : Type*} [Fintype I] [DecidableEq I] [Fintype ι] [DecidableEq ι]

noncomputable def physicalBoxTruncation (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ j, NeZero (q j)] (b : ℕ) (f : (I → ℤ) → ℝ) (x : I → ℤ) : ℝ :=
  if hx : x ∈ translatedIntegerBox lo N then
    let c := physicalBoxCell lo N P ⟨x, hx⟩
    residuePhysicalTruncation (fun i => intervalCellLower (lo i) (P i) (c i))
      (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hpos c) q b f x
  else 0

noncomputable def physicalBoxResidual (lo : I → ℤ) (N : I → ℕ)
    (P : ∀ i, FiniteProgressionPartition (N i)) (hpos : ∀ i c, 0 < (P i).length c)
    (q : ι → ℕ) [∀ j, NeZero (q j)] (b : ℕ) (f : (I → ℤ) → ℝ) (x : I → ℤ) : ℝ :=
  if x ∈ translatedIntegerBox lo N then f x - physicalBoxTruncation lo N P hpos q b f x else 0

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

theorem affineSampleParameterKernel_preserves_mean (π : FiniteProbabilityWeights (J → ZMod q))
    (f : (I → ZMod q) → ℝ) :
    (FiniteProbabilityWeights.uniform (Option J × I → ZMod q)).mean
      (fun z => (affineSampleParameterKernel π z).mean f) =
      (FiniteProbabilityWeights.uniform (I → ZMod q)).mean f := by
  simp only [affineSampleParameterKernel_mean]
  rw [FiniteProbabilityWeights.mean_comm]
  simp only [affineSampleFixedParameter_mean, FiniteProbabilityWeights.mean_const]

noncomputable def affineSampleParameterCoupling (π : FiniteProbabilityWeights (J → ZMod q)) :
    FiniteProbabilityCoupling (FiniteProbabilityWeights.uniform (Option J × I → ZMod q))
      (FiniteProbabilityWeights.uniform (I → ZMod q)) :=
  FiniteProbabilityCoupling.ofKernel _ _ (affineSampleParameterKernel π)
    (affineSampleParameterKernel_preserves_mean π)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J σ : Type*} [Fintype J] [Fintype σ]
  (q : ι → ℕ) [∀ i, NeZero (q i)]

noncomputable def affineParameterProductCoupling
    (π : ∀ i, FiniteProbabilityWeights (J → ZMod (q i))) :
    ∀ i, FiniteProbabilityCoupling
      (primeCoordinateReference (σ := Option J × σ) q i)
      (primeCoordinateReference (σ := σ) q i) :=
  fun i => affineSampleParameterCoupling (π i)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J σ : Type*} [Fintype J] [Fintype σ]
  (q : ι → ℕ) [∀ i, NeZero (q i)]

noncomputable def affinePeriodProductCoupling (D : ℕ) (a : J → ℤ) :
    ∀ i, FiniteProbabilityCoupling
      (primeCoordinateReference (σ := Option J × σ) q i)
      (primeCoordinateReference (σ := σ) q i) :=
  affineParameterProductCoupling q (fun i => affinePeriodParameterLaw (q := q i) D a)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {ι J I : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
  [Fintype I]
  (q : ι → ℕ) [∀ i, NeZero (q i)]
  (sourceLo : Option J × I → ℤ) (sourceN : Option J × I → ℕ)
  (sourceHne : Nonempty (IntegerResidueBox sourceLo (fun i => sourceLo i + sourceN i)
    (fun _ => 1) (fun _ => 0)))
  (paramLo : J → ℤ) (paramN : J → ℕ)
  (paramHne : Nonempty (IntegerResidueBox paramLo (fun j => paramLo j + paramN j)
    (fun _ => 1) (fun _ => 0)))
  (siteLo : I → ℤ) (siteN : I → ℕ)
  (siteHne : Nonempty (IntegerResidueBox siteLo (fun i => siteLo i + siteN i)
    (fun _ => 1) (fun _ => 0)))
  (D : ℕ) (a : J → ℤ) (b : ℕ) (w : (Option J × I → ℤ) → ℝ) (f : (I → ℤ) → ℝ)

noncomputable def residueAffineTruncationError : ℝ :=
  |(𝔼 z : IntegerResidueBox sourceLo (fun i => sourceLo i + sourceN i) (fun _ => 1) (fun _ => 0),
      w (fun i => (z i).val) *
        (𝔼 t : IntegerResidueBox paramLo (fun j => paramLo j + paramN j) (fun _ => 1) (fun _ => 0),
          residuePhysicalTruncation siteLo siteN 1 (fun _ => 0) siteHne q b f
            (smoothAffineSample (fun j => a j + (D : ℤ) * (t j).val) (fun i => (z i).val)))) -
    productTruncatedPairing (affinePeriodProductCoupling (σ := I) q D a) (lowDegreeCoordinateSets ι b)
      (residuePrimeCoordinateDensity sourceLo sourceN 1 (fun _ => 0) sourceHne q w)
      (residuePrimeCoordinateDensity siteLo siteN 1 (fun _ => 0) siteHne q f)|

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ScalarInitialPolynomialBudget
namespace OAI

section

namespace Erdos3

noncomputable def scalarInitialReferencePolynomial (d A : ℕ) : Polynomial ℕ :=
  let X := Polynomial.X
  let P := Polynomial.C A * (X + 1)
  let M := Polynomial.C (d + 1) * X
  let D := Polynomial.C d
  let input := M * (P + 3) + X * P + 2 * (X + 1) + P + 1
  let Z := 4 * (6 * input + P + 3 * D + 10) + 2 * P + 10
  let row := (16 + 4 * D) * Z + 16 * D + 48
  let error := Z + row + X * (row + 6 * Z + 12)
  let G := 2 * (30 + 2 * X * Z + 2 * X + error + X * (5 * Z + 11) + 10 * Z + 4 * (2 + D)) + 2
  G + Z + P + M + X + D + 2 * (3 * X + 10) + X + 20

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CanonicalZeroLayerBudgetedInitialization
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def unconditionedCommonSideExtra (n : ℕ) : ℝ :=
  Real.log ((1 + n * 2 ^ (n + 1) : ℕ) : ℝ)

@[simp] theorem exp_unconditionedCommonSideExtra (n : ℕ) :
    Real.exp (unconditionedCommonSideExtra n) = ((1 + n * 2 ^ (n + 1) : ℕ) : ℝ) := by
  exact Real.exp_log (by positivity)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteNestedSourceLatePowerBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical BigOperators NNReal

noncomputable def preparedEmptyLayerLocalTailWidthLog
    (m : ℕ) {K G : Type} [Fintype K] [Fintype G]
    (degree Cdetect : K → ℕ) (nX count : ℕ)
    (Bstruct pnum Qstride Qσ : ℝ) (u model : K → ℝ) : ℝ :=
  let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
  let D := allocatedComparisonDimension m pnum
  let pDetect := fun k => allocatedModelTestLog (u k) (model k)
  let aDetect := fun k => 2 * u k + 4 * model k + 7
  let gain := fun k => slicedDetectionGainLog (degree k) (Cdetect k) count
    (pDetect k) (pDetect k) (aDetect k)
  let Pk := fun k => scalarKernelLogarithmicBudget (Fin (degree k + 1)) G
    (gain k + pDetect k + 4)
  let physical := fun k => preparedFiniteScheduleLocalPhysical m nX count Qstride (Pk k)
  let target := fun k => gain k + 40 + coefficientErrorSpatialLog (physical k)
  let E := fun k => target k + D * ((m * 2 ^ (m + 1) : ℕ) * Pk k) + 5
  let tail := fun k => affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
    (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2)
  let scale := preparedUniformDegreeScaleLog (D + pRadius) tail Qσ
  (probabilityProfileLipschitz : ℝ) + 8 + (D + 4) + pRadius + scale

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedScalarNestedPowerDetection
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

noncomputable def preparedEmptyLayerLocalScaleFloor
    (m : ℕ) {K G : Type} [Fintype K] [Fintype G]
    (degree Cdetect : K → ℕ) (nX count : ℕ)
    (Bstruct pnum Qstride Qσ : ℝ) (u model : K → ℝ) : ℝ :=
  max (preparedEmptyLayerLocalTailWidthLog (G := G) m degree Cdetect nX count
    Bstruct pnum Qstride Qσ u model)
    (∑ k, max 0 (preparedEmptyLayerLocalLengthLog (G := G) m degree Cdetect nX count
      Bstruct pnum Qstride Qσ u model k))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedConcreteSlicedForecastPrimitiveCapBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedConcreteSlicedForecastPrimitiveCapLog_budget
    (m Ccontrol Cchild Cprimitive : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (M nX Jalloc : ℕ)
      {b Pdim pRadius gainLog Qstride Pchart childLog : ℝ},
      0 ≤ b →
      allocatedComparisonDimension m
        (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) ≤ b →
      ((nX + m * M : ℕ) : ℝ) ≤ b →
      Pdim ∈ Set.Icc 0 ((b + Cprimitive) ^ Cprimitive) →
      pRadius ∈ Set.Icc 0 ((b + Cprimitive) ^ Cprimitive) →
      gainLog ∈ Set.Icc 0 ((b + Cprimitive) ^ Cprimitive) →
      Qstride ∈ Set.Icc 0 ((b + Cprimitive) ^ Cprimitive) →
      Pchart ∈ Set.Icc 0 ((b + Cprimitive) ^ Cprimitive) →
      childLog ∈ Set.Icc 0 ((b + Cchild) ^ Cchild) →
      preparedConcreteSlicedForecastCapLog m M nX Jalloc
        Pdim ((b + Ccontrol) ^ Ccontrol) pRadius gainLog Qstride Pchart childLog ∈
          Set.Icc 0 ((b + C) ^ C) := by
  obtain ⟨Csp, _, hsp⟩ := exists_preparedCenteredForecastSpatialLog_budget
  obtain ⟨Cg, _, hgeneric⟩ := exists_actualSlicedForecastModelCapLog_budget m
  let Cprim : ℕ := ⌈preparedSlicedForecastPrimitiveCap⌉₊
  let X : Polynomial ℕ := Polynomial.X
  let Pr : Polynomial ℕ := (X + Polynomial.C Cprimitive) ^ Cprimitive
  let W : Polynomial ℕ := (X + Polynomial.C Ccontrol) ^ Ccontrol
  let H : Polynomial ℕ := (X + Polynomial.C Cchild) ^ Cchild
  let S : Polynomial ℕ := 2 * X + 8 + (Pr + Polynomial.C Csp) ^ Csp + W + 1
  let Bad : Polynomial ℕ := 2 * X * Pr +
    Polynomial.C (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m)) + Pr + 11
  let Jac : Polynomial ℕ := (X + Polynomial.C m) * (3 * Pr + X + 11)
  let Tail : Polynomial ℕ := Polynomial.C Cprim + W + 1
  let R : Polynomial ℕ := X + S + (X + Pr + 1) + Bad + Jac + (W + 1) + Tail + W + (H + 1)
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C Cg) ^ Cg)
  refine ⟨C, hC, ?_⟩
  intro M nX Jalloc b Pdim pRadius gainLog Qstride Pchart childLog
    hb hDbase hDmod hPdim hRadius hGain hStride hChart hChild
  let primitive : ℝ := (b + Cprimitive) ^ Cprimitive
  let cost : ℝ := (b + Ccontrol) ^ Ccontrol
  let child : ℝ := (b + Cchild) ^ Cchild
  let spatial : ℝ := 2 * b + 8 + (primitive + Csp) ^ Csp + cost + 1
  let bad : ℝ := 2 * b * primitive +
    (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + primitive + 11
  let jac : ℝ := (b + m) * (3 * primitive + b + 11)
  let tail : ℝ := Cprim + cost + 1
  let r : ℝ := b + spatial + (b + primitive + 1) + bad + jac + (cost + 1) + tail + cost + (child + 1)
  have hprimitive0 : 0 ≤ primitive := by dsimp only [primitive]; positivity
  have hcost0 : 0 ≤ cost := by dsimp only [cost]; positivity
  have hchild0 : 0 ≤ child := by dsimp only [child]; positivity
  have hspatial0 : 0 ≤ spatial := by dsimp only [spatial]; positivity
  have hbad0 : 0 ≤ bad := by dsimp only [bad]; positivity
  have hjac0 : 0 ≤ jac := by dsimp only [jac]; positivity
  have htail0 : 0 ≤ tail := by dsimp only [tail]; positivity
  have hr0 : 0 ≤ r := by dsimp only [r]; positivity
  have hbr : b ≤ r := by dsimp only [r]; linarith
  have hspatialr : spatial ≤ r := by dsimp only [r]; linarith
  have hscaler : b + primitive + 1 ≤ r := by dsimp only [r]; linarith
  have hbadr : bad ≤ r := by dsimp only [r]; linarith
  have hjacr : jac ≤ r := by dsimp only [r]; linarith
  have hcostr : cost + 1 ≤ r := by dsimp only [r]; linarith
  have htailr : tail ≤ r := by dsimp only [r]; linarith
  have hchildr : child + 1 ≤ r := by dsimp only [r]; linarith
  have hDbase0 := (allocatedComparisonDimension_bounds m
    (Nat.cast_nonneg (enlargedPreparedCommonSamplerDimension m M Jalloc))).1
  have hnX : (nX : ℝ) ≤ b := by
    have hnonneg : (0 : ℝ) ≤ m * M := by positivity
    have hdim : (nX : ℝ) + m * M ≤ b := by
      simpa only [Nat.cast_add, Nat.cast_mul] using hDmod
    linarith only [hdim, hnonneg]
  have hcenter : preparedCenteredForecastSpatialLog Pdim ≤ (primitive + Csp) ^ Csp :=
    (hsp hPdim.1).trans (pow_le_pow_left₀ (add_nonneg hPdim.1 (Nat.cast_nonneg Csp))
      (add_le_add hPdim.2 (le_refl (Csp : ℝ))) Csp)
  have hP0 : 0 ≤ preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost := by
    apply le_trans _ (le_max_left _ _)
    positivity
  have hP : preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost ≤ spatial := by
    unfold preparedSlicedForecastSpatialBudget
    apply max_le
    · dsimp only [spatial]
      have hpow : 0 ≤ (primitive + Csp) ^ Csp := by positivity
      linarith only [hDbase, hnX, hpow, hcost0]
    · apply max_le
      · dsimp only [spatial]
        linarith only [hcenter, hb, hcost0]
      · dsimp only [spatial]
        have hpow : 0 ≤ (primitive + Csp) ^ Csp := by positivity
        linarith only [hb, hpow]
  have hscale0 : 0 ≤ allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + pRadius + 1 := by
    linarith only [hDbase0, hRadius.1]
  have hscale : allocatedComparisonDimension m
      (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + pRadius + 1 ≤ r := by
    apply le_trans _ hscaler
    linarith only [hDbase, hRadius.2]
  have hbadInput0 : 0 ≤ preparedSlicedForecastBadLog m nX Qstride gainLog := by
    unfold preparedSlicedForecastBadLog
    have := hStride.1
    have := hGain.1
    positivity
  have hbadInput : preparedSlicedForecastBadLog m nX Qstride gainLog ≤ r := by
    apply le_trans _ hbadr
    have hmul : 2 * (nX : ℝ) * Qstride ≤ 2 * b * primitive :=
      mul_le_mul (mul_le_mul_of_nonneg_left hnX (by norm_num)) hStride.2 hStride.1
        (by positivity)
    dsimp only [preparedSlicedForecastBadLog, bad]
    nlinarith only [hmul, hGain.2]
  have hjacInput0 : 0 ≤ preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart := by
    unfold preparedSlicedForecastJacobianLog
    have := hRadius.1
    have := hGain.1
    have := hChart.1
    positivity
  have hjacInput : preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart ≤ r := by
    apply le_trans _ hjacr
    have hleft : ((nX + m + m * M : ℕ) : ℝ) ≤ b + m := by
      have hdim : (nX : ℝ) + m * M ≤ b := by
        simpa only [Nat.cast_add, Nat.cast_mul] using hDmod
      simp only [Nat.cast_add, Nat.cast_mul]
      linarith only [hdim]
    have hright : pRadius + gainLog + nX + Pchart + 11 ≤ 3 * primitive + b + 11 := by
      linarith only [hRadius.2, hGain.2, hnX, hChart.2]
    have hnX0 : (0 : ℝ) ≤ nX := Nat.cast_nonneg nX
    exact mul_le_mul hleft hright
      (by linarith only [hRadius.1, hGain.1, hChart.1, hnX0]) (by positivity)
  have htailInput0 : 0 ≤ preparedSlicedForecastTailLog cost :=
    preparedSlicedForecastTailLog_nonneg hcost0
  have htailInput : preparedSlicedForecastTailLog cost ≤ r := by
    apply le_trans _ htailr
    have hprimitive : preparedSlicedForecastPrimitiveCap ≤ (Cprim : ℝ) := Nat.le_ceil _
    dsimp only [preparedSlicedForecastTailLog, tail]
    linarith only [hprimitive]
  have hcap := hgeneric (nX + m * M) nX hr0 (hDmod.trans hbr) (hnX.trans hbr)
    ⟨hP0, hP.trans hspatialr⟩ ⟨hscale0, hscale⟩ ⟨hbadInput0, hbadInput⟩
    ⟨by linarith only [hcost0], hcostr⟩ ⟨hjacInput0, hjacInput⟩
    ⟨by linarith only [hcost0], hcostr⟩ ⟨htailInput0, htailInput⟩
    ⟨hcost0, by linarith only [hcostr]⟩
    ⟨by linarith only [hChild.1], (add_le_add hChild.2 (le_refl (1 : ℝ))).trans hchildr⟩
  have hfinal : (r + Cg) ^ Cg ≤ (b + C) ^ C := by
    simpa [R, S, Bad, Jac, Tail, W, H, Pr, X, r, spatial, bad, jac, tail, cost, child, primitive,
      Polynomial.eval₂_pow] using hpoly b hb
  exact ⟨hcap.1, hcap.2.trans hfinal⟩

noncomputable def preparedConcreteSlicedForecastPrimitiveCapExponent
    (m Ccontrol Cchild Cprimitive : ℕ) : ℕ :=
  Classical.choose (exists_preparedConcreteSlicedForecastPrimitiveCapLog_budget m Ccontrol Cchild Cprimitive)

end Erdos3.VectorPolynomial

end

end OAI
end


