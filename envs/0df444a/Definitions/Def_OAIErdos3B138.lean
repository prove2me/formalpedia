-- Prove2me | Definitions.Def_OAIErdos3B138
-- name    : OAIErdos3B138
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T16:59:21.465982+00:00
-- url     : https://prove2.me/theorems/549548b4-5a3d-42bb-b8e7-caf48f0ccda5
-- title:
--   OpenAI Erdős-3 split, definitions bundle 139 of 151
-- statement:
--   Definitions bundle 139 of 151 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B137`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 139 available.
--
--   Modules: `OAI.Erdos3.VectorPolynomial.AllocatedShortIntegerAxis`, `OAI.Erdos3.VectorPolynomial.PreparedModularCanonicalDetectorResourceConstants.casesOn`, `OAI.Erdos3.VectorPolynomial.PreparedModularCanonicalDetectorResources.Bounds`, `OAI.Erdos3.VectorPolynomial.PreparedModularCanonicalDetectorResources.casesOn`, `OAI.Erdos3.VectorPolynomial.PreparedModularCanonicalDetectorResources.map`, `OAI.Erdos3.VectorPolynomial.PreparedModularCanonicalDetectorResources.toList`, `OAI.Erdos3.VectorPolynomial.PreparedModularCanonicalDetectorResources.total`, `OAI.Erdos3.VectorPolynomial.allocatedOriginalSampleInactiveCoefficients`, `OAI.Erdos3.VectorPolynomial.allocatedOriginalSampleLiftLip`, `OAI.Erdos3.VectorPolynomial.allocatedShortIntegerAxisEquiv`, `OAI.Erdos3.VectorPolynomial.allocatedShortIntegerSelection`, `OAI.Erdos3.VectorPolynomial.exists_coefficient_ambient_cover_sampling`, `OAI.Erdos3.VectorPolynomial.exists_coefficient_ambient_l1_sampling`, `OAI.Erdos3.VectorPolynomial.instFintypeAllocatedShortIntegerAxis`, `OAI.Erdos3.VectorPolynomial.preparedModularCanonicalDetectorResources`, `OAI.Erdos3.allocatedIntegerCoefficient_le_radius`, `OAI.Erdos3.continuousPolynomialDensity_coefficient_le_radius`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B135
import Definitions.Def_OAIErdos3B141

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedOriginalSampleQuadratureUniformBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "vars" => LayerSamplerVariables G I n B
local notation "degree" => layerSamplerDegree I n
local notation "grid" => allocatedShortAxis (I := I) U basis S.value
local notation "Sample" => CoefficientSamplerArrays (K := vars) I n

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))

def allocatedOriginalSampleInactiveCoefficients
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n) :
    ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ :=
  fun a d => (sample (selected a).1).2 (selected a).2 d

variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (degree (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

noncomputable def allocatedOriginalSampleLiftLip : ℝ≥0 := Fintype.card Input * m

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)

def AllocatedShortIntegerAxis :=
  {a : Σ j : Fin m, Fin (n j) // basisAxisScale (b a.1) a.2 ≤ L ^ (a.1.val + 1)}

noncomputable instance : Fintype (AllocatedShortIntegerAxis U b L) :=
  inferInstanceAs (Fintype {a : Σ j : Fin m, Fin (n j) //
    basisAxisScale (b a.1) a.2 ≤ L ^ (a.1.val + 1)})

def allocatedShortIntegerSelection : AllocatedShortIntegerAxis U b L → Σ j, Fin (n j) :=
  Subtype.val

def allocatedShortIntegerAxisEquiv :
    AllocatedShortIntegerAxis U b L ≃
      {a : LayerSamplerAxis I n // allocatedShortAxis U b L a} where
  toFun a := ⟨⟨a.val.1, Sum.inr a.val.2⟩, a.property⟩
  invFun a := by
    rcases a with ⟨⟨j, i⟩, ha⟩
    cases i with
    | inl i => exact False.elim ha
    | inr i => exact ⟨⟨j, i⟩, ha⟩
  left_inv a := by cases a; rfl
  right_inv a := by
    rcases a with ⟨⟨j, i⟩, ha⟩
    cases i with
    | inl i => exact False.elim ha
    | inr i => rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "degree" => layerSamplerDegree I n
local notation "activeB" => (fun a : Active => B (Subtype.val a))
local notation "activeDegree" => (fun a : Active => degree (Subtype.val a))
local notation "Input" => PrincipalTupleIndex activeB activeDegree
local notation "Output" => (Σ _a : Active, Unit)
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "Active" => {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}
local notation "Input" => (Σ a : Active, B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.CoefficientUniformPerturbationSampling
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_coefficient_ambient_cover_sampling (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (_hq : 0 < q) (_hqP : (q : ℝ) ≤ Real.exp P)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (f : (CoefficientAmbientIndex K J → UnitAddCircle) → ℂ)
    (L B : ℝ≥0) (_hf : LipschitzWith L f) (_hb : ∀ y, ‖f y‖ ≤ B)
    {η Q : ℝ} (_hη : 0 < η) (_hQ : 0 ≤ Q)
    (_hdim : (Fintype.card (CoefficientAmbientIndex K J) : ℝ) ≤ Q)
    (_hLQ : (L : ℝ) ≤ Real.exp Q) (_hηQ : η⁻¹ ≤ Real.exp Q)
    (_hfreqP : Real.exp ((2 * Q + 2) ^ 4) ≤ Real.exp P)
    (_hcoeffP : Real.exp (2 * Q * (2 * Q + 2) ^ 4) * B ≤ Real.exp P),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        f (coefficientAmbientTorus U (affineCoefficientCoverSample U p _hm q (fun k j => (z (k, j) : ℝ))))) -
      (∫ x, f (coefficientAmbientTorus U x) ∂μ)‖ ≤ 2 * η + ε := by
  obtain ⟨A, hA, hcomparison⟩ := exists_affine_coefficient_cover_haar_approximation m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U _ _ μ _ _ p hp hm q hq hqP stride hs R S ρ ε
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    f L B hf hb η Q hη hQ hdim hLQ hηQ hfreqP hcoeffP
  obtain ⟨F, inst, frequency, coeff, _, hfreq, hcoeff, happ⟩ :=
    exists_ambient_torus_fourier_approximation f L B hf hb hη hQ hdim hLQ hηQ
  let _ := inst
  have hcont : Continuous (coefficientAmbientTorus (K := K) U) := by
    apply continuous_pi
    intro a
    exact (continuous_apply a.2).comp ((subspaceAmbientTorus_continuous (U a.1.1)).comp
      ((continuous_apply a.1).comp (coefficientCoordinateTorus_continuous U)))
  have hi : Integrable (fun x => f (coefficientAmbientTorus U x)) μ :=
    Integrable.of_bound (hf.continuous.comp hcont).measurable.aestronglyMeasurable B
      (Filter.Eventually.of_forall (fun x => hb _))
  have he (x) : ‖f (coefficientAmbientTorus U x) - coefficientTorusFourierSum U
      (fun a => coefficientSlotFrequency (fun s i => frequency a ⟨s,i⟩)) coeff x‖ ≤ η := by
    simpa only [coefficientAmbientTorus_character, coefficientTorusFourierSum] using happ (coefficientAmbientTorus U x)
  exact hcomparison hP hn hd U μ (Real.exp_nonneg _) hfreqP
    (fun a => coefficientSlotFrequency (fun s i => frequency a ⟨s,i⟩))
    (fun a => coefficientSlotFrequency_bound _ (fun s i => hfreq a ⟨s,i⟩)) coeff
    (mul_nonneg (Real.exp_nonneg _) B.coe_nonneg) hcoeffP hcoeff p hp hm q hq hqP stride hs
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    (fun x => f (coefficientAmbientTorus U x)) hi hη.le he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_coefficient_ambient_l1_sampling (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (_hq : 0 < q) (_hqP : (q : ℝ) ≤ Real.exp P)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (_hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (f g : (CoefficientAmbientIndex K J → UnitAddCircle) → ℂ)
    (Lf Lg Cf Cg : ℝ≥0) (_hf : LipschitzWith Lf f) (_hg : LipschitzWith Lg g)
    (_hfb : ∀ y, ‖f y‖ ≤ Cf) (_hgb : ∀ y, ‖g y‖ ≤ Cg)
    {η Q : ℝ} (_hη : 0 < η) (_hQ : 0 ≤ Q)
    (_hdim : (Fintype.card (CoefficientAmbientIndex K J) : ℝ) ≤ Q)
    (_hLQ : ((Lf + Lg : ℝ≥0) : ℝ) ≤ Real.exp Q) (_hηQ : η⁻¹ ≤ Real.exp Q)
    (_hfreqP : Real.exp ((2 * Q + 2) ^ 4) ≤ Real.exp P)
    (_hcoeffP : Real.exp (2 * Q * (2 * Q + 2) ^ 4) * (Cf + Cg : ℝ≥0) ≤ Real.exp P)
    {E : ℝ} (_hmass : (∫ x, ‖f (coefficientAmbientTorus U x) -
      g (coefficientAmbientTorus U x)‖ ∂μ) ≤ E),
    ∃ _hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
      selectedResidueDensityMass stride G V (fun z =>
        ‖f (coefficientAmbientTorus U (affineCoefficientCoverSample U p _hm q
          (fun k j => (z (k,j) : ℝ)))) -
          g (coefficientAmbientTorus U (affineCoefficientCoverSample U p _hm q
            (fun k j => (z (k,j) : ℝ))))‖) ≤ E + 2 * η + ε := by
  obtain ⟨A, hA, hsample⟩ := exists_coefficient_ambient_cover_sampling m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P hP hn hd U _ _ μ _ _ p hp hm q hq hqP stride hs R S ρ ε
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    f g Lf Lg Cf Cg hf hg hfb hgb η Q hη hQ hdim hLQ hηQ hfreqP hcoeffP E hmass
  let error := fun z => ‖f z - g z‖
  have hl : LipschitzWith (Lf + Lg) error := by
    simpa only [one_mul, Function.comp_def, Pi.sub_apply] using
      lipschitzWith_one_norm.comp (hf.sub hg)
  have hb (z) : error z ≤ (Cf + Cg : ℝ≥0) :=
    (norm_sub_le _ _).trans (add_le_add (hfb z) (hgb z))
  have hlc : LipschitzWith (Lf + Lg) (fun z => (error z : ℂ)) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    rw [Complex.isometry_ofReal.dist_eq]
    exact hl.dist_le_mul z w
  have hbc (z) : ‖(error z : ℂ)‖ ≤ (Cf + Cg : ℝ≥0) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ error z from norm_nonneg _)]
    exact hb z
  obtain ⟨hZ, he⟩ := hsample hP hn hd U μ p hp hm q hq hqP stride hs
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    (fun z => (error z : ℂ)) (Lf + Lg) (Cf + Cg) hlc hbc hη hQ hdim hLQ hηQ hfreqP hcoeffP
  refine ⟨hZ, ?_⟩
  let law := selectedResidueSmoothPMF stride G V hV hZ
  let sample := fun z : Option K × I → ℤ =>
    error (coefficientAmbientTorus U (affineCoefficientCoverSample U p hm q
      (fun k j => (z (k,j) : ℝ))))
  have hi : Integrable sample law.toMeasure :=
    Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (Cf + Cg : ℝ≥0)
      (Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact hb _))
  have he' : ‖(∫ z, (sample z : ℂ) ∂law.toMeasure) -
      ∫ x, (error (coefficientAmbientTorus U x) : ℂ) ∂μ‖ ≤ 2 * η + ε := by
    rw [PMF.integral_eq_tsum law _ hi.ofReal]
    simpa only [Complex.real_smul] using he
  rw [integral_complex_ofReal, integral_complex_ofReal, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at he'
  rw [selectedResidueDensityMass_integral stride G V hV hZ _ hi]
  have hle := (le_abs_self _).trans he'
  linarith only [hle, hmass]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedModularCanonicalDetectorResourceBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

structure PreparedModularCanonicalDetectorResourceConstants where
  m : ℕ
  Cperiod : ℕ
  Cgrid : ℕ
  Acover : ℕ
  Asample : ℕ
  Cpref : ℕ
  Apert : ℕ
  AmassWindow : ℕ
  Aproj : ℕ
  Aside : ℕ
  Cnative : ℕ
  Anorm : ℕ
  Amarginal : ℕ

structure PreparedModularCanonicalDetectorResources (α : Type*) where
  Q : α
  v : α
  w : α
  Dg : α
  Pproj : α
  coverLog : α
  Pmass : α
  Vlog : α
  Nlog : α
  Pbox : α
  Banalytic : α
  baseAmbient : α
  tq : α
  pq : α
  gridlog : α
  Fpref : α
  sumlog : α
  idealQ : α
  ambient : α
  Psample : α
  Pside : α
  Pnative : α
  nativeBudget : α
  E : α
  full : α
  required : α

namespace PreparedModularCanonicalDetectorResources

def toList {α : Type*} (r : PreparedModularCanonicalDetectorResources α) : List α :=
  [r.Q, r.v, r.w, r.Dg, r.Pproj, r.coverLog, r.Pmass, r.Vlog, r.Nlog, r.Pbox, r.Banalytic, r.baseAmbient, r.tq, r.pq, r.gridlog, r.Fpref, r.sumlog, r.idealQ, r.ambient, r.Psample, r.Pside, r.Pnative, r.nativeBudget, r.E, r.full, r.required]

def total {α : Type*} [AddMonoid α] (r : PreparedModularCanonicalDetectorResources α) : α :=
  r.toList.sum

def map {α β : Type*} (f : α → β) (r : PreparedModularCanonicalDetectorResources α) :
    PreparedModularCanonicalDetectorResources β :=
  { Q := f r.Q,
    v := f r.v,
    w := f r.w,
    Dg := f r.Dg,
    Pproj := f r.Pproj,
    coverLog := f r.coverLog,
    Pmass := f r.Pmass,
    Vlog := f r.Vlog,
    Nlog := f r.Nlog,
    Pbox := f r.Pbox,
    Banalytic := f r.Banalytic,
    baseAmbient := f r.baseAmbient,
    tq := f r.tq,
    pq := f r.pq,
    gridlog := f r.gridlog,
    Fpref := f r.Fpref,
    sumlog := f r.sumlog,
    idealQ := f r.idealQ,
    ambient := f r.ambient,
    Psample := f r.Psample,
    Pside := f r.Pside,
    Pnative := f r.Pnative,
    nativeBudget := f r.nativeBudget,
    E := f r.E,
    full := f r.full,
    required := f r.required }

structure Bounds (r : PreparedModularCanonicalDetectorResources ℝ) (budget : ℝ) : Prop where
  Q : r.Q ∈ Set.Icc 0 budget
  v : r.v ∈ Set.Icc 0 budget
  w : r.w ∈ Set.Icc 0 budget
  Dg : r.Dg ∈ Set.Icc 0 budget
  Pproj : r.Pproj ∈ Set.Icc 0 budget
  coverLog : r.coverLog ∈ Set.Icc 0 budget
  Pmass : r.Pmass ∈ Set.Icc 0 budget
  Vlog : r.Vlog ∈ Set.Icc 0 budget
  Nlog : r.Nlog ∈ Set.Icc 0 budget
  Pbox : r.Pbox ∈ Set.Icc 0 budget
  Banalytic : r.Banalytic ∈ Set.Icc 0 budget
  baseAmbient : r.baseAmbient ∈ Set.Icc 0 budget
  tq : r.tq ∈ Set.Icc 0 budget
  pq : r.pq ∈ Set.Icc 0 budget
  gridlog : r.gridlog ∈ Set.Icc 0 budget
  Fpref : r.Fpref ∈ Set.Icc 0 budget
  sumlog : r.sumlog ∈ Set.Icc 0 budget
  idealQ : r.idealQ ∈ Set.Icc 0 budget
  ambient : r.ambient ∈ Set.Icc 0 budget
  Psample : r.Psample ∈ Set.Icc 0 budget
  Pside : r.Pside ∈ Set.Icc 0 budget
  Pnative : r.Pnative ∈ Set.Icc 0 budget
  nativeBudget : r.nativeBudget ∈ Set.Icc 0 budget
  E : r.E ∈ Set.Icc 0 budget
  full : r.full ∈ Set.Icc 0 budget
  required : r.required ∈ Set.Icc 0 budget

end PreparedModularCanonicalDetectorResources

noncomputable def preparedModularCanonicalDetectorResources {α : Type*} [Semiring α]
    (K : PreparedModularCanonicalDetectorResourceConstants) (P : α) :
    PreparedModularCanonicalDetectorResources α :=
  let Q : α := (P + K.Cperiod) ^ K.Cperiod
  let v : α := P + 8
  let w : α := P + 1
  let Dg : α := 2 * P + K.m * P + (layerTailDegree K.m + 1 : ℕ) + K.m + comparisonProfileBound + 8
  let Pproj : α := 4 * (P + 8) ^ 2
  let coverLog : α := (Pproj + 3 + K.Acover) ^ K.Acover
  let Pmass : α := (Pproj + K.Asample) ^ K.Asample
  let Vlog : α := P ^ 2 * ((layerTailDegree K.m + 1 : ℕ) * P + 1)
  let Nlog : α := (2 * K.m : ℕ) * (2 * P + 16) * (1 + 4 * (2 * P + 8))
  let Pbox : α := 2 * P + 8
  let Banalytic : α := Dg + 4 * P + 32
  let baseAmbient : α := Pproj + coverLog + Vlog + Nlog + Q + (layerTailDegree K.m + 1 : ℕ) * P + 3 * P + comparisonProfileBound + 32
  let tq : α := 1 + Q + (P + 1) + 1
  let pq : α := K.Cgrid + 2 * Q + (P + 1) + 4
  let gridlog : α := slicedGridGeometryLog Dg v w tq + pq
  let Fpref : α := (P + K.Cpref) ^ K.Cpref
  let sumlog : α := Pbox + P + Vlog + Nlog + Q + P
  let idealQ : α := 1 + P * sumlog + (P + comparisonProfileBound + (P + 1) * sumlog) + sumlog + 1
  let ambient : α := affineAmbientPrimitiveBudget baseAmbient idealQ
  let Psample : α := Pmass + ambient + Pproj + 2 * P + K.m * (K.m + 2 : ℕ) + 8
  let Pside : α := Psample + Pproj + Pmass + 2 * P
  let Pnative : α := Dg + gridlog + v + Fpref + 6 * P + Banalytic
  let nativeBudget : α := ((Pnative + K.Cnative) ^ K.Cnative + K.Anorm) ^ K.Anorm
  let E : α := 3 * P + nativeBudget + 30
  let full : α := 4 * (P + 8) ^ 2
  let required : α := (Psample + K.Apert) ^ K.Apert + (Pmass + K.AmassWindow) ^ K.AmassWindow + (Pproj + K.Aproj) ^ K.Aproj + (Pside + K.Aside) ^ K.Aside + (full + E + K.Amarginal) ^ K.Amarginal
  { Q, v, w, Dg, Pproj, coverLog, Pmass, Vlog, Nlog, Pbox, Banalytic, baseAmbient, tq, pq, gridlog, Fpref, sumlog, idealQ, ambient, Psample, Pside, Pnative, nativeBudget, E, full, required }

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedNormalizedCoefficientBounds
namespace OAI

section

namespace Erdos3
open MeasureTheory

theorem continuousPolynomialDensity_coefficient_le_radius {J V : Type*} [Fintype J]
    (e : J → V →₀ ℕ) (T : V → ℝ) (hT : ∀ v, 0 < T v) (P : Finset J) (j₀ : J)
    (hj₀ : j₀ ∉ P) {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    {a : J → ℝ} (ha : continuousPolynomialDensity e T P j₀ R σ a ≠ 0) (j : J) :
    |a j| * monomialScale T (e j) ≤ R :=
  (continuousPolynomialDensity_coefficient_bound e T hT P j₀ hj₀ hR hσ hσ1 ha j).trans
    (by linarith)

theorem allocatedIntegerCoefficient_le_radius {J V : Type*} [Fintype J]
    (P : Finset J) (j₀ : J) (h K L s : ℕ) (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
    (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
    (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
    (R σ : ℝ) (hR : 0 < R) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hgap : L ^ h < K → (principalSamplingGapRatio (principalProfileSize R P.card) * L) ^ h ≤ K)
    (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ tailProfileSize R σ (Fintype.card J) * L)
    (hj₀ : j₀ ∉ P) (he₀ : e j₀ = 0)
    (hprincipal : ∀ j ∈ P, monomialScale T (e j) =
      (integerAxisSideLength h K L (principalProfileSize R P.card) : ℝ) ^ h)
    (j : J) {k : ℤ}
    (hk : k ∈ (allocatedIntegerPolynomialCoordinatePMF P j₀ h K L s hh hK hL T hT hTL e he
      R σ hR hσ hgap hεL j).support) :
    |(k : ℝ) / K| * monomialScale T (e j) ≤ R :=
  (allocatedIntegerCoefficient_bound P j₀ h K L s hh hK hL T hT hTL e he R σ hR hσ hσ1
    hgap hεL hj₀ he₀ hprincipal j hk).trans (by linarith)

end Erdos3

end

end OAI

end


