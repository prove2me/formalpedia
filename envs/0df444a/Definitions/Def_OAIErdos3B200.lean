-- Prove2me | Definitions.Def_OAIErdos3B200
-- name    : OAIErdos3B200
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T09:05:58.067566+00:00
-- url     : https://prove2.me/theorems/607d947e-8fea-432c-b184-81250d91e19c
-- title:
--   OpenAI Erdős-3 split, definitions bundle 201 of 206
-- statement:
--   Definitions bundle 201 of 206 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B199`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 201 available.
--
--   Modules: `OAI.Erdos3.BooleanCubeKernel.exists_physicalRowsProjectedMean_ambient`, `OAI.Erdos3.BooleanCubeKernel.exists_translated_physical_jet_l1_perturbation`, `OAI.Erdos3.BooleanCubeKernel.finiteProbability_ambient_mean`, `OAI.Erdos3.BooleanCubeKernel.physicalRowsAmbientFintype`, `OAI.Erdos3.BooleanCubeKernel.physicalRowsAmbientToStandard`, `OAI.Erdos3.BooleanCubeKernel.physicalRowsAmbientToStandard_eq`, `OAI.Erdos3.BooleanCubeKernel.physicalRowsAmbientToStandard_lipschitz`, `OAI.Erdos3.BooleanCubeKernel.physicalRowsProjectedMean`, `OAI.Erdos3.VectorPolynomial.exists_allocated_rows_ambient_projected_family_multiple`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B198

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRecenteredL1Source
namespace OAI

section

namespace Erdos3
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical

variable {X K : Type*} [Fintype X] [Fintype K] {dim : ℕ}
variable (stride : X → ℕ) (hs : ∀ x, 0 < stride x)
variable (root : K → ℤ) (D : Matrix (Fin dim) K ℤ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option K) X stride))
variable (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
variable (H T : X → ℝ) (hH : ∀ x, 0 < H x) (hT : ∀ x, 0 < T x)
variable {Wsp Lsp : ℝ} (hLsp : 0 < Lsp) (hsc : ∀ x, H x = (1 + Wsp) * T x)
variable (hrows : ∀ x i, (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) ≤ H x)
variable (hprofile : ∀ x, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H x)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical

variable {X K : Type*} [Fintype X] [Fintype K] {dim : ℕ}
variable (stride : X → ℕ) (hs : ∀ x, 0 < stride x)
variable (root : K → ℤ) (D : Matrix (Fin dim) K ℤ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option K) X stride))
variable (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
variable (H T : X → ℝ) (hH : ∀ x, 0 < H x) (hT : ∀ x, 0 < T x)
variable {Wsp Lsp : ℝ} (hLsp : 0 < Lsp) (hsc : ∀ x, H x = (1 + Wsp) * T x)
variable (hrows : ∀ x i, (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) ≤ H x)
variable (hprofile : ∀ x, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H x)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory
open scoped BigOperators Classical

variable {X K : Type*} [Fintype X] [Fintype K] {dim : ℕ}
variable (stride : X → ℕ) (hs : ∀ x, 0 < stride x)
variable (root : K → ℤ) (D : Matrix (Fin dim) K ℤ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option K) X stride))
variable (V : Option K × X → ℝ) (hV : ∀ z, 0 < V z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
variable (H T : X → ℝ) (hH : ∀ x, 0 < H x) (hT : ∀ x, 0 < T x)
variable {Wsp Lsp : ℝ} (hLsp : 0 < Lsp) (hsc : ∀ x, H x = (1 + Wsp) * T x)
variable (hrows : ∀ x i, (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) ≤ H x)
variable (hprofile : ∀ x, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H x)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_translated_physical_jet_l1_perturbation (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I : Type*}
    [Fintype I] [DecidableEq I]
    {J O : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset (Fin dim))
    (_hinj : ∀ j, Function.Injective (rows j))
    (_hrows : ∀ j t, (rows j t).card ≤ j.val + 1)
    {T : ℝ} (_hP : 0 ≤ T) (_hn : (Fintype.card I : ℝ) ≤ T)
    (_hd : (Fintype.card (Option (Fin dim) × I) : ℝ) ≤ T)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (base : I → ℤ) (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (_hq : 0 < q) (_hqP : (q : ℝ) ≤ Real.exp T)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp T) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp T) (_hεP : 1 / ε ≤ Real.exp T)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((T + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((T + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option (Fin dim)) I stride)) (_hG : G.Nonempty)
    (V : Option (Fin dim) × I → ℝ) (_hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (f g : (JetAmbientIndex O J → UnitAddCircle) → ℂ)
    (Lf Lg Cf Cg : ℝ≥0) (_hf : LipschitzWith Lf f) (_hg : LipschitzWith Lg g)
    (_hfb : ∀ y, ‖f y‖ ≤ Cf) (_hgb : ∀ y, ‖g y‖ ≤ Cg)
    {η : ℝ} (_hη : 0 < η)
    (_hdim : (Fintype.card (CoefficientAmbientIndex (Fin dim) J) : ℝ) ≤ T)
    (_hLf : (Lf : ℝ) ≤ Real.exp T) (_hLg : (Lg : ℝ) ≤ Real.exp T)
    (_hCf : (Cf : ℝ) ≤ Real.exp T) (_hCg : (Cg : ℝ) ≤ Real.exp T)
    (_hjet : (∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1)) : ℝ≥0) : ℝ≥0) ≤ Real.exp T)
    (_hηT : η⁻¹ ≤ Real.exp T)
    (ideal : EuclideanJetLayers U O → ℂ) (_hi : Measurable ideal)
    {δ : ℝ} (_happrox : ∀ y, ‖ideal y - g (coveredJetAmbientTorus U 1 y)‖ ≤ δ)
    {E : ℝ} (_hmass : (∫ y, ‖f (coveredJetAmbientTorus U 1 y) - ideal y‖
        ∂Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) ≤ E),
    ∃ _hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
      selectedResidueDensityMass stride G V (fun z =>
        ‖f (coveredJetAmbientTorus U 1
          (physicalCubeRowSample U q rows p _hm (translatePhysicalCube base (standardPhysicalCubeOutput z)))) -
          ideal (physicalCubeRowSample U q rows p _hm (translatePhysicalCube base (standardPhysicalCubeOutput z)))‖) ≤ E + 2 * δ + (2 * η + ε) := by
  obtain ⟨A, hA, hsample⟩ := exists_physical_jet_l1_perturbation_budgeted m dim
  refine ⟨A, hA, ?_⟩
  intro I _ _ J O _ _ rows hinj hrows T hT hn hd U _ _ _ μ _ _ ν _ _ base p hp hm q hq hqT stride hs R S ρ ε
    hS hST hρ hε hρT hεT hstride H hsize hrank hR G hG V hV hwidth
    f g Lf Lg Cf Cg hf hg hfb hgb η hη hdim hLf hLg hCf hCg hjet hηT ideal hi δ happ E hmass
  let p' := fun j => translate (fun x => (base x : ℝ)) (p j)
  have hp' (j) : DegreeLE (1 : I → ℕ) (j.val + 1) (p' j) :=
    degreeLE_translate _ (fun _ => Nat.zero_lt_one) _ _ (hp j)
  have hm' (j) : ∀ ex, coefficients (p' j) ex ∈ U j :=
    coefficients_translate_mem (U j) _ (p j) (hm j)
  have hrank' (j) : HasLayerSamplingRank (j.val + 1) H R (U j) (p' j) :=
    (hasLayerSamplingRank_translate_iff _ _ H R (U j) (p j) (hp j)).mpr (hrank j)
  obtain ⟨hZ, he⟩ := hsample rows hinj hrows hT hn hd U μ ν p' hp' hm' q hq hqT stride hs
    hS hST hρ hε hρT hεT hstride H hsize hrank' hR G hG V hV hwidth
    f g Lf Lg Cf Cg hf hg hfb hgb hη hdim hLf hLg hCf hCg hjet hηT ideal hi happ hmass
  refine ⟨hZ, ?_⟩
  have hid (z : Option (Fin dim) × I → ℤ) :
      physicalCubeRowSample U q rows p' hm' (standardPhysicalCubeOutput z) =
        physicalCubeRowSample U q rows p hm (translatePhysicalCube base (standardPhysicalCubeOutput z)) :=
    physicalCubeRowSample_translate U q rows p hm base _
  simp only [hid] at he
  exact he

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "sides" => allocatedPrincipalSides B U b S

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)


end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRowsAmbientProjectedFamilyMultiple
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.BooleanCubeKernel
open MeasureTheory VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {Y : Type*} [Fintype Y] (law : FiniteProbabilityWeights Y)
local notation "Row" => (fun j : Fin m => {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (Fin.val j + 1)})
variable (g : Y → EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)

noncomputable def physicalRowsProjectedMean (law : FiniteProbabilityWeights Y) (g : Y → EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ) (y : EuclideanJetLayers U Row) : ℂ :=
  law.complexMean (fun a => (g a (physicalRowsToStandard U y) : ℂ))

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel
open VectorPolynomial
open scoped Classical BigOperators NNReal

attribute [local irreducible] boundedBooleanJetRows

variable {m dim : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
local notation "Row" => (fun j : Fin m =>
  {s : Finset (Fin dim) // s ∈ boundedBooleanJetRows (Fin dim) (Fin.val j + 1)})
noncomputable local instance (priority := 2000) physicalRowsAmbientFintype (j : Fin m) : Fintype (Row j) :=
  Finset.Subtype.fintype (boundedBooleanJetRows (Fin dim) (j.val + 1))
local notation "Std" => (fun j : Fin m => BoundedBooleanJet (Fin dim) (Fin.val j + 1))

noncomputable def physicalRowsAmbientToStandard
    (z : JetAmbientIndex Row J → UnitAddCircle) : JetAmbientIndex Std J → UnitAddCircle :=
  fun a => z ⟨a.1, (boundedBooleanJetRowsEquiv (Fin dim) (a.1.val + 1)).symm a.2.1, a.2.2⟩

theorem physicalRowsAmbientToStandard_lipschitz :
    LipschitzWith 1 (physicalRowsAmbientToStandard (m := m) (dim := dim) (J := J)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro a
  exact dist_le_pi_dist z w _

theorem physicalRowsAmbientToStandard_eq (U : ∀ j, Submodule ℝ (J j → ℝ))
    (y : EuclideanJetLayers U Row) :
    physicalRowsAmbientToStandard (coveredJetAmbientTorus U 1 y) =
      coveredJetAmbientTorus U 1 (physicalRowsToStandard U y) := rfl

theorem finiteProbability_ambient_mean
    {Y X A B : Type*} [Fintype Y] [PseudoEMetricSpace A] [PseudoEMetricSpace B]
    (law : FiniteProbabilityWeights Y) (g : Y → X → ℝ) (F : Y → B → ℝ)
    (r : A → B) (q : X → A) {L C : ℝ≥0}
    (hr : LipschitzWith 1 r) (hF : ∀ a, LipschitzWith L (F a))
    (hFb : ∀ a z, F a z ∈ Set.Icc (0 : ℝ) C)
    (hFv : ∀ a x, g a x = F a (r (q x))) :
    ∃ G : A → ℂ, LipschitzWith L G ∧ (∀ z, ‖G z‖ ≤ C) ∧
      ∀ x, law.complexMean (fun a => (g a x : ℂ)) = G (q x) := by
  let R := fun z : A => law.mean (fun a => F a (r z))
  have hR : LipschitzWith L R := by
    apply law.mean_lipschitz_uniform_emetric
    intro a
    simpa only [mul_one, Function.comp_def] using (hF a).comp hr
  have hRb (z : A) : R z ∈ Set.Icc (0 : ℝ) C :=
    ⟨law.mean_nonneg (fun a => (hFb a _).1),
      (law.mean_mono (fun a => (hFb a _).2)).trans_eq (law.mean_const _)⟩
  refine ⟨fun z => (R z : ℂ), ?_, ?_, ?_⟩
  · simpa only [one_mul, Function.comp_def] using Complex.isometry_ofReal.lipschitz.comp hR
  · intro z
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hRb z).1]
    exact (hRb z).2
  · intro x
    simp only [hFv, law.complexMean_ofReal]
    rfl

theorem exists_physicalRowsProjectedMean_ambient
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {Y : Type*} [Fintype Y] (law : FiniteProbabilityWeights Y)
    (g : Y → EuclideanJetLayers U Std → ℝ)
    (F : Y → (JetAmbientIndex Std J → UnitAddCircle) → ℝ)
    {L C : ℝ≥0} (hF : ∀ a, LipschitzWith L (F a))
    (hFb : ∀ a z, F a z ∈ Set.Icc (0 : ℝ) C)
    (hFv : ∀ a y, g a y = F a (coveredJetAmbientTorus U 1 y)) :
    ∃ G : (JetAmbientIndex Row J → UnitAddCircle) → ℂ,
      LipschitzWith L G ∧ (∀ z, ‖G z‖ ≤ C) ∧
      ∀ y, physicalRowsProjectedMean U law g y = G (coveredJetAmbientTorus U 1 y) := by
  have he (a : Y) (y : EuclideanJetLayers U Row) :
      g a (physicalRowsToStandard U y) =
        F a (physicalRowsAmbientToStandard (coveredJetAmbientTorus U 1 y)) :=
    (hFv a (physicalRowsToStandard U y)).trans
      (congrArg (F a) (physicalRowsAmbientToStandard_eq U y).symm)
  obtain ⟨G, hG, hGb, hGv⟩ := finiteProbability_ambient_mean
    (X := EuclideanJetLayers U Row)
    (A := JetAmbientIndex Row J → UnitAddCircle)
    (B := JetAmbientIndex Std J → UnitAddCircle)
    law (fun a (y : EuclideanJetLayers U Row) => g a (physicalRowsToStandard U y)) F
    (physicalRowsAmbientToStandard (m := m) (dim := dim) (J := J))
    (coveredJetAmbientTorus (O := Row) U 1)
    physicalRowsAmbientToStandard_lipschitz hF hFb he
  refine ⟨G, ?_, hGb, hGv⟩
  convert hG using 1
  congr 1
  exact Subsingleton.elim _ _

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_allocated_rows_ambient_projected_family_multiple (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox (Fin q) S.value)
    {P : ℝ} (_hP : 0 ≤ P) (_hG : (Fintype.card G : ℝ) ≤ P)
    (_hc : ∀ g, |(c (.inl g) : ℝ)| ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M),
    ∀ (period : ℕ), 0 < period → (period : ℝ) ≤ Real.exp P →
    ∃ d : ℕ, period ∣ d ∧ 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + (q + 2 : ℕ) + A) ^ A) ∧
    ∀ [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin q)) U)] [BorelSpace (SiteTorus (Finset (Fin q)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    [CompactSpace (CoefficientTorus (K := Fin q) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin q) U)]
    [BorelSpace (CoefficientTorus (K := Fin q) U)]
    (μrows : Measure (CoefficientTorus (K := Fin q) U))
    [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows],
    let density := allocatedCoefficientDensity B U b hb o hR hσ S
    let cap := (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let cover := quotientIntegerCover (coefficientIntegerLattice U) d
    let ξ := Measure.pi (fun j => Measure.pi (fun _ : {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (j.val + 1)} => ν j))
    let densityLip := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) *
      allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V *
      allocatedAmbientFactorCap (G := G) B R σ S.value V ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let sectionLip := (Fintype.card (Finset (Fin q)) : ℝ≥0) *
      Real.toNNReal (Real.exp ((P + (q + 2 : ℕ) + A) ^ A))
    let reconstructionLip := ∑ j : Fin m, (Fintype.card (BoundedBooleanJet (Fin q) (j.val + 1)) : ℝ≥0)
    let Row := fun j : Fin m => {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (j.val + 1)}
    let Tuple := PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U b S)
    ∃ g : Tuple → EuclideanJetLayers U Row → ℝ,
      (∀ y, Continuous (g y)) ∧
      (∀ y z, g y z ∈ Set.Icc (0 : ℝ) cap) ∧
      (∀ y, Integrable (g y) ξ) ∧
      (∀ y, (∫ z, g y z ∂ξ) = 1) ∧
      (∀ y, (realDensityMeasure μ (fun z => density (cover z))).map
        (euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U b S c x y)
          (allocatedPhysicalCubeDirections B U b S x y)
          (fun j => (Subtype.val : Row j → Finset (Fin q)))) = realDensityMeasure ξ (g y)) ∧
      (∀ y, physicalDensityProjection U (allocatedPhysicalCubeRoot B U b S c x y)
        (allocatedPhysicalCubeDirections B U b S x y) d density
        (fun z => g y ((physicalRowsStandardEquiv U).symm z))) ∧
      (∀ y, ∃ F : (JetAmbientIndex Row J → UnitAddCircle) → ℂ,
        LipschitzWith (densityLip * sectionLip * reconstructionLip) F ∧
        (∀ z, ‖F z‖ ≤ cap) ∧
        ∀ z, (g y z : ℂ) = F (coveredJetAmbientTorus U 1 z)) ∧
      ∀ law : FiniteProbabilityWeights Tuple,
        ∃ F : (JetAmbientIndex Row J → UnitAddCircle) → ℂ,
          LipschitzWith (densityLip * sectionLip * reconstructionLip) F ∧
          (∀ z, ‖F z‖ ≤ cap) ∧
          ∀ z, law.complexMean (fun y => (g y z : ℂ)) = F (coveredJetAmbientTorus U 1 z) := by
  obtain ⟨A, hA, hcover⟩ := exists_allocated_ambient_projected_density_multiple m q
  refine ⟨A, hA, ?_⟩
  intro G _ I _ n B _ J _ U b R σ S c x P hP hG hc hL M hperiod period hp hpP
  obtain ⟨d, hdiv, hd, hdb, hcover⟩ := hcover B U b S c x hP hG hc hL hperiod period hp hpP
  refine ⟨d, hdiv, hd, hdb, ?_⟩
  intro _ _ _ _ _ _ hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _
    _ _ _ μrows _ _ density cap cover ξ densityLip sectionLip reconstructionLip Row Tuple
  have hex (y : Tuple) := hcover y hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ ν
  choose g F hgc hgb hgi hgm hglaw hprojection hFb hFl hvalue using hex
  let rowG := fun (y : Tuple) (z : EuclideanJetLayers U Row) => g y (physicalRowsToStandard U z)
  have hpres := physicalRowsToStandard_measurePreserving U μrows ν
  refine ⟨rowG, fun y => (hgc y).comp (physicalRowsToStandard_continuous U),
    fun y z => hgb y _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    convert hpres.integrable_comp_of_integrable (hgi y) using 1
    congr! (transparency := .reducible)
    dsimp only [ξ]
    congr! (transparency := .reducible)
  · intro y
    have he := hpres.integral_comp (physicalRowsStandardEquiv U).measurableEmbedding (g y)
    convert he.trans (hgm y) using 1
    congr! (transparency := .reducible)
  · intro y
    exact physicalRows_projected_density_law U μrows ν _ _ _ (g y) (hglaw y)
  · intro y
    exact hprojection y
  · intro y
    let pointLaw := FiniteProbabilityWeights.pointWeights y
    obtain ⟨Fmean, hFm, hFmb, hFmv⟩ := exists_physicalRowsProjectedMean_ambient U pointLaw g F
      (C := allocatedAmbientFactorCap (G := G) B R σ S.value V ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m))
      hFl (by simpa only [NNReal.coe_pow] using hFb) hvalue
    refine ⟨Fmean, hFm, ?_, ?_⟩
    · simpa only [NNReal.coe_pow] using hFmb
    · intro z
      simpa only [physicalRowsProjectedMean, pointLaw, FiniteProbabilityWeights.pointWeights_complexMean] using hFmv z
  · intro law
    obtain ⟨Fmean, hFm, hFmb, hFmv⟩ := exists_physicalRowsProjectedMean_ambient U law g F
      (C := allocatedAmbientFactorCap (G := G) B R σ S.value V ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m))
      hFl (by simpa only [NNReal.coe_pow] using hFb) hvalue
    refine ⟨Fmean, ?_, ?_, hFmv⟩
    · exact hFm
    · simpa only [NNReal.coe_pow] using hFmb

end Erdos3.VectorPolynomial

end

end OAI

end


