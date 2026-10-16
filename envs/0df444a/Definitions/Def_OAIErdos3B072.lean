-- Prove2me | Definitions.Def_OAIErdos3B072
-- name    : OAIErdos3B072
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-15T18:23:09.761811+00:00
-- url     : https://prove2.me/theorems/db0c0e87-b49a-4b6e-946d-3da6e621107d
-- title:
--   OpenAI Erdős-3 split, definitions bundle 73 of 1335
-- statement:
--   Definitions bundle 73 of 1335 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B071`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 73 available.
--
--   Modules: `OAI.Erdos3.VectorPolynomial.AllocatedCenteredFramedRecoveredSampleAt`, `OAI.Erdos3.VectorPolynomial.AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_low_residual`, `OAI.Erdos3.VectorPolynomial.AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_remainder`, `OAI.Erdos3.VectorPolynomial.AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_residual`, `OAI.Erdos3.VectorPolynomial.AllocatedCenteredRecoveredSampleReadAt.jointFrame`, `OAI.Erdos3.VectorPolynomial.allocatedActualModulusBad_jointFrame`, `OAI.Erdos3.VectorPolynomial.allocatedActualPrimeBad_depth_jointFrame`, `OAI.Erdos3.VectorPolynomial.allocatedActualPrimeBad_product_jointFrame`, `OAI.Erdos3.VectorPolynomial.allocatedCentered_badProduct_probability_le`, `OAI.Erdos3.VectorPolynomial.allocatedCentered_joint_positive_rankCertificate`, `OAI.Erdos3.VectorPolynomial.allocatedCentered_joint_weight_measurable`, `OAI.Erdos3.VectorPolynomial.allocatedCentered_recovered_sample_ae`, `OAI.Erdos3.VectorPolynomial.allocatedFixedScaleJoint_collision_small`, `OAI.Erdos3.VectorPolynomial.allocatedJointFrameRead`, `OAI.Erdos3.VectorPolynomial.allocatedJointFrameRead_badDepth`, `OAI.Erdos3.VectorPolynomial.allocatedJointFrameRead_deck`, `OAI.Erdos3.VectorPolynomial.allocatedJointFrameRead_noise`, `OAI.Erdos3.VectorPolynomial.allocatedJointFrameRead_noise_some`, `OAI.Erdos3.VectorPolynomial.allocatedJointFrameRead_projection`, `OAI.Erdos3.VectorPolynomial.allocatedJointFrameRead_rankBad`, `OAI.Erdos3.VectorPolynomial.allocatedJointFrameRead_reduce`, `OAI.Erdos3.VectorPolynomial.allocatedLayerSupported_polynomial_bound`, `OAI.Erdos3.VectorPolynomial.allocatedOriginalCongruenceTop_congr_slopes`, `OAI.Erdos3.VectorPolynomial.allocatedRecoveredIntegerFullChart`, `OAI.Erdos3.VectorPolynomial.allocatedRecoveredIntegerFullChart_spatial`, `OAI.Erdos3.VectorPolynomial.allocatedRecoveredIntegerFullChart_support`, `OAI.Erdos3.VectorPolynomial.allocatedReplaceReadNoise_eq_jointFrame`, `OAI.Erdos3.VectorPolynomial.allocatedReplaceReadNoise_primeBad`, `OAI.Erdos3.VectorPolynomial.allocatedResidueModulusBad_congr_slopes`, `OAI.Erdos3.VectorPolynomial.allocatedZeroLayerCenterLift`, `OAI.Erdos3.VectorPolynomial.allocatedZeroLayerFramedRead`, `OAI.Erdos3.VectorPolynomial.allocatedZeroLayerFramedRead_noise`, `OAI.Erdos3.VectorPolynomial.allocatedZeroLayerSample`, `OAI.Erdos3.VectorPolynomial.cast_jointIntegerPhysicalSite_eq_frame`, `OAI.Erdos3.VectorPolynomial.coefficientTorus_zeroLayer_subsingleton`, `OAI.Erdos3.VectorPolynomial.eval_jointIntegerPhysicalSite_eq_frame`, `OAI.Erdos3.VectorPolynomial.exists_allocatedCentered_badProduct_measurable_tail`, `OAI.Erdos3.VectorPolynomial.exists_allocatedCentered_badProduct_surrogate`, `OAI.Erdos3.VectorPolynomial.exists_allocatedCentered_measurable_framed_bad_tail`, `OAI.Erdos3.VectorPolynomial.exists_allocatedCentered_measurable_unframed_bad_tail`, `OAI.Erdos3.VectorPolynomial.exists_allocated_narrow_joint_collision`, `OAI.Erdos3.VectorPolynomial.jointIntegerFullChart`, `OAI.Erdos3.VectorPolynomial.jointIntegerFullChart_spatial`, `OAI.Erdos3.VectorPolynomial.jointIntegerFullChart_support`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B210
import Definitions.Def_OAIErdos3B1327

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCenteredMeasurableBadTail
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
variable (rankC : ℝ)
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable (center : C → ∀ j, U j) (hcenter : Measurable center)
variable (base : Ω → X → ℤ)
variable (noise : Ω → Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (law : C → FiniteProbabilityWeights Ω)
variable (read : C → Ω → AllocatedActualCoefficientIndex G X I E n B → ℤ)
variable (hcertificate : ∀ c x, 0 < (law c).weight x →
  AllocatedPhysicalRankReadCertificate B U bW b hb o
    (fun j => translate (fun v => (base x v : ℝ)) (subtractConstant (center c j).val (poly j)))
    (fun j => coefficients_translate_mem (U j) (fun v => (base x v : ℝ)) _
      (coefficients_subtractConstant_mem (U j) (center c j) (poly j) (hm j)))
    inactive spatial kernel block rankC (noise x) (read c x))
variable (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ) (cutoff : ℕ)

include hcenter hcertificate in

theorem exists_allocatedCentered_badProduct_surrogate :
    ∃ test : Set (C × Ω), MeasurableSet test ∧ ∀ c x, 0 < (law c).weight x →
      (cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A
        (allocatedActualPrimeBad inactive spatial kernel block P rankC) p (read c x) ↔
      (c,x) ∈ test) := by
  let surrogate : Ω → ℕ → ℕ → C → Prop := fun x p a c =>
    if hp : p ∈ P then
      let : NeZero p := inferInstanceAs (NeZero (⟨p,hp⟩ : P).val)
      allocatedPhysicalPrimePowerEvent B U bW b hb o
        (fun j => translate (fun v => (base x v : ℝ)) (subtractConstant (center c j).val (poly j)))
        (fun j => coefficients_translate_mem (U j) (fun v => (base x v : ℝ)) _
          (coefficients_subtractConstant_mem (U j) (center c j) (poly j) (hm j)))
        inactive rankC (noise x) p a
    else False
  have hsurrogate (x : Ω) (p : ℕ) (hp : p ∈ P) (a : ℕ) :
      MeasurableSet {c | surrogate x p a c} := by
    let : NeZero p := inferInstanceAs (NeZero (⟨p,hp⟩ : P).val)
    simp only [surrogate, dif_pos hp]
    exact allocatedPhysicalPrimePowerEvent_center_measurableSet B U bW b hb o poly hm
      inactive rankC center hcenter (base x) (noise x) p a
  let test : Set (C × Ω) := {z | cutoff <
    ∏ p ∈ P, p ^ largestTestedBadDepth A (surrogate z.2) p z.1}
  refine ⟨test, ?_, ?_⟩
  · apply centeredFinite_event_measurableSet
    intro x
    exact largestBadPrimeProduct_tail_measurableSet P A (surrogate x)
      (fun p hp a _ => hsurrogate x p hp a) cutoff
  · intro c x hx
    have heq : (∏ p ∈ P, p ^ largestTestedBadDepth A
        (fun p a c => allocatedActualPrimeBad inactive spatial kernel block P rankC p a (read c x)) p c) =
        ∏ p ∈ P, p ^ largestTestedBadDepth A (surrogate x) p c := by
      apply largestBadPrimeProduct_congr_on_tested
      intro p hp a _ _
      let : NeZero p := inferInstanceAs (NeZero (⟨p,hp⟩ : P).val)
      simp only [surrogate, dif_pos hp]
      have hactual := allocatedActualPrimeBad_iff_modulusBad inactive spatial kernel block P rankC
        ⟨p,hp⟩ a (read c x)
      exact hactual.trans ((hcertificate c x hx).primePowerEvent_iff B U bW b hb o _ _
        inactive rankC spatial kernel block p a).symm
    change (cutoff < _) ↔ (cutoff < _)
    exact congrArg (fun v : ℕ => cutoff < v) heq |>.to_iff

include hcenter hcertificate in

theorem allocatedCentered_badProduct_probability_le
    (μ : Measure C) [IsProbabilityMeasure μ]
    (hweight : ∀ x, Measurable (fun c => (law c).weight x))
    {ε : ℝ} (hbound : ∀ c, (law c).mean (fun x =>
      if cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A
        (allocatedActualPrimeBad inactive spatial kernel block P rankC) p (read c x)
      then (1 : ℝ) else 0) ≤ ε) :
    (centeredFiniteProbabilityMeasure μ law).real {z | cutoff < ∏ p ∈ P,
      p ^ largestTestedBadDepth A (allocatedActualPrimeBad inactive spatial kernel block P rankC)
        p (read z.1 z.2)} ≤ ε := by
  obtain ⟨test, htest, heq⟩ := exists_allocatedCentered_badProduct_surrogate B U bW b hb o
    poly hm inactive spatial kernel block rankC center hcenter base noise law read hcertificate P A cutoff
  apply centeredFiniteProbabilityMeasure_real_event_le_of_support μ law hweight _ test htest heq
  intro c
  convert hbound c using 1
  apply congrArg (law c).mean
  funext x
  simp only [Set.mem_ofPred_eq]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
variable (rankC : ℝ)
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable (center : C → ∀ j, U j) (hcenter : Measurable center)
variable (base : Ω → X → ℤ)
variable (noise : Ω → Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (law : C → FiniteProbabilityWeights Ω)
variable (read : C → Ω → AllocatedActualCoefficientIndex G X I E n B → ℤ)
variable (hcertificate : ∀ c x, 0 < (law c).weight x →
  AllocatedPhysicalRankReadCertificate B U bW b hb o
    (fun j => translate (fun v => (base x v : ℝ)) (subtractConstant (center c j).val (poly j)))
    (fun j => coefficients_translate_mem (U j) (fun v => (base x v : ℝ)) _
      (coefficients_subtractConstant_mem (U j) (center c j) (poly j) (hm j)))
    inactive spatial kernel block rankC (noise x) (read c x))
variable (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ) (cutoff : ℕ)

include hcenter hcertificate in

theorem exists_allocatedCentered_badProduct_measurable_tail
    (μ : Measure C) [IsProbabilityMeasure μ]
    (hweight : ∀ x, Measurable (fun c => (law c).weight x))
    {ε : ℝ} (hbound :
      (centeredFiniteProbabilityMeasure μ law).real {z | cutoff < ∏ p ∈ P,
        p ^ largestTestedBadDepth A (allocatedActualPrimeBad inactive spatial kernel block P rankC)
          p (read z.1 z.2)} ≤ ε) :
    ∃ bad : Set (C × Ω), MeasurableSet bad ∧
      (centeredFiniteProbabilityMeasure μ law).real bad ≤ ε ∧
      (∀ c x, 0 < (law c).weight x →
        (cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A
          (allocatedActualPrimeBad inactive spatial kernel block P rankC) p (read c x) ↔
        (c,x) ∈ bad)) ∧
      {z | cutoff < ∏ p ∈ P,
        p ^ largestTestedBadDepth A (allocatedActualPrimeBad inactive spatial kernel block P rankC)
          p (read z.1 z.2)} =ᵐ[centeredFiniteProbabilityMeasure μ law] bad := by
  obtain ⟨bad, hbad, heq⟩ := exists_allocatedCentered_badProduct_surrogate B U bW b hb o
    poly hm inactive spatial kernel block rankC center hcenter base noise law read hcertificate P A cutoff
  have hae : {z | cutoff < ∏ p ∈ P,
      p ^ largestTestedBadDepth A (allocatedActualPrimeBad inactive spatial kernel block P rankC)
        p (read z.1 z.2)} =ᵐ[centeredFiniteProbabilityMeasure μ law] bad :=
    (centeredFiniteProbabilityMeasure_ae_positive_weight μ law hweight).mono
      (fun z hz => propext (heq z.1 z.2 hz))
  refine ⟨bad, hbad, ?_, heq, hae⟩
  simpa only [measureReal_def, measure_congr hae] using hbound

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedNarrowJointCollision
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
variable (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
variable (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
variable (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)

local notation "K" => LayerSamplerVariables G I n B

include hC hV hσ1 hCinv hchart hsmall in

theorem allocatedFixedScaleJoint_collision_small
    {X Tsite : Type*} [Fintype X] [DecidableEq X] [Fintype Tsite] [DecidableEq Tsite]
    (point : (X → ℤ) → (Option K × X → ℤ) → CoefficientTorus («K» := K) U)
    {P δ : ℝ} (hP : 0 ≤ P) (hm : (m : ℝ) ≤ P)
    (hK : (Fintype.card K : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent K (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hSP : (S.value : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
    (site : Tsite → K → ℤ) (hsite : Function.Injective site) (i : X)
    (hδ : 0 < δ) (hδP : δ⁻¹ ≤ Real.exp P)
    (hbound : ∀ s k, |(site s k : ℝ)| ≤ Real.exp P)
    (modulus : X → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (hmodP : (modulus i : ℝ) ≤ Real.exp P)
    (cells : Finset (ColumnResiduePattern (Option K) X modulus)) (hcells : cells.Nonempty)
    (W : Option K × X → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus cells W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z)
    {ρ N : ℝ} (hρ : 0 < ρ) (hρP : 1/ρ ≤ Real.exp (spatialSamplingBudget P))
    (hN : Real.exp (allocatedFixedScaleCollisionLog m P) ≤ N)
    (hwidth : ∀ k, ρ*N ≤ W (some k,i)) :
    let D := fun a z => allocatedCoefficientDensity B U b hb o hR hσ S (point a z)
    ∀ (hD0 : ∀ a z, 0 ≤ D a z)
      (hD : 0 < selectedJointDensityMass bases modulus cells W D),
    1/2 ≤ selectedJointDensityMass bases modulus cells W D →
    (selectedJointFiniteLaw bases hbases modulus cells W hW hZ D hD0 hD).mean
      (fun z => noninjectivityIndicator
        (fun t => jointIntegerPhysicalSite (site t) (z.1.val,z.2.val))) ≤ δ := by
  intro D hD0 hD hlower
  apply selectedJointFiniteLaw_collision_small_with_cap bases hbases site hsite i hP hδ hδP
    hK hbound modulus hmodulus hmodP cells hcells W hW hZ hscale hρ hρP
    hN hwidth D hD0 hD hlower
  intro a z
  exact allocatedCoefficientDensity_fixedScale_le_exp B U b hb o hR hσ S C V hC hV
    hσ1 Cinv hCinv hchart hsmall hP hm hK hRP hσP hcount hI hn hJ hAP hSP hCP hVP _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem exists_allocated_narrow_joint_collision (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G Sites : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype G] [Fintype Sites] [DecidableEq Sites]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U b R σ)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    {P δ : ℝ} (_hP : 0 ≤ P) (_hm : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (_hSP : (S.value : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
    (site : Sites → LayerSamplerVariables G I n B → ℤ) (_hsite : Function.Injective site)
    (_hδ : 0 < δ) (_hδP : δ⁻¹ ≤ Real.exp P)
    {W τ ξ : ℝ} (_hW : 0 ≤ W) (_hWP : W ≤ Real.exp P)
    (_hroot : ∀ q, (∑ k, |(site q k : ℝ)|) ≤ W)
    (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N stride : X → ℕ) (_hs : ∀ i, 0 < stride i) (_hsP : ∀ i, (stride i : ℝ) ≤ Real.exp P)
    (_hsize : ∀ i, Real.exp ((P + A)^A) ≤ (N i : ℝ))
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (_hcells : cells.Nonempty) (bases : Finset (X → ℤ)) (hbases : bases.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    ∀ (hwidths : ∀ z, 0 < widths z)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
      (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U),
    let density := allocatedCenteredJointDensity B U b hb o hR hσ S poly hmem center
    ∀ (hD : 0 < selectedJointDensityMass bases stride cells widths density),
    1/2 ≤ selectedJointDensityMass bases stride cells widths density →
    (selectedJointFiniteLaw bases hbases stride cells widths hwidths hmass density
      (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hmem center) hD).mean
      (fun z => noninjectivityIndicator
        (fun q => jointIntegerPhysicalSite (site q) (z.1.val,z.2.val))) ≤ δ := by
  obtain ⟨A₁, _, hcollisionBudget⟩ := exists_allocatedFixedScaleCollisionLog_bound m
  obtain ⟨A, hA, hbudget⟩ := exists_narrow_sampler_threshold 0 A₁
  refine ⟨A, hA, ?_⟩
  intro X G Sites _ _ _ _ _ _ I _ n B _ J _ U b hb o R σ hR hσ S _
    C V hC hV hσ1 Cinv hCinv hchart hsmall P δ hP hm hK hRP hσP hcount hI hn hJ
    hAP hSP hCP hVP poly hmem site hsite hδ hδP W τ ξ hW hWP hroot
    hτ hτP hξ hξ1 hξP N stride hs hsP hsize cells hcells bases hbases
    widths hwidths hmass center density hD hlower
  let P' := spatialSamplingBudget (2*P)
  have hPP' : P ≤ P' := by dsimp [P', spatialSamplingBudget]; linarith
  have hP' : 0 ≤ P' := hP.trans hPP'
  have hexp := Real.exp_le_exp.mpr hPP'
  obtain ⟨_, hcut, hlargeLog⟩ := hbudget P hP
  have hlarge i : Real.exp (10*P+128) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr hlargeLog).trans (hsize i)
  have hN i : 0 < N i := by exact_mod_cast (Real.exp_pos _).trans_le (hlarge i)
  obtain ⟨hρ, hρP, hwidth⟩ := narrow_sampler_width_bounds (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    hP hW hWP hτ hτP hξ hξ1 hξP N hN
  have hscale := narrow_sampler_residue_scale (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    hP hW hWP hτ hτP hξ hξ1 hξP N stride hs hsP hAP hlarge
  let i : X := Classical.choice inferInstance
  apply allocatedFixedScaleJoint_collision_small B U b hb o hR hσ S C V hC hV hσ1
    Cinv hCinv hchart hsmall
    (fun a z => coefficientConstantCenter U center + affineSampleCoefficientTorus U poly hmem
      (fun k v => (jointIntegerFrame (a,z) k v : ℝ)))
    hP' (hm.trans hPP') (hK.trans hPP')
    (fun j => (hRP j).trans hexp) (fun j => (hσP j).trans hexp)
    (fun j => (hcount j).trans hPP') (fun j => (hI j).trans hPP')
    (fun j => (hn j).trans hPP') (fun j => (hJ j).trans hPP')
    (hAP.trans hexp) (hSP.trans hexp) (fun j => (hCP j).trans hexp) (fun j => (hVP j).trans hexp)
    bases hbases site hsite i hδ (hδP.trans hexp)
    (fun q k => ((Finset.single_le_sum (fun j _ => abs_nonneg (site q j : ℝ))
      (Finset.mem_univ k)).trans (hroot q)).trans (hWP.trans hexp))
    stride hs ((hsP i).trans hexp) cells hcells widths hwidths hmass hscale hρ
    (hρP.trans (Real.exp_le_exp.mpr (le_spatialSamplingBudget hP')))
    ((Real.exp_le_exp.mpr (hcollisionBudget P' hP')).trans
      ((Real.exp_le_exp.mpr hcut).trans (hsize i)))
    (fun k => hwidth (some k,i))
    (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hmem center) hD hlower

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedCenteredMeasurableFramedBadTail
namespace OAI

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

def allocatedJointFrameRead {R : Type*} [Add R] (a : X → R)
    (f : AllocatedActualCoefficientIndex G X I E n B → R) :
    AllocatedActualCoefficientIndex G X I E n B → R
  | .inl (none,x) => a x + f (.inl (none,x))
  | .inl (some k,x) => f (.inl (some k,x))
  | .inr k => f (.inr k)

theorem allocatedJointFrameRead_noise (a : X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedReadNoise (allocatedJointFrameRead a f) =
      fun t => BooleanCubeKernel.jointIntegerFrame (a, allocatedReadNoise f) t.1 t.2 := by
  funext t
  rcases t with ⟨k,x⟩
  cases k <;> rfl

@[simp] theorem allocatedJointFrameRead_noise_some {R : Type*} [Add R] (a : X → R)
    (f : AllocatedActualCoefficientIndex G X I E n B → R)
    (k : LayerSamplerVariables G I n B) (x : X) :
    allocatedReadNoise (allocatedJointFrameRead a f) (some k,x) =
      allocatedReadNoise f (some k,x) := rfl

@[simp] theorem allocatedJointFrameRead_deck {R : Type*} [Add R] (a : X → R)
    (f : AllocatedActualCoefficientIndex G X I E n B → R) :
    allocatedReadDeck (allocatedJointFrameRead a f) = allocatedReadDeck f := rfl

@[simp] theorem allocatedJointFrameRead_projection {R : Type*} [Add R] (a : X → R)
    (f : AllocatedActualCoefficientIndex G X I E n B → R) :
    allocatedReadProjection (allocatedJointFrameRead a f) = allocatedReadProjection f := rfl

theorem allocatedJointFrameRead_reduce (M : ℕ) (a : X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    (fun i => ((allocatedJointFrameRead a f i : ℤ) : ZMod M)) =
      allocatedJointFrameRead (fun x => (a x : ZMod M)) (fun i => (f i : ZMod M)) := by
  funext i
  rcases i with ⟨k,x⟩ | k
  · cases k
    · exact Int.cast_add _ _
    · rfl
  · rfl

variable [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]

theorem allocatedOriginalCongruenceTop_congr_slopes
    (inactive : LayerSamplerAxis I n → Prop) (M : ℕ)
    (f g : AllocatedActualCoefficientIndex G X I E n B → ZMod M)
    (hnoise : ∀ (k : LayerSamplerVariables G I n B) (x : X),
      allocatedReadNoise f (some k,x) = allocatedReadNoise g (some k,x))
    (hdeck : allocatedReadDeck f = allocatedReadDeck g)
    (hinteger : ∀ (j : Fin m) (i : Fin (n j)),
      allocatedReadProjection f ⟨j,Sum.inr i⟩ = allocatedReadProjection g ⟨j,Sum.inr i⟩)
    (j : Fin m) (v : LayerSamplerVariables G I n B → ZMod M)
    (o : AllocatedCongruenceRankOutput X E inactive j) :
    allocatedOriginalTaggedTop inactive j (allocatedReadNoise f) (allocatedReadDeck f)
      (fun a => allocatedReadProjection f ⟨j,a.val⟩) v
      (allocatedCongruenceOutputEmbedding inactive j o) =
    allocatedOriginalTaggedTop inactive j (allocatedReadNoise g) (allocatedReadDeck g)
      (fun a => allocatedReadProjection g ⟨j,a.val⟩) v
      (allocatedCongruenceOutputEmbedding inactive j o) := by
  rcases o with x | i | a
  · exact spatialRankPolynomial_conditioned_top_congr (allocatedLongEmbedding inactive)
      (fun k => allocatedReadNoise f (k,x.val)) (fun k => allocatedReadNoise g (k,x.val))
      (fun k => hnoise k x.val) v v
  · simp only [allocatedCongruenceOutputEmbedding_deck, allocatedOriginalTaggedTop, hdeck]
  · simp only [allocatedCongruenceOutputEmbedding_integer, allocatedOriginalTaggedTop, hinteger]

variable [Fintype X] [∀ j, Fintype (E j)]

theorem allocatedResidueModulusBad_congr_slopes
    (inactive : LayerSamplerAxis I n → Prop) (C : ℝ) (M : ℕ) [NeZero M]
    (f g : AllocatedActualCoefficientIndex G X I E n B → ZMod M)
    (hnoise : ∀ (k : LayerSamplerVariables G I n B) (x : X),
      allocatedReadNoise f (some k,x) = allocatedReadNoise g (some k,x))
    (hdeck : allocatedReadDeck f = allocatedReadDeck g)
    (hinteger : ∀ (j : Fin m) (i : Fin (n j)),
      allocatedReadProjection f ⟨j,Sum.inr i⟩ = allocatedReadProjection g ⟨j,Sum.inr i⟩) :
    allocatedResidueModulusBad inactive C M f = allocatedResidueModulusBad inactive C M g := by
  unfold allocatedResidueModulusBad
  simp only [allocatedOriginalCongruenceTop_congr_slopes inactive M f g hnoise hdeck hinteger]

theorem allocatedActualModulusBad_jointFrame
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (C : ℝ) (M : ℕ) [NeZero M] (a : X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedActualModulusBad inactive spatial kernel block C M (allocatedJointFrameRead a f) =
      allocatedActualModulusBad inactive spatial kernel block C M f := by
  rw [allocatedActualModulusBad_eq_residue, allocatedActualModulusBad_eq_residue,
    allocatedJointFrameRead_reduce]
  exact allocatedResidueModulusBad_congr_slopes inactive C M _ _ (fun _ _ => rfl) rfl (fun _ _ => rfl)

theorem allocatedJointFrameRead_rankBad
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (C : ℝ) (p d : ℕ)
    (a : X → ℤ) (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedCongruenceRankBad inactive
      (allocatedReadNoise (allocatedJointFrameRead a f)) (allocatedReadDeck (allocatedJointFrameRead a f))
      (fun j b => allocatedReadProjection (allocatedJointFrameRead a f) ⟨j,b.val⟩)
      spatial kernel block P C p d
      (allocatedCongruenceIntegerSelectedCoefficients inactive
        (allocatedReadNoise (allocatedJointFrameRead a f)) (allocatedReadDeck (allocatedJointFrameRead a f))
        (fun j b => allocatedReadProjection (allocatedJointFrameRead a f) ⟨j,b.val⟩)
        spatial kernel block) =
    allocatedCongruenceRankBad inactive (allocatedReadNoise f) (allocatedReadDeck f)
      (fun j b => allocatedReadProjection f ⟨j,b.val⟩) spatial kernel block P C p d
      (allocatedCongruenceIntegerSelectedCoefficients inactive (allocatedReadNoise f) (allocatedReadDeck f)
        (fun j b => allocatedReadProjection f ⟨j,b.val⟩) spatial kernel block) := by
  unfold allocatedCongruenceRankBad smoothResiduePrimeBad
  apply propext
  apply exists_congr
  intro hp
  let : NeZero p := inferInstanceAs (NeZero (⟨p,hp⟩ : P).val)
  exact (allocatedActualModulusBad_jointFrame inactive spatial kernel block C (p ^ d) a f).to_iff

theorem allocatedJointFrameRead_badDepth
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ) (C : ℝ) (p : ℕ)
    (a : X → ℤ) (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedCongruenceBadDepth inactive
      (allocatedReadNoise (allocatedJointFrameRead a f)) (allocatedReadDeck (allocatedJointFrameRead a f))
      (fun j b => allocatedReadProjection (allocatedJointFrameRead a f) ⟨j,b.val⟩)
      spatial kernel block P A C p =
    allocatedCongruenceBadDepth inactive (allocatedReadNoise f) (allocatedReadDeck f)
      (fun j b => allocatedReadProjection f ⟨j,b.val⟩) spatial kernel block P A C p := by
  unfold allocatedCongruenceBadDepth largestTestedBadDepth
  simp only [allocatedJointFrameRead_rankBad]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

omit [Fintype G] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ a, Fintype (B a)] in

theorem allocatedReplaceReadNoise_eq_jointFrame
    (base : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hf : allocatedReadNoise f = integerBaseTranslation base + z) :
    allocatedReplaceReadNoise B z f = allocatedJointFrameRead (-base) f := by
  funext i
  rcases i with ⟨k,x⟩ | i
  · have h := congrFun hf (k,x)
    cases k with
    | none =>
      change z (none,x) = -base x + f (.inl (none,x))
      change f (.inl (none,x)) = base x + z (none,x) at h
      omega
    | some k =>
      change z (some k,x) = f (.inl (some k,x))
      simpa only [allocatedReadNoise, Pi.add_apply, integerBaseTranslation,
        baseArrayJoin, Pi.zero_apply, zero_add] using h.symm
  · rfl

variable [Fintype X]

theorem allocatedReplaceReadNoise_primeBad
    (base : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hf : allocatedReadNoise f = integerBaseTranslation base + z)
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ}
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,b.val⟩)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (C : ℝ) (p d : ℕ) :
    allocatedActualPrimeBad inactive spatial kernel block P C p d (allocatedReplaceReadNoise B z f) =
      allocatedActualPrimeBad inactive spatial kernel block P C p d f := by
  rw [allocatedReplaceReadNoise_eq_jointFrame B base z f hf]
  exact allocatedJointFrameRead_rankBad inactive spatial kernel block P C p d (-base) f

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

section BadDepth
variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]
variable (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (C : ℝ)

theorem allocatedActualPrimeBad_depth_jointFrame (A : ℕ → ℕ) (p : ℕ) (a : X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    largestTestedBadDepth A (allocatedActualPrimeBad inactive spatial kernel block P C) p
        (allocatedJointFrameRead a f) =
      largestTestedBadDepth A (allocatedActualPrimeBad inactive spatial kernel block P C) p f := by
  rw [allocatedActualPrimeBad_depth, allocatedActualPrimeBad_depth]
  exact allocatedJointFrameRead_badDepth inactive spatial kernel block P A C p a f

theorem allocatedActualPrimeBad_product_jointFrame (A : ℕ → ℕ) (a : X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    (∏ p ∈ P, p ^ largestTestedBadDepth A
      (allocatedActualPrimeBad inactive spatial kernel block P C) p (allocatedJointFrameRead a f)) =
    ∏ p ∈ P, p ^ largestTestedBadDepth A
      (allocatedActualPrimeBad inactive spatial kernel block P C) p f := by
  simp only [allocatedActualPrimeBad_depth_jointFrame]

end BadDepth

section RecoveredSample
variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
variable (C : ℝ)
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {c : ∀ j, U j} {a : X → ℤ}
variable {sample : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n}
variable {read : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  AllocatedActualCoefficientIndex G X I E n B → ℤ}

theorem AllocatedCenteredRecoveredSampleReadAt.jointFrame
    (h : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ poly hm
      inactive spatial kernel block C center c a sample read)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    allocatedReadNoise (allocatedJointFrameRead a (read z)) =
        (fun t => jointIntegerFrame (a,z) t.1 t.2) ∧
    allocatedReadDeck (allocatedJointFrameRead a (read z)) = allocatedReadDeck (read z) ∧
    allocatedReadProjection (allocatedJointFrameRead a (read z)) = allocatedReadProjection (read z) ∧
    (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center a z ≠ 0 →
      canonicalCoefficientSample U b hb o (sample z) =
        affineSampleCoefficientTorus U (fun j => subtractConstant (c j).val (poly j))
          (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hm j))
          (fun k x => (jointIntegerFrame (a,z) k x : ℝ)) ∧
      (∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (sample z j) ∧
        mixedArraySupported (allocatedLayerCenters B U b S j)
          (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample z j)) ∧
      (∀ d, |coefficientSamplerAmbientPoint U b o (sample z) d| < 1/2) ∧
      (∀ (j : Fin m) (i : Fin (n j))
        (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
        allocatedReadProjection (allocatedJointFrameRead a (read z)) ⟨j, Sum.inr i⟩ e =
          (sample z j).2 i e)) := by
  refine ⟨?_, rfl, rfl, ?_⟩
  · rw [allocatedJointFrameRead_noise, (h z).1]
  · intro hz
    have hs := (h z).2 hz
    refine ⟨?_, hs.2.1, hs.2.2.1, hs.2.2.2.1⟩
    exact hs.1.trans (affineSampleCoefficientTorus_joint_frame U
      (fun j => subtractConstant (c j).val (poly j))
      (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hm j)) a z)

end RecoveredSample
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
variable (C : ℝ)
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {c : ∀ j, U j} {a : X → ℤ}
variable {sample : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n}
variable {read : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  AllocatedActualCoefficientIndex G X I E n B → ℤ}

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
variable (rankC : ℝ)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (c : CoefficientTorus (K := LayerSamplerVariables G I n B) U → ∀ j, U j)
variable (hc : Measurable c)
variable (sample : CoefficientTorus (K := LayerSamplerVariables G I n B) U → (X → ℤ) →
  (Option (LayerSamplerVariables G I n B) × X → ℤ) → CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (read : CoefficientTorus (K := LayerSamplerVariables G I n B) U → (X → ℤ) →
  (Option (LayerSamplerVariables G I n B) × X → ℤ) → AllocatedActualCoefficientIndex G X I E n B → ℤ)
variable (hread : ∀ center a, AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ poly hm
  inactive spatial kernel block rankC center (c center) a (sample center a) (read center a))
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
variable (width : Option (LayerSamplerVariables G I n B) × X → ℝ) (hwidth : ∀ z, 0 < width z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (hD : ∀ center, 0 < selectedJointDensityMass bases stride cells width
  (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center))
local notation "jointLaw" => (fun center => selectedJointFiniteLaw bases hbases stride cells width hwidth hZ
  (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center)
  (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm center) (hD center))
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U)) [IsProbabilityMeasure μ]
variable (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ) (cutoff : ℕ)

omit [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)] in
theorem allocatedCentered_joint_weight_measurable : ∀ x, Measurable (fun center => (jointLaw center).weight x) :=
    selectedJointFiniteLaw_weight_measurable bases hbases stride cells width hwidth hZ
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm)
      (allocatedCenteredJointDensity_measurable_center B U b hb o hR hσ S poly hm)
      (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm) hD

omit [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
  [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
  [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)] in
include hread in
theorem allocatedCentered_joint_positive_rankCertificate : ∀ center (x : bases × rectangularWeightIndices 0 width 1),
      0 < (jointLaw center).weight x →
      AllocatedPhysicalRankReadCertificate B U bW b hb o
        (allocatedCenteredConditionalPolynomial U poly (c center) x.1.val)
        (allocatedCenteredConditionalPolynomial_mem U poly hm (c center) x.1.val)
        inactive spatial kernel block rankC x.2.val (read center x.1.val x.2.val) := by
    intro center x hx
    have hdensity := (selectedJointFiniteLaw_support bases hbases stride cells width hwidth hZ
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center)
      (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm center) (hD center) x hx).2.ne'
    exact ((hread center x.1.val x.2.val).2 hdensity).2.2.2.2.2

include hc hread in

theorem exists_allocatedCentered_measurable_unframed_bad_tail
    {ε : ℝ} (hbound : (centeredFiniteProbabilityMeasure μ jointLaw).real
      {z | cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A
        (allocatedActualPrimeBad inactive spatial kernel block P rankC) p
        (read z.1 z.2.1.val z.2.2.val)} ≤ ε) :
    ∃ bad : Set (CoefficientTorus (K := LayerSamplerVariables G I n B) U ×
        (bases × rectangularWeightIndices 0 width 1)),
      MeasurableSet bad ∧ (centeredFiniteProbabilityMeasure μ jointLaw).real bad ≤ ε ∧
      ∀ center x, 0 < (jointLaw center).weight x →
        (cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A
          (allocatedActualPrimeBad inactive spatial kernel block P rankC) p
          (read center x.1.val x.2.val) ↔ (center,x) ∈ bad) := by
  have hweight := allocatedCentered_joint_weight_measurable B U b hb o S hR hσ poly hm
    stride cells width hwidth hZ bases hbases hD
  have hcertificate := allocatedCentered_joint_positive_rankCertificate B U bW b hb o S hR hσ poly hm
    inactive spatial kernel block rankC c sample read hread stride cells width hwidth hZ bases hbases hD
  obtain ⟨bad, hbad, hmassbad, heq, _⟩ := exists_allocatedCentered_badProduct_measurable_tail
    (C := CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (Ω := bases × rectangularWeightIndices 0 width 1) B U bW b hb o poly hm inactive spatial kernel block rankC c hc
    (fun x => x.1.val) (fun x => x.2.val) jointLaw
    (fun center x => read center x.1.val x.2.val) hcertificate P A cutoff μ hweight hbound
  exact ⟨bad, hbad, hmassbad, heq⟩

include hc hread in

theorem exists_allocatedCentered_measurable_framed_bad_tail
    {ε : ℝ} (hbound : (centeredFiniteProbabilityMeasure μ jointLaw).real
      {z | cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A
        (allocatedActualPrimeBad inactive spatial kernel block P rankC) p
        (read z.1 z.2.1.val z.2.2.val)} ≤ ε) :
    ∃ bad : Set (CoefficientTorus (K := LayerSamplerVariables G I n B) U ×
        (bases × rectangularWeightIndices 0 width 1)),
      MeasurableSet bad ∧ (centeredFiniteProbabilityMeasure μ jointLaw).real bad ≤ ε ∧
      (∀ center x, 0 < (jointLaw center).weight x →
        ((center,x) ∈ bad ↔ cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A
          (allocatedActualPrimeBad inactive spatial kernel block P rankC) p
          (allocatedJointFrameRead x.1.val (read center x.1.val x.2.val)))) ∧
      ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ jointLaw,
        z ∈ bad ↔ cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A
          (allocatedActualPrimeBad inactive spatial kernel block P rankC) p
          (allocatedJointFrameRead z.2.1.val (read z.1 z.2.1.val z.2.2.val)) := by
  have hweight := allocatedCentered_joint_weight_measurable B U b hb o S hR hσ poly hm
    stride cells width hwidth hZ bases hbases hD
  obtain ⟨bad, hbad, hmassbad, heq⟩ := exists_allocatedCentered_measurable_unframed_bad_tail
    B U bW b hb o S hR hσ poly hm inactive spatial kernel block rankC c hc sample read hread
    stride cells width hwidth hZ bases hbases hD μ P A cutoff hbound
  have hpositive : ∀ center x, 0 < (jointLaw center).weight x →
      ((center,x) ∈ bad ↔ cutoff < ∏ p ∈ P, p ^ largestTestedBadDepth A
        (allocatedActualPrimeBad inactive spatial kernel block P rankC) p
        (allocatedJointFrameRead x.1.val (read center x.1.val x.2.val))) := by
    intro center x hx
    rw [allocatedActualPrimeBad_product_jointFrame]
    exact (heq center x hx).symm
  refine ⟨bad, hbad, hmassbad, hpositive, ?_⟩
  exact (centeredFiniteProbabilityMeasure_ae_positive_weight μ jointLaw hweight).mono
    (fun z hz => hpositive z.1 z.2 hz)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRecoveredPreparedFreeze
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G V : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ) (hσ1 : ∀ j, σ j ≤ 1)
variable (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)

include hσ1 hC hchart

theorem allocatedLayerSupported_polynomial_bound (j : Fin m) (a)
    (ha : mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) a)
    (x : LayerSamplerVariables G I n B → ℝ) (hx : ∀ v, |x v| ≤ layerSamplerBox B U b S v)
    (i : J j) :
    |mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val a.1 a.2 x i| ≤
      C j * (((Fintype.card (I j) : ℝ) + 1) * R j) := by
  have hT : ∀ v, 0 < layerSamplerBox B U b S v :=
    fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S v)
  have hs := (allocatedArraySupported_iff_rows Subtype.val (layerSamplerBox B U b S)
    (layerContinuousPrincipalSlots B j) (constantCoefficientSlot _ _) (R j) (σ j)
    (allocatedLayerIntegerPMFs B U b hR hσ S j) a).mp ha
  have hc (k : I j) : |MvPolynomial.eval x (monomialArrayPolynomial Subtype.val (a.1 k))| ≤ R j :=
    (continuousPolynomialDensity_box Subtype.val _ hT _ _
      (layerContinuousPrincipalSlots_not_constant B j k) (hR j) (hσ j) (hσ1 j)
      (hs.1 k) x hx).trans (by linarith [hR j])
  have hz (k : Fin (n j)) :
      |MvPolynomial.eval x (monomialArrayPolynomial Subtype.val
        (fun d => (a.2 k d : ℝ) / basisAxisScale (b j) k))| ≤ R j := by
    exact (allocatedIntegerPolynomial_box (layerIntegerPrincipalSlots B j k) (constantCoefficientSlot _ _)
      (j.val + 1) (basisAxisScale (b j) k) S.value (layerTailDegree m) (Nat.zero_lt_succ _)
      (basisAxisScale_pos (b j) k) S.positive (layerSamplerBox B U b S) hT
      (layerSamplerBox_le B U b S) Subtype.val (fun d => d.property.trans (layerDegree_le_tailDegree j))
      (R j) (σ j) (hR j) (hσ j) (S.gap j k) (S.width j)
      (layerIntegerPrincipalSlots_not_constant B j k) rfl (hσ1 j)
      (layerSamplerSides_integer_principal B U b R S.value j k) (a.2 k) (hs.2 k) x hx).trans
        (by linarith [hR j])
  have hnorm := mixedRealPoint_norm_le (euclideanSubspace (U j)) (b j) (o j)
    (hC j) (hR j).le (hchart j) _ _ hc hz
  have hi := PiLp.norm_apply_le
    (mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val a.1 a.2 x) i
  simpa only [Real.norm_eq_abs] using hi.trans hnorm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open Module Submodule VectorPolynomial
open scoped BigOperators TensorProduct

variable {X G : Type} [Fintype G] {s D E m : ℕ}
variable {A : PolynomialPatch X s (D + E)}
variable (L : RankPreparationFamily X (Fin D) m)
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (L j).space)ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (L j).space))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B (fun j => (L j).space) b R σ)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
variable (C : ℝ)
variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

def AllocatedCenteredFramedRecoveredSampleAt
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (s : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) : Prop :=
  allocatedReadNoise f = (fun t => jointIntegerFrame (a,v) t.1 t.2) ∧
  canonicalCoefficientSample U b hb o s =
    affineSampleCoefficientTorus U (fun j => subtractConstant (c j).val (poly j))
      (fun j => coefficients_subtractConstant_mem (U j) (c j) (poly j) (hm j))
      (fun k x => (jointIntegerFrame (a,v) k x : ℝ)) ∧
  (∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (s j) ∧
    mixedArraySupported (allocatedLayerCenters B U b S j)
      (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) (s j)) ∧
  (∀ d, |coefficientSamplerAmbientPoint U b o s d| < 1/2) ∧
  (∀ (j : Fin m) (i : Fin (n j))
    (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
    allocatedReadProjection f ⟨j, Sum.inr i⟩ e = (s j).2 i e)

theorem allocatedCentered_recovered_sample_ae
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    (bases : Finset (X → ℤ)) (hbases : bases.Nonempty) (stride : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (width : Option (LayerSamplerVariables G I n B) × X → ℝ) (hwidth : ∀ z, 0 < width z)
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z)
    (hD : ∀ center, 0 < selectedJointDensityMass bases stride cells width
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center))
    (c : CoefficientTorus (K := LayerSamplerVariables G I n B) U → ∀ j, U j)
    (sample : CoefficientTorus (K := LayerSamplerVariables G I n B) U → (X → ℤ) →
      (Option (LayerSamplerVariables G I n B) × X → ℤ) →
        CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : CoefficientTorus (K := LayerSamplerVariables G I n B) U → (X → ℤ) →
      (Option (LayerSamplerVariables G I n B) × X → ℤ) →
        AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hread : ∀ center a, AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ poly hm
      inactive spatial kernel block C center (c center) a (sample center a) (read center a)) :
    let law := fun center => selectedJointFiniteLaw bases hbases stride cells width hwidth hmass
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center)
      (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm center) (hD center)
    ∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law,
      columnResiduePattern stride z.2.2.val ∈ cells ∧
      0 < allocatedCenteredJointDensity B U b hb o hR hσ S poly hm z.1 z.2.1.val z.2.2.val ∧
      AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
        (c z.1) z.2.1.val z.2.2.val (sample z.1 z.2.1.val z.2.2.val)
        (allocatedJointFrameRead z.2.1.val (read z.1 z.2.1.val z.2.2.val)) := by
  intro law
  have hweight : ∀ x, Measurable (fun center => (law center).weight x) :=
    selectedJointFiniteLaw_weight_measurable bases hbases stride cells width hwidth hmass
      (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm)
      (allocatedCenteredJointDensity_measurable_center B U b hb o hR hσ S poly hm)
      (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm) hD
  apply (centeredFiniteProbabilityMeasure_ae_positive_weight μ law hweight).mono
  intro z hz
  have hs := selectedJointFiniteLaw_support bases hbases stride cells width hwidth hmass
    (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm z.1)
    (allocatedCenteredJointDensity_nonneg B U b hb o hR hσ S poly hm z.1) (hD z.1) z.2 hz
  have hf := (hread z.1 z.2.1.val).jointFrame B U bW b hb o S hR hσ poly hm
    inactive spatial kernel block C z.2.2.val
  exact ⟨hs.1, hs.2, hf.1, hf.2.2.2 hs.2.ne'⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped Classical

instance coefficientTorus_zeroLayer_subsingleton {K : Type*} {J : Fin 0 → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) :
    Subsingleton (CoefficientTorus (K := K) U) where
  allEq x y := by
    refine Quotient.inductionOn₂ x y ?_
    intro c d
    change QuotientAddGroup.mk' (coefficientIntegerLattice U) c =
      QuotientAddGroup.mk' (coefficientIntegerLattice U) d
    apply congrArg (QuotientAddGroup.mk' (coefficientIntegerLattice U))
    funext t
    exact Fin.elim0 t.1

variable {G X : Type*} {I E J : Fin 0 → Type*} {n : Fin 0 → ℕ}
variable (B : LayerSamplerAxis I n → Type*)

def allocatedZeroLayerFramedRead (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    AllocatedActualCoefficientIndex G X I E n B → ℤ
  | .inl t => jointIntegerFrame (a, v) t.1 t.2
  | .inr (.inl ⟨j, _, _⟩) => Fin.elim0 j
  | .inr (.inr ⟨⟨j, _⟩, _⟩) => Fin.elim0 j

@[simp] theorem allocatedZeroLayerFramedRead_noise (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    allocatedReadNoise (allocatedZeroLayerFramedRead (E := E) B a v) =
      fun t => jointIntegerFrame (a, v) t.1 t.2 := rfl

def allocatedZeroLayerSample :
    CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n :=
  fun j => Fin.elim0 j

variable [Fintype G]
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

def allocatedZeroLayerCenterLift : ∀ j, U j := fun j => Fin.elim0 j

variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin 0 → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open VectorPolynomial Module Submodule BooleanCubeKernel
open scoped BigOperators TensorProduct Classical

variable {m s D E : ℕ} {X G : Type} [Fintype X] [Fintype G]
variable (L : RankPreparationFamily X (Fin D) m)
variable {I Deck : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (Deck j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ ((L j).Coord → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

end Erdos3.PolynomialPatch.LowestLayerModel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedRecoveredIntegerFullChart
namespace OAI

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators
variable {m : ℕ} {K X : Type*} [Fintype K] (J : Fin m → Type*)
    (a : X → ℤ) (v : Option K × X → ℤ)
    (tag : ∀ j, J j → MvPolynomial K ℤ)

noncomputable def jointIntegerFullChart : X ⊕ (Σ j, J j) → MvPolynomial K ℤ :=
  Sum.elim (affineFramePolynomial (jointIntegerFrame (a, v))) (fun z => tag z.1 z.2)

theorem jointIntegerFullChart_support
    (htag : ∀ j b, (tag j b).totalDegree ≤ j.val + 1) :
    ∀ i, integerSampledRealChart (jointIntegerFullChart J a v tag) i ∈
      weightedSupportLE (fun _ : K => 1) (fullTaggedVariableWeight J i) := by
  intro i
  apply (mem_weightedSupportLE_one_iff _ _).mpr
  cases i with
  | inl x =>
    change (MvPolynomial.map (Int.castRingHom ℝ)
      (affineFramePolynomial (jointIntegerFrame (a, v)) x)).totalDegree ≤ 1
    exact (totalDegree_map_le _ _).trans (affineFramePolynomial_degree _ _)
  | inr z =>
    change (MvPolynomial.map (Int.castRingHom ℝ) (tag z.1 z.2)).totalDegree ≤ z.1.val + 1
    exact (totalDegree_map_le _ _).trans (htag z.1 z.2)

theorem jointIntegerFullChart_spatial (x : K → ℤ) :
    integerSampledSpatial (jointIntegerFullChart J a v tag) x =
      jointIntegerPhysicalSite x (a, v) := by
  funext i
  change MvPolynomial.aeval x (affineFramePolynomial (jointIntegerFrame (a, v)) i) = _
  rw [affineFramePolynomial_eval]
  have h := congrFun (integerAffineMap_jointIntegerFrame (a, v) x) i
  simpa only [integerAffineMap] using h

theorem cast_jointIntegerPhysicalSite_eq_frame (x : K → ℤ) :
    (fun i => (jointIntegerPhysicalSite x (a, v) i : ℝ)) =
      (fun i => (jointIntegerFrame (a, v) none i : ℝ) +
        ∑ k, (jointIntegerFrame (a, v) (some k) i : ℝ) * (x k : ℝ)) := by
  rw [← integerAffineMap_jointIntegerFrame]
  funext i
  simp only [integerAffineMap, Int.cast_add, Int.cast_sum, Int.cast_mul]

theorem eval_jointIntegerPhysicalSite_eq_frame
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (p : VectorPolynomial X ℝ V) (x : K → ℤ) :
    eval (fun i => (jointIntegerPhysicalSite x (a, v) i : ℝ)) p =
      eval (fun i => (jointIntegerFrame (a, v) none i : ℝ) +
        ∑ k, (jointIntegerFrame (a, v) (some k) i : ℝ) * (x k : ℝ)) p := by
  rw [cast_jointIntegerPhysicalSite_eq_frame]
end Erdos3.VectorPolynomial

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

noncomputable def allocatedRecoveredIntegerFullChart
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n) :
    X ⊕ (Σ j, J j) → MvPolynomial (LayerSamplerVariables G I n B) ℤ :=
  jointIntegerFullChart J a v
    (coefficientIntegerFloorPolynomial U b o sample
      (centeredAffineCoefficientArray U poly hm c
        (fun k z => (jointIntegerFrame (a, v) k z : ℝ))))

theorem allocatedRecoveredIntegerFullChart_support
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n) :
    ∀ i, integerSampledRealChart (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) i ∈
      weightedSupportLE (fun _ : LayerSamplerVariables G I n B => 1) (fullTaggedVariableWeight J i) := by
  apply jointIntegerFullChart_support
  exact coefficientIntegerFloorPolynomial_degree U b o sample _

theorem allocatedRecoveredIntegerFullChart_spatial
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (x : LayerSamplerVariables G I n B → ℤ) :
    integerSampledSpatial (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) x =
      jointIntegerPhysicalSite x (a, v) :=
  jointIntegerFullChart_spatial J a v _ x

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_remainder
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (x : LayerSamplerVariables G I n B → ℝ) (j : Fin m) (i : J j) :
    eval (fun z => (jointIntegerFrame (a, v) none z : ℝ) +
      ∑ k, (jointIntegerFrame (a, v) (some k) z : ℝ) * x k) (poly j) i - (c j).val i =
      mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val
        (sample j).1 (sample j).2 x i +
      MvPolynomial.eval x (integerSampledRealChart
        (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) (Sum.inr ⟨j, i⟩)) := by
  let frame : Option (LayerSamplerVariables G I n B) → X → ℝ :=
    fun k z => (jointIntegerFrame (a, v) k z : ℝ)
  have hc : canonicalCoefficientSample U b hb o sample =
      QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (centeredAffineCoefficientArray U poly hm c frame) :=
    h.2.1.trans (affineSampleCoefficientTorus_subtractConstant U poly hm c frame)
  have hβ := canonicalCoefficientSample_floor_polynomial_remainder U b hb o sample
    (centeredAffineCoefficientArray U poly hm c frame) hc j i
  change eval (fun z => frame none z + ∑ k, frame (some k) z * x k) (poly j) i - (c j).val i =
    mixedPolynomialPoint (euclideanSubspace (U j)) (b j) (o j) Subtype.val
      (sample j).1 (sample j).2 x i +
      MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom ℝ)
        (coefficientIntegerFloorPolynomial U b o sample
          (centeredAffineCoefficientArray U poly hm c frame) j i))
  rw [← coefficientRowPolynomial_centered_affine_eval U poly hm hp c frame j i x,
    hβ.1, map_add, mixedLiftPolynomial_eval]

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_residual
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (x : LayerSamplerVariables G I n B → ℤ)
    (hx : ∀ k, |(x k : ℝ)| ≤ layerSamplerBox B U b S k) (j : Fin m) (i : J j) :
    |eval (fun z => (jointIntegerPhysicalSite x (a, v) z : ℝ)) (poly j) i - (c j).val i -
      (MvPolynomial.eval x (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample
        (Sum.inr ⟨j, i⟩)) : ℝ)| ≤ C j * (((Fintype.card (I j) : ℝ) + 1) * R j) := by
  rw [eval_jointIntegerPhysicalSite_eq_frame a v,
    ← integerSampledRealChart_eval (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample),
    h.integerFullChart_remainder B U b hb o S hR hσ poly hm hp c a v sample read,
    add_sub_cancel_right]
  exact allocatedLayerSupported_polynomial_bound B U b o hR hσ S hσ1 C hC hchart
    j (sample j) (h.2.2.1 j).2 (fun k => (x k : ℝ)) hx i

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_low_residual
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (k : ℕ) (x : LayerSamplerVariables G I n B → ℤ)
    (hx : ∀ z, |(x z : ℝ)| ≤ layerSamplerBox B U b S z)
    (i : Fin (Fintype.card (LowTaggedIndex J k))) :
    |MvPolynomial.eval
      (fun z => (integerSampledSpatial (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) x z : ℝ))
      (lowTaggedPolynomial J k poly i) - (c (lowTaggedIndex J k i).1).val (lowTaggedIndex J k i).2 -
      (integerSampledLowTags J k (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) x i : ℝ)| ≤ 1 / 8 := by
  rw [allocatedRecoveredIntegerFullChart_spatial, lowTaggedPolynomial_eval]
  exact (h.integerFullChart_residual B U b hb o S hR hσ poly hm hσ1 C hC hchart hp
    c a v sample read x hx (lowTaggedIndex J k i).1 (lowTaggedIndex J k i).2).trans
      (hsmall (lowTaggedIndex J k i).1)

end Erdos3.VectorPolynomial

end

end OAI

end


