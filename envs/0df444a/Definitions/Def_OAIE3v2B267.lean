-- Prove2me | Definitions.Def_OAIE3v2B267
-- name    : OAIE3v2B267
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T06:14:00.0622+00:00
-- url     : https://prove2.me/theorems/971995b1-c124-445c-b043-e7434da3fa21
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 276 of 311
-- statement:
--   Definitions bundle 276 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B218`, `OAIE3v2B258`, `OAIE3v2B261`, `OAIE3v2B262` of this split.
--
--   Modules: `Estimates/AllocatedZeroLayerCommonSideInitializationUniform.lean`, `Sampling/PreparedActualForecastSetup.lean`, `Sampling/PreparedActualSlicedForecastSetup.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B218
import Definitions.Def_OAIE3v2B258
import Definitions.Def_OAIE3v2B261
import Definitions.Def_OAIE3v2B262

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedActualForecastSetup
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {X₀ J₀ : Type} {m : ℕ} (L : RankPreparationFamily X₀ J₀ m) (Jalloc : ℕ)
local notation "G" => EnlargedPreparedCommonKernel m Jalloc
local notation "I" => PreparedSamplerContinuous L
local notation "n" => preparedSamplerTransverse L
local notation "B" => EnlargedPreparedCommonSamplerBlock L Jalloc
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale («G» := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock L Jalloc) U b R σ)
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

noncomputable def preparedActualForecastSetup {M nX : ℕ}
    (hm : 0 < m) (hCoord : ∀ j, Fintype.card (L j).Coord ≤ M)
    {pRadius gainLog Pbad Ppres PF Pκ κ : ℝ}
    (hpRadius : 0 ≤ pRadius) (hGain : 0 ≤ gainLog)
    (hPbad : 0 ≤ Pbad) (hPpres : 0 ≤ Ppres) (hPF : 0 ≤ PF) (hPκ : 0 ≤ Pκ)
    (hκ : 0 ≤ κ) (hκcap : κ ≤ Real.exp Pκ)
    (hR : ∀ j, 0 < R j) (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius) (hσone : ∀ j, σ j ≤ 1)
    (forward : Fin m → ℝ≥0)
    (hforward : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ forward j * ‖w‖)
    (hforwardBound : ∀ j, (forward j : ℝ) ≤ Real.exp PF)
    (radius : ℝ≥0) (T : Fin m → ℝ)
    (hT : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      (2 * 2 ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j : Fin m, (boundedBooleanJetRows (Fin 1) (j.val + 1)).card * T j ≤ (radius : ℝ))
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j (w : euclideanSubspace (U j) × (Fin (preparedSamplerTransverse L j) → ℝ)), ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
    (hsourceBudget : ∀ j : Fin m,
      ((boundedBooleanJetRows (Fin 1) (j.val + 1)).card + 1 : ℝ) *
        (Fintype.card (Finset (Fin 1)) : ℝ) *
        (inverse j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (radius : ℝ) * R j))) ≤ 1 / 4) :
    ActualFixedSpatialForecastSetup (X := Fin nX) (Eout := Eout)
      («G» := G) («I» := I) («n» := n) (A := PreparedActualForecastShortIndex («G» := G) B U b S)
      B U b S (nX + m * M) (preparedActualForecastShortSelection («G» := G) B U b S)
      (Real.exp (-(gainLog + (nX : ℝ) + 8))) (1 / 2) := by
  let pnum : ℝ := enlargedPreparedCommonSamplerDimension m M Jalloc
  let D : ℝ := allocatedComparisonDimension m pnum
  let P : ℝ := D + nX + 8
  obtain ⟨hvars, hI, hn⟩ := enlargedPreparedCommonSampler_dimensions L Jalloc hCoord
  have hd : AllocatedComparisonDimensions («G» := G) B Empty
      (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D :=
    allocatedComparisonDimensions_of_primitive B (fun _ => Subtype.val)
      (by simp) (fun _ => Subtype.val_injective) (Nat.cast_nonneg _)
      (Nat.cast_le.mpr hvars) (fun j => Nat.cast_le.mpr (hI j)) (fun j => Nat.cast_le.mpr (hn j))
  have hP : 1 ≤ P := by dsimp only [P]; have := hd.nonneg; have := Nat.cast_nonneg (α := ℝ) nX; linarith
  have hDP : D ≤ P := by dsimp only [P]; have := Nat.cast_nonneg (α := ℝ) nX; linarith
  have hdimEq : (∑ j, Fintype.card (J j) : ℕ) = Fintype.card (LayerSamplerAxis I n) := by
    simp only [LayerSamplerAxis, Fintype.card_sigma, Fintype.card_sum, Fintype.card_fin]
    apply Finset.sum_congr rfl
    intro j _
    simpa only [PreparedSamplerContinuous, Fintype.card_fin] using
      (allocatedAmbientDimension_eq U b o j).symm
  have hDmod : Fintype.card (Fin nX) + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ nX + m * M := by
    simp only [Fintype.card_fin]
    apply Nat.add_le_add_left
    calc
      _ = ∑ j : Fin m, Fintype.card (L j).Coord := by
        apply Finset.sum_congr rfl
        intro j _
        rw [allocatedLatticeDimension_eq U b o hb bW j]
        exact preparedSampler_axis_card L j
      _ ≤ ∑ _j : Fin m, M := Finset.sum_le_sum (fun j _ => hCoord j)
      _ = m * M := by simp
  have hblocks : (∑ a, (Fintype.card (B a) : ℝ)) ≤ P := by
    have hh := Nat.cast_le (α := ℝ).mpr (enlargedPreparedCommonSampler_block_sum_le_principal_card L Jalloc)
    rw [Nat.cast_sum] at hh
    exact hh.trans (hd.tuples.trans hDP)
  have hscale : 0 ≤ D + pRadius + 1 := by linarith only [hd.nonneg, hpRadius]
  have hscaleRadius : pRadius ≤ D + pRadius + 1 := by linarith only [hd.nonneg]
  obtain ⟨hr3, hrcoeff⟩ := preparedActualForecast_radius_bounds hm T radius hT hradius
  obtain ⟨hτlog, hτ, _, _, hτinv, _⟩ := preparedEarlySpatialWidth nX hGain
  let transition := scalarSourceTransitionBound
  let Pcap := max 1 (scalarCubePrimitiveEnvelope Empty transition 1 0 1)
  have hPcap : 1 ≤ Pcap := le_max_left _ _
  refine {
    hm := hm
    hDmod := hDmod
    hselected := preparedActualForecastShortSelection_injective («G» := G) B U b S
    selectedNonempty := enlargedPreparedActualForecastShortSelection_nonempty L Jalloc U b S
    D := D, P := P, Pcap := Pcap, pcap := Pcap
    Pscale := D + pRadius + 1, Pbad := Pbad, Ppres := Ppres
    Pτ := gainLog + nX + 8, PK := pRadius, PF := PF, Pκ := Pκ, κ := κ
    hD := hd, hP := hP, hDP := hDP, haxes := hd.axes
    hdim := by rw [hdimEq]; exact hd.axes
    hX := by simp only [Fintype.card_fin]; dsimp only [P]; linarith only [hd.nonneg]
    hblocks := hblocks
    hPcap := hPcap, hpcap := zero_le_one.trans hPcap
    hPcapp := by linarith only [Real.add_one_le_exp Pcap]
    hPscale := hscale, hPbad := hPbad, hPpres := hPpres, hPτ := hτlog
    hPK := hpRadius, hPF := hPF, hPκ := hPκ, hκ := hκ, hκcap := hκcap
    hτ := hτ, hτinv := hτinv.le
    hδslice := by norm_num
    hδsliceInv := by norm_num; linarith only [Real.add_one_le_exp P, hP]
    hR1 := fun a => hRone _, hσ1 := fun a => hσone _
    hsmall := preparedActualForecastShortSelection_small («G» := G) B U b S
    L := transition, hL := scalarSourceTransitionBound_spec.2
    hprimitiveCap := le_max_right _ _
    hB := fun a => enlargedPreparedCommonSamplerBlock_transverse_uniform L Jalloc _ _
    hRinv := fun a => (hRinv _).trans (Real.exp_le_exp.mpr hscaleRadius)
    hslots := ?_
    hBactive := fun a => enlargedPreparedCommonSamplerBlock_four L Jalloc a.val
    forward := forward, hforward := hforward, hforwardBound := hforwardBound
    K := ⟨Real.exp pRadius, Real.exp_nonneg _⟩, hK := hRinv, hKBound := le_rfl
    radius := radius, hr3 := hr3, hradius := hrcoeff
    inverse := inverse, hinverse := hinverse, hchart := hchart
    hbudget := ?_
    hexhaustive := preparedActualForecastShortSelection_exhaustive («G» := G) B U b S }
  · intro a
    have hh := (Nat.cast_le (α := ℝ).mpr (Finset.card_le_univ
      (layerIntegerPrincipalSlots («G» := G) B a.val.1 a.val.2))).trans (hd.coefficients a.val.1)
    exact hh.trans (by linarith only [hpRadius])
  · intro j
    have hinner : 0 ≤ inverse j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (radius : ℝ) * R j)) :=
      mul_nonneg (hinverse j) (mul_nonneg (by positivity) (mul_nonneg (by positivity) (hR j).le))
    have hrows : (0 : ℝ) ≤ (boundedBooleanJetRows (Fin 1) (j.val + 1)).card := Nat.cast_nonneg _
    have hfactor : (1 : ℝ) ≤
        ((boundedBooleanJetRows (Fin 1) (j.val + 1)).card + 1 : ℝ) *
          (Fintype.card (Finset (Fin 1)) : ℝ) := by
      norm_num only [Fintype.card_finset, Fintype.card_fin, Nat.cast_ofNat, pow_one]
      linarith only [hrows]
    exact (le_mul_of_one_le_left hinner hfactor).trans (hsourceBudget j)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedActualSlicedForecastSetup
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {X₀ J₀ : Type} {m : ℕ} (L : RankPreparationFamily X₀ J₀ m) (Jalloc : ℕ)
variable (U : ∀ j : Fin m, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) («G» := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock L Jalloc) U b R σ)
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (RankPreparationLayer.Coord (L j))) (euclideanSubspace (U j)))]
noncomputable def preparedActualSlicedForecastSetup {M nX : ℕ}
    (hm : 0 < m) (hCoord : ∀ j, Fintype.card (L j).Coord ≤ M)
    {pRadius gainLog Qstride PF Pchart cost : ℝ} (Pdim : ℝ)
    (hpRadius : 0 ≤ pRadius) (hGain : 0 ≤ gainLog)
    (hQstride : 0 ≤ Qstride) (hPF : 0 ≤ PF) (hChart : 0 ≤ Pchart)
    (hcost : 0 ≤ cost)
    (hratio : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp Pchart)
    (hR : ∀ j, 0 < R j) (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius) (hσone : ∀ j, σ j ≤ 1)
    (forward : Fin m → ℝ≥0)
    (hforward : ∀ j : Fin m, ∀ w : EuclideanSpace ℝ (RankPreparationLayer.Coord (L j)), ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ forward j * ‖w‖)
    (hforwardBound : ∀ j, (forward j : ℝ) ≤ Real.exp PF)
    (radius : ℝ≥0) (T : Fin m → ℝ)
    (hT : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables (EnlargedPreparedCommonKernel m Jalloc) (PreparedSamplerContinuous L) (preparedSamplerTransverse L) (EnlargedPreparedCommonSamplerBlock L Jalloc)) (j.val + 1)) : ℝ) *
      (2 * 2 ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j : Fin m, (boundedBooleanJetRows (Fin 1) (j.val + 1)).card * T j ≤ (radius : ℝ))
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j (w : euclideanSubspace (U j) × (Fin (preparedSamplerTransverse L j) → ℝ)), ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
    (hsourceBudget : ∀ j : Fin m,
      ((boundedBooleanJetRows (Fin 1) (j.val + 1)).card + 1 : ℝ) *
        (Fintype.card (Finset (Fin 1)) : ℝ) *
        (inverse j * (((Fintype.card ((PreparedSamplerContinuous L) j) : ℝ) + 1) * (2 * (radius : ℝ) * R j))) ≤ 1 / 4) :
    ActualFixedSpatialForecastSetup («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) (X := Fin nX) (Eout := Eout)
      («G» := (EnlargedPreparedCommonKernel m Jalloc)) («I» := (PreparedSamplerContinuous L)) («n» := (preparedSamplerTransverse L)) (A := PreparedActualForecastShortIndex («I» := (PreparedSamplerContinuous L)) («n» := (preparedSamplerTransverse L)) («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) («G» := (EnlargedPreparedCommonKernel m Jalloc)) (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S)
      (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S (nX + m * M) (preparedActualForecastShortSelection («I» := (PreparedSamplerContinuous L)) («n» := (preparedSamplerTransverse L)) («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) («G» := (EnlargedPreparedCommonKernel m Jalloc)) (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S)
      (Real.exp (-(gainLog + (nX : ℝ) + 8))) (Real.exp (-cost) / 2) := by
  let Pbad := preparedSlicedForecastBadLog m nX Qstride gainLog
  let Pκ := preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart
  let κ := forecastGeometricJacobian (X := Fin nX) («I» := (PreparedSamplerContinuous L)) U b R S.value
    (preparedForecastGridVolume L Jalloc U b S) (Real.exp (-(gainLog + (nX : ℝ) + 8)))
  have hPbad : 0 ≤ Pbad := by dsimp only [Pbad, preparedSlicedForecastBadLog]; positivity
  obtain ⟨hκ, hPκ, hκcap⟩ := preparedActualForecastJacobian_ratio_budget (nX := nX) L
    (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S
    hCoord hpRadius hGain hChart hR hRinv hratio
  let s := preparedActualForecastSetup (nX := nX) L Jalloc U b o S bW hb hm hCoord
    hpRadius hGain hPbad (show 0 ≤ cost + 1 by linarith) hPF hPκ hκ.le hκcap
    hR hRone hRinv hσone forward hforward hforwardBound radius T hT hradius
    inverse hinverse hchart hsourceBudget
  have hsP : s.P = allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + nX + 8 := by
    simp only [s, preparedActualForecastSetup, and_rec_projection_p0]
  have hP : s.P ≤ preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost := by
    rw [hsP]
    exact le_max_left _ _
  let s' := s.enlargeP hP
  have hwidth : (Real.exp (-cost) / 2)⁻¹ ≤ Real.exp s'.P :=
    (preparedSliceWidth_inverse cost).trans (Real.exp_le_exp.mpr
      ((le_max_right _ _).trans (le_max_right _ _)))
  exact s'.withSliceWidth (div_pos (Real.exp_pos _) (by norm_num)) hwidth

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedZeroLayerCommonSideInitializationUniform
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

structure ScalarCommonBoxSource {K X : Type} [Fintype K] [Fintype X]
    [DecidableEq K] (s d₀ D : ℕ) (N : X → ℕ) (τ : ℝ) (sides : K → ℕ)
    (W : Option K × X → ℝ) (f : (X → ℤ) → ℝ) (Λ cost budget mass : ℝ) where
  width_pos : ∀ z, 0 < W z
  proper : ∀ x, 2 * spatialTrimMargin τ N x < N x
  smooth_pos : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0} W z
  rank : ℕ
  patch : PolynomialPatch K s rank
  rank_le : rank ≤ d₀
  rank_le_early : rank ≤ D
  lip_le : (patch.kernel.lip : ℝ) ≤ Real.exp budget
  center_le : ∀ j, realPolynomialMass (patch.form.center j) ≤ budget
  localForm : (trimmedIntegerBox N (spatialTrimMargin τ N) ×
    rectangularWeightIndices 0 W 1) → PolynomialSlots K rank patch.weight
  localLaw : (trimmedIntegerBox N (spatialTrimMargin τ N) ×
    rectangularWeightIndices 0 W 1) → FiniteProbabilityWeights (integerBox sides)
  retained : Finset (trimmedIntegerBox N (spatialTrimMargin τ N) ×
    rectangularWeightIndices 0 W 1)
  mass_le : mass ≤ (selectedJointReference (trimmedIntegerBox N (spatialTrimMargin τ N))
    (trimmedIntegerBox_nonempty N _ proper) (fun _ : X => 1) {0} W width_pos smooth_pos).mass retained
  slice : ∀ z ∈ retained,
    RelativeReturnedFiberLaw (fun _ : K => True) sides cost (localLaw z)
  score : ∀ z ∈ retained, Real.exp (-budget) ≤ (localLaw z).mean
    (fun x => (f (jointIntegerPhysicalSite x.val (z.1.val,z.2.val)) - Λ) *
      (patch.form.shearTransformedSlots patch.weight_mono
        ((localForm z).loweringAt (fun j => (x.val j : ℝ)))).patchValue patch.kernel)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

structure UniformScalarCommonBoxSource {K X : Type} [Fintype K] [Fintype X]
    [DecidableEq K] (s d₀ D : ℕ) (N : X → ℕ) (τ : ℝ) (sides : K → ℕ)
    (W : Option K × X → ℝ) (f : (X → ℤ) → ℝ) (Λ cost budget mass : ℝ) where
  width_pos : ∀ z, 0 < W z
  proper : ∀ x, 2 * spatialTrimMargin τ N x < N x
  smooth_pos : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0} W z
  rank : ℕ
  patch : PolynomialPatch K s rank
  rank_le : rank ≤ d₀
  rank_le_early : rank ≤ D
  lip_le : (patch.kernel.lip : ℝ) ≤ Real.exp budget
  center_le : ∀ j, realPolynomialMass (patch.form.center j) ≤ budget
  localForm : (trimmedIntegerBox N (spatialTrimMargin τ N) ×
    rectangularWeightIndices 0 W 1) → PolynomialSlots K rank patch.weight
  localLaw : (trimmedIntegerBox N (spatialTrimMargin τ N) ×
    rectangularWeightIndices 0 W 1) → FiniteProbabilityWeights (integerBox sides)
  retained : Finset (trimmedIntegerBox N (spatialTrimMargin τ N) ×
    rectangularWeightIndices 0 W 1)
  mass_le : mass ≤ (selectedJointReference (trimmedIntegerBox N (spatialTrimMargin τ N))
    (trimmedIntegerBox_nonempty N _ proper) (fun _ : X => 1) {0} W width_pos smooth_pos).mass retained
  slice : ∀ z ∈ retained,
    RelativeReturnedFiberLaw (fun _ : K => True) sides cost (localLaw z)
  score : ∀ z ∈ retained, Real.exp (-budget) ≤ (localLaw z).mean
    (fun x => (f (jointIntegerPhysicalSite x.val (z.1.val,z.2.val)) - Λ) *
      (patch.form.shearTransformedSlots patch.weight_mono
        ((localForm z).loweringAt (fun j => (x.val j : ℝ)))).patchValue patch.kernel)

end Erdos3.VectorPolynomial

end

end OAI
end


