-- Prove2me | Definitions.Def_OAIQ087A005
-- name    : OAIQ087A005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:18:19.491563+00:00
-- url     : https://prove2.me/theorems/6ce8d3a2-8f91-4501-a703-5e51546279a8
-- title:
--   Definitions bundle OAIQ087A005 of the split of OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 420 declarations of OpenAI's Lean: 248 definitions, 9 inductive types or structures, 8 instances and 155 theorems. The definitions and types are `OAI.MaxCutGames.Gadget.FreshGenericity.linearEquivFintype`, `OAI.MaxCutGames.Gadget.FreshGenericity.linearMapFintype`, `OAI.MaxCutGames.Gadget.FreshGenericity.submoduleFintype`, `OAI.MaxCutGames.Gadget.NonlinearRecurrence.change`, `OAI.MaxCutGames.Gadget.Parameters.initialRank`, `OAI.MaxCutGames.Gadget.Parameters.rankFor`, `OAI.MaxCutGames.Gadget.QuadraticStageNoise.rate`, `OAI.MaxCutGames.Gadget.StageNoiseRecurrence.average`, `OAI.MaxCutGames.Inverse.EqualityFiber.equalityAcceptance`, `OAI.MaxCutGames.Inverse.EqualityFiber.fiberFlow`, `OAI.MaxCutGames.Inverse.EqualityFiber.fiberMass`, `OAI.MaxCutGames.Inverse.KMS.Adjacent`, `OAI.MaxCutGames.Inverse.KMS.Ambient`, `OAI.MaxCutGames.Inverse.KMS.ExpansionPrinciple`, `OAI.MaxCutGames.Inverse.KMS.F2`, `OAI.MaxCutGames.Inverse.KMS.Vertex`, `OAI.MaxCutGames.Inverse.KMS.interval`, `OAI.MaxCutGames.Inverse.KMS.neighbors`, `OAI.MaxCutGames.Inverse.KMS.relativeDensity`, `OAI.MaxCutGames.Inverse.KMS.retention`, `OAI.MaxCutGames.Inverse.KMSAffineRestriction.affineCoordinates`, `OAI.MaxCutGames.Inverse.KMSAffineRestriction.complementBasis`, `OAI.MaxCutGames.Inverse.KMSAnalyticCompatibleSplitting.CompatibleSplitting`, `OAI.MaxCutGames.Inverse.KMSAnalyticCompatibleSplitting.CompatibleSplitting.B`, `OAI.MaxCutGames.Inverse.KMSAnalyticCompatibleSplitting.CompatibleSplitting.J`, `OAI.MaxCutGames.Inverse.KMSAnalyticCompatibleSplitting.CompatibleSplitting.K0`, `OAI.MaxCutGames.Inverse.KMSAnalyticCompatibleSplitting.CompatibleSplitting.leftEquiv`, `OAI.MaxCutGames.Inverse.KMSAnalyticCompatibleSplitting.CompatibleSplitting.leftMap`, `OAI.MaxCutGames.Inverse.KMSAnalyticCompatibleSplitting.CompatibleSplitting.rightEquiv`, `OAI.MaxCutGames.Inverse.KMSAnalyticCompatibleSplitting.CompatibleSplitting.rightMap`, `OAI.MaxCutGames.Inverse.KMSAnalyticCompatibleSplitting.CompatibleSplitting.targetEquiv`, `OAI.MaxCutGames.Inverse.KMSAnalyticCompatibleSplitting.F2`, `OAI.MaxCutGames.Inverse.KMSAnalyticCompatibleSplitting.chooseSplit`, `OAI.MaxCutGames.Inverse.KMSAnalyticFunctionalSplit.splitEquiv`, `OAI.MaxCutGames.Inverse.KMSAnalyticHybridCoordinates.Coordinates`, `OAI.MaxCutGames.Inverse.KMSAnalyticHybridCoordinates.assemble`, `OAI.MaxCutGames.Inverse.KMSAnalyticHybridCoordinates.compressBlock`, `OAI.MaxCutGames.Inverse.KMSAnalyticHybridCoordinates.compressedFiberEquiv`, `OAI.MaxCutGames.Inverse.KMSAnalyticHybridCoordinates.embedLast`, `OAI.MaxCutGames.Inverse.KMSAnalyticHybridCoordinates.extract` and 217 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MaxCut_Encoding_BitCube`, `MaxCut_Encoding_BitValue`, `MaxCut_Encoding_KMSKernelOrbits`, `MaxCut_Estimates_CorrectSum`, `MaxCut_Estimates_Density`, `MaxCut_Estimates_Put`, `MaxCut_Estimates_Rename`, `MaxCut_Estimates_Sample`, `MaxCut_Gadgets_ValuePolynomial`, `MaxCut_Games_AnswerBridge`, `MaxCut_Games_BaseDetection`, `MaxCut_Games_FiniteFieldChoice`, `MaxCut_Games_GenericPolynomial`, `MaxCut_Games_HarmonicLoss`, `MaxCut_Games_IncidenceExtraction`, `MaxCut_Games_Information`, `MaxCut_Games_KMSAnalyticHybridEnergyImageSplit`, `MaxCut_Games_KMSAnalyticHybridEnergyImageTransportCore`, `MaxCut_Games_KMSAnalyticRestrictionTransport`, `MaxCut_Games_KMSAnalyticSmallInvariant`, `MaxCut_Games_KMSBasisComparisonNeighborsFiberFunctional`, `MaxCut_Games_KMSBasisComparisonPseudorandomTupleMap`, `MaxCut_Games_KMSFourthMomentPointShuffle`, `MaxCut_Games_KMSFourthMomentZoomInvariant`, `MaxCut_Games_KMSMomentConstants`, `MaxCut_Games_KMSMomentTheorem`, `MaxCut_Games_MatrixChartDegreeNeighbors`, `MaxCut_Games_MatrixChartKMSNeighbors`, `MaxCut_Games_MatrixChartShortcode`, `MaxCut_Games_OrientationVectors`, `MaxCut_Games_OrientedBlockKernel`, `MaxCut_Games_PartnerFullSampling`, `MaxCut_Games_RowErasure`, `MaxCut_Games_RowErasureSelection`, `MaxCut_Games_SeparationCertificate`, `MaxCut_Games_StageNoiseRecurrence`, `MaxCut_Machines_FramedLen`, `MaxCut_PCP_ParityIndependence`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ087A012`, `OAIQ087A013` and `OAIQ087A020`; the statement `OAI_MaxCutGames_Decoder_MatrixGap_parameters_of_inverse`.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Density
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.GaussianBellman

open scoped Real Topology NNReal ContDiff
open Set Filter MeasureTheory
open ProbabilityTheory

noncomputable def density (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

noncomputable def cdf (x : ℝ) : ℝ := (1 / 2 : ℝ) + ∫ t in (0 : ℝ)..x, density t

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def sign (b : Bool) : ℝ := if b then -1 else 1

noncomputable def bitPairWeight (t : ℝ) (a b : Bool) : ℝ := (1 + t * sign a * sign b) / 4

 theorem bitPairWeight_nonneg {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) (a b : Bool) :
    0 ≤ bitPairWeight t a b := by
  cases a <;> cases b <;> simp [bitPairWeight, sign] <;> linarith [ht.1, ht.2]

end OptimalMaxCut.GaussianBellman

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_BitCube
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.GaussianBellman
open scoped BigOperators
open Set Finset
abbrev BitCube (n : ℕ) := Fin n → Bool

end OptimalMaxCut.GaussianBellman

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_KMSKernelOrbits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Equal kernels give the same orbit under invertible postcomposition.
The canonical range equivalence comes from the first isomorphism theorem;
Mathlib's finite-dimensional subspace extension theorem then extends it to an
automorphism of the ambient codomain. No orbit or counting premise is assumed.
-/

namespace MaxCutGames.Inverse.KMSKernelOrbits

noncomputable section

variable {K E F : Type*} [DivisionRing K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

/-- The range identification induced by a common kernel. -/
def rangeEquivOfKerEq (S T : F →ₗ[K] E) (hker : S.ker = T.ker) :
    S.range ≃ₗ[K] T.range :=
  S.quotKerEquivRange.symm ≪≫ₗ
    Submodule.quotEquivOfEq S.ker T.ker hker ≪≫ₗ T.quotKerEquivRange

end
end MaxCutGames.Inverse.KMSKernelOrbits

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSAnalyticHybridEnergyImageSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Partition frequencies by their actual image

A map with image `W` is uniquely a surjection onto `W`, followed by the
subspace inclusion. Consequently a sum over rank-`q` frequencies splits
exactly over dimension-`q` image subspaces and surjections onto each image.
The identities hold for arbitrary real weights and use no analytic estimate.
-/

noncomputable section

namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical

variable {R B U : Type*} [Ring R]
  [AddCommGroup B] [Module R B] [AddCommGroup U] [Module R U]

/-- The inclusion of the target subspace preserves the prescribed image of
a surjective map. -/
theorem range_subtype_comp_of_surjective (W : Submodule R U)
    (z : B →ₗ[R] W) (hz : Function.Surjective z) :
    (W.subtype.comp z).range = W := by
  ext u
  constructor
  · rintro ⟨b, rfl⟩
    exact (z b).property
  · intro hu
    obtain ⟨b, hb⟩ := hz ⟨u, hu⟩
    exact ⟨b, congrArg Subtype.val hb⟩

/-- The full fixed-image fiber, with its canonical surjective coordinates. -/
def fixedImageEquivSurjection (W : Submodule R U) :
    {z : B →ₗ[R] U // z.range = W} ≃
      {z : B →ₗ[R] W // Function.Surjective z} where
  toFun z := ⟨z.val.codRestrict W (fun b => z.property.le (LinearMap.mem_range_self z.val b)), by
    intro w
    have hw : w.val ∈ z.val.range := z.property.symm ▸ w.property
    obtain ⟨b, hb⟩ := hw
    exact ⟨b, Subtype.ext hb⟩⟩
  invFun z := ⟨W.subtype.comp z.val, range_subtype_comp_of_surjective W z.val z.property⟩
  left_inv z := by
    apply Subtype.ext
    apply LinearMap.ext
    intro b
    rfl
  right_inv z := by
    apply Subtype.ext
    apply LinearMap.ext
    intro b
    apply Subtype.ext
    rfl

@[simp] theorem fixedImageEquivSurjection_symm_val (W : Submodule R U)
    (z : {z : B →ₗ[R] W // Function.Surjective z}) :
    ((fixedImageEquivSurjection W).symm z).val = W.subtype.comp z.val := rfl

@[simp] theorem fixedImageEquivSurjection_apply_coe (W : Submodule R U)
    (z : {z : B →ₗ[R] U // z.range = W}) (b : B) :
    ((fixedImageEquivSurjection W z).val b : U) = z.val b := rfl

/-- Frequencies of an exact rank. -/
abbrev ImageRankFrequency (q : ℕ) :=
  {z : B →ₗ[R] U // Module.finrank R z.range = q}

/-- Actual image subspaces of the required dimension. -/
abbrev RankImage (R U : Type*) [Ring R] [AddCommGroup U] [Module R U] (q : ℕ) :=
  {W : Submodule R U // Module.finrank R W = q}

/-- The image classification of an exact-rank frequency. -/
def frequencyImage (q : ℕ) (z : ImageRankFrequency (R := R) (B := B) (U := U) q) :
    RankImage R U q := ⟨z.val.range, z.property⟩

/-- Removing the redundant rank certificate from a fixed-image fiber. -/
def frequencyImageFiberEquiv (q : ℕ) (W : RankImage R U q) :
    {z : ImageRankFrequency (R := R) (B := B) (U := U) q // frequencyImage q z = W} ≃
      {z : B →ₗ[R] U // z.range = W.val} where
  toFun z := ⟨z.val.val, congrArg Subtype.val z.property⟩
  invFun z := ⟨⟨z.val, by rw [z.property]; exact W.property⟩, Subtype.ext z.property⟩
  left_inv z := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv z := by apply Subtype.ext; rfl

/-- Exact rank frequencies are in bijection with a choice of actual image
and a surjective map onto it. -/
def rankFrequencyImageEquiv (q : ℕ) :
    ImageRankFrequency (R := R) (B := B) (U := U) q ≃
      Σ W : RankImage R U q, {z : B →ₗ[R] W.val // Function.Surjective z} :=
  (Equiv.sigmaFiberEquiv (frequencyImage (R := R) (B := B) (U := U) q)).symm.trans
    (Equiv.sigmaCongrRight fun W =>
      (frequencyImageFiberEquiv q W).trans (fixedImageEquivSurjection W.val))

@[simp] theorem rankFrequencyImageEquiv_symm_val (q : ℕ)
    (p : Σ W : RankImage R U q, {z : B →ₗ[R] W.val // Function.Surjective z}) :
    ((rankFrequencyImageEquiv q).symm p).val = p.1.val.subtype.comp p.2.val := rfl

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Coordinates adapted to a prescribed image and any chosen complement. -/
def imageCoordinates (W D : Submodule K V) (h : IsCompl W D) : V ≃ₗ[K] (W × D) :=
  (Submodule.prodEquivOfIsCompl W D h).symm

/-- Vectors in the prescribed image have zero complementary coordinate. -/
@[simp] theorem imageCoordinates_subtype (W D : Submodule K V) (h : IsCompl W D)
    (w : W) : imageCoordinates W D h (w : V) = (w, 0) :=
  Submodule.prodEquivOfIsCompl_symm_apply_left W D h w

end MaxCutGames.Inverse.KMSAnalyticHybridEnergy

end

namespace MaxCutGames.Inverse.KMSAnalyticHybridCoordinates

variable {R A W D B C : Type*} [Ring R]
  [AddCommGroup A] [Module R A] [AddCommGroup W] [Module R W]
  [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

/-- The chosen block compression: restrict to `B`, then forget `A`. -/
def compressBlock (S : (B × C) →ₗ[R] (A × (W × D))) : B →ₗ[R] (W × D) :=
  (LinearMap.snd R A (W × D)).comp (S.comp (LinearMap.inl R B C))

@[simp] theorem compressBlock_apply
    (S : (B × C) →ₗ[R] (A × (W × D))) (b : B) :
    compressBlock S b = (S (b, 0)).2 := rfl

/-- Coordinates of a map whose compression is `(z,0)`. -/
structure Coordinates (z : B →ₗ[R] W) where
  alpha : (B × C) →ₗ[R] A
  psi : (B × C) →ₗ[R] W
  psi_left : psi.comp (LinearMap.inl R B C) = z
  v : C →ₗ[R] D

@[ext] theorem Coordinates.ext {z : B →ₗ[R] W} {p q : Coordinates (A := A) (D := D)
    (C := C) z} (ha : p.alpha = q.alpha) (hp : p.psi = q.psi) (hv : p.v = q.v) : p = q := by
  cases p
  cases q
  cases ha
  cases hp
  cases hv
  rfl

/-- Assemble the three blocks. The last coordinate vanishes on `B`. -/
def assemble {z : B →ₗ[R] W} (p : Coordinates (A := A) (D := D) (C := C) z) :
    (B × C) →ₗ[R] (A × (W × D)) :=
  p.alpha.prod (p.psi.prod (p.v.comp (LinearMap.snd R B C)))

@[simp] theorem assemble_apply {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) (x : B × C) :
    assemble p x = (p.alpha x, p.psi x, p.v x.2) := rfl

@[simp] theorem compressBlock_assemble {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) :
    compressBlock (assemble p) = z.prod (0 : B →ₗ[R] D) := by
  apply LinearMap.ext
  intro b
  have hp : p.psi (b, 0) = z b :=
    congrArg (fun L : (B →ₗ[R] W) => L b) p.psi_left
  simp [compressBlock, assemble, hp]

/-- Extract the unique coordinates from an actual compressed-fiber element. -/
def extract (z : B →ₗ[R] W)
    (S : {S : (B × C) →ₗ[R] (A × (W × D)) //
      compressBlock S = z.prod (0 : B →ₗ[R] D)}) :
    Coordinates (A := A) (D := D) (C := C) z where
  alpha := (LinearMap.fst R A (W × D)).comp S.val
  psi := (LinearMap.fst R W D).comp ((LinearMap.snd R A (W × D)).comp S.val)
  psi_left := by
    apply LinearMap.ext
    intro b
    exact congrArg (fun L : B →ₗ[R] (W × D) => (L b).1) S.property
  v := (LinearMap.snd R W D).comp
    ((LinearMap.snd R A (W × D)).comp (S.val.comp (LinearMap.inr R B C)))

@[simp] theorem assemble_extract (z : B →ₗ[R] W)
    (S : {S : (B × C) →ₗ[R] (A × (W × D)) //
      compressBlock S = z.prod (0 : B →ₗ[R] D)}) :
    assemble (extract z S) = S.val := by
  apply LinearMap.ext
  rintro ⟨b, c⟩
  have hzero : (S.val (b, 0)).2.2 = 0 :=
    congrArg (fun L : B →ₗ[R] (W × D) => (L b).2) S.property
  have hlast : (S.val (b, c)).2.2 = (S.val (0, c)).2.2 := by
    calc
      _ = (S.val ((b, 0) + (0, c))).2.2 := by simp
      _ = (S.val (b, 0)).2.2 + (S.val (0, c)).2.2 := by rw [map_add]; rfl
      _ = _ := by rw [hzero, zero_add]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · exact hlast.symm

@[simp] theorem extract_assemble {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) :
    extract z ⟨assemble p, compressBlock_assemble p⟩ = p := by
  apply Coordinates.ext
  · apply LinearMap.ext
    intro x
    rfl
  · apply LinearMap.ext
    intro x
    rfl
  · apply LinearMap.ext
    intro c
    rfl

/-- An exact compressed-fiber parametrization, valid over any ring. -/
def compressedFiberEquiv (z : B →ₗ[R] W) :
    {S : (B × C) →ₗ[R] (A × (W × D)) //
      compressBlock S = z.prod (0 : B →ₗ[R] D)} ≃
      Coordinates (A := A) (D := D) (C := C) z where
  toFun := extract z
  invFun p := ⟨assemble p, compressBlock_assemble p⟩
  left_inv S := Subtype.ext (assemble_extract z S)
  right_inv := extract_assemble

end MaxCutGames.Inverse.KMSAnalyticHybridCoordinates

/-!
# The actual hybrid selector in compressed-fiber coordinates

When the prescribed compression is onto `W`, the hybrid image and preimage
conditions are equivalent to injectivity of the complementary target map
and surjectivity of the remaining coordinate map. These are conditions on
the actual assembled linear map, with no rank or analytic hypothesis.
-/

/-! The exact injection/surjection factorization of the adapted coordinates. -/

namespace MaxCutGames.Inverse.KMSAnalyticHybridCoordinates

variable {R A W D B C : Type*} [Ring R]
  [AddCommGroup A] [Module R A] [AddCommGroup W] [Module R W]
  [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

/-- The small frequency map before its last coordinate is embedded into `D`. -/
def fullCoordinates {z : B →ₗ[R] W}
    (p : Coordinates (A := A) (D := D) (C := C) z) :
    (B × C) →ₗ[R] (A × (W × C)) :=
  p.alpha.prod (p.psi.prod (LinearMap.snd R B C))

/-- The injection chosen by the last block, keeping the first two blocks fixed. -/
def embedLast (v : C →ₗ[R] D) : (A × (W × C)) →ₗ[R] (A × (W × D)) :=
  (LinearMap.id : A →ₗ[R] A).prodMap ((LinearMap.id : W →ₗ[R] W).prodMap v)

@[simp] theorem embedLast_apply (v : C →ₗ[R] D) (x : A × (W × C)) :
    embedLast v x = (x.1, x.2.1, v x.2.2) := rfl

end MaxCutGames.Inverse.KMSAnalyticHybridCoordinates

/-! The actual hybrid compressed fiber, with no coordinate multiplicity. -/

/-!
# The actual small-space Fourier component

An injection from the small domain into the large domain lifts dual
frequencies by composition. Only surjective small-space frequencies are
retained. The identities below use the actual trace-character coefficients
and normalized primal expectation; no fourth-moment estimate is assumed.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSAnalyticSmallInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The small-space Fourier component inherits the original function's actual
basis invariance. Kernel-orbit transitivity supplies coefficient independence
of the embedding; finite character reindexing supplies function invariance.
There is no additional Fourier-invariance or analytic estimate hypothesis.
-/

/-! Exact coefficient arrays in an adapted hybrid fiber. -/

namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergy
noncomputable section
open scoped BigOperators Classical
open KMSAnalyticHybridCoordinates

variable {R A W D B C : Type*} [Ring R]
  [AddCommGroup A] [Module R A] [AddCommGroup W] [Module R W]
  [AddCommGroup D] [Module R D] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]

/-- The unnormalized fiber of extensions of one compressed frequency. -/
abbrev Extension (z : B →ₗ[R] W) :=
  {ψ : (B × C) →ₗ[R] W // ψ.comp (LinearMap.inl R B C) = z}

/-- The coordinate record has precisely three independent entries. -/
def coordinatesDataEquiv (z : B →ₗ[R] W) :
    Coordinates (A := A) (D := D) (C := C) z ≃
      ((B × C) →ₗ[R] A) × (Extension (C := C) z) × (C →ₗ[R] D) where
  toFun p := (p.alpha, ⟨p.psi, p.psi_left⟩, p.v)
  invFun p := ⟨p.1, p.2.1.val, p.2.1.property, p.2.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by rcases p with ⟨a, ⟨ψ, hψ⟩, v⟩; rfl

def compressedFiberDataEquiv (z : B →ₗ[R] W) :
    {S : (B × C) →ₗ[R] (A × (W × D)) //
      compressBlock S = z.prod (0 : B →ₗ[R] D)} ≃
      ((B × C) →ₗ[R] A) × (Extension (C := C) z) × (C →ₗ[R] D) :=
  (compressedFiberEquiv z).trans (coordinatesDataEquiv z)

/-- Specifying the value on the complementary block gives every extension
exactly once. This will give the cardinality factor `|Hom(C,W)|`. -/
def extensionEquiv (z : B →ₗ[R] W) : Extension (C := C) z ≃ (C →ₗ[R] W) where
  toFun ψ := ψ.val.comp (LinearMap.inr R B C)
  invFun u := ⟨z.coprod u, by ext b; simp⟩
  left_inv ψ := by
    apply Subtype.ext
    apply LinearMap.ext
    rintro ⟨b, c⟩
    have hb : ψ.val (b, 0) = z b :=
      congrArg (fun t : B →ₗ[R] W => t b) ψ.property
    change z b + ψ.val (0, c) = ψ.val (b, c)
    rw [← hb, ← map_add]
    simp
  right_inv u := by ext c; simp

end
end MaxCutGames.Inverse.KMSAnalyticHybridEnergy

/-!
Exact trace-character identities for the adapted Hybrid coordinates. The
three coordinate blocks contribute multiplicatively to the actual character,
and assembling through the last-block embedding preserves the small phase.
These identities require neither rank assumptions nor analytic estimates.
-/

/-!
The frequency dichotomy behind the KMS point-restriction recursion.
A row appended to a surjective frequency is either independent, or is the
unique pullback of a functional on the smaller frequency space.
-/

/-!
Exact Fourier slice energies and their one-point KMS recurrence. The energy
is an unnormalized sum of actual squared coefficients. Translation changes
only a unit sign, so the dependent graph terms in the point recursion have
identical slice energies, without an ambient-cardinality loss.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSAnalyticHybridEnergyImageTransportCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Transport of a prescribed compressed image to adapted coordinates

The complement is an arbitrary actual complement to the image subspace.
The resulting coordinate change carries each original Fourier fiber to the
adapted fiber, preserving coefficients, phases, and the actual selector.
-/

/-!
Transport of actual small components when the ambient domain changes by a
linear equivalence. The coefficient and component identities hold for every
real function; basis invariance is separately transported when available.
-/

/-!
# Product Hybrid energy from actual mixed slices

The derivative's exact rank support is partitioned by its actual compressed
image. Each image is put in complement coordinates, and the proved coefficient
factorization bounds that contribution by an actual mixed slice. The finite
image, extension, and complementary-map counts fit the mixed denominator.
The sole analytic premise is the displayed uniform bound on actual slices.
-/

noncomputable section

namespace MaxCutGames.Inverse.KMSAnalyticHybridEnergy

open scoped BigOperators Classical

local instance (priority := 2000) classicalSurjective {X Y : Type*} :
    DecidablePred (Function.Surjective : (X → Y) → Prop) :=
  fun g => Classical.propDecidable (Function.Surjective g)

end MaxCutGames.Inverse.KMSAnalyticHybridEnergy

/-!
# Exact transport of mixed small-component slices

A codomain equivalence transports the fixed primal coordinates and the
prescribed partial frequency together. The frequency reindexing is bijective,
so the actual slice energy has no multiplicity or normalization factor.
-/

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSFourthMomentPointShuffle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Move one fixed coordinate to the last position while preserving the free
block. These are identities of actual linear maps and restricted functions;
no Fourier support or analytic estimate is assumed.
-/

/-!
# Restricted Fourier sums on the small space

A prescribed partial frequency is encoded by an actual linear projection of
the small codomain. This gives a coordinate-free index for the fixed-character
induction in KMS Lemma 3.19. The statements below establish its exact base
normalization and remove impossible partial frequencies.
-/

/-!
Coordinates adapted to an injected distinguished point. The complementary
subspace contains all old injected directions, so that the original injection
becomes exactly `pointLift` in the constructed coordinates.
-/

/-!
Exact coordinate alignment for the mixed-norm induction. A chosen fixed point
is moved to the last small coordinate, and an actual ambient complement makes
its injection a pointLift. Small-component transport identifies the resulting
functions exactly, so the next recursive estimate concerns the same law.
-/

namespace MaxCutGames.Inverse.KMSFourthMoment

/-!
With no fixed points, the mixed energy is exactly the fixed-character energy
of the actual small component. This is the base interface between the two
KMS inductions; no norm estimate is assumed or altered by the identification.
-/

/-!
The actual mixed-energy induction step of KMS Lemma 3.20. Previously fixed
points form A, the remaining Fourier coordinates form I, and the new fixed
point is last. The dependent graphs translate the old fixed points, which
is why the inductive bound must hold uniformly over those prescribed values.
-/

/-!
Scalar accounting for the genuine point-restriction induction. All ambient
weights remain explicit. A global rank cap R gives a dimension-independent
factor per fixed point; the proof does not assume any mixed-norm estimate.
-/

/-- A deliberately generous rank-dependent cost for one fixed point. -/
def mixedStepFactor (R : ℕ) : ℝ := 2 ^ (2 * R + 2)

end MaxCutGames.Inverse.KMSFourthMoment

/-!
# Homogeneous restriction bounds for the KMS character induction

The restriction below samples linear maps into an actual subspace of the
output. Quantifying over injective presentations makes the bound invariant
under a choice of coordinates. This is a transparent squared-density
hypothesis, not a Fourier, inverse, or fourth-moment estimate.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSFourthMomentZoomInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Point restrictions inherit basis invariance in the remaining coordinates.
Translations split into a shift of the fixed point and a translation of the
remaining matrix; both identities are exact, with no probability loss.
-/

/-!
A transparent local squared-density hypothesis for the new KMS point and
character inductions. The sampled maps are actual affine restrictions,
presented by a surjective domain quotient and an injective codomain map.
No Fourier, hybrid-derivative, rank-level, or inverse estimate is included.
The Grassmann application discharges this predicate from its actual local
density bounds; the analytic induction must still be proved separately.
-/

/-!
# Exact orbit grouping for KMS Fourier norms

The frequency fibers are finite sets with their real cardinality as the
multiplicity. No probability normalization or orbit-size estimate is assumed
by the grouping identity. The later kernel-orbit count supplies these sizes
for the actual binary linear maps.
-/

/-!
The common kernel index for binary maps of fixed rank and for surjective maps
to a fixed comparison space. Both maps below send an actual linear map to its
literal kernel; quotient dimensions follow from the first isomorphism theorem.
-/

namespace MaxCutGames.Inverse.KMSKernelFiberCard

noncomputable section

abbrev F2 := ZMod 2

variable (F E I : Type*)
  [AddCommGroup F] [Module F2 F]
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup I] [Module F2 I]

abbrev KernelClass :=
  {K : Submodule F2 F // Module.finrank F2 (F ⧸ K) = Module.finrank F2 I}

abbrev RankFrequency :=
  {S : F →ₗ[F2] E // Module.finrank F2 S.range = Module.finrank F2 I}

abbrev FullFrequency := {T : F →ₗ[F2] I // Function.Surjective T}

variable {F E I}

def rankKernel (S : RankFrequency F E I) : KernelClass F I :=
  ⟨S.val.ker, S.val.quotKerEquivRange.finrank_eq.trans S.property⟩

def fullKernel (T : FullFrequency F I) : KernelClass F I :=
  ⟨T.val.ker, (T.val.quotKerEquivOfSurjective T.property).finrank_eq⟩

@[simp] theorem rankKernel_val (S : RankFrequency F E I) :
    (rankKernel S).val = S.val.ker := rfl

@[simp] theorem fullKernel_val (T : FullFrequency F I) :
    (fullKernel T).val = T.val.ker := rfl

end
end MaxCutGames.Inverse.KMSKernelFiberCard

/-!
# Fixed kernels and injective quotient maps

Linear maps with a prescribed kernel are in explicit bijection with injective
maps from the corresponding quotient. This elementary counting foundation
works over any ring, and in particular over the binary field used by KMS.
No expansion or rank-level estimate is assumed.
-/

namespace MaxCutGames.Inverse.KMSAnalyticKernelCount

noncomputable section

variable {R E F : Type*} [Ring R]
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

/-- Composing an injective map with the quotient projection has exactly the
prescribed kernel. -/
theorem ker_comp_mkQ (K : Submodule R F) (J : (F ⧸ K) →ₗ[R] E)
    (hJ : Function.Injective J) : (J.comp K.mkQ).ker = K := by
  rw [LinearMap.ker_comp_of_ker_eq_bot K.mkQ (LinearMap.ker_eq_bot.mpr hJ),
    Submodule.ker_mkQ]

/-- Every map with kernel `K` factors uniquely through an injective quotient
map; the inverse sends that quotient map to its composition with `K.mkQ`. -/
def fixedKernelEquivQuotientInjection (K : Submodule R F) :
    {S : F →ₗ[R] E // S.ker = K} ≃
      {J : (F ⧸ K) →ₗ[R] E // Function.Injective J} where
  toFun S := ⟨K.liftQ S.val S.property.symm.le,
    LinearMap.ker_eq_bot.mp (K.ker_liftQ_eq_bot S.val _ S.property.le)⟩
  invFun J := ⟨J.val.comp K.mkQ, ker_comp_mkQ K J.val J.property⟩
  left_inv S := by
    apply Subtype.ext
    exact K.liftQ_mkQ S.val _
  right_inv J := by
    apply Subtype.ext
    apply LinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ := K.mkQ_surjective q
    rfl

@[simp]
theorem fixedKernelEquiv_apply_mkQ (K : Submodule R F)
    (S : {S : F →ₗ[R] E // S.ker = K}) (x : F) :
    (fixedKernelEquivQuotientInjection K S).val (K.mkQ x) = S.val x := rfl

@[simp]
theorem fixedKernelEquiv_symm_apply (K : Submodule R F)
    (J : {J : (F ⧸ K) →ₗ[R] E // Function.Injective J}) :
    ((fixedKernelEquivQuotientInjection K).symm J).val = J.val.comp K.mkQ := rfl

/-- Quotient factorization leaves the image subspace unchanged. -/
theorem range_forward (K : Submodule R F)
    (S : {S : F →ₗ[R] E // S.ker = K}) :
    (fixedKernelEquivQuotientInjection K S).val.range = S.val.range :=
  K.range_liftQ S.val _

/-- A prescribed kernel fixes the rank to the dimension of its quotient. -/
theorem fixedKernel_finrank_eq_quotient (K : Submodule R F)
    (S : {S : F →ₗ[R] E // S.ker = K}) :
    Module.finrank R S.val.range = Module.finrank R (F ⧸ K) := by
  rw [← range_forward K S]
  exact LinearMap.finrank_range_of_inj (fixedKernelEquivQuotientInjection K S).property

end
end MaxCutGames.Inverse.KMSAnalyticKernelCount

/-!
Every kernel class is realized by both families of maps. The witnesses are
constructed from a linear equivalence of the quotient with the comparison
space, followed (for the rank family) by an injection into the ambient space.
No uniformity or fiber-count assertion is assumed.
-/

namespace MaxCutGames.Inverse.KMSKernelFiberCard

open KMSAnalyticKernelCount

noncomputable section

variable {F E I : Type*}
  [AddCommGroup F] [Module F2 F] [FiniteDimensional F2 F]
  [AddCommGroup E] [Module F2 E] [FiniteDimensional F2 E]
  [AddCommGroup I] [Module F2 I] [FiniteDimensional F2 I]

/-- Equal quotient dimension gives an actual linear equivalence. -/
def quotientEquiv (K : KernelClass F I) : (F ⧸ K.val) ≃ₗ[F2] I :=
  Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq K.property)

end
end MaxCutGames.Inverse.KMSKernelFiberCard

/-! Exact counts of injective binary linear maps. Evaluating a map on a
chosen domain basis is a bijection with linearly independent image families.
The count uses the proved finite-field independent-family enumeration. -/

namespace MaxCutGames.Inverse.KMSInjectionCount

open scoped BigOperators

noncomputable section

abbrev F2 := ZMod 2

variable (I E : Type*) [AddCommGroup I] [Module F2 I]
  [AddCommGroup E] [Module F2 E]

/-- The actual number of injective linear maps, with no asymptotic convention. -/
def beta : ℕ := Nat.card {J : I →ₗ[F2] E // Function.Injective J}

/-- A domain basis turns injective maps into independent image families. -/
def injectiveEquivIndependent {ι : Type*} (b : Module.Basis ι F2 I) :
    {J : I →ₗ[F2] E // Function.Injective J} ≃
      {s : ι → E // LinearIndependent F2 s} where
  toFun J := ⟨J.val ∘ b, b.linearIndependent.map' J.val (LinearMap.ker_eq_bot.mpr J.property)⟩
  invFun s := ⟨b.constr F2 s.val, b.injective_constr_of_linearIndependent s.property⟩
  left_inv J := by
    apply Subtype.ext
    exact b.constr_self F2 J.val
  right_inv s := by
    apply Subtype.ext
    funext i
    exact b.constr_basis F2 s.val i

end
end MaxCutGames.Inverse.KMSInjectionCount

/-!
Exact kernel-fiber cardinalities. Factoring through the actual quotient turns
the fixed-kernel fiber into injections, and a quotient equivalence identifies
these with the binary injection count. Restricting to the prescribed rank or
to surjections does not remove any member of the corresponding fiber.
-/

namespace MaxCutGames.Inverse.KMSKernelFiberCard

open KMSAnalyticKernelCount KMSInjectionCount
open scoped Classical

noncomputable section

variable {F E I J : Type*}
  [AddCommGroup F] [Module F2 F]
  [AddCommGroup E] [Module F2 E]
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup J] [Module F2 J]

/-- Changing the domain by a linear equivalence preserves the set of actual
injective linear maps. -/
def injectionEquivOfDomainEquiv (e : J ≃ₗ[F2] I) :
    {u : J →ₗ[F2] E // Function.Injective u} ≃
      {u : I →ₗ[F2] E // Function.Injective u} where
  toFun u := ⟨u.val.comp e.symm.toLinearMap, u.property.comp e.symm.injective⟩
  invFun u := ⟨u.val.comp e.toLinearMap, u.property.comp e.injective⟩
  left_inv u := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change u.val (e.symm (e x)) = u.val x
    rw [e.symm_apply_apply]
  right_inv u := by
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change u.val (e (e.symm x)) = u.val x
    rw [e.apply_symm_apply]

variable [FiniteDimensional F2 F] [FiniteDimensional F2 I]

/-- A fixed-kernel fiber is in explicit bijection with injections from the
comparison space. This includes the zero-dimensional comparison space. -/
def fixedKernelEquivInjection (K : KernelClass F I) :
    {S : F →ₗ[F2] E // S.ker = K.val} ≃
      {J : I →ₗ[F2] E // Function.Injective J} :=
  (fixedKernelEquivQuotientInjection K.val).trans
    (injectionEquivOfDomainEquiv (quotientEquiv K))

/-- The kernel condition already forces the rank condition. -/
def rankFiberEquivFixedKernel (K : KernelClass F I) :
    {S : RankFrequency F E I // rankKernel S = K} ≃
      {S : F →ₗ[F2] E // S.ker = K.val} where
  toFun S := ⟨S.val.val, congrArg Subtype.val S.property⟩
  invFun S := ⟨⟨S.val,
    (fixedKernel_finrank_eq_quotient K.val S).trans K.property⟩,
    Subtype.ext S.property⟩
  left_inv S := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv S := by
    apply Subtype.ext
    rfl

omit [FiniteDimensional F2 F] in
/-- A map into the comparison space with this kernel has full range. -/
theorem surjective_of_kernel_class (K : KernelClass F I)
    (T : F →ₗ[F2] I) (hT : T.ker = K.val) : Function.Surjective T := by
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  exact (fixedKernel_finrank_eq_quotient K.val ⟨T, hT⟩).trans K.property

/-- The kernel condition already forces surjectivity onto the comparison
space. -/
def fullFiberEquivFixedKernel (K : KernelClass F I) :
    {T : FullFrequency F I // fullKernel T = K} ≃
      {T : F →ₗ[F2] I // T.ker = K.val} where
  toFun T := ⟨T.val.val, congrArg Subtype.val T.property⟩
  invFun T := ⟨⟨T.val, surjective_of_kernel_class K T.val T.property⟩,
    Subtype.ext T.property⟩
  left_inv T := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv T := by
    apply Subtype.ext
    rfl

end
end MaxCutGames.Inverse.KMSKernelFiberCard

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSAnalyticRestrictionTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate and budget transport for the genuine homogeneous character
induction. These statements only change presentations of the actual local
squared-density hypothesis and prescribed Fourier sums. -/

/-!
An explicit splitting of a linear functional with a chosen unit preimage.
Both directions retain the chosen vector, permitting compatible splittings of
nested spaces and subspaces in the KMS argument.
-/

namespace MaxCutGames.Inverse.KMSAnalyticFunctionalSplit

variable {K F : Type*} [Field K] [AddCommGroup F] [Module K F]

/-- Split off the coordinate measured by `a`, using the prescribed vector `t`.
The kernel coordinate is exactly `x - a x • t`. -/
def splitEquiv (a : F →ₗ[K] K) (t : F) (ht : a t = 1) :
    F ≃ₗ[K] (a.ker × K) where
  toFun x := (⟨x - a x • t, by simp [LinearMap.mem_ker, ht]⟩, a x)
  invFun p := (p.1 : F) + p.2 • t
  map_add' x y := by
    apply Prod.ext
    · apply Subtype.ext
      change x + y - a (x + y) • t = (x - a x • t) + (y - a y • t)
      rw [map_add, add_smul]
      abel
    · exact a.map_add x y
  map_smul' c x := by
    apply Prod.ext
    · apply Subtype.ext
      change c • x - a (c • x) • t = c • (x - a x • t)
      simp [smul_sub, smul_smul]
    · exact a.map_smul c x
  left_inv x := by
    change x - a x • t + a x • t = x
    exact sub_add_cancel _ _
  right_inv p := by
    have hp : a (p.1 : F) = 0 := p.1.property
    apply Prod.ext
    · apply Subtype.ext
      change (p.1 : F) + p.2 • t - a ((p.1 : F) + p.2 • t) • t = p.1
      simp [hp, ht]
    · change a ((p.1 : F) + p.2 • t) = p.2
      simp [hp, ht]

@[simp] theorem splitEquiv_apply_snd (a : F →ₗ[K] K) (t : F) (ht : a t = 1) (x : F) :
    (splitEquiv a t ht x).2 = a x := rfl

@[simp] theorem splitEquiv_apply_fst_coe (a : F →ₗ[K] K) (t : F) (ht : a t = 1) (x : F) :
    ((splitEquiv a t ht x).1 : F) = x - a x • t := rfl

@[simp] theorem splitEquiv_symm_apply (a : F →ₗ[K] K) (t : F) (ht : a t = 1)
    (p : a.ker × K) :
    (splitEquiv a t ht).symm p = (p.1 : F) + p.2 • t := rfl

@[simp] theorem splitEquiv_symm_apply_zero (a : F →ₗ[K] K) (t : F) (ht : a t = 1)
    (b : a.ker) : (splitEquiv a t ht).symm (b, 0) = (b : F) := by
  simp

@[simp] theorem splitEquiv_apply_ker (a : F →ₗ[K] K) (t : F) (ht : a t = 1)
    (b : a.ker) : splitEquiv a t ht (b : F) = (b, 0) := by
  apply (splitEquiv a t ht).symm.injective
  simp

@[simp] theorem splitEquiv_apply_unit (a : F →ₗ[K] K) (t : F) (ht : a t = 1) :
    splitEquiv a t ht t = (0, 1) := by
  apply (splitEquiv a t ht).symm.injective
  simp

end MaxCutGames.Inverse.KMSAnalyticFunctionalSplit

/-!
Compatible one-coordinate splittings of two surjections with a common target.
A single target coordinate is lifted through both maps. The three resulting
linear equivalences put both surjections into the product of their kernel
restriction with the identity on the binary field.
-/

namespace MaxCutGames.Inverse.KMSAnalyticCompatibleSplitting

noncomputable section

abbrev F2 := ZMod 2

variable {I F K : Type*}
  [AddCommGroup I] [Module F2 I]
  [AddCommGroup F] [Module F2 F]
  [AddCommGroup K] [Module F2 K]

/-- Data of one common coordinate and compatible section vectors. All maps
and all smaller spaces below are constructed from these original data. -/
structure CompatibleSplitting (π : I →ₗ[F2] K) (A : F →ₗ[F2] K) where
  functional : K →ₗ[F2] F2
  targetVector : K
  functional_targetVector : functional targetVector = 1
  leftVector : I
  leftVector_image : π leftVector = targetVector
  rightVector : F
  rightVector_image : A rightVector = targetVector
  left_surjective : Function.Surjective π
  right_surjective : Function.Surjective A

namespace CompatibleSplitting

variable {π : I →ₗ[F2] K} {A : F →ₗ[F2] K}

abbrev K0 (s : CompatibleSplitting π A) := s.functional.ker
abbrev J (s : CompatibleSplitting π A) := (s.functional.comp π).ker
abbrev B (s : CompatibleSplitting π A) := (s.functional.comp A).ker

def targetEquiv (s : CompatibleSplitting π A) : K ≃ₗ[F2] (s.K0 × F2) :=
  KMSAnalyticFunctionalSplit.splitEquiv s.functional s.targetVector
    s.functional_targetVector

def leftEquiv (s : CompatibleSplitting π A) : I ≃ₗ[F2] (s.J × F2) :=
  KMSAnalyticFunctionalSplit.splitEquiv (s.functional.comp π) s.leftVector
    (by change s.functional (π s.leftVector) = 1
        rw [s.leftVector_image, s.functional_targetVector])

def rightEquiv (s : CompatibleSplitting π A) : F ≃ₗ[F2] (s.B × F2) :=
  KMSAnalyticFunctionalSplit.splitEquiv (s.functional.comp A) s.rightVector
    (by change s.functional (A s.rightVector) = 1
        rw [s.rightVector_image, s.functional_targetVector])

/-- The remaining part of the left surjection is its literal restriction. -/
def leftMap (s : CompatibleSplitting π A) : s.J →ₗ[F2] s.K0 :=
  (π.comp (s.functional.comp π).ker.subtype).codRestrict s.functional.ker
    (fun x => x.property)

/-- The remaining part of the right surjection is its literal restriction. -/
def rightMap (s : CompatibleSplitting π A) : s.B →ₗ[F2] s.K0 :=
  (A.comp (s.functional.comp A).ker.subtype).codRestrict s.functional.ker
    (fun x => x.property)

@[simp] theorem leftMap_apply_val (s : CompatibleSplitting π A) (x : s.J) :
    (s.leftMap x : K) = π x := rfl

@[simp] theorem rightMap_apply_val (s : CompatibleSplitting π A) (x : s.B) :
    (s.rightMap x : K) = A x := rfl

@[simp] theorem leftEquiv_symm_apply (s : CompatibleSplitting π A) (x : s.J × F2) :
    s.leftEquiv.symm x = (x.1 : I) + x.2 • s.leftVector := rfl

@[simp] theorem rightEquiv_symm_apply (s : CompatibleSplitting π A) (x : s.B × F2) :
    s.rightEquiv.symm x = (x.1 : F) + x.2 • s.rightVector := rfl

@[simp] theorem targetEquiv_symm_apply (s : CompatibleSplitting π A) (x : s.K0 × F2) :
    s.targetEquiv.symm x = (x.1 : K) + x.2 • s.targetVector := rfl

end CompatibleSplitting

/-- Positive target dimension supplies a basis coordinate; surjectivity
supplies its two lifts. No additional splitting hypothesis is required. -/
theorem exists_compatibleSplitting [FiniteDimensional F2 K]
    (π : I →ₗ[F2] K) (A : F →ₗ[F2] K)
    (hπ : Function.Surjective π) (hA : Function.Surjective A)
    (hdim : 0 < Module.finrank F2 K) : Nonempty (CompatibleSplitting π A) := by
  classical
  let b := Module.finBasis F2 K
  let j : Fin (Module.finrank F2 K) := ⟨0, hdim⟩
  obtain ⟨i, hi⟩ := hπ (b j)
  obtain ⟨f, hf⟩ := hA (b j)
  refine ⟨⟨b.coord j, b j, ?_, i, hi, f, hf, hπ, hA⟩⟩
  simp

def chooseSplit [FiniteDimensional F2 K]
    (π : I →ₗ[F2] K) (A : F →ₗ[F2] K)
    (hπ : Function.Surjective π) (hA : Function.Surjective A)
    (hdim : 0 < Module.finrank F2 K) : CompatibleSplitting π A :=
  Classical.choice (exists_compatibleSplitting π A hπ hA hdim)

end
end MaxCutGames.Inverse.KMSAnalyticCompatibleSplitting

/-! The full fixed-character induction for the actual KMS small component.
The only local hypothesis bounds squared norms of homogeneous restrictions;
all Fourier recursions, multiplicities and coordinate changes are proved.
-/

/-!
The closed KMS mixed restriction estimate. The fixed-character base in the
point induction is discharged by the actual homogeneous character theorem.
Only basis invariance and the transparent local affine squared-density bound
remain; no Fourier-energy or missing-estimate premise occurs here.
-/

namespace MaxCutGames.Inverse.KMSFourthMoment
noncomputable section
open scoped BigOperators Classical

universe u v

variable {E A I J : Type u}
  {F : Type v}
  [AddCommGroup E]
  [AddCommGroup A]
  [AddCommGroup I]
  [AddCommGroup J]
  [AddCommGroup F]
  [Fintype E]
  [Fintype A]
  [Fintype I]
  [Fintype J]
  [Fintype F]

/-- A single uniform constant for all fixed-point dimensions at rank at most R. -/
def mixedRankConstant (R : ℕ) : ℝ := (2 : ℝ) ^ (4 * R * R) * mixedStepFactor R ^ R

end
end MaxCutGames.Inverse.KMSFourthMoment

/-!
A uniform formulation of the genuine KMS mixed estimate. Every instance is
the actual Fourier slice of a partially restricted small component. The
property is preserved by coordinate pullback and follows from the proved
mixed estimate under the affine squared-density hypothesis.
-/

/-! The actual arbitrary-subspace hybrid energy estimate. The proof changes
both ambient spaces to complement coordinates, invokes the proved image
decomposition, and obtains every mixed slice from the actual KMS mixed
restriction theorem. No derivative or moment estimate is assumed. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSMomentConstants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit dimension-independent constants for the new KMS mixed-energy
argument and the generic A5 aggregation. The eventual expansion theorem only
uses positivity and finiteness of these constants, so no rank cutoff exception
or comparison with an earlier rank-level constant is needed. -/

namespace MaxCutGames.Inverse.KMSMomentConstants
noncomputable section
open KMSFourthMoment

/-- The constant after the genuine mixed-energy estimate and A5 aggregation. -/
def fourthMomentConstant (r : ℕ) : ℝ := 2 ^ (109 * r * r + 2 * r)

end
end MaxCutGames.Inverse.KMSMomentConstants

namespace MaxCutGames.Inverse.KMS

noncomputable section
open scoped BigOperators Classical

section FiniteDensity

variable {Ω : Type*} [DecidableEq Ω]

/-- Relative density, with value zero when the conditioning set is empty. -/
def relativeDensity (S I : Finset Ω) : ℝ :=
  ((S ∩ I).card : ℝ) / I.card

end FiniteDensity

abbrev F2 := ZMod 2
abbrev Ambient (n : ℕ) := Fin n → F2

/-- Actual `ell`-dimensional subspaces of the ambient binary vector space. -/
def Vertex (n ell : ℕ) :=
  {L : Submodule F2 (Ambient n) // Module.finrank F2 L = ell}

instance vertexFinite (n ell : ℕ) : Finite (Vertex n ell) := by
  let : Finite (Submodule F2 (Ambient n)) :=
    Finite.of_injective (fun L : Submodule F2 (Ambient n) => (L : Set (Ambient n)))
      SetLike.coe_injective
  exact inferInstanceAs (Finite {L : Submodule F2 (Ambient n) //
    Module.finrank F2 L = ell})

instance vertexFintype (n ell : ℕ) : Fintype (Vertex n ell) := Fintype.ofFinite _

/-- A neighbor is distinct and meets the vertex in a hyperplane. The explicit
distinctness also makes the definition harmless at dimension zero. -/
def Adjacent {n ell : ℕ} (L M : Vertex n ell) : Prop :=
  L ≠ M ∧ Module.finrank F2 ↥(L.val ⊓ M.val : Submodule F2 (Ambient n)) + 1 = ell

def neighbors {n ell : ℕ} (L : Vertex n ell) : Finset (Vertex n ell) :=
  Finset.univ.filter (Adjacent L)

/-- Uniform start in `S`, followed by a uniform Grassmann neighbor. -/
def retention {n ell : ℕ} (S : Finset (Vertex n ell)) : ℝ :=
  (∑ L ∈ S, relativeDensity S (neighbors L)) / S.card

/-- The actual interval `A ≤ L ≤ B` among the `ell`-dimensional vertices. -/
def interval {n ell : ℕ} (A B : Submodule F2 (Ambient n)) :
    Finset (Vertex n ell) :=
  Finset.univ.filter fun L => A ≤ L.val ∧ L.val ≤ B

/-- The parameter order needed from KMS, including a nonempty dense interval.
OPEN: no inhabitant of this proposition is supplied. In particular `r` and
`alpha` must be fixed before `ell`, and the ambient threshold may then depend
on `ell`. A bound with `alpha = 2^(-ell)` does not meet this interface. -/
def ExpansionPrinciple : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ζ < 1 →
    ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧
      ∃ r : ℕ, 1 ≤ r ∧ ∃ ell₀ : ℕ, ∀ ell : ℕ, ell₀ ≤ ell →
        ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          ∀ S : Finset (Vertex n ell), S.Nonempty → ζ ≤ retention S →
            ∃ A B : Submodule F2 (Ambient n),
              A ≤ B ∧ Module.finrank F2 A + (n - Module.finrank F2 B) ≤ r ∧
                (S ∩ interval A B).Nonempty ∧ α ≤ relativeDensity S (interval A B)

end
end MaxCutGames.Inverse.KMS

/-!
# The ordered-basis lift of a Grassmann set

The ambient sample space contains every linear map, including singular maps.
The lift accepts exactly maps whose range is one of the specified
`ell`-dimensional subspaces. Thus dependence is rejected, rather than silently
conditioning the ambient uniform distribution on independence.
-/

namespace MaxCutGames.Inverse.KMSBasisComparison

noncomputable section
open scoped Classical

abbrev BasisMap (n ell : ℕ) := KMS.Ambient ell →ₗ[KMS.F2] KMS.Ambient n

instance basisMapFinite (n ell : ℕ) : Finite (BasisMap n ell) :=
  Finite.of_injective (fun X : BasisMap n ell => (X : KMS.Ambient ell → KMS.Ambient n))
    DFunLike.coe_injective

instance basisMapFintype (n ell : ℕ) : Fintype (BasisMap n ell) := Fintype.ofFinite _

/-- Membership in the lift, expressed by the actual linear-map range. -/
def InLift {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) (X : BasisMap n ell) : Prop :=
  ∃ L ∈ S, LinearMap.range X = L.val

/-- The lifted finite set in the whole map space. -/
def lift {n ell : ℕ} (S : Finset (KMS.Vertex n ell)) : Finset (BasisMap n ell) :=
  Finset.univ.filter (InLift S)

@[simp] theorem mem_lift {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) : X ∈ lift S ↔ InLift S X := by
  simp [lift]

/-- Real Boolean indicator, in the orientation used by the matrix Fourier transform. -/
def liftedIndicator {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) : ℝ := if InLift S X then 1 else 0

/-- A map accepted by the lift has full column rank. -/
theorem injective_of_inLift {n ell : ℕ} {S : Finset (KMS.Vertex n ell)}
    {X : BasisMap n ell} (h : InLift S X) : Function.Injective X := by
  obtain ⟨L, _, hL⟩ := h
  have hr : Module.finrank KMS.F2 (LinearMap.range X) = ell := by
    rw [hL]
    exact L.property
  have hd := X.finrank_range_add_finrank_ker
  have he : Module.finrank KMS.F2 (KMS.Ambient ell) = ell := by
    simp [KMS.Ambient]
  have hk : Module.finrank KMS.F2 (LinearMap.ker X) = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)

/-- The actual Grassmann vertex represented by an injective map. -/
def rangeVertex {n ell : ℕ} (X : BasisMap n ell) (hX : Function.Injective X) :
    KMS.Vertex n ell :=
  ⟨LinearMap.range X, by
    rw [LinearMap.finrank_range_of_inj hX]
    simp [KMS.Ambient]⟩

theorem inLift_iff_rangeVertex_mem {n ell : ℕ} (S : Finset (KMS.Vertex n ell))
    (X : BasisMap n ell) (hX : Function.Injective X) :
    InLift S X ↔ rangeVertex X hX ∈ S := by
  constructor
  · rintro ⟨L, hL, hXL⟩
    have he : rangeVertex X hX = L := Subtype.ext hXL
    simpa only [he] using hL
  · intro h
    exact ⟨rangeVertex X hX, h, rfl⟩

end
end MaxCutGames.Inverse.KMSBasisComparison

/-! Exact finite counting for the restricted-basis lift.  In particular, failed
independent completions contribute zero rather than an additive error. -/

namespace MaxCutGames.Inverse.KMSBasisComparisonPseudorandom

/-!
An independent frame inside `L` can be completed using vectors from `W` whenever
`L` lies in the sum of the frame's span and `W`.
-/

/-!
# Equal fibers for restricted basis completion

A fixed independent tuple may have vectors outside the restricting submodule.
Nevertheless, any two nonempty fibers of independent completions inside that
submodule are equivalent. The change of basis fixes the fixed tuple, and its
difference from the identity has image in the restricting submodule.
-/

noncomputable section
open scoped Classical

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {q t : ℕ}

/-- Ordered completions in `W` of `Q` to an independent spanning tuple for `L`. -/
def RestrictedCompletion (Q : Fin q → V) (W L : Submodule K V) :=
  {z : Fin t → W //
    LinearIndependent K (Sum.elim Q (fun i => (z i : V))) ∧
      Submodule.span K (Set.range (Sum.elim Q (fun i => (z i : V)))) = L}

variable {Q : Fin q → V} {W L M N : Submodule K V}

/-- A completion, regarded as a basis of the resulting subspace. -/
def completionBasis (z : RestrictedCompletion (t := t) Q W L) :
    Module.Basis (Fin q ⊕ Fin t) K L :=
  (Module.Basis.span z.property.1).map (LinearEquiv.ofEq _ _ z.property.2)

@[simp] theorem completionBasis_coe
    (z : RestrictedCompletion (t := t) Q W L) (i : Fin q ⊕ Fin t) :
    (completionBasis z i : V) = Sum.elim Q (fun j => (z.val j : V)) i := by
  simp [completionBasis]

/-- Recover a restricted completion from a basis having the prescribed prefix. -/
def completionOfBasis (b : Module.Basis (Fin q ⊕ Fin t) K L)
    (hQ : ∀ i, (b (Sum.inl i) : V) = Q i)
    (hW : ∀ i, (b (Sum.inr i) : V) ∈ W) :
    RestrictedCompletion (t := t) Q W L := by
  have hb : Sum.elim Q (fun i => ((⟨b (Sum.inr i), hW i⟩ : W) : V)) =
      fun i => (b i : V) := by
    funext i
    cases i with
    | inl i => exact (hQ i).symm
    | inr i => rfl
  refine ⟨fun i => ⟨b (Sum.inr i), hW i⟩, ?_, ?_⟩
  · rw [hb]
    exact b.linearIndependent.map' L.subtype (by simp)
  · rw [hb]
    calc
      Submodule.span K (Set.range fun i => (b i : V)) =
          (Submodule.span K (Set.range b)).map L.subtype := by
        rw [Submodule.map_span, ← Set.range_comp]
        rfl
      _ = L := by rw [b.span_eq]; simp

/-- The unique basis change carrying the first completion to the second. -/
def completionSpanEquiv
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) : L ≃ₗ[K] M :=
  (completionBasis x).equiv (completionBasis y) (Equiv.refl _)

@[simp] theorem completionSpanEquiv_basis
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) (i : Fin q ⊕ Fin t) :
    completionSpanEquiv x y (completionBasis x i) = completionBasis y i := by
  simp [completionSpanEquiv]

@[simp] theorem completionSpanEquiv_symm
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) :
    (completionSpanEquiv x y).symm = completionSpanEquiv y x := by
  simp [completionSpanEquiv]

/-- Changing the completion changes every vector by an element of `W`. -/
theorem completionSpanEquiv_sub_mem
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) (v : L) :
    (completionSpanEquiv x y v : V) - (v : V) ∈ W := by
  let d : L →ₗ[K] V := M.subtype.comp (completionSpanEquiv x y).toLinearMap - L.subtype
  have hd : (⊤ : Submodule K L) ≤ W.comap d := by
    rw [← (completionBasis x).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change d (completionBasis x i) ∈ W
    change (completionSpanEquiv x y (completionBasis x i) : V) -
      (completionBasis x i : V) ∈ W
    rw [completionSpanEquiv_basis]
    cases i with
    | inl i => simp
    | inr i =>
      simpa only [completionBasis_coe, Sum.elim_inr] using
        W.sub_mem (y.val i).property (x.val i).property
  exact hd (Submodule.mem_top : v ∈ (⊤ : Submodule K L))

/-- The basis change preserves membership in `W`, without requiring `Q ⊆ W`. -/
theorem completionSpanEquiv_mem_iff
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) (v : L) :
    (completionSpanEquiv x y v : V) ∈ W ↔ (v : V) ∈ W := by
  have hd := completionSpanEquiv_sub_mem x y v
  constructor
  · intro hv
    exact (W.sub_mem_iff_right hv).mp hd
  · intro hv
    exact (W.sub_mem_iff_left hv).mp hd

/-- Transport every restricted completion along one fixed basis change. -/
def transportCompletion
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M)
    (z : RestrictedCompletion (t := t) Q W L) :
    RestrictedCompletion (t := t) Q W M :=
  completionOfBasis ((completionBasis z).map (completionSpanEquiv x y))
    (by
      intro i
      have h : completionBasis z (Sum.inl i) = completionBasis x (Sum.inl i) := by
        apply Subtype.ext
        simp
      simp [Module.Basis.map_apply, h])
    (by
      intro i
      change (completionSpanEquiv x y (completionBasis z (Sum.inr i)) : V) ∈ W
      apply (completionSpanEquiv_mem_iff x y _).mpr
      simp)

@[simp] theorem transportCompletion_coe
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M)
    (z : RestrictedCompletion (t := t) Q W L) (i : Fin t) :
    ((transportCompletion x y z).val i : V) =
      (completionSpanEquiv x y (completionBasis z (Sum.inr i)) : V) := rfl

theorem transportCompletion_inverse
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M)
    (z : RestrictedCompletion (t := t) Q W L) :
    transportCompletion y x (transportCompletion x y z) = z := by
  apply Subtype.ext
  funext i
  apply Subtype.ext
  rw [transportCompletion_coe]
  have hb : completionBasis (transportCompletion x y z) (Sum.inr i) =
      completionSpanEquiv x y (completionBasis z (Sum.inr i)) := by
    apply Subtype.ext
    simp
  rw [hb, ← completionSpanEquiv_symm, LinearEquiv.symm_apply_apply]
  simp

/-- All nonempty restricted-completion fibers are equivalent. -/
def restrictedCompletionEquiv
    (x : RestrictedCompletion (t := t) Q W L)
    (y : RestrictedCompletion (t := t) Q W M) :
    RestrictedCompletion (t := t) Q W L ≃ RestrictedCompletion (t := t) Q W M where
  toFun := transportCompletion x y
  invFun := transportCompletion y x
  left_inv := transportCompletion_inverse x y
  right_inv := transportCompletion_inverse y x

end

/-!
# Restricted densities in the ordered-basis lift

The prefix vectors are arbitrary: they may be dependent, and they need not lie
in the subspace from which the remaining vectors are sampled. The relevant
Grassmann interval has lower endpoint `span Q` and upper endpoint `span Q ⊔ W`.
-/

noncomputable section
open scoped BigOperators Classical
open KMS

variable {n q t : ℕ}

def prefixSpan (Q : Fin q → Ambient n) : Submodule F2 (Ambient n) :=
  Submodule.span F2 (Set.range Q)

def joinedTuple (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (z : Fin t → W) : (Fin q ⊕ Fin t) → Ambient n :=
  Sum.elim Q (fun i => (z i : Ambient n))

abbrev IndependentCompletion (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n)) :=
  {z : Fin t → W // LinearIndependent F2 (joinedTuple Q W z)}

def completionVertex (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (z : IndependentCompletion (t := t) Q W) : Vertex n (q + t) :=
  ⟨Submodule.span F2 (Set.range (joinedTuple Q W z.val)), by
    simpa using finrank_span_eq_card z.property⟩

theorem prefix_le_completion (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (z : IndependentCompletion (t := t) Q W) :
    prefixSpan Q ≤ (completionVertex Q W z).val := by
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨Sum.inl i, rfl⟩

theorem completion_le_sup (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (z : IndependentCompletion (t := t) Q W) :
    (completionVertex Q W z).val ≤ prefixSpan Q ⊔ W := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  cases i with
  | inl i =>
      exact (le_sup_left : prefixSpan Q ≤ prefixSpan Q ⊔ W)
        (Submodule.subset_span ⟨i, rfl⟩)
  | inr i =>
      exact (le_sup_right : W ≤ prefixSpan Q ⊔ W) (z.val i).property

theorem completion_mem_interval (Q : Fin q → Ambient n)
    (W : Submodule F2 (Ambient n)) (z : IndependentCompletion (t := t) Q W) :
    completionVertex Q W z ∈ interval (prefixSpan Q) (prefixSpan Q ⊔ W) := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    prefix_le_completion Q W z, completion_le_sup Q W z⟩

def GrassmannPseudorandom {ell : ℕ} (S : Finset (Vertex n ell))
    (r : ℕ) (ε : ℝ) : Prop :=
  ∀ A B : Submodule F2 (Ambient n), A ≤ B →
    Module.finrank F2 A + (n - Module.finrank F2 B) ≤ r →
      relativeDensity S (interval A B) ≤ ε

def completionEvent (S : Finset (Vertex n (q + t)))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n)) (z : Fin t → W) : Prop :=
  ∃ h : LinearIndependent F2 (joinedTuple Q W z), completionVertex Q W ⟨z, h⟩ ∈ S

/-- The denominator counts *all* remaining tuples drawn uniformly from W.
Dependent completions are rejected, without conditioning away their mass. -/
def restrictedLiftDensity (S : Finset (Vertex n (q + t)))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n)) : ℝ :=
  (Nat.card {z : Fin t → W // completionEvent S Q W z} : ℝ) /
    Nat.card (Fin t → W)

def TuplePseudorandom {ell : ℕ} (S : Finset (Vertex n ell))
    (r : ℕ) (ε : ℝ) : Prop :=
  ∀ q t : ℕ, ∀ h : q + t = ell, ∀ Q : Fin q → Ambient n,
    ∀ W : Submodule F2 (Ambient n), q + (n - Module.finrank F2 W) ≤ r →
      restrictedLiftDensity (h.symm ▸ S) Q W ≤ ε

abbrev IntervalVertex (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n)) :=
  ↥(interval (ell := q + t) (prefixSpan Q) (prefixSpan Q ⊔ W))

def completionIntervalVertex (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (z : IndependentCompletion (t := t) Q W) : IntervalVertex (t := t) Q W :=
  ⟨completionVertex Q W z, completion_mem_interval Q W z⟩

def completionFiberEquiv (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n))
    (L : IntervalVertex (t := t) Q W) :
    {z : IndependentCompletion (t := t) Q W // completionIntervalVertex Q W z = L} ≃
      RestrictedCompletion (t := t) Q W L.val.val where
  toFun z := ⟨z.val.val, z.val.property,
    congrArg (fun M => M.val.val) z.property⟩
  invFun z := ⟨⟨z.val, z.property.1⟩, Subtype.ext (Subtype.ext z.property.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

def completionEventEquiv (S : Finset (Vertex n (q + t)))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n)) :
    {z : Fin t → W // completionEvent S Q W z} ≃
      {z : IndependentCompletion (t := t) Q W // completionVertex Q W z ∈ S} where
  toFun z := ⟨⟨z.val, z.property.choose⟩, z.property.choose_spec⟩
  invFun z := ⟨z.val.val, z.val.property, z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def intervalEventEquiv (S : Finset (Vertex n (q + t)))
    (Q : Fin q → Ambient n) (W : Submodule F2 (Ambient n)) :
    {L : IntervalVertex (t := t) Q W // L.val ∈ S} ≃
      ↥(S ∩ interval (prefixSpan Q) (prefixSpan Q ⊔ W)) where
  toFun L := ⟨L.val.val, Finset.mem_inter.mpr ⟨L.property, L.val.property⟩⟩
  invFun L := ⟨⟨L.val, (Finset.mem_inter.mp L.property).2⟩,
    (Finset.mem_inter.mp L.property).1⟩
  left_inv _ := rfl
  right_inv _ := rfl

end
end MaxCutGames.Inverse.KMSBasisComparisonPseudorandom

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSBasisComparisonPseudorandomTupleMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The restricted tuple law is the actual linear-map lift law in coordinates,
with all singular tuples still present in the uniform denominator. -/

namespace MaxCutGames.Inverse.KMSBasisComparisonPseudorandom

noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison

variable {n q t : ℕ}

def tupleBasis (q t : ℕ) : Module.Basis (Fin q ⊕ Fin t) F2 (Ambient (q + t)) :=
  (Pi.basisFun F2 (Fin (q + t))).reindex finSumFinEquiv.symm

def tupleMap (x : (Fin q ⊕ Fin t) → Ambient n) : BasisMap n (q + t) :=
  (tupleBasis q t).constr F2 x

@[simp] theorem tupleMap_basis (x : (Fin q ⊕ Fin t) → Ambient n)
    (i : Fin q ⊕ Fin t) : tupleMap x (tupleBasis q t i) = x i :=
  (tupleBasis q t).constr_basis F2 x i

end
end MaxCutGames.Inverse.KMSBasisComparisonPseudorandom

/-!
The KMS restricted-tuple bound in any adapted basis, followed by an exact
uniform affine translation of the free coordinates. No generic rank-level
inequality is used: this is a change of coordinates for the actual lift.
-/

namespace MaxCutGames.Inverse.KMSAffineRestriction
noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison KMSBasisComparisonPseudorandom

variable {n ell q t r : ℕ} {ε : ℝ}

/-- Coordinates of a uniform linear map, translated by a fixed linear map,
are still exactly uniform. This also covers zero-dimensional free domains. -/
def affineCoordinates {E W : Type*}
    [AddCommGroup E] [Module F2 E] [AddCommGroup W] [Module F2 W]
    (b : Module.Basis (Fin t) F2 E) (T : E →ₗ[F2] W) :
    (E →ₗ[F2] W) ≃ (Fin t → W) :=
  ((b.constr F2).toEquiv).symm.trans (Equiv.addLeft (fun i => T (b i)))

@[simp] theorem affineCoordinates_apply {E W : Type*}
    [AddCommGroup E] [Module F2 E] [AddCommGroup W] [Module F2 W]
    (b : Module.Basis (Fin t) F2 E) (T H : E →ₗ[F2] W) (i : Fin t) :
    affineCoordinates b T H i = T (b i) + H (b i) := rfl

end
end MaxCutGames.Inverse.KMSAffineRestriction

/-!
Complements adapted to an affine restriction. The prescribed directions are
contained in a small summand, and the complementary directions are mapped into
the prescribed target subspace. This is ordinary finite-dimensional geometry;
no Fourier inequality or pseudorandomness hypothesis is used.
-/

/-!
The actual parameter space of an affine matrix restriction splits along a
complementary domain decomposition. The constrained coordinate is a map out of
`U / D`, while the complementary coordinate is an unrestricted map into `W`.
The equivalence transports the full uniform law to independent uniform factors.
-/

/-!
Grassmann interval pseudorandomness controls actual arbitrary affine matrix
restrictions, at twice the restriction order. The proof chooses a bounded
prefix containing the vanishing subspace and all nonhomogeneous directions,
splits the exact quotient-map parameter law, and applies the tuple estimate.
-/

namespace MaxCutGames.Inverse.KMSAffineRestriction
noncomputable section
open scoped BigOperators Classical
open KMS KMSBasisComparison KMSBasisComparisonPseudorandom

variable {n ell q t : ℕ}

/-- Basis obtained from a genuine complementary domain decomposition. -/
def complementBasis (U E0 : Submodule F2 (Ambient ell)) (hc : IsCompl U E0)
    (bU : Module.Basis (Fin q) F2 U) (b0 : Module.Basis (Fin t) F2 E0) :
    Module.Basis (Fin q ⊕ Fin t) F2 (Ambient ell) :=
  (bU.prod b0).map (Submodule.prodEquivOfIsCompl U E0 hc)

end
end MaxCutGames.Inverse.KMSAffineRestriction

/-!
An affine map family presented by a surjective input map and an injective
output map is precisely the quotient-parameter family with vanishing subspace
the input kernel and target subspace the output range. Both its uniform law
and its dimension budget agree exactly with the intrinsic restriction data.
-/

/-! The actual Grassmann local-density hypothesis discharges the affine
squared-density predicate used by the new KMS point/character inductions. -/

/-!
# Tuple pseudorandomness controls the actual affine squared density

This is the input conversion needed by the ordered-basis expansion theorem.
It starts directly from its tuple pseudorandomness assumption. All affine
intercepts and the full uniform parameter law are preserved by the checked
adapted-complement, split, and presentation equivalences.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSMomentTheorem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual upper fourth-moment theorem for the full-rank lift of a
Grassmann set. Its hypotheses are literal tuple probabilities. The affine
sampling law, mixed estimate and hybrid derivative estimate are all discharged
by proved lemmas; there is no analytic estimate among the hypotheses. -/

namespace MaxCutGames.Inverse.KMSMomentScalar

noncomputable section
open scoped BigOperators Classical

variable {X : Type*} [Fintype X]

def IsBoolean (f : X → ℝ) : Prop := ∀ x, f x = 0 ∨ f x = 1

end
end MaxCutGames.Inverse.KMSMomentScalar

/-!
The spectral cutoff step of KMS on the actual full uniform rank-one noise.
The low-level fourth-moment estimate remains an explicit input to the last
combining lemma; none of these statements asserts that estimate or expansion.
The multiplier is reused from the proved uniform-subspace kernel count.
-/

namespace MaxCutGames.Inverse.KMSLowLevel
noncomputable section
open scoped BigOperators Classical
open MaxCutGames.Inverse.KMSMomentScalar

section FiniteCutoff
variable {I : Type*} [Fintype I]

def rankEnergy (rank : I → ℕ) (a : I → ℝ) (i : ℕ) : ℝ :=
  ∑ s, if rank s = i then a s ^ 2 else 0

end FiniteCutoff

end
end MaxCutGames.Inverse.KMSLowLevel

/-!
The KMS scalar and spectral conclusion with an arbitrary dimension-independent
upper-moment constant. This accommodates quantitative proofs with coarser
constants without changing the order of any dimension choices.
-/

/-! Exact finite conditioning error for bounded functions. These identities
keep the rejected mass visible when comparing all maps with independent bases.
-/

/-!
The good event for an ordered-basis rank-one update is that its functional
is nonzero and its direction lies outside the starting range. Its exact
finite cardinality gives the exceptional-mass bound without conditioning
either factor of the original uniform experiment.
-/

/-!
Exact finite counts for the Grassmann graph comparison in Section 4.
The quotient-line parametrization is independent of any expansion theorem.
-/

namespace MaxCutGames.Inverse.MatrixChart

open Module

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

/-- One-dimensional vector subspaces. -/
abbrev Lines (K E : Type*) [Field K] [AddCommGroup E] [Module K E] :=
  {L : Submodule K E // finrank K L = 1}

/-- Hyperplanes, expressed without truncated dimension subtraction. -/
abbrev Hyperplanes (K E : Type*) [Field K] [AddCommGroup E] [Module K E] :=
  {H : Submodule K E // finrank K H + 1 = finrank K E}

/-- Dual annihilation bijects hyperplanes with lines in the dual space. -/
noncomputable def hyperplanesEquivDualLines [FiniteDimensional K E] :
    Hyperplanes K E ≃ Lines K (Module.Dual K E) where
  toFun H := ⟨H.val.dualAnnihilator, by
    have h := Subspace.finrank_add_finrank_dualAnnihilator_eq H.val
    have hH := H.property
    omega⟩
  invFun L := ⟨L.val.dualCoannihilator, by
    have h := Subspace.finrank_add_finrank_dualCoannihilator_eq L.val
    rw [L.property] at h
    omega⟩
  left_inv H := by
    apply Subtype.ext
    exact Subspace.dualAnnihilator_dualCoannihilator_eq
  right_inv L := by
    apply Subtype.ext
    exact Subspace.dualCoannihilator_dualAnnihilator_eq

/-- A dimension identity for the quotient correspondence, retaining addition. -/
theorem finrank_map_mkQ_add [FiniteDimensional K E]
    (H W : Submodule K E) (hHW : H ≤ W) :
    finrank K (W.map H.mkQ) + finrank K H = finrank K W := by
  have h := LinearMap.finrank_range_add_finrank_ker (H.mkQ.comp W.subtype)
  have hr : LinearMap.range (H.mkQ.comp W.subtype) = W.map H.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hk : LinearMap.ker (H.mkQ.comp W.subtype) = H.comap W.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  rw [hr, hk, (Submodule.comapSubtypeEquivOfLe hHW).finrank_eq] at h
  exact h

/-- One-dimensional extensions of a subspace. -/
abbrev Extensions (H : Submodule K E) :=
  {W : Submodule K E // H ≤ W ∧ finrank K W = finrank K H + 1}

/-- The quotient correspondence identifies extensions with quotient lines. -/
noncomputable def extensionsEquivLines [FiniteDimensional K E]
    (H : Submodule K E) : Extensions H ≃ Lines K (E ⧸ H) where
  toFun W := ⟨W.val.map H.mkQ, by
    have h := finrank_map_mkQ_add H W.val W.property.1
    rw [W.property.2] at h
    omega⟩
  invFun L := ⟨L.val.comap H.mkQ, Submodule.le_comap_mkQ H L.val, by
    have h := finrank_map_mkQ_add H (L.val.comap H.mkQ)
      (Submodule.le_comap_mkQ H L.val)
    have heq : (L.val.comap H.mkQ).map H.mkQ = L.val :=
      Submodule.map_comap_eq_self (by simp)
    rw [heq, L.property] at h
    omega⟩
  left_inv W := by
    apply Subtype.ext
    simp [Submodule.comap_map_mkQ, sup_eq_right.mpr W.property.1]
  right_inv L := by
    apply Subtype.ext
    exact Submodule.map_comap_eq_self (by simp)

end MaxCutGames.Inverse.MatrixChart

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Sample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace OptimalMaxCut.CounterMachine
open Turing

inductive Tape (R : Type) where
  | input | backup | output | reg (r : R)
  deriving DecidableEq, Fintype

inductive Instruction (R L : Type) where
  | inc (r : R) (next : L)
  | dec (r : R) (positive zero : L)
  | test (r : R) (zero positive : L)
  | read (one zero empty : L)
  | back (nonempty empty : L)
  | write (b : Bool) (next : L)
  | discard (next : L)
  | jump (next : L)
  | halt

structure Data (R : Type) where
  reg : R → ℕ
  input : List Bool
  backup : List Bool
  output : List Bool

structure Configuration (R L : Type) extends Data R where
  label : Option L

variable {R L : Type} [DecidableEq R]

def Instruction.execute (i : Instruction R L) (d : Data R) : Configuration R L :=
  match i with
  | .inc r next => ⟨{ d with reg := Function.update d.reg r (d.reg r + 1) }, some next⟩
  | .dec r positive zero =>
    ⟨{ d with reg := Function.update d.reg r (d.reg r - 1) },
      some (if d.reg r = 0 then zero else positive)⟩
  | .test r zero positive => ⟨d, some (if d.reg r = 0 then zero else positive)⟩
  | .read one zero empty =>
    ⟨{ d with input := d.input.tail, backup := d.input.take 1 ++ d.backup }, some (match d.input with
      | [] => empty | true :: _ => one | false :: _ => zero)⟩
  | .back nonempty empty =>
    ⟨{ d with input := d.backup.take 1 ++ d.input, backup := d.backup.tail },
      some (if d.backup = [] then empty else nonempty)⟩
  | .write b next => ⟨{ d with output := b :: d.output }, some next⟩
  | .discard next => ⟨{d with input := d.input.tail}, some next⟩
  | .jump next => ⟨d, some next⟩
  | .halt => ⟨d, none⟩

def step (p : L → Instruction R L) (c : Configuration R L) : Option (Configuration R L) :=
  c.label.map (fun l => (p l).execute c.toData)

def tapes (d : Data R) : Tape R → List Bool
  | .input => d.input
  | .backup => d.backup
  | .output => d.output
  | .reg r => List.replicate (d.reg r) true

def embed (c : Configuration R L) : TM2.Cfg (fun _ : Tape R => Bool) L (Option Bool) :=
  ⟨c.label, none, tapes c.toData⟩

def goto (l : L) : TM2.Stmt (fun _ : Tape R => Bool) L (Option Bool) :=
  .load (fun _ => none) (.goto (fun _ => l))

def Instruction.code : Instruction R L → TM2.Stmt (fun _ : Tape R => Bool) L (Option Bool)
  | .inc r next => .push (.reg r) (fun _ => true) (goto next)
  | .dec r positive zero => .pop (.reg r) (fun _ b => b)
      (.branch (fun b => b.isSome) (goto positive) (goto zero))
  | .test r zero positive => .peek (.reg r) (fun _ b => b)
      (.branch (fun b => b.isSome) (goto positive) (goto zero))
  | .read one zero empty => .pop .input (fun _ b => b)
      (.branch (fun b => b.isSome)
        (.push .backup (fun b => b.getD false)
          (.branch (fun b => b.getD false) (goto one) (goto zero))) (goto empty))
  | .back nonempty empty => .pop .backup (fun _ b => b)
      (.branch (fun b => b.isSome)
        (.push .input (fun b => b.getD false) (goto nonempty)) (goto empty))
  | .write b next => .push .output (fun _ => b) (goto next)
  | .discard next => .pop .input (fun _ _ => none) (goto next)
  | .jump next => goto next
  | .halt => .halt

 theorem tapes_inc (d : Data R) (r : R) :
    tapes { d with reg := Function.update d.reg r (d.reg r + 1) } =
      Function.update (tapes d) (.reg r) (true :: tapes d (.reg r)) := by
  funext k
  cases k with
  | input => simp [tapes]
  | output => simp [tapes]
  | backup => simp [tapes]
  | reg s => by_cases h : s = r <;> simp [tapes, h, List.replicate_succ]

 theorem tapes_dec (d : Data R) (r : R) :
    tapes { d with reg := Function.update d.reg r (d.reg r - 1) } =
      Function.update (tapes d) (.reg r) (tapes d (.reg r)).tail := by
  funext k
  cases k with
  | input => simp [tapes]
  | output => simp [tapes]
  | backup => simp [tapes]
  | reg s => by_cases h : s = r <;> simp [tapes, h]

 theorem tapes_read (d : Data R) :
    tapes { d with input := d.input.tail, backup := d.input.take 1 ++ d.backup } =
      Function.update (Function.update (tapes d) .input d.input.tail) .backup
        (d.input.take 1 ++ d.backup) := by
  funext k; cases k <;> simp [tapes]

 theorem tapes_back (d : Data R) :
    tapes { d with input := d.backup.take 1 ++ d.input, backup := d.backup.tail } =
      Function.update (Function.update (tapes d) .backup d.backup.tail) .input
        (d.backup.take 1 ++ d.input) := by
  funext k; cases k <;> simp [tapes]

 theorem tapes_write (d : Data R) (b : Bool) :
    tapes { d with output := b :: d.output } =
      Function.update (tapes d) .output (b :: d.output) := by
  funext k; cases k <;> simp [tapes]

 theorem instruction_simulation (i : Instruction R L) (d : Data R) :
    TM2.stepAux i.code none (tapes d) = embed (i.execute d) := by
  cases i with
  | inc r next => simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed, tapes_inc]
  | dec r pos zero =>
    cases h : d.reg r with
    | zero =>
      simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed, tapes, h]
      simpa [h, tapes] using (tapes_dec d r).symm
    | succ n =>
      simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed,
        tapes, h, List.replicate_succ]
      simpa [h, tapes] using (tapes_dec d r).symm
  | test r zero pos =>
    cases h : d.reg r <;>
      simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed, tapes, h, List.replicate_succ]
  | read one zero empty =>
    cases h : d.input with
    | nil =>
      simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed, tapes, h]
      funext k; cases k <;> simp [tapes]
    | cons b rest =>
      cases b <;>
        simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed, tapes, h] <;>
        simpa [h] using (tapes_read d).symm
  | back nonempty empty =>
    cases h : d.backup with
    | nil =>
      simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed, tapes, h]
      funext k; cases k <;> simp [tapes]
    | cons b rest =>
      cases b <;>
        simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed, tapes, h] <;>
        simpa [h] using (tapes_back d).symm
  | write b next =>
    simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed, tapes_write, tapes]
  | discard next =>
    simp [Instruction.code, Instruction.execute, goto, TM2.stepAux, embed]
    funext k; cases k <;> simp [tapes]
  | jump next => rfl
  | halt => rfl

 theorem step_simulation (p : L → Instruction R L) (c : Configuration R L) :
    TM2.step (fun l => (p l).code) (embed c) = (step p c).map embed := by
  cases c with
  | mk d l =>
    cases l with
    | none => rfl
    | some l => simpa [TM2.step, step, embed] using congrArg some (instruction_simulation (p l) d)

/-- No semantic atomic arithmetic operation is being charged unit time: only
unary increment/decrement, one input/output bit, and finite jumps are atomic. -/
def machine [Fintype R] [Fintype L] (p : L → Instruction R L) (main : L) : FinTM2 where
  K := Tape R
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := L
  main := main
  σ := Option Bool
  initialState := none
  m l := (p l).code

end OptimalMaxCut.CounterMachine

namespace OptimalMaxCut.CounterMachine
variable {R L : Type} [DecidableEq R]

/-- A structured program still has only finitely many syntactic labels.
`loop r c` tests/decrements its own unary counter, then runs `c`. It is a genuine
while loop: no claim of termination is built into the syntax. -/
inductive Command (R : Type) where
  | skip
  | inc (r : R)
  | dec (r : R)
  | write (b : Bool)
  | discard
  | rewind
  | seq (first second : Command R)
  | test (r : R) (zero positive : Command R)
  | read (one zero empty : Command R)
  | loop (r : R) (body : Command R)

namespace Command

def Label : Command R → Type
  | .skip | .inc _ | .dec _ | .write _ | .discard | .rewind => Unit
  | .seq a b => Label a ⊕ Label b
  | .test _ a b => Unit ⊕ Label a ⊕ Label b
  | .read a b c => Unit ⊕ Label a ⊕ Label b ⊕ Label c
  | .loop _ b => Unit ⊕ Label b

noncomputable instance labelFintype (c : Command R) : Fintype (Label c) := by
  induction c with
  | skip | inc | dec | write | discard | rewind => exact inferInstanceAs (Fintype Unit)
  | seq a b ia ib => exact inferInstanceAs (Fintype (Label a ⊕ Label b))
  | test r a b ia ib => exact inferInstanceAs (Fintype (Unit ⊕ Label a ⊕ Label b))
  | read a b c ia ib ic => exact inferInstanceAs (Fintype (Unit ⊕ Label a ⊕ Label b ⊕ Label c))
  | loop r b ib => exact inferInstanceAs (Fintype (Unit ⊕ Label b))

def entry : (c : Command R) → Label c
  | .skip | .inc _ | .dec _ | .write _ | .discard | .rewind => ()
  | .seq a _ => .inl a.entry
  | .test _ _ _ | .read _ _ _ | .loop _ _ => .inl ()

def code : (c : Command R) → (Label c → L) → L → Label c → Instruction R L
  | .skip, _, exit, _ => .jump exit
  | .inc r, _, exit, _ => .inc r exit
  | .dec r, _, exit, _ => .dec r exit exit
  | .write b, _, exit, _ => .write b exit
  | .discard, _, exit, _ => .discard exit
  | .rewind, labels, exit, _ => .back (labels ()) exit
  | .seq a b, labels, _exit, .inl l =>
      a.code (fun l => labels (.inl l)) (labels (.inr b.entry)) l
  | .seq _a b, labels, exit, .inr l => b.code (fun l => labels (.inr l)) exit l
  | .test r a b, labels, _, .inl _ =>
      .test r (labels (.inr (.inl a.entry))) (labels (.inr (.inr b.entry)))
  | .test _ a _, labels, exit, .inr (.inl l) =>
      a.code (fun l => labels (.inr (.inl l))) exit l
  | .test _ _ b, labels, exit, .inr (.inr l) =>
      b.code (fun l => labels (.inr (.inr l))) exit l
  | .read a b c, labels, _, .inl _ =>
      .read (labels (.inr (.inl a.entry))) (labels (.inr (.inr (.inl b.entry))))
        (labels (.inr (.inr (.inr c.entry))))
  | .read a _ _, labels, exit, .inr (.inl l) =>
      a.code (fun l => labels (.inr (.inl l))) exit l
  | .read _ b _, labels, exit, .inr (.inr (.inl l)) =>
      b.code (fun l => labels (.inr (.inr (.inl l)))) exit l
  | .read _ _ c, labels, exit, .inr (.inr (.inr l)) =>
      c.code (fun l => labels (.inr (.inr (.inr l)))) exit l
  | .loop r b, labels, exit, .inl _ => .dec r (labels (.inr b.entry)) exit
  | .loop _ b, labels, _, .inr l => b.code (fun l => labels (.inr l)) (labels (.inl ())) l

def incData (d : Data R) (r : R) : Data R :=
  { d with reg := Function.update d.reg r (d.reg r + 1) }
def decData (d : Data R) (r : R) : Data R :=
  { d with reg := Function.update d.reg r (d.reg r - 1) }
def readData (d : Data R) : Data R :=
  { d with input := d.input.tail, backup := d.input.take 1 ++ d.backup }
def backData (d : Data R) : Data R :=
  { d with input := d.backup.take 1 ++ d.input, backup := d.backup.tail }
def discardData (d : Data R) : Data R := {d with input := d.input.tail}
def writeData (d : Data R) (b : Bool) : Data R := { d with output := b :: d.output }

/-- Timed operational semantics. Loop termination and the number of iterations
must be proved by the caller; there is no hidden bounded-search oracle. -/
inductive Evaluates : Command R → Data R → Data R → ℕ → Prop
  | skip (d) : Evaluates .skip d d 1
  | inc (d r) : Evaluates (.inc r) d (incData d r) 1
  | dec (d r) : Evaluates (.dec r) d (decData d r) 1
  | write (d b) : Evaluates (.write b) d (writeData d b) 1
  | discard (d) : Evaluates .discard d (discardData d) 1
  | rewind_empty {d} : d.backup = [] → Evaluates .rewind d d 1
  | rewind_cons {d e n b rest} : d.backup = b :: rest →
      Evaluates .rewind (backData d) e n → Evaluates .rewind d e (1 + n)
  | seq {a b d e f n m} : Evaluates a d e n → Evaluates b e f m →
      Evaluates (.seq a b) d f (n + m)
  | test_zero {r a b d e n} : d.reg r = 0 → Evaluates a d e n →
      Evaluates (.test r a b) d e (1 + n)
  | test_pos {r a b d e n} : d.reg r ≠ 0 → Evaluates b d e n →
      Evaluates (.test r a b) d e (1 + n)
  | read_one {a b c d e n rest} : d.input = true :: rest →
      Evaluates a (readData d) e n → Evaluates (.read a b c) d e (1 + n)
  | read_zero {a b c d e n rest} : d.input = false :: rest →
      Evaluates b (readData d) e n → Evaluates (.read a b c) d e (1 + n)
  | read_empty {a b c d e n} : d.input = [] →
      Evaluates c (readData d) e n → Evaluates (.read a b c) d e (1 + n)
  | loop_zero {r b d} : d.reg r = 0 → Evaluates (.loop r b) d d 1
  | loop_pos {r b d e f n m} : d.reg r ≠ 0 →
      Evaluates b (decData d r) e n → Evaluates (.loop r b) e f m →
      Evaluates (.loop r b) d f (1 + n + m)

end Command

/-- Propagation through halt is explicit, as in the supplied TM2 support. -/
def advance (p : L → Instruction R L) : Option (Configuration R L) → Option (Configuration R L) :=
  fun c => c.bind (step p)

def atCfg (l : L) (d : Data R) : Option (Configuration R L) := some ⟨d, some l⟩

def Runs (p : L → Instruction R L) (n : ℕ) (l : L) (d : Data R) (l' : L) (d' : Data R) : Prop :=
  (advance p)^[n] (atCfg l d) = atCfg l' d'

 theorem runs_one (p : L → Instruction R L) (l : L) (d : Data R) (l' : L) (d' : Data R)
    (h : (p l).execute d = ⟨d', some l'⟩) : Runs p 1 l d l' d' := by
  simpa [Runs, advance, atCfg, step] using congrArg some h

 theorem Runs.trans {p : L → Instruction R L} {n m : ℕ} {l l' l'' : L} {d e f : Data R}
    (h : Runs p n l d l' e) (h' : Runs p m l' e l'' f) : Runs p (n + m) l d l'' f := by
  unfold Runs at *
  rw [Nat.add_comm n m, Function.iterate_add_apply, h, h']

namespace Command
 theorem trace {c : Command R} {d d' : Data R} {n : ℕ} (h : Evaluates c d d' n)
    (p : L → Instruction R L) (labels : c.Label → L) (exit : L)
    (atLabels : ∀ l, p (labels l) = c.code labels exit l) :
    Runs p n (labels c.entry) d exit d' := by
  induction h generalizing L with
  | skip d =>
    apply runs_one
    rw [atLabels]; rfl
  | inc d r =>
    apply runs_one
    rw [atLabels]; rfl
  | dec d r =>
    apply runs_one
    rw [atLabels]
    simp [code, Instruction.execute, decData]
  | write d b =>
    apply runs_one
    rw [atLabels]; rfl
  | discard d =>
    apply runs_one
    rw [atLabels]; rfl
  | @rewind_empty d hd =>
    apply runs_one
    rw [atLabels]
    simp [code, Instruction.execute, hd]
    cases d; simp_all
  | @rewind_cons d e n b rest hd he ih =>
    refine Runs.trans (runs_one p _ _ _ _ ?_) (ih p labels exit atLabels)
    rw [atLabels]
    simp [code, entry, Instruction.execute, backData, hd]
  | @seq a b d e f n m h h' ih ih' =>
    exact Runs.trans
      (ih p (fun l => labels (.inl l)) (labels (.inr b.entry)) (fun l => atLabels (.inl l)))
      (ih' p (fun l => labels (.inr l)) exit (fun l => atLabels (.inr l)))
  | @test_zero r a b d e n hr h ih =>
    refine Runs.trans (runs_one p _ _ _ _ ?_) (ih p _ exit (fun l => atLabels (.inr (.inl l))))
    rw [atLabels]
    simp [code, entry, Instruction.execute, hr]
  | @test_pos r a b d e n hr h ih =>
    refine Runs.trans (runs_one p _ _ _ _ ?_) (ih p _ exit (fun l => atLabels (.inr (.inr l))))
    rw [atLabels]
    simp [code, entry, Instruction.execute, hr]
  | @read_one a b c d e n rest hin h ih =>
    refine Runs.trans (runs_one p _ _ _ _ ?_) (ih p _ exit (fun l => atLabels (.inr (.inl l))))
    rw [atLabels]
    simp [code, entry, Instruction.execute, readData, hin]
  | @read_zero a b c d e n rest hin h ih =>
    refine Runs.trans (runs_one p _ _ _ _ ?_) (ih p _ exit (fun l => atLabels (.inr (.inr (.inl l)))))
    rw [atLabels]
    simp [code, entry, Instruction.execute, readData, hin]
  | @read_empty a b c d e n hin h ih =>
    refine Runs.trans (runs_one p _ _ _ _ ?_) (ih p _ exit (fun l => atLabels (.inr (.inr (.inr l)))))
    rw [atLabels]
    simp [code, entry, Instruction.execute, readData, hin]
  | @loop_zero r b d hr =>
    apply runs_one
    rw [atLabels]
    simp [code, entry, Instruction.execute, hr]
    rw [← hr, Function.update_eq_self]
  | @loop_pos r b d e f n m hr h h' ih ih' =>
    refine Runs.trans (Runs.trans (runs_one p _ _ _ _ ?_)
      (ih p (fun l => labels (.inr l)) (labels (.inl ())) (fun l => atLabels (.inr l))))
        (ih' p labels exit atLabels)
    rw [atLabels]
    simp [code, entry, Instruction.execute, decData, hr]
end Command
end OptimalMaxCut.CounterMachine

namespace OptimalMaxCut.CounterMachine
open Turing
variable {R L : Type} [DecidableEq R]

 theorem advance_simulation (p : L → Instruction R L) (a : Option (Configuration R L)) :
    (a.map embed).bind (TM2.step (fun l => (p l).code)) = (advance p a).map embed := by
  cases a with
  | none => rfl
  | some c => exact step_simulation p c

 theorem iterate_simulation (p : L → Instruction R L) (n : ℕ)
    (a : Option (Configuration R L)) :
    (fun a => a.bind (TM2.step (fun l => (p l).code)))^[n] (a.map embed) =
      ((advance p)^[n] a).map embed := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, advance_simulation, Function.iterate_succ_apply']

namespace Command

abbrev FinalLabel (c : Command R) := c.Label ⊕ Unit

def finalCode (c : Command R) : c.FinalLabel → Instruction R c.FinalLabel
  | .inl l => c.code Sum.inl (.inr ()) l
  | .inr _ => .halt

def initial (input : List Bool) : Data R :=
  ⟨fun _ => 0, input, [], []⟩

noncomputable def finiteMachine [Fintype R] (c : Command R) : FinTM2 :=
  machine c.finalCode (.inl c.entry)

 theorem finiteMachine_initial [Fintype R] (c : Command R) (input : List Bool) :
    initList c.finiteMachine input = embed ⟨initial input, some (.inl c.entry)⟩ := by
  unfold initList
  congr 1
  funext k
  cases k <;> simp [finiteMachine, machine, tapes, initial]
  rfl

/-- Every derived structured evaluation is an actual finite-alphabet execution,
including the final halt transition. No arithmetic oracle is added. -/
 noncomputable def machine_run [Fintype R] {c : Command R} {input : List Bool} {out : Data R} {n : ℕ}
    (h : Evaluates c (initial input) out n) :
    StateTransition.EvalsToInTime c.finiteMachine.step (initList c.finiteMachine input)
      (some (embed ⟨out, none⟩)) (n + 1) := by
  have hr := trace h c.finalCode Sum.inl (.inr ()) (fun _ => rfl)
  have hi := iterate_simulation c.finalCode n (atCfg (.inl c.entry) (initial input))
  have hit : (fun a : Option (Configuration R c.FinalLabel) => advance c.finalCode a)^[n + 1]
      (atCfg (.inl c.entry) (initial input)) = some ⟨out, none⟩ := by
    rw [Function.iterate_succ_apply', hr]
    rfl
  refine ⟨⟨n + 1, ?_⟩, le_rfl⟩
  rw [finiteMachine_initial]
  change (fun a => a.bind (TM2.step (fun l => (c.finalCode l).code)))^[n + 1]
      ((atCfg (.inl c.entry) (initial input)).map embed) = _
  rw [iterate_simulation, hit]
  rfl

end Command
end OptimalMaxCut.CounterMachine

namespace OptimalMaxCut.CounterMachine
open scoped BigOperators
variable {R : Type} [DecidableEq R]

namespace Data

def set (d : Data R) (r : R) (v : ℕ) : Data R :=
  { d with reg := Function.update d.reg r v }

@[simp] theorem set_self (d : Data R) (r : R) : d.set r (d.reg r) = d := by
  simp [set]

@[simp] theorem set_set (d : Data R) (r : R) (v w : ℕ) :
    (d.set r v).set r w = d.set r w := by simp [set]

@[simp] theorem set_reg_same (d : Data R) (r : R) (v : ℕ) :
    (d.set r v).reg r = v := by simp [set]

@[simp] theorem set_reg_ne (d : Data R) (r s : R) (v : ℕ) (h : s ≠ r) :
    (d.set r v).reg s = d.reg s := by simp [set, h]

 theorem set_comm (d : Data R) (r s : R) (v w : ℕ) (h : r ≠ s) :
    (d.set r v).set s w = (d.set s w).set r v := by
  simp only [set]
  congr 1
  exact Function.update_comm h v w d.reg

end Data

namespace Command

def clear (r : R) : Command R := .loop r .skip

def move (r s : R) : Command R := .loop r (.inc s)

 theorem clear_evaluates (d : Data R) (r : R) :
    Evaluates (clear r) d (d.set r 0) (2 * d.reg r + 1) := by
  generalize hn : d.reg r = n
  induction n generalizing d with
  | zero =>
    have hs : d.set r 0 = d := by rw [← hn, Data.set_self]
    simpa [clear, hs] using (Evaluates.loop_zero (b := .skip) hn)
  | succ n ih =>
    have hr : d.reg r ≠ 0 := by omega
    have hd : (decData d r).reg r = n := by simp [decData, hn]
    have he := ih (decData d r) hd
    have hf : (decData d r).set r 0 = d.set r 0 := by simp [decData, Data.set]
    have ht : 1 + 1 + (2 * n + 1) = 2 * (n + 1) + 1 := by omega
    simpa only [clear, hf, ht] using
      (Evaluates.loop_pos hr (Evaluates.skip (decData d r)) he)

 theorem move_evaluates (d : Data R) (r s : R) (hrs : r ≠ s) :
    Evaluates (move r s) d ((d.set r 0).set s (d.reg s + d.reg r))
      (2 * d.reg r + 1) := by
  generalize hn : d.reg r = n
  induction n generalizing d with
  | zero =>
    have hz : d.set r 0 = d := by rw [← hn, Data.set_self]
    simpa [move, hz] using (Evaluates.loop_zero (b := .inc s) hn)
  | succ n ih =>
    have hr : d.reg r ≠ 0 := by omega
    let e := incData (decData d r) s
    have er : e.reg r = n := by simp [e, incData, decData, hrs, hn]
    have es : e.reg s = d.reg s + 1 := by simp [e, incData, decData, Ne.symm hrs]
    have he := ih e er
    have hf : (e.set r 0).set s (e.reg s + n) =
        (d.set r 0).set s (d.reg s + (n + 1)) := by
      simp only [es]
      have hc : e.set r 0 = (d.set r 0).set s (d.reg s + 1) := by
        dsimp [e, incData, decData, Data.set]
        congr 1
        ext t
        by_cases ht : t = r <;> by_cases hs : t = s <;> simp_all
      rw [hc, Data.set_set]
      congr 1
      omega
    have ht : 1 + 1 + (2 * n + 1) = 2 * (n + 1) + 1 := by omega
    simpa only [move, hf, ht] using (Evaluates.loop_pos hr (Evaluates.inc (decData d r) s) he)

/-- A definite cutoff clock for an actually terminating command, not an
assumed machine-computability predicate. -/
def Within (c : Command R) (d e : Data R) (B : ℕ) : Prop :=
  ∃ n ≤ B, Evaluates c d e n

 theorem Within.seq {a b : Command R} {d e f : Data R} {B C : ℕ}
    (h : Within a d e B) (h' : Within b e f C) : Within (.seq a b) d f (B + C) := by
  obtain ⟨n, hn, he⟩ := h
  obtain ⟨m, hm, hf⟩ := h'
  exact ⟨n + m, Nat.add_le_add hn hm, Evaluates.seq he hf⟩

 theorem Within.mono {c : Command R} {d e : Data R} {B C : ℕ}
    (h : Within c d e B) (hBC : B ≤ C) : Within c d e C := by
  obtain ⟨n, hn, he⟩ := h
  exact ⟨n, hn.trans hBC, he⟩

end Command
end OptimalMaxCut.CounterMachine

namespace OptimalMaxCut.CounterMachine
open scoped BigOperators
variable {R : Type} [DecidableEq R]

omit [DecidableEq R] in
@[ext] theorem Data.ext {d e : Data R} (hr : d.reg = e.reg)
    (hi : d.input = e.input) (hb : d.backup = e.backup) (ho : d.output = e.output) : d = e := by
  cases d; cases e; simp_all

namespace Command

theorem Within.loop (r : R) (b : Command R) (state : ℕ → Data R) (n B : ℕ)
    (hr : ∀ i ≤ n, (state i).reg r = i)
    (hb : ∀ i < n, Within b (decData (state (i+1)) r) (state i) B) :
    Within (.loop r b) (state n) (state 0) (n * (B + 1) + 1) := by
  induction n with
  | zero => exact ⟨1, by omega, Evaluates.loop_zero (hr 0 le_rfl)⟩
  | succ n ih =>
    obtain ⟨a, ha, ea⟩ := hb n (by omega)
    obtain ⟨b', hb', eb⟩ := ih (fun i hi => hr i (by omega)) (fun i hi => hb i (by omega))
    refine ⟨1 + a + b', ?_, Evaluates.loop_pos (by rw [hr (n+1) le_rfl]; omega) ea eb⟩
    nlinarith

 theorem Within.inc (d : Data R) (r : R) : Within (.inc r) d (incData d r) 1 :=
  ⟨1, le_rfl, Evaluates.inc d r⟩
 theorem Within.dec (d : Data R) (r : R) : Within (.dec r) d (decData d r) 1 :=
  ⟨1, le_rfl, Evaluates.dec d r⟩
 theorem Within.skip (d : Data R) : Within (.skip : Command R) d d 1 :=
  ⟨1, le_rfl, Evaluates.skip d⟩
 theorem Within.clear (d : Data R) (r : R) :
    Within (clear r) d (d.set r 0) (2*d.reg r+1) :=
  ⟨_, le_rfl, clear_evaluates d r⟩
 theorem Within.move (d : Data R) (r s : R) (h : r ≠ s) :
    Within (move r s) d ((d.set r 0).set s (d.reg s+d.reg r)) (2*d.reg r+1) :=
  ⟨_, le_rfl, move_evaluates d r s h⟩

/-- Copy without destruction using a disjoint zeroed backup register. -/
def copy (r s t : R) : Command R :=
  .seq (.loop r (.seq (.inc s) (.inc t))) (move t r)

 theorem copy_evaluates (d : Data R) (r s t : R)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) (ht : d.reg t = 0) :
    Within (copy r s t) d (d.set s (d.reg s + d.reg r)) (5*d.reg r+2) := by
  let n := d.reg r
  let state : ℕ → Data R := fun i => ((d.set r i).set s (d.reg s+n-i)).set t (n-i)
  have hn : state n = d := by
    ext u <;> simp [state, Data.set, n]
    by_cases hu : u = r <;> by_cases hs : u = s <;> by_cases ht' : u = t <;> simp_all
  have hloop : Within (.loop r (.seq (.inc s) (.inc t))) (state n) (state 0) (n*3+1) := by
    apply Within.loop r _ state n 2
    · intro i hi; simp [state, Data.set, hrs, hrt]
    · intro i hi
      have he := (Within.inc (decData (state (i+1)) r) s).seq
        (Within.inc (incData (decData (state (i+1)) r) s) t)
      have hout : incData (incData (decData (state (i+1)) r) s) t = state i := by
        ext u <;> simp only [incData, decData, state, Data.set]
        by_cases hu : u = r <;> by_cases hs : u = s <;> by_cases ht' : u = t <;>
          simp [hu, hs, ht', hrs, hrt, hst, Ne.symm hrs, Ne.symm hrt, Ne.symm hst] <;> omega
      simpa only [hout] using he
  rw [hn] at hloop
  have hm := Within.move (state 0) t r (Ne.symm hrt)
  have hout : ((state 0).set t 0).set r ((state 0).reg r + (state 0).reg t) =
      d.set s (d.reg s + d.reg r) := by
    ext u <;> simp only [state, Data.set]
    by_cases hu : u = r <;> by_cases hs : u = s <;> by_cases ht' : u = t <;>
      simp [hu, hs, ht', hrs, hrt, hst, Ne.symm hrs, Ne.symm hrt, Ne.symm hst, ht, n]
  have ht' : (state 0).reg t = n := by simp [state, Data.set]
  have h := hloop.seq hm
  rw [hout, ht'] at h
  convert h using 1 <;> dsimp [copy, n] ; omega

def mulAdd (count source target backup : R) : Command R :=
  .loop count (copy source target backup)

 theorem mulAdd_evaluates (d : Data R) (c r s t : R)
    (hcr : c ≠ r) (hcs : c ≠ s) (hct : c ≠ t)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) (ht : d.reg t = 0) :
    Within (mulAdd c r s t) d ((d.set c 0).set s (d.reg s+d.reg c*d.reg r))
      (d.reg c*(5*d.reg r+3)+1) := by
  let n := d.reg c
  let state : ℕ → Data R := fun i => (d.set c i).set s (d.reg s+(n-i)*d.reg r)
  have hn : state n = d := by
    simp [state, n]
  have hloop : Within (.loop c (copy r s t)) (state n) (state 0)
      (n*(5*d.reg r+3)+1) := by
    apply Within.loop c _ state n (5*d.reg r+2)
    · intro i hi; simp [state, Data.set, hcs]
    · intro i hi
      have hr' : (decData (state (i+1)) c).reg r = d.reg r := by
        simp [state, decData, Data.set, Ne.symm hcr, hrs]
      have ht' : (decData (state (i+1)) c).reg t = 0 := by
        simp [state, decData, Data.set, Ne.symm hct, Ne.symm hst, ht]
      have h := copy_evaluates (decData (state (i+1)) c) r s t hrs hrt hst ht'
      rw [hr'] at h
      have hout : (decData (state (i+1)) c).set s
          ((decData (state (i+1)) c).reg s + d.reg r) = state i := by
        have hh : (n-(i+1))*d.reg r+d.reg r = (n-i)*d.reg r := by
          have : n-i = n-(i+1)+1 := by omega
          rw [this, Nat.add_mul, Nat.one_mul]
        ext u <;> simp only [decData, state, Data.set]
        by_cases hu : u = c <;> by_cases hs : u = s <;>
          simp [hu, hs, hcs, Ne.symm hcs, Nat.add_assoc] ; omega
      simpa only [hout] using h
  simpa [mulAdd, hn, state, n] using hloop

end Command
end OptimalMaxCut.CounterMachine

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Put
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.CounterMachine
variable {R : Type} [DecidableEq R]
namespace Command

def put (r : R) : ℕ → Command R
  | 0 => .skip
  | n+1 => .seq (.inc r) (put r n)

 theorem put_evaluates (d : Data R) (r : R) (n : ℕ) :
    Within (put r n) d (d.set r (d.reg r+n)) (n+1) := by
  induction n generalizing d with
  | zero => simpa [put] using Within.skip d
  | succ n ih =>
    have h := (Within.inc d r).seq (ih (incData d r))
    have he : (incData d r).set r ((incData d r).reg r+n) = d.set r (d.reg r+(n+1)) := by
      simp [incData, Data.set, Nat.add_assoc, Nat.add_comm]
    rw [he] at h
    simpa only [put, show 1+(n+1) = n+1+1 by omega] using h

 def subFrom (r s : R) : Command R := .loop r (.dec s)

 theorem subFrom_evaluates (d : Data R) (r s : R) (h : r ≠ s) :
    Within (subFrom r s) d ((d.set r 0).set s (d.reg s-d.reg r)) (2*d.reg r+1) := by
  let n := d.reg r
  let state : ℕ → Data R := fun i => (d.set r i).set s (d.reg s-(n-i))
  have hn : state n = d := by simp [state, n]
  have hl : Within (.loop r (.dec s)) (state n) (state 0) (n*2+1) := by
    apply Within.loop r _ state n 1
    · intro i hi; simp [state, Data.set, h]
    · intro i hi
      have he : decData (decData (state (i+1)) r) s = state i := by
        ext u <;> simp only [decData, state, Data.set]
        by_cases hu : u = r <;> by_cases hs : u = s <;>
          simp [hu, hs, h, Ne.symm h] ; omega
      simpa only [he] using Within.dec (decData (state (i+1)) r) s
  simpa [subFrom, state, n, hn, Nat.mul_comm] using hl

 theorem rewind_evaluates (d : Data R) :
    Within (.rewind : Command R) d {d with input := d.backup.reverse++d.input, backup := []}
      (d.backup.length+1) := by
  generalize he : d.backup = xs
  induction xs generalizing d with
  | nil =>
    have hd : {d with input := [].reverse++d.input, backup := []} = d := by
      cases d; simp_all
    exact ⟨1, by simp, by rw [hd]; exact Evaluates.rewind_empty he⟩
  | cons b rest ih =>
    have hb : (backData d).backup = rest := by simp [backData, he]
    obtain ⟨n, hn, h⟩ := ih (backData d) hb
    have hout : {backData d with input := rest.reverse++(backData d).input, backup := []} =
        {d with input := (b::rest).reverse++d.input, backup := []} := by
      simp [backData, he, List.reverse_cons, List.append_assoc]
    rw [hout] at h
    exact ⟨1+n, by simp; omega, Evaluates.rewind_cons he h⟩

/-- Skip exactly the prescribed number of attempted reads, recording only real
bits on the backup. EOF is handled by a genuine branch. -/
def skipInput (r : R) : Command R := .loop r (.read .skip .skip .skip)

 theorem skipInput_evaluates (d : Data R) (r : R) :
    Within (skipInput r) d
      {(d.set r 0) with input := d.input.drop (d.reg r), backup := (d.input.take (d.reg r)).reverse++d.backup}
      (3*d.reg r+1) := by
  generalize hn : d.reg r = n
  induction n generalizing d with
  | zero =>
    have he : {d.set r 0 with input := d.input.drop 0, backup := (d.input.take 0).reverse++d.backup} = d := by
      simp only [List.drop_zero, List.take_zero, List.reverse_nil, List.nil_append]
      rw [← hn, Data.set_self]
    rw [he]
    exact ⟨1, by omega, Evaluates.loop_zero hn⟩
  | succ n ih =>
    let e := readData (decData d r)
    have he : e.reg r = n := by simp [e, readData, decData, hn]
    obtain ⟨a, ha, hr⟩ := ih e he
    have hb : Evaluates (.read .skip .skip .skip) (decData d r) e 2 := by
      cases hinput : d.input with
      | nil => exact Evaluates.read_empty (d := decData d r) hinput (Evaluates.skip _)
      | cons b rest =>
        cases b
        · exact Evaluates.read_zero (d := decData d r) hinput (Evaluates.skip _)
        · exact Evaluates.read_one (d := decData d r) hinput (Evaluates.skip _)
    have hout : {e.set r 0 with input := e.input.drop n, backup := (e.input.take n).reverse++e.backup} =
        {d.set r 0 with input := d.input.drop (n+1), backup := (d.input.take (n+1)).reverse++d.backup} := by
      cases hi : d.input with
      | nil => simp [e, readData, decData, Data.set, hi]
      | cons b rest => simp [e, readData, decData, Data.set, hi, List.reverse_cons, List.append_assoc]
    rw [hout] at hr
    refine ⟨1+2+a, by omega, Evaluates.loop_pos (by omega) hb hr⟩

/-- Read one bit at a unary index; a missing bit is false. Input is restored. -/
def inputBit (index result : R) : Command R :=
  .seq (skipInput index) (.seq (.read (.inc result) .skip .skip) .rewind)

 theorem inputBit_evaluates (d : Data R) (i r : R) (hir : i ≠ r)
    (hb : d.backup = []) (hr : d.reg r = 0) :
    Within (inputBit i r) d ((d.set i 0).set r (if d.input[d.reg i]?.getD false then 1 else 0))
      (3*d.reg i+d.input.length+4) := by
  let e : Data R := {d.set i 0 with input := d.input.drop (d.reg i), backup := (d.input.take (d.reg i)).reverse++d.backup}
  have he := skipInput_evaluates d i
  let bit := (d.input[d.reg i]?).getD false
  let f : Data R := (readData e).set r (if bit then 1 else 0)
  have hread : Within (.read (.inc r) .skip .skip) e f 2 := by
    have er : e.reg r = 0 := by simp [e, Data.set, Ne.symm hir, hr]
    have bit_head : (e.input.head?).getD false = bit := by
      simp [e, bit, List.head?_drop]
    cases hi : e.input with
    | nil =>
      have hbit : bit = false := by simpa [hi] using bit_head.symm
      have hf : f = readData e := by simp [f, hbit, readData, ← er]
      exact ⟨2, le_rfl, by rw [hf]; exact Evaluates.read_empty hi (Evaluates.skip _)⟩
    | cons b rest =>
      cases b
      · have hbit : bit = false := by simpa [hi] using bit_head.symm
        have hf : f = readData e := by simp [f, hbit, readData, ← er]
        exact ⟨2, le_rfl, by rw [hf]; exact Evaluates.read_zero hi (Evaluates.skip _)⟩
      · have hbit : bit = true := by simpa [hi] using bit_head.symm
        have hf : f = incData (readData e) r := by simp [f, hbit, incData, Data.set, readData, er]
        exact ⟨2, le_rfl, by rw [hf]; exact Evaluates.read_one hi (Evaluates.inc _ _)⟩
  have hrew := rewind_evaluates f
  have restored : {f with input := f.backup.reverse++f.input, backup := []} =
      (d.set i 0).set r (if bit then 1 else 0) := by
    have heq : e.backup.reverse ++ e.input = d.input := by
      simp [e, hb]
    have heq' : (readData e).backup.reverse ++ (readData e).input = d.input := by
      rw [readData]
      simp only [List.reverse_append, List.reverse_take]
      cases hi : e.input <;> simpa [hi, List.append_assoc] using heq
    apply Data.ext
    · rfl
    · exact heq'
    · exact hb.symm
    · rfl
  have size : f.backup.length ≤ d.input.length := by
    dsimp [f, Data.set, readData, e]
    simp only [List.length_append, List.length_take, List.length_reverse, hb, List.length_nil,
      add_zero, List.length_drop]
    omega
  have hh := he.seq (hread.seq hrew)
  rw [restored] at hh
  exact hh.mono (by omega)

end Command
end OptimalMaxCut.CounterMachine

namespace OptimalMaxCut.CounterMachine
variable {R : Type} [DecidableEq R]
namespace Command

def lengthLoop (guard result : R) : Command R :=
  .loop guard (.read (.seq (.inc guard) (.inc result)) (.seq (.inc guard) (.inc result)) .skip)

 theorem lengthLoop_evaluates (d : Data R) (g r : R) (hgr : g ≠ r) (hg : d.reg g = 1) :
    Within (lengthLoop g r) d
      {((d.set g 0).set r (d.reg r+d.input.length)) with
        input := [], backup := d.input.reverse++d.backup}
      (4*d.input.length+4) := by
  generalize hx : d.input = xs
  induction xs generalizing d with
  | nil =>
    have he : readData (decData d g) = d.set g 0 := by
      simp [readData, decData, Data.set, hx, hg]
    have hread : Evaluates (.read (.seq (.inc g) (.inc r)) (.seq (.inc g) (.inc r)) .skip)
        (decData d g) (d.set g 0) 2 := by
      rw [← he]
      exact Evaluates.read_empty (d := decData d g) hx (Evaluates.skip _)
    have hloop : Evaluates (lengthLoop g r) d (d.set g 0) 4 :=
      Evaluates.loop_pos (by omega) hread (Evaluates.loop_zero (by simp))
    have hf : {((d.set g 0).set r (d.reg r + ([] : List Bool).length)) with input := [], backup := [].reverse++d.backup} = d.set g 0 := by
      apply Data.ext
      · simp [Data.set, Ne.symm hgr]
      · exact hx.symm
      · simp [Data.set]
      · rfl
    exact ⟨4, by simp, by rw [hf]; exact hloop⟩
  | cons b xs ih =>
    let e := incData (incData (readData (decData d g)) g) r
    have eg : e.reg g = 1 := by simp [e, incData, decData, readData, hgr, hg]
    have ei : e.input = xs := by simp [e, incData, decData, readData, hx]
    obtain ⟨n, hn, he⟩ := ih e eg ei
    have hread : Evaluates (.read (.seq (.inc g) (.inc r)) (.seq (.inc g) (.inc r)) .skip)
        (decData d g) e 3 := by
      have hi := Evaluates.seq (Evaluates.inc (readData (decData d g)) g)
        (Evaluates.inc (incData (readData (decData d g)) g) r)
      cases b
      · exact Evaluates.read_zero (d := decData d g) hx hi
      · exact Evaluates.read_one (d := decData d g) hx hi
    have heq : {((e.set g 0).set r (e.reg r+xs.length)) with input := [], backup := xs.reverse++e.backup} =
        {((d.set g 0).set r (d.reg r+(b::xs).length)) with input := [], backup := (b::xs).reverse++d.backup} := by
      apply Data.ext
      · ext u
        by_cases hu : u = g <;> by_cases hr : u = r <;>
          simp [e, incData, decData, readData, Data.set, hu, hr,
            hgr, Ne.symm hgr, hg, Nat.add_assoc, Nat.add_comm]
      · rfl
      · simp [e, incData, decData, readData, hx, List.reverse_cons, List.append_assoc]
      · rfl
    rw [heq] at he
    exact ⟨1+3+n, by simp; omega, Evaluates.loop_pos (by omega) hread he⟩

 def inputLength (g r : R) : Command R := .seq (.inc g) (.seq (lengthLoop g r) .rewind)

 theorem inputLength_evaluates (d : Data R) (g r : R) (hgr : g ≠ r)
    (hg : d.reg g = 0) (hr : d.reg r = 0) (hb : d.backup = []) :
    Within (inputLength g r) d (d.set r d.input.length) (5*d.input.length+6) := by
  have he := lengthLoop_evaluates (incData d g) g r hgr (by simp [incData, hg])
  obtain ⟨n,hn,h⟩ := he
  let e : Data R := {((incData d g).set g 0).set r ((incData d g).reg r+d.input.length)
    with input := [], backup := d.input.reverse++d.backup}
  have he' : Within (lengthLoop g r) (incData d g) e (4*d.input.length+4) := ⟨n,hn,h⟩
  have hw := rewind_evaluates e
  have hout : {e with input := e.backup.reverse++e.input, backup := []} = d.set r d.input.length := by
    apply Data.ext
    · ext u
      by_cases hu : u = g <;> by_cases hu' : u = r <;>
        simp [e, incData, Data.set, hu, hu', hgr, Ne.symm hgr, hg, hr]
    · simp [e, hb, Data.set]
    · exact hb.symm
    · rfl
  have size : e.backup.length = d.input.length := by simp [e, hb]
  have hfull := (Within.inc d g).seq (he'.seq hw)
  rw [hout, size] at hfull
  exact hfull.mono (by omega)

end Command
end OptimalMaxCut.CounterMachine

namespace OptimalMaxCut.CounterMachine
open scoped BigOperators
open Finset

/-- Polynomially bounded arithmetic expressions with finite bounded summation.
The only inspection of the input is by actual bit-read or length macros above.
Bounded sums suffice for divisions, remainder, bounded minimization and every
finite loop in the rounded long-code graph printer. -/
inductive Expr where
  | const (n : ℕ)
  | arg (i : ℕ)
  | length
  | bit (index : Expr)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  | zero (a : Expr)
  | sum (bound body : Expr)

namespace Expr

def bind (v : ℕ → ℕ) (a : ℕ) : ℕ → ℕ
  | 0 => a
  | n+1 => v n

 def eval (input : List Bool) (args : ℕ → ℕ) : Expr → ℕ
  | .const n => n
  | .arg i => args i
  | .length => input.length
  | .bit e => if (input[eval input args e]?).getD false then 1 else 0
  | .add a b => eval input args a + eval input args b
  | .sub a b => eval input args a - eval input args b
  | .mul a b => eval input args a * eval input args b
  | .zero a => if eval input args a = 0 then 1 else 0
  | .sum b f => ∑ i ∈ range (eval input args b), eval input (bind args i) f

 def valueBudget : Expr → ℕ → ℕ
  | .const n, _ => n
  | .arg _, M => M
  | .length, M => M
  | .bit _, _ => 1
  | .add a b, M => valueBudget a M + valueBudget b M
  | .sub a _, M => valueBudget a M
  | .mul a b, M => valueBudget a M * valueBudget b M
  | .zero _, _ => 1
  | .sum b f, M => valueBudget b M * valueBudget f (M+valueBudget b M)

 theorem eval_le (e : Expr) (input : List Bool) (args : ℕ → ℕ) (M : ℕ)
    (hi : input.length ≤ M) (ha : ∀ i, args i ≤ M) :
    e.eval input args ≤ e.valueBudget M := by
  induction e generalizing args M with
  | const n => exact le_rfl
  | arg i => exact ha i
  | length => exact hi
  | bit e ih => simp only [eval, valueBudget]; split_ifs <;> omega
  | zero e ih => simp only [eval, valueBudget]; split_ifs <;> omega
  | add a b ia ib => exact Nat.add_le_add (ia _ _ hi ha) (ib _ _ hi ha)
  | sub a b ia ib => exact (Nat.sub_le _ _).trans (ia _ _ hi ha)
  | mul a b ia ib => exact Nat.mul_le_mul (ia _ _ hi ha) (ib _ _ hi ha)
  | sum b f ib iF =>
    have hb := ib args M hi ha
    calc
      _ ≤ ∑ _ ∈ range (eval input args b), f.valueBudget (M+b.valueBudget M) := by
        apply sum_le_sum; intro i hi'
        apply iF
        · omega
        · intro j
          cases j with
          | zero => dsimp [bind]; have := mem_range.mp hi'; omega
          | succ j => exact (ha j).trans (by omega)
      _ = eval input args b * f.valueBudget (M+b.valueBudget M) := by simp
      _ ≤ b.valueBudget M * f.valueBudget (M+b.valueBudget M) := Nat.mul_le_mul_right _ hb

 def timeBudget : Expr → ℕ → ℕ
  | .const n, _ => n+1
  | .arg _, M => 5*M+2
  | .length, M => 5*M+6
  | .bit e, M => timeBudget e M+3*valueBudget e M+M+7
  | .add a b, M | .sub a b, M => timeBudget a M+timeBudget b M+2*valueBudget b M+1
  | .mul a b, M => timeBudget a M+timeBudget b M+
      valueBudget b M*(5*valueBudget a M+3)+1+2*valueBudget a M+1+
      2*(valueBudget a M*valueBudget b M)+1
  | .zero a, M => timeBudget a M+2*valueBudget a M+2
  | .sum b f, M => timeBudget b M+valueBudget b M*
      (timeBudget f (M+valueBudget b M)+2*valueBudget f (M+valueBudget b M)+3)+2*valueBudget b M+2

 def compile (vars : ℕ → ℕ) (k : ℕ) : Expr → Command ℕ
  | .const n => Command.put k n
  | .arg i => Command.copy (vars i) k (k+1)
  | .length => Command.inputLength (k+1) k
  | .bit e => .seq (compile vars k e)
      (.seq (Command.inputBit k (k+1)) (Command.move (k+1) k))
  | .add a b => .seq (compile vars k a) (.seq (compile vars (k+1) b) (Command.move (k+1) k))
  | .sub a b => .seq (compile vars k a) (.seq (compile vars (k+1) b) (Command.subFrom (k+1) k))
  | .mul a b => .seq (compile vars k a) (.seq (compile vars (k+1) b)
      (.seq (Command.mulAdd (k+1) k (k+2) (k+3))
        (.seq (Command.clear k) (Command.move (k+2) k))))
  | .zero a => .seq (compile vars k a) (.test k (.inc k) (Command.clear k))
  | .sum b f => .seq (compile vars (k+1) b)
      (.seq (.loop (k+1) (.seq (compile (bind vars (k+2)) (k+3) f)
        (.seq (Command.move (k+3) k) (.inc (k+2))))) (Command.clear (k+2)))

end Expr
namespace Data

def Clean (d : Data ℕ) (k : ℕ) : Prop := ∀ r, k ≤ r → d.reg r = 0

 theorem Clean.mono {d : Data ℕ} {k l : ℕ} (hc : d.Clean k) (h : k ≤ l) : d.Clean l :=
  fun r hr => hc r (h.trans hr)

 theorem Clean.set_succ {d : Data ℕ} {k : ℕ} (hc : d.Clean k) (v : ℕ) :
    (d.set k v).Clean (k+1) := by
  intro r hr
  rw [set_reg_ne _ _ _ _ (by omega)]
  exact hc r (by omega)

 theorem set_args (d : Data ℕ) (vars : ℕ → ℕ) (k v : ℕ) (h : ∀ i, vars i < k) :
    (fun i => (d.set k v).reg (vars i)) = (fun i => d.reg (vars i)) := by
  funext i
  exact set_reg_ne _ _ _ _ (by have := h i; omega)

 theorem set_clean_zero {d : Data ℕ} {k r : ℕ} (hc : d.Clean k) (h : k ≤ r) :
    d.set r 0 = d := by rw [← hc r h, set_self]

end Data
end OptimalMaxCut.CounterMachine

namespace OptimalMaxCut.CounterMachine.Expr
open scoped BigOperators
open Finset Command

/-- Exact operational contract: all scratch counters are returned to zero,
original arguments and input are preserved, and a fixed explicit clock holds. -/
def Correct (e : Expr) : Prop := ∀ (vars : ℕ → ℕ) (k : ℕ) (d : Data ℕ) (M : ℕ),
    (∀ i, vars i < k) → d.Clean k → d.backup = [] → d.input.length ≤ M →
    (∀ i, d.reg (vars i) ≤ M) →
    Within (e.compile vars k) d (d.set k (e.eval d.input (fun i => d.reg (vars i)))) (e.timeBudget M)

 theorem correct_const (n : ℕ) : Correct (.const n) := by
  intro vars k d M hv hc hb hi ha
  simpa [compile, eval, timeBudget, hc k le_rfl] using put_evaluates d k n

 theorem correct_arg (i : ℕ) : Correct (.arg i) := by
  intro vars k d M hv hc hb hi ha
  have he := copy_evaluates d (vars i) k (k+1) (by have := hv i; omega)
    (by have := hv i; omega) (by omega) (hc _ (by omega))
  simp only [hc k le_rfl, zero_add] at he
  exact he.mono (by dsimp [timeBudget]; have := ha i; omega)

 theorem correct_length : Correct .length := by
  intro vars k d M hv hc hb hi ha
  exact (inputLength_evaluates d (k+1) k (by omega) (hc _ (by omega)) (hc _ le_rfl) hb).mono
    (by dsimp [timeBudget]; omega)

 theorem binary_start {a b : Expr} (hca : Correct a) (hcb : Correct b)
    (vars : ℕ → ℕ) (k : ℕ) (d : Data ℕ) (M : ℕ)
    (hv : ∀ i, vars i < k) (hc : d.Clean k) (hb : d.backup = []) (hi : d.input.length ≤ M)
    (ha : ∀ i, d.reg (vars i) ≤ M) :
    Within (.seq (a.compile vars k) (b.compile vars (k+1))) d
      ((d.set k (a.eval d.input (fun i => d.reg (vars i)))).set (k+1)
        (b.eval d.input (fun i => d.reg (vars i))))
      (a.timeBudget M+b.timeBudget M) := by
  have h1 := hca vars k d M hv hc hb hi ha
  let A := a.eval d.input (fun i => d.reg (vars i))
  have h2 := hcb vars (k+1) (d.set k A) M (fun i => by have := hv i; omega)
    (hc.set_succ A) hb hi (fun i => by
      rw [Data.set_reg_ne d k (vars i) A (Nat.ne_of_lt (hv i))]
      exact ha i)
  rw [Data.set_args d vars k A hv] at h2
  exact h1.seq h2

 theorem correct_add {a b : Expr} (hca : Correct a) (hcb : Correct b) : Correct (.add a b) := by
  intro vars k d M hv hc hb hi ha
  let A := a.eval d.input (fun i => d.reg (vars i))
  let B := b.eval d.input (fun i => d.reg (vars i))
  let e := (d.set k A).set (k+1) B
  have hs := binary_start hca hcb vars k d M hv hc hb hi ha
  have hm := Within.move e (k+1) k (by omega)
  have hout : (e.set (k+1) 0).set k (e.reg k+e.reg (k+1)) = d.set k (A+B) := by
    have hz := hc (k+1) (by omega)
    apply Data.ext
    · ext u
      by_cases hu : u = k <;> by_cases hu' : u = k+1 <;>
        simp [e, Data.set, hu, hu', hz]
    all_goals rfl
  have hm' : Within (move (k+1) k) e (d.set k (A+B)) (2*B+1) := by
    rw [hout] at hm
    simpa only [show e.reg (k+1) = B by simp [e]] using hm
  obtain ⟨s, hsb, hse⟩ := hs
  cases hse with
  | seq h1 h2 =>
    have hh := (show Within _ _ _ _ from ⟨_,le_rfl,h1⟩).seq
      ((show Within _ _ _ _ from ⟨_,le_rfl,h2⟩).seq hm')
    exact hh.mono (by have hB := b.eval_le d.input _ M hi ha; dsimp [timeBudget, B] at *; omega)

 theorem correct_sub {a b : Expr} (hca : Correct a) (hcb : Correct b) : Correct (.sub a b) := by
  intro vars k d M hv hc hb hi ha
  let A := a.eval d.input (fun i => d.reg (vars i))
  let B := b.eval d.input (fun i => d.reg (vars i))
  let e := (d.set k A).set (k+1) B
  have hs := binary_start hca hcb vars k d M hv hc hb hi ha
  have hm := subFrom_evaluates e (k+1) k (by omega)
  have hout : (e.set (k+1) 0).set k (e.reg k-e.reg (k+1)) = d.set k (A-B) := by
    have hz := hc (k+1) (by omega)
    apply Data.ext
    · ext u
      by_cases hu : u = k <;> by_cases hu' : u = k+1 <;>
        simp [e, Data.set, hu, hu', hz]
    all_goals rfl
  have hm' : Within (subFrom (k+1) k) e (d.set k (A-B)) (2*B+1) := by
    rw [hout] at hm
    simpa only [show e.reg (k+1) = B by simp [e]] using hm
  obtain ⟨s, hsb, hse⟩ := hs
  cases hse with
  | seq h1 h2 =>
    have hh := (show Within _ _ _ _ from ⟨_,le_rfl,h1⟩).seq
      ((show Within _ _ _ _ from ⟨_,le_rfl,h2⟩).seq hm')
    exact hh.mono (by have hB := b.eval_le d.input _ M hi ha; dsimp [timeBudget, B] at *; omega)

 theorem correct_zero {a : Expr} (hca : Correct a) : Correct (.zero a) := by
  intro vars k d M hv hc hb hi ha
  let A := a.eval d.input (fun i => d.reg (vars i))
  have h1 := hca vars k d M hv hc hb hi ha
  have h2 : Within (.test k (.inc k) (clear k)) (d.set k A)
      (d.set k (if A=0 then 1 else 0)) (2*A+2) := by
    by_cases hA : A=0
    · refine ⟨2, by omega, Evaluates.test_zero (r := k) (n := 1) (d := d.set k A) (by simp [hA]) ?_⟩
      simpa [hA, incData, Data.set] using Evaluates.inc (d.set k A) k
    · refine ⟨1+(2*A+1), by omega, Evaluates.test_pos (r := k) (d := d.set k A) (by simpa using hA) ?_⟩
      simpa [hA] using clear_evaluates (d.set k A) k
  have h := h1.seq h2
  exact h.mono (by dsimp [timeBudget]; have := a.eval_le d.input _ M hi ha; dsimp [A] at *; omega)

 theorem correct_bit {a : Expr} (hca : Correct a) : Correct (.bit a) := by
  intro vars k d M hv hc hb hi ha
  let A := a.eval d.input (fun i => d.reg (vars i))
  let B := if (d.input[A]?).getD false then 1 else 0
  have h1 := hca vars k d M hv hc hb hi ha
  have h2 := inputBit_evaluates (d.set k A) k (k+1) (by omega) hb
    (by rw [Data.set_reg_ne _ _ _ _ (by omega)]; exact hc _ (by omega))
  have hout2 : ((d.set k A).set k 0).set (k+1) B = d.set (k+1) B := by
    rw [Data.set_set, Data.set_clean_zero hc le_rfl]
  simp only [Data.set_reg_same] at h2
  change Within (inputBit k (k+1)) (d.set k A)
    (((d.set k A).set k 0).set (k+1) B) (3*A+d.input.length+4) at h2
  rw [hout2] at h2
  have h3 := Within.move (d.set (k+1) B) (k+1) k (by omega)
  have hout3 : ((d.set (k+1) B).set (k+1) 0).set k
      ((d.set (k+1) B).reg k+(d.set (k+1) B).reg (k+1)) = d.set k B := by
    simp only [Data.set_set]
    rw [Data.set_clean_zero hc (by omega)]
    simp [Data.set, hc k le_rfl]
  have h3' : Within (move (k+1) k) (d.set (k+1) B) (d.set k B) (2*B+1) := by
    rw [hout3] at h3
    simpa only [Data.set_reg_same] using h3
  have h := h1.seq (h2.seq h3')
  have hB : B ≤ 1 := by dsimp [B]; split_ifs <;> omega
  exact h.mono (by have hA := a.eval_le d.input _ M hi ha; dsimp [timeBudget, A] at *; omega)

end OptimalMaxCut.CounterMachine.Expr

namespace OptimalMaxCut.CounterMachine.Command
variable {R : Type} [DecidableEq R]
 theorem Within.assoc {a b c : Command R} {d e : Data R} {B : ℕ}
    (h : Within (.seq (.seq a b) c) d e B) : Within (.seq a (.seq b c)) d e B := by
  obtain ⟨n, hn, he⟩ := h
  cases he with
  | seq hab hc =>
    cases hab with
    | seq ha hb =>
      exact ⟨_, by omega, Evaluates.seq ha (Evaluates.seq hb hc)⟩
end OptimalMaxCut.CounterMachine.Command
namespace OptimalMaxCut.CounterMachine.Expr
open Command

 theorem correct_mul {a b : Expr} (hca : Correct a) (hcb : Correct b) : Correct (.mul a b) := by
  intro vars k d M hv hc hb hi ha
  let A := a.eval d.input (fun i => d.reg (vars i))
  let B := b.eval d.input (fun i => d.reg (vars i))
  let e := (d.set k A).set (k+1) B
  have hs := binary_start hca hcb vars k d M hv hc hb hi ha
  have hz1 := hc (k+1) (by omega)
  have hz2 := hc (k+2) (by omega)
  have hz3 := hc (k+3) (by omega)
  have hm := mulAdd_evaluates e (k+1) k (k+2) (k+3) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by simp [e, hz3, Data.set])
  have hout : (e.set (k+1) 0).set (k+2) (e.reg (k+2)+e.reg (k+1)*e.reg k) =
      (d.set k A).set (k+2) (A*B) := by
    apply Data.ext
    · ext u
      by_cases h0 : u = k <;> by_cases h1 : u = k+1 <;> by_cases h2 : u = k+2 <;>
        simp [e, Data.set, h0, h1, h2, hz1, hz2, Nat.mul_comm]
    all_goals rfl
  rw [hout] at hm
  have hm' : Within (mulAdd (k+1) k (k+2) (k+3)) e ((d.set k A).set (k+2) (A*B))
      (B*(5*A+3)+1) := by simpa [e, Data.set] using hm
  let f := (d.set k A).set (k+2) (A*B)
  have hf := Within.clear f k
  have houtf : f.set k 0 = d.set (k+2) (A*B) := by
    change (((d.set k A).set (k+2) (A*B)).set k 0) = _
    rw [Data.set_comm _ k (k+2) _ _ (by omega)]
    rw [Data.set_set]
    rw [Data.set_comm _ (k+2) k _ _ (by omega), Data.set_clean_zero hc le_rfl]
  rw [houtf] at hf
  have hf' : Within (clear k) f (d.set (k+2) (A*B)) (2*A+1) := by
    simpa [f, Data.set] using hf
  have hg := Within.move (d.set (k+2) (A*B)) (k+2) k (by omega)
  have houtg : ((d.set (k+2) (A*B)).set (k+2) 0).set k
      ((d.set (k+2) (A*B)).reg k+(d.set (k+2) (A*B)).reg (k+2)) = d.set k (A*B) := by
    rw [Data.set_set, Data.set_clean_zero hc (by omega)]
    simp [Data.set, hc k le_rfl]
  rw [houtg] at hg
  have hg' : Within (move (k+2) k) (d.set (k+2) (A*B)) (d.set k (A*B)) (2*(A*B)+1) := by
    simpa only [Data.set_reg_same] using hg
  have hh := (hs.seq (hm'.seq (hf'.seq hg'))).assoc
  apply hh.mono
  have hA := a.eval_le d.input _ M hi ha
  have hB := b.eval_le d.input _ M hi ha
  change a.timeBudget M+b.timeBudget M+(B*(5*A+3)+1+(2*A+1+(2*(A*B)+1))) ≤ _
  change A ≤ a.valueBudget M at hA
  change B ≤ b.valueBudget M at hB
  dsimp only [timeBudget]
  calc
    _ ≤ a.timeBudget M+b.timeBudget M+
        (b.valueBudget M*(5*a.valueBudget M+3)+1+
          (2*a.valueBudget M+1+(2*(a.valueBudget M*b.valueBudget M)+1))) := by gcongr
    _ = _ := by omega

end OptimalMaxCut.CounterMachine.Expr

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Rename
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.CounterMachine.Expr
open scoped BigOperators
open Finset

def rename (ρ : ℕ → ℕ) : Expr → Expr
  | .const n => .const n
  | .arg i => .arg (ρ i)
  | .length => .length
  | .bit e => .bit (rename ρ e)
  | .add a b => .add (rename ρ a) (rename ρ b)
  | .sub a b => .sub (rename ρ a) (rename ρ b)
  | .mul a b => .mul (rename ρ a) (rename ρ b)
  | .zero a => .zero (rename ρ a)
  | .sum b f => .sum (rename ρ b) (rename (bind (fun i => ρ i+1) 0) f)

@[simp] theorem rename_eval (e : Expr) (ρ : ℕ → ℕ) (input : List Bool) (args : ℕ → ℕ) :
    (e.rename ρ).eval input args = e.eval input (fun i => args (ρ i)) := by
  induction e generalizing ρ args <;> simp only [rename, eval] at *
  all_goals try simp_all
  case sum b f ib iF =>
    apply sum_congr rfl
    intro i hi
    congr 1
    funext j
    cases j <;> rfl

def bindExpr (σ : ℕ → Expr) (e : Expr) : ℕ → Expr
  | 0 => e
  | i+1 => σ i

def positive (a : Expr) : Expr := .zero (.zero a)
def equal (a b : Expr) : Expr := .zero (.add (.sub a b) (.sub b a))
def le (a b : Expr) : Expr := .zero (.sub a b)
def lt (a b : Expr) : Expr := le (.add a (.const 1)) b

@[simp] theorem positive_eval (a : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (positive a).eval input args = if a.eval input args ≠ 0 then 1 else 0 := by
  simp [positive, eval]

end OptimalMaxCut.CounterMachine.Expr

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_BitValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.CounterMachine.Expr
open scoped BigOperators
open Finset

def bitValue (input : List Bool) (i : ℕ) : ℕ := if (input[i]?).getD false then 1 else 0

def zeroPrefix (input : List Bool) (i : ℕ) : ℕ :=
  ∑ j ∈ range i, (1-bitValue input j)

def wordValue (input : List Bool) (k : ℕ) : ℕ :=
  ∑ i ∈ range input.length, bitValue input i * (if zeroPrefix input i = k then 1 else 0)

@[simp] theorem bitValue_cons_zero (a : Bool) (s : List Bool) :
    bitValue (a::s) 0 = if a then 1 else 0 := by simp [bitValue]
@[simp] theorem bitValue_cons_succ (a : Bool) (s : List Bool) (i : ℕ) :
    bitValue (a::s) (i+1) = bitValue s i := by simp [bitValue]

def unaryWords (words : List ℕ) : List Bool := words.flatMap (fun n => List.replicate n true ++ [false])

end OptimalMaxCut.CounterMachine.Expr

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_CorrectSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.CounterMachine.Expr
open scoped BigOperators
open Finset Command

 theorem correct_sum {b f : Expr} (hcb : Correct b) (hcf : Correct f) : Correct (.sum b f) := by
  intro vars k d M hv hc hb hi ha
  let args := fun i => d.reg (vars i)
  let B := b.eval d.input args
  let F := fun i => f.eval d.input (bind args i)
  let V := b.valueBudget M
  let W := f.valueBudget (M+V)
  let T := f.timeBudget (M+V)
  have hB : B ≤ V := b.eval_le d.input args M hi ha
  have hF : ∀ i < B, F i ≤ W := by
    intro i hi'
    apply f.eval_le
    · omega
    · intro j; cases j with
      | zero => dsimp [bind]; omega
      | succ j => exact (ha j).trans (by omega)
  let state : ℕ → Data ℕ := fun i =>
    ((d.set k (∑ j ∈ range (B-i), F j)).set (k+1) i).set (k+2) (B-i)
  have hz : ∀ r, k ≤ r → d.reg r = 0 := hc
  have hbnd := hcb vars (k+1) d M (fun i => by have := hv i; omega)
    (hc.mono (by omega)) hb hi ha
  have hstart : state B = d.set (k+1) B := by
    simp only [state, Nat.sub_self, range_zero, sum_empty]
    rw [Data.set_clean_zero hc le_rfl]
    exact Data.set_clean_zero ((hc.mono (by omega)).set_succ B) le_rfl
  have hloop : Within (.loop (k+1) (.seq (compile (bind vars (k+2)) (k+3) f)
      (.seq (move (k+3) k) (.inc (k+2))))) (state B) (state 0) (B*(T+2*W+3)+1) := by
    apply (Within.loop (k+1) _ state B (T+2*W+2))
    · intro i hi'
      simp [state, Data.set]
    · intro i hi'
      let j := B-(i+1)
      let e := decData (state (i+1)) (k+1)
      have hj : j < B := by dsimp [j]; omega
      have hindex : B-i = j+1 := by dsimp [j]; omega
      have heclean : e.Clean (k+3) := by
        intro r hr
        have h0 : r ≠ k := by omega
        have h1 : r ≠ k+1 := by omega
        have h2 : r ≠ k+2 := by omega
        simp [e, decData, state, Data.set, h0, h1, h2, hc r (by omega)]
      have henv : (fun u => e.reg (bind vars (k+2) u)) = bind args j := by
        funext u
        cases u with
        | zero => simp [e, decData, state, Data.set, bind, j]
        | succ u =>
          have h0 : vars u ≠ k := by have := hv u; omega
          have h1 : vars u ≠ k+1 := by have := hv u; omega
          have h2 : vars u ≠ k+2 := by have := hv u; omega
          simp [e, decData, state, Data.set, bind, args, h0, h1, h2]
      have heargs : ∀ u, e.reg (bind vars (k+2) u) ≤ M+V := by
        intro u
        change (fun u => e.reg (bind vars (k+2) u)) u ≤ M+V
        rw [henv]
        cases u with
        | zero => dsimp [bind]; omega
        | succ u => exact (ha u).trans (by omega)
      have hf := hcf (bind vars (k+2)) (k+3) e (M+V)
        (fun u => by cases u with
          | zero => dsimp [bind]; omega
          | succ u => dsimp [bind]; have := hv u; omega) heclean hb (by exact hi.trans (by omega)) heargs
      rw [henv] at hf
      change Within _ e (e.set (k+3) (F j)) T at hf
      have hm := Within.move (e.set (k+3) (F j)) (k+3) k (by omega)
      let out := (((e.set (k+3) (F j)).set (k+3) 0).set k
        ((e.set (k+3) (F j)).reg k+(e.set (k+3) (F j)).reg (k+3)))
      have hh := hf.seq (hm.seq (Within.inc out (k+2)))
      have hsum : (∑ u ∈ range (B-i), F u) = (∑ u ∈ range j, F u)+F j := by
        rw [hindex, sum_range_succ]
      have hout : incData out (k+2) = state i := by
        apply Data.ext
        · ext u
          have hz3 := hc (k+3) (by omega)
          by_cases h0 : u = k <;> by_cases h1 : u = k+1 <;>
            by_cases h2 : u = k+2 <;> by_cases h3 : u = k+3 <;>
            simp [out, e, state, Data.set, incData, decData,
              h0, h1, h2, h3, j, hsum, hz3] <;> omega
        all_goals rfl
      rw [hout] at hh
      apply hh.mono
      simp only [Data.set_reg_same]
      have := hF j hj
      omega
  rw [hstart] at hloop
  have hclear := Within.clear (state 0) (k+2)
  have hout : (state 0).set (k+2) 0 = d.set k (∑ j ∈ range B, F j) := by
    dsimp only [state]
    rw [Data.set_set]
    apply Data.ext
    · ext u
      have hz1 := hc (k+1) (by omega)
      have hz2 := hc (k+2) (by omega)
      by_cases h0 : u = k <;> by_cases h1 : u = k+1 <;> by_cases h2 : u = k+2 <;>
        simp [Data.set, h0, h1, h2, hz1, hz2]
    all_goals rfl
  rw [hout] at hclear
  have hclear' : Within (clear (k+2)) (state 0) (d.set k (∑ j ∈ range B, F j)) (2*B+1) := by
    simpa [state, Data.set] using hclear
  have hh := hbnd.seq (hloop.seq hclear')
  apply hh.mono

  change _ ≤ b.timeBudget M+V*(T+2*W+3)+2*V+2
  have ht := Nat.mul_le_mul_right (T+2*W+3) hB
  omega

 theorem correct (e : Expr) : Correct e := by
  induction e with
  | const n => exact correct_const n
  | arg i => exact correct_arg i
  | length => exact correct_length
  | bit a ih => exact correct_bit ih
  | add a b ia ib => exact correct_add ia ib
  | sub a b ia ib => exact correct_sub ia ib
  | mul a b ia ib => exact correct_mul ia ib
  | zero a ih => exact correct_zero ih
  | sum b f ib iF => exact correct_sum ib iF

end OptimalMaxCut.CounterMachine.Expr

namespace OptimalMaxCut.CounterMachine

 def Data.restrict (N : ℕ) (d : Data ℕ) : Data (Fin N) :=
  ⟨fun r => d.reg r.val, d.input, d.backup, d.output⟩

namespace Command

 def Bounded (N : ℕ) : Command ℕ → Prop
  | .skip | .write _ | .discard | .rewind => True
  | .inc r | .dec r => r < N
  | .seq a b => Bounded N a ∧ Bounded N b
  | .test r a b => r < N ∧ Bounded N a ∧ Bounded N b
  | .read a b c => Bounded N a ∧ Bounded N b ∧ Bounded N c
  | .loop r b => r < N ∧ Bounded N b

 def regCount : Command ℕ → ℕ
  | .skip | .write _ | .discard | .rewind => 0
  | .inc r | .dec r => r+1
  | .seq a b => max a.regCount b.regCount
  | .test r a b => max (r+1) (max a.regCount b.regCount)
  | .read a b c => max a.regCount (max b.regCount c.regCount)
  | .loop r b => max (r+1) b.regCount

 theorem bounded_of_count (c : Command ℕ) (N : ℕ) (h : c.regCount ≤ N) : c.Bounded N := by
  induction c <;> simp_all [Bounded, regCount]

 def restrict (N : ℕ) : (c : Command ℕ) → Bounded N c → Command (Fin N)
  | .skip, _ => .skip
  | .inc r, h => .inc ⟨r,h⟩
  | .dec r, h => .dec ⟨r,h⟩
  | .write b, _ => .write b
  | .discard, _ => .discard
  | .rewind, _ => .rewind
  | .seq a b, h => .seq (restrict N a h.1) (restrict N b h.2)
  | .test r a b, h => .test ⟨r,h.1⟩ (restrict N a h.2.1) (restrict N b h.2.2)
  | .read a b c, h => .read (restrict N a h.1) (restrict N b h.2.1) (restrict N c h.2.2)
  | .loop r b, h => .loop ⟨r,h.1⟩ (restrict N b h.2)

 theorem restrict_inc (N : ℕ) (d : Data ℕ) (r : ℕ) (h : r<N) :
    (incData d r).restrict N = incData (d.restrict N) ⟨r,h⟩ := by
  apply Data.ext
  · ext u
    simp only [Data.restrict, incData]
    by_cases hu : u.val = r
    · have he : u = ⟨r,h⟩ := Fin.ext hu
      simp [he]
    · have he : u ≠ ⟨r,h⟩ := fun he => hu (congrArg Fin.val he)
      simp [hu, he]
  all_goals rfl

 theorem restrict_dec (N : ℕ) (d : Data ℕ) (r : ℕ) (h : r<N) :
    (decData d r).restrict N = decData (d.restrict N) ⟨r,h⟩ := by
  apply Data.ext
  · ext u
    simp only [Data.restrict, decData]
    by_cases hu : u.val = r
    · have he : u = ⟨r,h⟩ := Fin.ext hu
      simp [he]
    · have he : u ≠ ⟨r,h⟩ := fun he => hu (congrArg Fin.val he)
      simp [hu, he]
  all_goals rfl

 theorem Evaluates.restrict {c : Command ℕ} {d e : Data ℕ} {n : ℕ}
    (he : Evaluates c d e n) (N : ℕ) (h : Bounded N c) :
    Evaluates (c.restrict N h) (d.restrict N) (e.restrict N) n := by
  induction he with
  | skip d => exact Evaluates.skip _
  | inc d r => simpa only [Command.restrict, restrict_inc N d r h] using Evaluates.inc (d.restrict N) ⟨r,h⟩
  | dec d r => simpa only [Command.restrict, restrict_dec N d r h] using Evaluates.dec (d.restrict N) ⟨r,h⟩
  | write d b => exact Evaluates.write _ _
  | discard d => exact Evaluates.discard _
  | rewind_empty hh => exact Evaluates.rewind_empty hh
  | rewind_cons hh he ih => exact Evaluates.rewind_cons hh (ih trivial)
  | seq h1 h2 i1 i2 => exact (i1 h.1).seq (i2 h.2)
  | test_zero hr he ih => exact Evaluates.test_zero hr (ih h.2.1)
  | test_pos hr he ih => exact Evaluates.test_pos hr (ih h.2.2)
  | read_one hr he ih => exact Evaluates.read_one hr (ih h.1)
  | read_zero hr he ih => exact Evaluates.read_zero hr (ih h.2.1)
  | read_empty hr he ih => exact Evaluates.read_empty hr (ih h.2.2)
  | loop_zero hr => exact Evaluates.loop_zero hr
  | @loop_pos r b d e f n m hr h1 h2 i1 i2 =>
    exact Evaluates.loop_pos hr (by simpa only [restrict_dec N d r h.1] using i1 h.2) (i2 h)

 def finite (c : Command ℕ) : Command (Fin c.regCount) :=
  c.restrict c.regCount (c.bounded_of_count _ le_rfl)

 theorem finite_evaluates {c : Command ℕ} {d e : Data ℕ} {n : ℕ}
    (h : Evaluates c d e n) : Evaluates c.finite (d.restrict c.regCount) (e.restrict c.regCount) n :=
  h.restrict _ _

end Command

open scoped BigOperators
open Command

/-- A bit table specified by two bounded-arithmetic expressions. These are
syntax, not assumed computable functions or unit-time arithmetic oracles. -/
def table (len bit : Expr) (input : List Bool) : List Bool :=
  List.ofFn (fun i : Fin (len.eval input (fun _ => 0)) =>
    decide (bit.eval input (fun _ => i.val) ≠ 0))

 def emit (r : ℕ) : Command ℕ := .test r (.write false) (.seq (clear r) (.write true))

 theorem emit_evaluates (d : Data ℕ) (r : ℕ) :
    Within (emit r) d (writeData (d.set r 0) (decide (d.reg r ≠ 0))) (2*d.reg r+3) := by
  by_cases hr : d.reg r = 0
  · refine ⟨2, by omega, ?_⟩
    have h := Evaluates.test_zero (r := r) (b := .seq (clear r) (.write true)) hr
      (Evaluates.write d false)
    have hd : d.set r 0 = d := by rw [← hr, Data.set_self]
    simpa [emit, hr, hd] using h
  · have h := Evaluates.test_pos (a := .write false) hr
      ((clear_evaluates d r).seq (Evaluates.write (d.set r 0) true))
    exact ⟨1+(2*d.reg r+1+1), by omega, by simpa [emit, hr] using h⟩

 def print (len bit : Expr) : Command ℕ :=
  .seq (len.compile (fun _ => 0) 1)
    (.loop 1 (.seq (bit.compile (fun _ => 1) 2) (emit 2)))

/-- Required cleanup before Mathlib's exact halt-list convention. -/
def eraseInput : Command ℕ := .seq (inputLength 1 0) (.loop 0 .discard)

end OptimalMaxCut.CounterMachine

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Gadgets_ValuePolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.CounterMachine.Expr
open Polynomial

 noncomputable def valuePolynomial : Expr → Polynomial ℕ
  | .const n => C n
  | .arg _ | .length => X
  | .bit _ | .zero _ => 1
  | .add a b => valuePolynomial a+valuePolynomial b
  | .sub a _ => valuePolynomial a
  | .mul a b => valuePolynomial a*valuePolynomial b
  | .sum b f => valuePolynomial b*(valuePolynomial f).comp (X+valuePolynomial b)

 theorem valuePolynomial_eval (e : Expr) (M : ℕ) :
    e.valuePolynomial.eval M = e.valueBudget M := by
  induction e generalizing M <;>
    simp_all [valuePolynomial, valueBudget, Polynomial.eval_comp]

 noncomputable def timePolynomial : Expr → Polynomial ℕ
  | .const n => C (n+1)
  | .arg _ => 5*X+2
  | .length => 5*X+6
  | .bit e => timePolynomial e+3*valuePolynomial e+X+7
  | .add a b | .sub a b => timePolynomial a+timePolynomial b+2*valuePolynomial b+1
  | .mul a b => timePolynomial a+timePolynomial b+
      valuePolynomial b*(5*valuePolynomial a+3)+1+2*valuePolynomial a+1+
      2*(valuePolynomial a*valuePolynomial b)+1
  | .zero a => timePolynomial a+2*valuePolynomial a+2
  | .sum b f => timePolynomial b+valuePolynomial b*
      ((timePolynomial f).comp (X+valuePolynomial b)+
        2*(valuePolynomial f).comp (X+valuePolynomial b)+3)+2*valuePolynomial b+2

 theorem timePolynomial_eval (e : Expr) (M : ℕ) :
    e.timePolynomial.eval M = e.timeBudget M := by
  induction e generalizing M <;>
    simp_all [timePolynomial, timeBudget, valuePolynomial_eval, Polynomial.eval_comp]

end OptimalMaxCut.CounterMachine.Expr

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_Information
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MaxCutGames.Soundness.ZeroInformation

/-! ## The observation fibre is a Cartesian product -/

/-! ## Exact weighted finite counting -/

/-! ## Position-indexed row maps -/

/-! ## Complete private-input reconstruction -/

/-- A total fixed decoder for a retained index. On supported (o,n) it is uniquely
determined by the distinctness of the three names. -/
noncomputable def decodeIndex {O N : Type} (name : O → Fin 3 → N)
    (occurrence : O) (n : N) : Fin 3 := by
  classical
  exact if h : ∃ i, name occurrence i = n then Classical.choose h else 0

def reconstructQuestion {P X : Type} (hidden : P → Bool) (inside outside : P → X) : P → X :=
  fun j => if hidden j then inside j else outside j

end MaxCutGames.Soundness.ZeroInformation

section

open scoped BigOperators

namespace MaxCutGames.Soundness.ConditionalIncidences

def incidence {O N : Type} (name : O → Fin 3 → N) (draw : O × Fin 3) : O × N :=
  (draw.1, name draw.1 draw.2)

end MaxCutGames.Soundness.ConditionalIncidences
end

/-!
# Every partner linear map has independent raw coefficient coordinates

The coefficient index is exactly `ConditionalIncidences.RawSlot`: one global
coefficient, two coefficients at every full position, and one at every single
position.  The coordinate bijection below is for every actual partner linear
map, and its finite-uniform-law theorem has no distributional hypothesis.
-/

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_IncidenceExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
This bridge connects the concrete partner projection to the actual equation/name
predicate of the incidence game. It uses no probabilistic or analytic hypotheses.
-/

namespace MaxCutGames.Reduction.ActualCanonical

open scoped BigOperators

universe u v w
variable {k : Nat}
variable {Name : Type u} {Id : Type v} {R : Type w}
variable [AddCommGroup R]
  [DecidableEq R]

def singletonTriple (i : Fin 3) (c : R) : Fin 3 → R := Pi.single i c

end MaxCutGames.Reduction.ActualCanonical

/-! Canonical-row descent for every actual partner linear map. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_AnswerBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit hidden-coordinate enumeration in the actual conditional law. -/

namespace MaxCutGames.Soundness.ConditionalIncidences
open scoped BigOperators

def coordinateReindex {A B X : Type} (e : B ≃ A) : (A → X) ≃ (B → X) where
  toFun f := fun b => f (e b)
  invFun g := fun a => g (e.symm a)
  left_inv f := by
    funext a
    exact congrArg f (e.apply_symm_apply a)
  right_inv g := by
    funext b
    exact congrArg g (e.symm_apply_apply b)

end MaxCutGames.Soundness.ConditionalIncidences

/-!
# Weighted conditional product law for the clean coordinates

The equation distribution is arbitrary.  All identities below are identities
of finite sums of its actual weights, rather than a reduction to uniform
occurrence sampling.  The clean set is fixed by independently sampled advice;
the only subsequently exposed question data lie outside that set.  Conditioning
on such data preserves the entire joint law of the clean questions.
-/

/-!
Weighted total probability for the public clean-coordinate observation.
The observation may have zero-probability fibres. Only its positive fibres
require a conditional bound; the identity itself is proved from finite sums.
-/

/-!
The actual local simulation in Lemma 6.8 after fixing H. These reconstruction
maps consume only the first player's occurrence tuple or the second player's
name tuple. Its winning-event containment is proved from the concrete equation
and named-projection predicates.
-/

/-! The genuine conditional experiment is the reconstructed repeated-game law. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_OrientationVectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
# Fresh orientations of nonzero perturbations

This is the nonzero-symbol uniformity step in the latent-noise recurrence.
The perturbation is fixed before the orientation, and zero is excluded from
both sample spaces explicitly.
-/

section

open scoped BigOperators

namespace MaxCutGames.Gadget.OrientationVectors

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem equiv_apply_ne_zero {B U : Type*} [AddCommGroup B] [Module K B]
    [AddCommGroup U] [Module K U] (J : B ≃ₗ[K] U) {b : B} (hb : b ≠ 0) :
    J b ≠ 0 := by
  intro h
  apply hb
  exact J.injective (h.trans (map_zero J).symm)

instance nonzeroAction : MulAction (V ≃ₗ[K] V) {x : V // x ≠ 0} where
  smul a x := ⟨a x.val, equiv_apply_ne_zero a x.property⟩
  one_smul x := by apply Subtype.ext; rfl
  mul_smul a b x := by apply Subtype.ext; rfl

end MaxCutGames.Gadget.OrientationVectors
end

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_OrientedBlockKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MaxCutGames.Quadratic

/-!
# Trace coordinates for families of binary characters

The trace pairing identifies the binary dual of `F³` with `F³` itself.  Its
inverse is linear, so a common-parent family of binary functionals produces
one binary-linear lift `g`, as required by the all-lifts genericity theorem.
-/

/-!
# The binary trace annihilator of a quadratic-block hyperplane

The trace annihilator of the field hyperplane perpendicular to a nonzero
vector is exactly its field line.  Scaling test vectors first upgrades binary
trace orthogonality to field-valued orthogonality; explicit coordinate test
vectors then identify the annihilator.  No earlier gadget result is used.
-/

/-!
# Character kernels on quadratic blocks

The character with horizontal coefficient `g` and vertical coefficient `z`
annihilates the block attached to `Fz` precisely when the alignment
equation holds.  The predicate below is annihilation of the actual binary
submodule, rather than an abstract replacement for that condition.
-/

section

open Module
open scoped BigOperators Matrix

variable {R F V ι n E : Type*}
variable [Field R] [Field F] [Algebra R F]
variable [AddCommGroup V] [Module R V]
variable [Fintype ι] [Fintype n]

/-- The `|n| * |ι|` alignment columns for a fixed parametrization and input set.
The input set is represented by any map `point : E → V`; no injectivity is
needed for the exact algebraic equivalence. -/
def alignmentMatrix (b : Basis ι R V) (point : E → V) (z : V → n → F) :
    Matrix E (n × ι) F :=
  fun e ij => algebraMap R F (b.repr (point e) ij.2) * z (point e) ij.1

end

/-!
# Rank-loss accounting for quadratic blocks

A nonzero kernel character determines the field line of a lossy block.  On
a generic space there is at most one such character on each field line, so
the rank drops by at most one.  Counting the possible determining characters
also bounds the number of lossy lines.  These are deterministic statements;
the random orientation may be selected only after this data is fixed.
-/

variable {R V W I : Type*} [Field R]
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]

variable [Fintype V] [Fintype I] [DecidableEq I]

/-- The actual finite event of a child map having a nonzero kernel. -/
def lossIndices (f : I → V →ₗ[R] W) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => ∃ v : V, v ≠ 0 ∧ f i v = 0)

def alignedCharacters (aligned : V → Prop) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => v ≠ 0 ∧ aligned v)

end MaxCutGames.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_HarmonicLoss
attribute [-instance] _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
# Harmonic loss for the actual quadratic child maps

The probabilistic hypotheses of the MaxCutGames.Gadget.Harmonic.harmonic accounting lemmas are discharged
here by the proved field-line kernel criterion and genericity count.
-/

/-!
# Outgoing MaxCutGames.Gadget.Harmonic.harmonic loss for the actual adaptive child map

Uniform sampling of the concrete pair `(field line, binary orientation)` has
the uniform field-line marginal. The child rank is independent of orientation,
so the proved quadratic kernel count gives the outgoing conditional loss for
the common map produced by every parent lift.
-/

/-!
# The finite nongeneric fraction

This definition records the actual uniform event on the rank-indexed
Grassmannian. Its quantitative bounds are proved in GenericSubspaceProbability;
orientation arguments can use the definition independently of that proof.
-/

section

open scoped BigOperators Classical
open Module

namespace MaxCutGames.Gadget.FreshGenericity

open Quadratic

section RankTransport

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]

local instance linearMapFintype [Fintype V] [Fintype W] : Fintype (V →ₗ[K] W) :=
  Fintype.ofInjective (fun f : V →ₗ[K] W => (f : V → W)) DFunLike.coe_injective

local instance linearEquivFintype [Fintype V] [Fintype W] : Fintype (V ≃ₗ[K] W) :=
  Fintype.ofInjective (fun e : V ≃ₗ[K] W => (e : V → W)) DFunLike.coe_injective

local instance submoduleFintype [Fintype V] : Fintype (Submodule K V) :=
  Fintype.ofInjective (fun S : Submodule K V => (S : Set V)) SetLike.coe_injective

end RankTransport

attribute [local instance] linearMapFintype linearEquivFintype submoduleFintype

end MaxCutGames.Gadget.FreshGenericity
end

/-!
# Harmonic potential for the actual recursively selected lifts

This is the adaptive induction on the concrete descendant lift construction.
The first outgoing step may begin at a bad subspace; every later orientation
is fresh. Accordingly the bound has one initial bad-space penalty, which
vanishes for the fixed generic top subspace.
-/

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_BaseDetection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# From full character lifts to linear-map detection

If a target linear map is injective on the logical alphabet, a linear left
inverse of that restriction turns all logical characters into a full lift.
Detection by this lift implies that the target map does not annihilate the
noise. The left inverse is proved to exist by the vector-space splitting
theorem; it is not an additional premise.
-/

/-!
# Detection survives the logical-kernel quotient

A full family of logical characters on the quotient pulls back to a full
lift on the original stage. Its detection event is the same pointwise.
Combining this with the proved left-inverse construction gives detection of
every linear map injective on the quotient's logical subspace.
-/

namespace MaxCutGames.Gadget.NonlinearRecurrence

open scoped BigOperators

variable {k I P R X B : Type*} [CommRing k]
variable [Fintype I] [DecidableEq I]
variable [AddCommGroup P] [Module k P] [Fintype P]
variable [AddCommGroup R] [Module k R]
variable [AddCommGroup X] [Module k X] [Fintype X]
variable [AddCommGroup B] [Module k B] [Fintype B] [DecidableEq B]

def change (F : X × B → B) (p d : X × B) : ℚ :=
  if F (p + d) ≠ F p then 1 else 0

end MaxCutGames.Gadget.NonlinearRecurrence

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_ParityIndependence
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Separation of polynomial parity classes

The genericity argument uses monomials with distinct squarefree
exponent vectors. Polynomial coefficients in the original «variables» become
polynomials in squares after adjoining their square roots. The lemmas below
prove the resulting coefficient separation directly, without assuming an
algebraic independence witness.
-/

namespace MaxCutGames.Quadratic

open MvPolynomial
open scoped BigOperators

variable {σ ι R : Type*} [CommSemiring R]

/-- Exponents zero or one represent parity classes. -/
def SquarefreeExponent (a : σ →₀ ℕ) : Prop := ∀ k, a k < 2

noncomputable def blockExponent {κ J : Type*} [Finite κ] [Finite J]
    (v : κ → J) : (κ × J) →₀ ℕ := by
  classical
  exact Finsupp.equivFunOnFinite.symm (fun x => if x.2 = v x.1 then 1 else 0)

@[simp] theorem blockExponent_apply {κ J : Type*} [Finite κ] [Finite J] [DecidableEq J]
    (v : κ → J) (x : κ × J) :
    blockExponent v x = if x.2 = v x.1 then 1 else 0 := by
  classical
  by_cases h : x.2 = v x.1 <;> simp [blockExponent, h]

end MaxCutGames.Quadratic

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_GenericPolynomial
attribute [-instance] _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
# Polynomial parity obstruction

This supplies the algebraic obstruction step in the v2 genericity proof.
Squaring a cleared dual row exposes its distinct squarefree parity classes.
No genericity or minor-existence conclusion is assumed here.
-/

namespace MaxCutGames.Quadratic

section

open MvPolynomial
open scoped BigOperators
open scoped nonZeroDivisors

variable {σ : Type*}

variable {J X : Type*} [Fintype J] [Fintype X]

/-- The universal coordinate `z_i(t)` with the `x_ij` as indeterminates. -/
noncomputable def universalLinearForm (t : J → ZMod 2) (i : Fin 3) :
    MvPolynomial (Fin 3 × J) (ZMod 2) :=
  ∑ j, C (t j) * MvPolynomial.X (i, j)

/-- Polynomial alignment columns; every lift is one linear combination of
these columns. -/
noncomputable def universalAlignmentColumn (t : X → J → ZMod 2)
    (ij : Fin 3 × J) (x : X) : MvPolynomial (Fin 3 × J) (ZMod 2) :=
  C (t x ij.2) * universalLinearForm (t x) ij.1

/-- Coefficient obtained by pairing a polynomial row with a cubic binary
evaluation. -/
noncomputable def cubicPairing (t : X → J → ZMod 2)
    (p : X → MvPolynomial (Fin 3 × J) (ZMod 2)) (v : Fin 3 → J) :
    MvPolynomial (Fin 3 × J) (ZMod 2) :=
  ∑ x, p x * C (∏ i, t x (v i))

/-- Clearing the rational dual's denominator and squaring gives this one
polynomial obstruction to simultaneous alignment. Its degree is finite and
depends only on the fixed set of inputs. -/
noncomputable def alignmentObstruction (t : X → J → ZMod 2)
    (p : X → MvPolynomial (Fin 3 × J) (ZMod 2)) :
    MvPolynomial (Fin 3 × J) (ZMod 2) :=
  ∑ x, p x ^ 2 * ∏ i, universalLinearForm (t x) i

end

section

open scoped BigOperators

/-- Degree-two evaluation space. Repeated indices are allowed, so on binary
points this also contains every degree-one evaluation. -/
def quadraticEvaluationSpan {F X I : Type*} [Field F]
    (c : I → X → F) : Submodule F (X → F) :=
  Submodule.span F (Set.range fun ij : I × I => fun x => c ij.1 x * c ij.2 x)

/-- Degree-three evaluation space. Repeated indices recover all lower
positive degrees on binary points. -/
def cubicEvaluationSpan {F X I : Type*} [Field F]
    (c : I → X → F) : Submodule F (X → F) :=
  Submodule.span F
    (Set.range fun ijk : I × I × I => fun x => c ijk.1 x * c ijk.2.1 x * c ijk.2.2 x)

end

/-! The low-dimension obstruction used by the v2 all-lifts genericity proof. -/

/-! The actual random binary-linear parametrization used in the genericity proof. -/

section

open Module
open scoped BigOperators

variable {F J : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F] [Fintype J]

/-- Independent field entries specify a binary-linear map into `F³`. -/
def parameterMap (x : (Fin 3 × J) → F) : (J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F) :=
  (Pi.basisFun (ZMod 2) J).constr (ZMod 2) (fun j i => x (i, j))

omit [CharP F 2] in
theorem parameterMap_basis (x : (Fin 3 × J) → F) (j : J) (i : Fin 3) :
    parameterMap x ((Pi.basisFun (ZMod 2) J) j) i = x (i, j) := by
  exact congrFun ((Pi.basisFun (ZMod 2) J).constr_basis (ZMod 2)
    (fun j i => x (i, j)) j) i

end

/-!
# One polynomial controls all binary linear lifts

For fixed binary dimension, multiply the nonzero obstructions for the finitely
many sets of `3r + 1` nonzero inputs.  A nonvanishing specialization then obeys
the alignment bound simultaneously for every binary linear map.  The resulting
polynomial and its degree are chosen before the extension field.
-/

/-!
# Polynomial obstructions to collapsed or proportional binary inputs

One linear polynomial detects each nonzero input. One quadratic polynomial
detects each pair of distinct nonzero binary inputs. The witnesses are proved
nonzero by explicit coordinate-selector evaluations. Together with the
alignment obstruction they yield a finite product whose zero set contains
every failure of v2 genericity. An `O_r(1/q)` bound suffices here.
-/

open MvPolynomial

variable {J : Type*} [Fintype J]

/-- Set the first two rows of the indeterminate matrix to coordinate
selectors. The third row is zero. -/
noncomputable def selectorAssignment (j k : J) : (Fin 3 × J) → ZMod 2 := by
  classical
  exact fun x => if x.1 = 0 then (if x.2 = j then 1 else 0)
    else if x.1 = 1 then (if x.2 = k then 1 else 0) else 0

/-- A two-row determinant, with subtraction equal to addition in
characteristic two. -/
noncomputable def universalPairMinor (t u : J → ZMod 2) :
    MvPolynomial (Fin 3 × J) (ZMod 2) :=
  universalLinearForm t 0 * universalLinearForm u 1 +
    universalLinearForm t 1 * universalLinearForm u 0

end MaxCutGames.Quadratic

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_SeparationCertificate
attribute [-instance] _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! A single finite polynomial certifies injectivity and pair separation of
the actual binary-linear parametrization. -/

namespace MaxCutGames.Quadratic

section

open MvPolynomial
open scoped BigOperators

variable (J : Type*) [Fintype J]

def nonzeroBinaryInputs : Finset (J → ZMod 2) := by
  classical
  exact Finset.univ.erase 0

def distinctNonzeroBinaryPairs : Finset ((J → ZMod 2) × (J → ZMod 2)) := by
  classical
  exact Finset.univ.filter (fun tu => tu.1 ≠ 0 ∧ tu.2 ≠ 0 ∧ tu.1 ≠ tu.2)

def separationPolynomial : MvPolynomial (Fin 3 × J) (ZMod 2) :=
  (∏ t ∈ nonzeroBinaryInputs J, universalLinearForm t 0) *
    ∏ tu ∈ distinctNonzeroBinaryPairs J, universalPairMinor tu.1 tu.2

end

/-!
# Passing genericity from a parametrization to its actual image

An injective binary-linear parametrization identifies its domain with the
image subspace. The universal quantifier over linear lifts is transported
by composition, and alignment-event cardinalities agree exactly.
-/

/-!
# Finite-field polynomial exceptional events

The nonzero polynomial obstruction for each fixed input set gives a uniform
bound over all linear lifts.  Its coefficients lie in the binary prime field,
so its degree is fixed before the extension field is chosen.  The theorems
below keep this order explicit and combine finitely many obstructions without
any union over maps.
-/

section

open scoped BigOperators

variable {K F : Type*} [Field K] [Field F] [Fintype F]

/-- The exact uniform probability on an explicit finite assignment space. -/
def assignmentProbability {n : ℕ} (event : (Fin n → F) → Prop) : ℚ≥0 := by
  classical
  exact ((Finset.univ.filter event).card : ℚ≥0) / (Fintype.card F : ℚ≥0) ^ n

end

/-!
# Polynomial exceptional events on arbitrary finite variable sets

Reindexing the variable set transports both the polynomial and the uniform
assignment space. Thus the checked finite-field zero bound applies directly
to the three-by-r «variables» in the genericity proof, without changing the
degree or taking a union over possible linear lifts.
-/

section

open scoped BigOperators

variable {σ τ K F : Type*} [Field K] [Field F] [Fintype F]

/-- Reindexing an assignment transports it contravariantly along the variable
equivalence. -/
def reindexAssignments (e : σ ≃ τ) : (σ → F) ≃ (τ → F) where
  toFun x := fun t => x (e.symm t)
  invFun y := fun s => y (e s)
  left_inv x := by funext s; simp
  right_inv y := by funext t; simp

/-- Uniform assignment probability for an arbitrary finite variable set. -/
def finiteAssignmentProbability [Fintype σ] (event : (σ → F) → Prop) : ℚ≥0 := by
  classical
  exact ((Finset.univ.filter event).card : ℚ≥0) /
    (Fintype.card F : ℚ≥0) ^ Fintype.card σ

end

/-!
# A fixed polynomial certifies genuine all-lifts generic subspaces

The certificate is constructed from binary input sets and is independent of
the extension field.  It combines injectivity, pairwise nonproportionality,
and the simultaneous alignment bound, then transports the latter to the
actual image subspace.  The finite-field exceptional probability tends to
zero with field size using a fixed finite numerator.
-/

/-! Exact correspondence between uniform field entries and all binary-linear maps. -/

variable {F J : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F] [Fintype J]

/-- Every binary-linear map is determined by its freely chosen field-valued
basis entries, with no rejection or nonuniform multiplicity. -/
def parameterMapEquiv : ((Fin 3 × J) → F) ≃
    ((J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F)) where
  toFun := parameterMap
  invFun g ij := g ((Pi.basisFun (ZMod 2) J) ij.2) ij.1
  left_inv x := by
    funext ij
    exact parameterMap_basis x ij.2 ij.1
  right_inv g := by
    apply (Pi.basisFun (ZMod 2) J).ext
    intro j
    funext i
    exact parameterMap_basis _ j i

end MaxCutGames.Quadratic

/-!
Uniform injective parameter maps induce the uniform law on subspaces of the
specified rank.  The proof uses actual transitivity of ambient linear
automorphisms on injections, not an assumed distributional premise.
-/

section

open scoped BigOperators
open Module

namespace MaxCutGames.Quadratic.UniformSubspaces

variable {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- A linear parameter map with its injectivity proof. -/
def Injection (K V W : Type*) [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] :=
  {J : V →ₗ[K] W // Function.Injective J}

instance injectionAction : MulAction (W ≃ₗ[K] W) (Injection K V W) where
  smul a J := ⟨a.toLinearMap.comp J.val, a.injective.comp J.property⟩
  one_smul J := by
    apply Subtype.ext
    ext x
    rfl
  mul_smul a b J := by
    apply Subtype.ext
    ext x
    rfl

end MaxCutGames.Quadratic.UniformSubspaces
end

/-!
The polynomial exceptional-event bound is transported first to all binary
linear parameter maps and then, by proved uniformity conditional on
injectivity, to the actual finite Grassmannian.  The same argument supplies
a generic subspace, rather than presupposing that one exists.
-/

open Module

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_StageNoiseRecurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact finite-stage nonlinear noise law

This packages the one-level recurrence for the actual recursive `Stage`, solves
it at every height, and proves that the ambient-kernel quotient preserves it.
The averaged block kernel remains an explicit argument for later instantiation
with the concrete quadratic family.
-/

namespace MaxCutGames.Gadget.StageNoiseRecurrence

open scoped BigOperators

noncomputable def average {A : Type*} [Finite A] (f : A → ℚ) : ℚ :=
  letI := Fintype.ofFinite A
  𝔼 a, f a

universe u v

end MaxCutGames.Gadget.StageNoiseRecurrence

/-!
The spanning clause of v2 Lemma `latent-block`.  Three coordinate lines
already suffice.  Horizontal coordinate vectors lie in their own block;
vertical coordinate vectors lie in either of the other two blocks.
-/

/-! Surjectivity of the actual all-lines/all-orientations parent aggregate. -/

noncomputable section

namespace MaxCutGames.Gadget.QuadraticStageNoise

open scoped BigOperators Classical
open Quadratic

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

def rate (F : Type*) [Fintype F] : ℚ :=
  1 - 1 / ((Nat.card F : ℚ) ^ 2 + (Nat.card F : ℚ) + 1)

end MaxCutGames.Gadget.QuadraticStageNoise
end

namespace MaxCutGames.Gadget.Parameters

open scoped BigOperators

/-- Computable rank exceeding any prescribed rational MaxCutGames.Gadget.Harmonic.harmonic level. -/
def rankFor (level : ℚ) : ℕ := 2 ^ ⌈2 * level⌉₊

/-- Explicit threshold depending only on the requested nonlinear error. -/
def initialRank (p : ℚ) : ℕ := rankFor (8 * (p⁻¹ + 1))

end MaxCutGames.Gadget.Parameters

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_FiniteFieldChoice
attribute [-instance] _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
A concrete mathematical family of finite binary fields of unbounded size.
The extension degree is chosen from numerical thresholds alone, before the
logical output dimension of the latent gadget is selected.
-/

namespace MaxCutGames.Quadratic

/-- The degree-`d` binary Galois field.  Cardinality statements below require
`d > 0`; the degenerate exponent zero is deliberately excluded. -/
abbrev BinaryField (d : ℕ) := GaloisField 2 d

/-- A deliberately simple explicit upper choice; optimization of the field
size is irrelevant because these thresholds are fixed before the input. -/
def fieldDegree (cardThreshold rankThreshold : ℕ) : ℕ :=
  cardThreshold + rankThreshold + 1

end MaxCutGames.Quadratic

/-!
# One field for every rank up to a fixed threshold

The extension degree is chosen using only the rank threshold and the requested
genericity error.  In particular it is fixed before the logical dimension in
the later enlargement construction.  A generic top-rank space exists in the
same field.
-/

namespace MaxCutGames.Quadratic

open scoped BigOperators

noncomputable section

noncomputable instance binaryFieldFintype (d : ℕ) : Fintype (BinaryField d) :=
  Fintype.ofFinite _

end

end MaxCutGames.Quadratic

/-!
# The finite base gadget with arbitrarily small nonlinear change

The harmonic rank and genericity error are chosen first. A single finite field
then supplies all required genericity statements, and the actual recursion is
run to its harmonic depth. The kernel quotient injects the logical alphabet.
Every linear map injective there detects at least one quarter of the noise.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_MatrixChartDegreeNeighbors
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The full Grassmann degree, by choosing the intersection hyperplane and a
different one-dimensional extension. No graph regularity is assumed.
-/

namespace MaxCutGames.Inverse.MatrixChart

open Module

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

abbrev HyperplanesBelow (L : Submodule K E) :=
  {H : Submodule K E // H ≤ L ∧ finrank K H + 1 = finrank K L}

abbrev GrassmannNeighbors (L : Submodule K E) :=
  {W : Submodule K E // finrank K W = finrank K L ∧
    finrank K (L ⊓ W : Submodule K E) + 1 = finrank K L}

noncomputable def hyperplanesBelowEquiv (L : Submodule K E) :
    HyperplanesBelow L ≃ Hyperplanes K L where
  toFun H := ⟨H.val.comap L.subtype, by
    rw [(Submodule.comapSubtypeEquivOfLe H.property.1).finrank_eq]
    exact H.property.2⟩
  invFun H := ⟨H.val.map L.subtype, Submodule.map_subtype_le L H.val, by
    rw [Submodule.finrank_map_subtype_eq]
    exact H.property⟩
  left_inv H := by
    apply Subtype.ext
    simp [Submodule.map_comap_subtype, inf_eq_right.mpr H.property.1]
  right_inv H := by
    apply Subtype.ext
    exact Submodule.comap_map_eq_of_injective Subtype.val_injective H.val

/-- Distinct one-dimensional extensions intersect in their common base. -/
theorem inf_eq_base_of_distinct_extensions [FiniteDimensional K E]
    (H L W : Submodule K E) (hHL : H ≤ L) (hHW : H ≤ W)
    (hL : finrank K L = finrank K H + 1)
    (hW : finrank K W = finrank K H + 1) (hWL : W ≠ L) :
    L ⊓ W = H := by
  apply le_antisymm
  · by_contra hn
    have hlt : H < L ⊓ W := lt_of_le_of_ne (le_inf hHL hHW) (by
      intro heq
      exact hn heq.ge)
    have hd := Submodule.finrank_lt_finrank_of_lt hlt
    have hi := Submodule.finrank_mono (show L ⊓ W ≤ L from inf_le_left)
    have heq : L ⊓ W = L := Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
    have hLW : L ≤ W := by rw [← heq]; exact inf_le_right
    exact hWL (Submodule.eq_of_le_of_finrank_eq hLW (hL.trans hW.symm)).symm
  · exact le_inf hHL hHW

abbrev NeighborExtensionData (L : Submodule K E) :=
  (H : HyperplanesBelow L) × {W : Extensions H.val // W.val ≠ L}

/-- Each neighbor has a unique intersection hyperplane and extension. -/
noncomputable def neighborsEquivExtensionData [FiniteDimensional K E]
    (L : Submodule K E) : GrassmannNeighbors L ≃ NeighborExtensionData L where
  toFun W :=
    ⟨⟨L ⊓ W.val, inf_le_left, W.property.2⟩,
      ⟨⟨W.val, inf_le_right, W.property.1.trans W.property.2.symm⟩, by
        intro heq
        have h := W.property.2
        rw [heq, inf_idem] at h
        omega⟩⟩
  invFun d := ⟨d.2.val.val, by
    have hI := inf_eq_base_of_distinct_extensions d.1.val L d.2.val.val
      d.1.property.1 d.2.val.property.1 d.1.property.2.symm
      d.2.val.property.2 d.2.property
    exact ⟨d.2.val.property.2.trans d.1.property.2,
      by rw [hI]; exact d.1.property.2⟩⟩
  left_inv W := by rfl
  right_inv d := by
    rcases d with ⟨⟨H, hHL, hH⟩, ⟨⟨W, hHW, hW⟩, hWL⟩⟩
    have hI := inf_eq_base_of_distinct_extensions H L W hHL hHW hH.symm hW hWL
    cases hI
    rfl

end MaxCutGames.Inverse.MatrixChart

/-!
The local neighbor law for the ordered-basis lift used in KMS Lemma 2.7.
The map is an arbitrary injective linear map, not a matrix graph chart.
An update in a direction outside its image stays injective, and its image
intersects the original image in exactly the transported functional kernel.
-/

namespace MaxCutGames.Inverse.KMSBasisComparison

open Module

variable {K E F : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

/-- The actual rank-one update of an ordered basis map. -/
def rankOneUpdate (X : E →ₗ[K] F) (a : E →ₗ[K] K) (y : F) : E →ₗ[K] F :=
  X + a.smulRight y

@[simp] theorem rankOneUpdate_apply (X : E →ₗ[K] F) (a : E →ₗ[K] K)
    (y : F) (x : E) : rankOneUpdate X a y x = X x + a x • y := rfl

/-- An outside direction returns to the original image exactly when its
coefficient vanishes. This does not require injectivity of `X`. -/
theorem rankOneUpdate_mem_range_iff (X : E →ₗ[K] F) (a : E →ₗ[K] K)
    {y : F} (hy : y ∉ LinearMap.range X) (x : E) :
    rankOneUpdate X a y x ∈ LinearMap.range X ↔ a x = 0 := by
  constructor
  · intro h
    have hs : a x • y ∈ LinearMap.range X := by
      have hh := (LinearMap.range X).sub_mem h (LinearMap.mem_range_self X x)
      simpa only [rankOneUpdate_apply, add_sub_cancel_left] using hh
    by_contra ha
    exact hy (((LinearMap.range X).smul_mem_iff ha).mp hs)
  · intro ha
    simpa only [rankOneUpdate_apply, ha, zero_smul, add_zero] using
      LinearMap.mem_range_self X x

/-- Rank-one perturbation in an outside direction preserves independence. -/
theorem injective_rankOneUpdate (X : E →ₗ[K] F) (hX : Function.Injective X)
    (a : E →ₗ[K] K) {y : F} (hy : y ∉ LinearMap.range X) :
    Function.Injective (rankOneUpdate X a y) := by
  apply (injective_iff_map_eq_zero (rankOneUpdate X a y)).mpr
  intro x hx
  have ha : a x = 0 := (rankOneUpdate_mem_range_iff X a hy x).mp
    (by rw [hx]; exact (LinearMap.range X).zero_mem)
  have hxx : X x = 0 := by simpa only [rankOneUpdate_apply, ha, zero_smul,
    add_zero] using hx
  exact hX (by simpa only [map_zero] using hxx)

/-- Exact intersection, retaining the functional rather than only its rank. -/
theorem range_inf_rankOneUpdate (X : E →ₗ[K] F) (a : E →ₗ[K] K)
    {y : F} (hy : y ∉ LinearMap.range X) :
    LinearMap.range X ⊓ LinearMap.range (rankOneUpdate X a y) =
      (LinearMap.ker a).map X := by
  ext z
  constructor
  · rintro ⟨hz, x, hx⟩
    have ha : a x = 0 := (rankOneUpdate_mem_range_iff X a hy x).mp
      (by rw [hx]; exact hz)
    refine ⟨x, ha, ?_⟩
    simpa only [rankOneUpdate_apply, ha, zero_smul, add_zero] using hx
  · rintro ⟨x, hx, rfl⟩
    refine ⟨LinearMap.mem_range_self X x, x, ?_⟩
    have ha : a x = 0 := hx
    simp only [rankOneUpdate_apply, ha, zero_smul, add_zero]

/-- The updated image is a genuine Grassmann neighbor, with the full
ambient neighbor predicate rather than its chart restriction. -/
noncomputable def rankOneUpdateNeighbor [FiniteDimensional K E]
    (X : E →ₗ[K] F) (hX : Function.Injective X)
    (a : E →ₗ[K] K) (ha : a ≠ 0)
    (y : F) (hy : y ∉ LinearMap.range X) :
    MatrixChart.GrassmannNeighbors (LinearMap.range X) :=
  ⟨LinearMap.range (rankOneUpdate X a y), by
    constructor
    · rw [LinearMap.finrank_range_of_inj (injective_rankOneUpdate X hX a hy),
        LinearMap.finrank_range_of_inj hX]
    · rw [range_inf_rankOneUpdate X a hy,
        ← (Submodule.equivMapOfInjective X hX (LinearMap.ker a)).finrank_eq,
        LinearMap.finrank_range_of_inj hX]
      exact Module.Dual.finrank_ker_add_one_of_ne_zero ha⟩

@[simp] theorem rankOneUpdateNeighbor_val [FiniteDimensional K E]
    (X : E →ₗ[K] F) (hX : Function.Injective X)
    (a : E →ₗ[K] K) (ha : a ≠ 0) (y : F) (hy : y ∉ LinearMap.range X) :
    (rankOneUpdateNeighbor X hX a ha y hy).val =
      LinearMap.range (rankOneUpdate X a y) := rfl

end MaxCutGames.Inverse.KMSBasisComparison

/-! Every full Grassmann neighbor is reached by an outside rank-one update.
The proof works over every field and never selects a graph chart. -/

namespace MaxCutGames.Inverse.MatrixChart

variable {K X Y : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

/-- The first coordinate identifies the graph with its domain. -/
def graphEquiv (T : X →ₗ[K] Y) : X ≃ₗ[K] T.graph where
  toFun x := ⟨(x, T x), rfl⟩
  invFun x := x.val.1
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    exact Prod.ext rfl x.property.symm
  map_add' _ _ := by
    apply Subtype.ext
    exact Prod.ext rfl (map_add T _ _)
  map_smul' _ _ := by
    apply Subtype.ext
    exact Prod.ext rfl (map_smul T _ _)

theorem graph_injective : Function.Injective (LinearMap.graph (R := K) (M := X) (M₂ := Y)) := by
  intro T U h
  apply LinearMap.ext
  intro x
  have hx : (x, T x) ∈ U.graph := h ▸ (show (x, T x) ∈ T.graph from rfl)
  exact hx

/-- Common graph vectors correspond exactly to the kernel of the difference. -/
def intersectionEquiv (T U : X →ₗ[K] Y) :
    LinearMap.ker (T - U) ≃ₗ[K] (T.graph ⊓ U.graph : Submodule K (X × Y)) where
  toFun x := ⟨(x.val, T x.val), by
    refine ⟨rfl, ?_⟩
    have hx : T x.val - U x.val = 0 := x.property
    exact sub_eq_zero.mp hx⟩
  invFun x := ⟨x.val.1, by
    change T x.val.1 - U x.val.1 = 0
    exact sub_eq_zero.mpr (x.property.1.symm.trans x.property.2)⟩
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    exact Prod.ext rfl x.property.1.symm
  map_add' _ _ := by
    apply Subtype.ext
    exact Prod.ext rfl (map_add T _ _)
  map_smul' _ _ := by
    apply Subtype.ext
    exact Prod.ext rfl (map_smul T _ _)

theorem finrank_graph [FiniteDimensional K X] (T : X →ₗ[K] Y) :
    Module.finrank K T.graph = Module.finrank K X :=
  (graphEquiv T).finrank_eq.symm

/-- Rank-nullity in the graph chart, without truncated natural subtraction. -/
theorem finrank_intersection_add_rank [FiniteDimensional K X] (T U : X →ₗ[K] Y) :
    Module.finrank K (T.graph ⊓ U.graph : Submodule K (X × Y)) +
      Module.finrank K (LinearMap.range (T - U)) = Module.finrank K X := by
  rw [← (intersectionEquiv T U).finrank_eq, Nat.add_comm]
  exact LinearMap.finrank_range_add_finrank_ker (T - U)

/-- Grassmann adjacency within the chart is exactly rank-one difference. -/
theorem adjacent_iff_rank_one [FiniteDimensional K X] (T U : X →ₗ[K] Y) :
    Module.finrank K (T.graph ⊓ U.graph : Submodule K (X × Y)) + 1 =
        Module.finrank K X ↔
      Module.finrank K (LinearMap.range (T - U)) = 1 := by
  have h := finrank_intersection_add_rank T U
  omega

/-- A nonzero rank-one perturbation gives an adjacent graph vertex. -/
theorem adjacent_rank_one_step [FiniteDimensional K X]
    (T : X →ₗ[K] Y) (a : X →ₗ[K] K) (l : Y) (ha : a ≠ 0) (hl : l ≠ 0) :
    Module.finrank K (T.graph ⊓ (T + a.smulRight l).graph :
      Submodule K (X × Y)) + 1 = Module.finrank K X := by
  apply (adjacent_iff_rank_one T (T + a.smulRight l)).mpr
  have heq : T - (T + a.smulRight l) = (-a).smulRight l := by
    apply LinearMap.ext
    intro x
    simp []
  rw [heq, LinearMap.range_smulRight_apply (neg_ne_zero.mpr ha)]
  exact finrank_span_singleton hl

/-- The lower end of an interval is given by a spanning list of graph vectors. -/
def lowerRows {ι : Type*} (d : ι → X) (s : ι → Y) : Submodule K (X × Y) :=
  Submodule.span K (Set.range fun i => (d i, s i))

def upperColumns {ι : Type*} (t : ι → X →ₗ[K] K) (q : ι → Y →ₗ[K] K) :
    Submodule K (X × Y) :=
  ⨅ i, LinearMap.ker ((q i).comp (LinearMap.snd K X Y) -
    (t i).comp (LinearMap.fst K X Y))

end MaxCutGames.Inverse.MatrixChart

/-!
Exact rank-one sampling in the binary matrix chart. Nonzero pairs of a
functional and a vector represent rank-one maps uniquely over `ZMod 2`.
Thus uniform nonzero factors give uniform rank-one maps. Zero factors are
excluded explicitly; no conditioned/unconditioned sampling is identified.
-/

namespace MaxCutGames.Inverse.MatrixChart

section ArbitraryField

variable {K X Y : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

/-- Every map with one-dimensional range is a nonzero functional times a
nonzero vector. This existence statement is valid over any field. -/
theorem exists_smulRight_of_rank_one (T : X →ₗ[K] Y)
    (hT : Module.finrank K T.range = 1) :
    ∃ (a : X →ₗ[K] K) (l : Y), a ≠ 0 ∧ l ≠ 0 ∧ T = a.smulRight l := by
  classical
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one hT
  let a : X →ₗ[K] K := e.symm.toLinearMap.comp T.rangeRestrict
  have ha : a ≠ 0 := LinearMap.surjective_iff_ne_zero.mp
    (e.symm.surjective.comp T.surjective_rangeRestrict)
  have hl : (e 1 : Y) ≠ 0 := by
    intro h
    have he : e 1 = e 0 := by
      apply Subtype.ext
      simp at h
    exact one_ne_zero (e.injective he)
  refine ⟨a, (e 1 : Y), ha, hl, ?_⟩
  apply LinearMap.ext
  intro x
  have h : a x • e 1 = T.rangeRestrict x := by
    calc
      a x • e 1 = e (a x • (1 : K)) := (e.map_smul _ _).symm
      _ = e (a x) := by rw [smul_eq_mul, mul_one]
      _ = T.rangeRestrict x := e.apply_symm_apply _
  exact (congrArg Subtype.val h).symm

/-- The exact algebraic characterization of nonzero rank-one maps. -/
theorem rank_one_iff_exists_smulRight (T : X →ₗ[K] Y) :
    Module.finrank K T.range = 1 ↔
      ∃ (a : X →ₗ[K] K) (l : Y), a ≠ 0 ∧ l ≠ 0 ∧ T = a.smulRight l := by
  constructor
  · exact exists_smulRight_of_rank_one T
  · rintro ⟨a, l, ha, hl, rfl⟩
    rw [LinearMap.range_smulRight_apply ha]
    exact finrank_span_singleton hl

end ArbitraryField

variable {X Y : Type*}
  [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]

/-- Over the two-element field there is no nontrivial rescaling ambiguity. -/
theorem binary_smulRight_unique
    {a b : X →ₗ[ZMod 2] ZMod 2} {l k : Y}
    (ha : a ≠ 0) (hl : l ≠ 0)
    (h : a.smulRight l = b.smulRight k) : a = b ∧ l = k := by
  obtain ⟨x, hx⟩ := a.surjective ha 1
  have hx' : l = b x • k := by
    simpa only [LinearMap.smulRight_apply, hx, one_smul] using
      LinearMap.congr_fun h x
  have scalar_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hlk : l = k := by
    rcases scalar_cases (b x) with hb | hb
    · exact False.elim (hl (by simpa only [hb, zero_smul] using hx'))
    · simpa only [hb, one_smul] using hx'
  refine ⟨?_, hlk⟩
  apply LinearMap.ext
  intro y
  apply smul_left_injective (ZMod 2) hl
  have hy := LinearMap.congr_fun h y
  simpa only [LinearMap.smulRight_apply, ← hlk] using hy

/-- Ordered nonzero factors, with functional coordinate first. -/
abbrev BinaryRankOneFactors (X Y : Type*)
    [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y] :=
  {a : X →ₗ[ZMod 2] ZMod 2 // a ≠ 0} × {l : Y // l ≠ 0}

/-- The actual linear maps whose range has dimension one. -/
abbrev BinaryRankOneMaps (X Y : Type*)
    [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y] :=
  {T : X →ₗ[ZMod 2] Y // Module.finrank (ZMod 2) T.range = 1}

def binaryRankOneMap (p : BinaryRankOneFactors X Y) : BinaryRankOneMaps X Y :=
  ⟨p.1.val.smulRight p.2.val,
    (rank_one_iff_exists_smulRight _).mpr
      ⟨p.1.val, p.2.val, p.1.property, p.2.property, rfl⟩⟩

theorem binary_smulRight_injective :
    Function.Injective (binaryRankOneMap (X := X) (Y := Y)) := by
  intro p q h
  obtain ⟨ha, hl⟩ := binary_smulRight_unique p.1.property p.2.property
    (congrArg Subtype.val h)
  exact Prod.ext (Subtype.ext ha) (Subtype.ext hl)

theorem binary_smulRight_surjective :
    Function.Surjective (binaryRankOneMap (X := X) (Y := Y)) := by
  intro T
  obtain ⟨a, l, ha, hl, h⟩ := exists_smulRight_of_rank_one T.val T.property
  exact ⟨(⟨a, ha⟩, ⟨l, hl⟩), Subtype.ext h.symm⟩

/-- Bijection justifying uniform rank-one sampling by independent uniform
nonzero factors. The inverse uses choice only to select the proved unique pair. -/
noncomputable def binaryRankOneEquiv :
    BinaryRankOneFactors X Y ≃ BinaryRankOneMaps X Y :=
  Equiv.ofBijective binaryRankOneMap
    ⟨binary_smulRight_injective, binary_smulRight_surjective⟩

@[simp] theorem binaryRankOneEquiv_apply (p : BinaryRankOneFactors X Y) :
    (binaryRankOneEquiv p).val = p.1.val.smulRight p.2.val := rfl

end MaxCutGames.Inverse.MatrixChart

/-!
For a fixed nonzero binary functional, all updates with a prescribed image
form one affine coset of the image of its kernel. This is an exact fiber
equivalence, so it retains the multiplicities needed for uniform sampling.
-/

namespace MaxCutGames.Inverse.KMSBasisComparison

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]

/-- Vectors external to the starting image which give the same updated image. -/
abbrev FixedFunctionalNeighborFiber (X : E →ₗ[ZMod 2] F)
    (a : E →ₗ[ZMod 2] ZMod 2) (y₀ : F) :=
  {y : F // y ∉ X.range ∧
    (X + a.smulRight y).range = (X + a.smulRight y₀).range}

theorem add_image_not_mem_range (X : E →ₗ[ZMod 2] F)
    {y : F} (hy : y ∉ X.range) (z : E) : y + X z ∉ X.range := by
  intro h
  exact hy (by simpa using X.range.sub_mem h (X.mem_range_self z))

/-- Kernel translations of the perturbation vector preserve its image. -/
theorem range_update_add_kernel (X : E →ₗ[ZMod 2] F)
    (a : E →ₗ[ZMod 2] ZMod 2) (y : F) (z : a.ker) :
    (X + a.smulRight (y + X z)).range = (X + a.smulRight y).range := by
  have hz : a z = 0 := z.property
  have hforward (x : E) :
      (X + a.smulRight (y + X z)) x =
        (X + a.smulRight y) (x + a x • z) := by
    simp [hz, smul_add] ; abel
  have hbackward (x : E) :
      (X + a.smulRight y) x =
        (X + a.smulRight (y + X z)) (x - a x • z) := by
    simp [hz, smul_add]
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact ⟨x + a x • z, (hforward x).symm⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨x - a x • z, (hbackward x).symm⟩

/-- The affine parametrization of a fixed-functional image fiber. -/
def fixedFunctionalFiberMap (X : E →ₗ[ZMod 2] F)
    (a : E →ₗ[ZMod 2] ZMod 2) {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    a.ker → FixedFunctionalNeighborFiber X a y₀ :=
  fun z => ⟨y₀ + X z, add_image_not_mem_range X hy₀ z,
    range_update_add_kernel X a y₀ z⟩

theorem fixedFunctionalFiberMap_injective (X : E →ₗ[ZMod 2] F)
    (hX : Function.Injective X) (a : E →ₗ[ZMod 2] ZMod 2)
    {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    Function.Injective (fixedFunctionalFiberMap X a hy₀) := by
  intro z w h
  apply Subtype.ext
  apply hX
  exact add_left_cancel (congrArg Subtype.val h)

theorem fixedFunctionalFiberMap_surjective (X : E →ₗ[ZMod 2] F)
    (a : E →ₗ[ZMod 2] ZMod 2) (ha : a ≠ 0)
    {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    Function.Surjective (fixedFunctionalFiberMap X a hy₀) := by
  intro y
  obtain ⟨x, hx⟩ := a.surjective ha 1
  have hmem : X x + y.val ∈ (X + a.smulRight y₀).range := by
    exact y.property.2.le ⟨x, by simp [hx]⟩
  obtain ⟨t, ht⟩ := hmem
  have hbinary : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hat : a t = 1 := by
    rcases hbinary (a t) with hat | hat
    · have he : X t = X x + y.val := by simpa [hat] using ht
      have hy : y.val = X (t - x) := by
        rw [map_sub, he]
        abel
      exact False.elim (y.property.1 ⟨t - x, hy.symm⟩)
    · exact hat
  have hz : t - x ∈ a.ker := by
    change a (t - x) = 0
    simp [hat, hx]
  refine ⟨⟨t - x, hz⟩, ?_⟩
  apply Subtype.ext
  change y₀ + X (t - x) = y.val
  have he : X t + y₀ = X x + y.val := by simpa [hat] using ht
  calc
    y₀ + X (t - x) = (X t + y₀) - X x := by rw [map_sub]; abel
    _ = y.val := by rw [he]; abel

/-- Exact constant-multiplicity fiber over an updated subspace. -/
def fixedFunctionalNeighborFiberEquiv (X : E →ₗ[ZMod 2] F)
    (hX : Function.Injective X) (a : E →ₗ[ZMod 2] ZMod 2)
    (ha : a ≠ 0) {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    a.ker ≃ FixedFunctionalNeighborFiber X a y₀ :=
  Equiv.ofBijective (fixedFunctionalFiberMap X a hy₀)
    ⟨fixedFunctionalFiberMap_injective X hX a hy₀,
      fixedFunctionalFiberMap_surjective X a ha hy₀⟩

end
end MaxCutGames.Inverse.KMSBasisComparison

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_KMSBasisComparisonNeighborsFiberFunctional
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Binary linear functionals are determined by their kernels. The statement
includes the zero functional; no choice of a nonzero normalization is needed.
Injective linear images retain the same uniqueness property.
-/

namespace MaxCutGames.Inverse.KMSBasisComparison

variable {E F : Type*}
  [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]

/-- A binary functional is determined by its zero set. -/
theorem binary_functional_eq_of_ker_eq
    {a b : E →ₗ[ZMod 2] ZMod 2} (h : a.ker = b.ker) : a = b := by
  have scalar_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  apply LinearMap.ext
  intro x
  have hzero : a x = 0 ↔ b x = 0 := by
    change x ∈ a.ker ↔ x ∈ b.ker
    rw [h]
  rcases scalar_cases (a x) with ha | ha
  · exact ha.trans (hzero.mp ha).symm
  · rcases scalar_cases (b x) with hb | hb
    · exact False.elim (zero_ne_one ((hzero.mpr hb).symm.trans ha))
    · exact ha.trans hb.symm

/-- The image of a binary functional's kernel under an injective linear map
still determines that functional uniquely. -/
theorem binary_functional_eq_of_map_ker_eq
    (X : E →ₗ[ZMod 2] F) (hX : Function.Injective X)
    {a b : E →ₗ[ZMod 2] ZMod 2}
    (h : a.ker.map X = b.ker.map X) : a = b := by
  exact binary_functional_eq_of_ker_eq (Submodule.map_injective_of_injective hX h)

end MaxCutGames.Inverse.KMSBasisComparison

/-!
The complete pair fiber of the ordered-basis neighbor sampler. Equal updated
images determine the binary functional exactly. The remaining ambiguity is
the affine kernel coset, of cardinality `2 ^ (dim E - 1)`.
-/

namespace MaxCutGames.Inverse.KMSBasisComparison

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]

abbrev OutsideNeighborFactors (X : E →ₗ[ZMod 2] F) :=
  {a : E →ₗ[ZMod 2] ZMod 2 // a ≠ 0} × {y : F // y ∉ X.range}

abbrev OutsideNeighborPairFiber (X : E →ₗ[ZMod 2] F)
    (a : E →ₗ[ZMod 2] ZMod 2) (y : F) :=
  {p : OutsideNeighborFactors X //
    (rankOneUpdate X p.1.val p.2.val).range = (rankOneUpdate X a y).range}

/-- The common-parent intersection recovers the binary functional uniquely. -/
theorem functional_eq_of_update_range_eq (X : E →ₗ[ZMod 2] F)
    (hX : Function.Injective X) {a b : E →ₗ[ZMod 2] ZMod 2}
    {y z : F} (hy : y ∉ X.range) (hz : z ∉ X.range)
    (h : (rankOneUpdate X a y).range = (rankOneUpdate X b z).range) :
    a = b := by
  apply binary_functional_eq_of_map_ker_eq X hX
  rw [← range_inf_rankOneUpdate X a hy, ← range_inf_rankOneUpdate X b hz, h]

def fixedToPairFiber (X : E →ₗ[ZMod 2] F)
    (a : E →ₗ[ZMod 2] ZMod 2) (ha : a ≠ 0) (y₀ : F) :
    FixedFunctionalNeighborFiber X a y₀ → OutsideNeighborPairFiber X a y₀ :=
  fun y => ⟨(⟨a, ha⟩, ⟨y.val, y.property.1⟩), y.property.2⟩

theorem fixedToPairFiber_injective (X : E →ₗ[ZMod 2] F)
    (a : E →ₗ[ZMod 2] ZMod 2) (ha : a ≠ 0) (y₀ : F) :
    Function.Injective (fixedToPairFiber X a ha y₀) := by
  intro y z h
  apply Subtype.ext
  exact congrArg (fun p => p.val.2.val) h

theorem fixedToPairFiber_surjective (X : E →ₗ[ZMod 2] F)
    (hX : Function.Injective X) (a : E →ₗ[ZMod 2] ZMod 2)
    (ha : a ≠ 0) {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    Function.Surjective (fixedToPairFiber X a ha y₀) := by
  intro p
  have haeq : p.val.1.val = a :=
    functional_eq_of_update_range_eq X hX p.val.2.property hy₀ p.property
  have he : (X + a.smulRight p.val.2.val).range =
      (X + a.smulRight y₀).range := by
    simpa only [rankOneUpdate, haeq] using p.property
  refine ⟨⟨p.val.2.val, p.val.2.property, he⟩, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext haeq.symm
  · rfl

/-- Every pair in a fixed neighbor fiber has the same functional. -/
def fixedFunctionalEquivPairFiber (X : E →ₗ[ZMod 2] F)
    (hX : Function.Injective X) (a : E →ₗ[ZMod 2] ZMod 2)
    (ha : a ≠ 0) {y₀ : F} (hy₀ : y₀ ∉ X.range) :
    FixedFunctionalNeighborFiber X a y₀ ≃ OutsideNeighborPairFiber X a y₀ :=
  Equiv.ofBijective (fixedToPairFiber X a ha y₀)
    ⟨fixedToPairFiber_injective X a ha y₀,
      fixedToPairFiber_surjective X hX a ha hy₀⟩

end

/-!
# Constant ordered-basis fibers

An injective linear map with a fixed range is exactly an ordered basis of that
range. Choosing one such basis identifies this fiber with the automorphisms of
the domain. The generic finite-fiber lemma below proves uniformity, including
the complete normalization in the rational density identity.
-/

noncomputable section
open scoped BigOperators Classical

section UniformFibers

variable {X Y G : Type*}

/-- Trivializing equal-size fibers identifies the full sample space with a
product; the first coordinate remains the original quotient map. -/
def fiberProductEquiv (f : X → Y) (e : ∀ y, {x : X // f x = y} ≃ G) : X ≃ Y × G :=
  (Equiv.sigmaFiberEquiv f).symm.trans (Equiv.sigmaEquivProdOfEquiv e)

@[simp] theorem fiberProductEquiv_fst (f : X → Y)
    (e : ∀ y, {x : X // f x = y} ≃ G) (x : X) :
    (fiberProductEquiv f e x).1 = f x := rfl

end UniformFibers

section LinearFibers

variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]

/-- The actual fiber of injective maps over a specified range subspace. -/
def RangeFiber (L : Submodule K F) :=
  {X : E →ₗ[K] F // Function.Injective X ∧ LinearMap.range X = L}

/-- A range fiber is the set of linear equivalences onto that range. -/
def rangeFiberEquiv (L : Submodule K F) : RangeFiber (E := E) L ≃ (E ≃ₗ[K] L) where
  toFun X := LinearEquiv.ofBijective
    (X.val.codRestrict L (fun x =>
      X.property.2.le (LinearMap.mem_range_self X.val x)))
    ⟨fun _ _ h => X.property.1 (congrArg Subtype.val h), by
      intro y
      have hy : (y : F) ∈ LinearMap.range X.val := X.property.2.ge y.property
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩⟩
  invFun e := ⟨L.subtype.comp e.toLinearMap,
    (Submodule.subtype_injective L).comp e.injective, by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact (e x).property
      · intro hy
        obtain ⟨x, hx⟩ := e.surjective ⟨y, hy⟩
        exact ⟨x, congrArg Subtype.val hx⟩⟩
  left_inv X := by
    apply Subtype.ext
    ext x
    rfl
  right_inv e := by
    ext x
    rfl

/-- After choosing one basis of a subspace, its ordered-basis fiber is exactly
the domain's automorphism group. -/
def rangeFiberEquivAut {L : Submodule K F} (e : E ≃ₗ[K] L) :
    RangeFiber (E := E) L ≃ (E ≃ₗ[K] E) :=
  (rangeFiberEquiv L).trans
    { toFun := fun a => a.trans e.symm
      invFun := fun a => a.trans e
      left_inv := by intro a; ext x; simp
      right_inv := by intro a; ext x; simp }

end LinearFibers

end
end MaxCutGames.Inverse.KMSBasisComparison

namespace MaxCutGames.Inverse.KMSBasisComparison

noncomputable section
open scoped BigOperators Classical

variable {E F : Type*}
  [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]
  [FiniteDimensional (ZMod 2) E] [FiniteDimensional (ZMod 2) F]

/-- The full-neighbor sampler on its exact good-event factor space. -/
def outsideNeighborSample (X : E →ₗ[ZMod 2] F) (hX : Function.Injective X)
    (p : OutsideNeighborFactors X) : MatrixChart.GrassmannNeighbors X.range :=
  rankOneUpdateNeighbor X hX p.1.val p.1.property p.2.val p.2.property

omit [FiniteDimensional (ZMod 2) F] in
@[simp] theorem outsideNeighborSample_val (X : E →ₗ[ZMod 2] F)
    (hX : Function.Injective X) (p : OutsideNeighborFactors X) :
    (outsideNeighborSample X hX p).val =
      (rankOneUpdate X p.1.val p.2.val).range := rfl

end
end MaxCutGames.Inverse.KMSBasisComparison

/-!
Rank-one differences parametrize the actual Grassmann neighbors that remain
in the matrix chart. The equivalences retain the graph subspaces themselves,
so cardinalities and uniform sampling can be transported to the graph.
-/

namespace MaxCutGames.Inverse.MatrixChart

variable {X Y : Type*}
  [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]
  [FiniteDimensional (ZMod 2) X]

/-- Coordinate matrices adjacent to a fixed graph matrix. -/
abbrev BinaryChartNeighbors (T : X →ₗ[ZMod 2] Y) :=
  {U : X →ₗ[ZMod 2] Y //
    Module.finrank (ZMod 2) (T.graph ⊓ U.graph : Submodule (ZMod 2) (X × Y)) + 1 =
      Module.finrank (ZMod 2) X}

/-- The actual adjacent subspaces that lie in the graph chart. -/
abbrev BinaryGraphChartNeighbors (T : X →ₗ[ZMod 2] Y) :=
  {L : Submodule (ZMod 2) (X × Y) //
    (∃ U : X →ₗ[ZMod 2] Y, L = U.graph) ∧
      Module.finrank (ZMod 2) (T.graph ⊓ L : Submodule (ZMod 2) (X × Y)) + 1 =
        Module.finrank (ZMod 2) X}

/-- Difference from a fixed matrix is an exact bijection between rank-one
maps and adjacent matrices. Subtraction also makes this construction valid
without invoking characteristic-two simplification. -/
def rankOneEquivChartNeighbors (T : X →ₗ[ZMod 2] Y) :
    BinaryRankOneMaps X Y ≃ BinaryChartNeighbors T where
  toFun D := ⟨T - D.val, (adjacent_iff_rank_one T (T - D.val)).mpr (by
    have he : T - (T - D.val) = D.val := by
      exact sub_sub_cancel T _
    rw [he]
    exact D.property)⟩
  invFun U := ⟨T - U.val, (adjacent_iff_rank_one T U.val).mp U.property⟩
  left_inv D := by
    apply Subtype.ext
    change T - (T - D.val) = D.val
    exact sub_sub_cancel T _
  right_inv U := by
    apply Subtype.ext
    change T - (T - U.val) = U.val
    exact sub_sub_cancel T _

def graphChartNeighbor (T : X →ₗ[ZMod 2] Y)
    (U : BinaryChartNeighbors T) : BinaryGraphChartNeighbors T :=
  ⟨U.val.graph, ⟨U.val, rfl⟩, U.property⟩

omit [FiniteDimensional (ZMod 2) X] in
theorem graphChartNeighbor_injective (T : X →ₗ[ZMod 2] Y) :
    Function.Injective (graphChartNeighbor T) := by
  intro U V h
  apply Subtype.ext
  exact graph_injective (congrArg Subtype.val h)

omit [FiniteDimensional (ZMod 2) X] in
theorem graphChartNeighbor_surjective (T : X →ₗ[ZMod 2] Y) :
    Function.Surjective (graphChartNeighbor T) := by
  intro L
  obtain ⟨U, hU⟩ := L.property.1
  have h :
      Module.finrank (ZMod 2) (T.graph ⊓ U.graph : Submodule (ZMod 2) (X × Y)) + 1 =
        Module.finrank (ZMod 2) X := by
    rw [← hU]
    exact L.property.2
  exact ⟨⟨U, h⟩, Subtype.ext hU.symm⟩

noncomputable def chartNeighborsEquivGraphNeighbors (T : X →ₗ[ZMod 2] Y) :
    BinaryChartNeighbors T ≃ BinaryGraphChartNeighbors T :=
  Equiv.ofBijective (graphChartNeighbor T)
    ⟨graphChartNeighbor_injective T, graphChartNeighbor_surjective T⟩

/-- The complete nonzero-factor sampling equivalence, ending in actual
Grassmann subspaces in the chart. -/
noncomputable def binaryFactorsEquivGraphNeighbors (T : X →ₗ[ZMod 2] Y) :
    BinaryRankOneFactors X Y ≃ BinaryGraphChartNeighbors T :=
  binaryRankOneEquiv.trans
    ((rankOneEquivChartNeighbors T).trans (chartNeighborsEquivGraphNeighbors T))

@[simp] theorem binaryFactorsEquivGraphNeighbors_apply (T : X →ₗ[ZMod 2] Y)
    (p : BinaryRankOneFactors X Y) :
    (binaryFactorsEquivGraphNeighbors T p).val =
      (T - p.1.val.smulRight p.2.val).graph := rfl

end MaxCutGames.Inverse.MatrixChart

/-! Exact chart-to-Grassmann degree comparison over the binary field. -/

namespace MaxCutGames.Inverse.MatrixChart

open Module

variable {ell m : ℕ}

abbrev CoordinateMatrix (ell m : ℕ) :=
  (Fin ell → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)

end MaxCutGames.Inverse.MatrixChart

/-! Concrete matrix coordinates for the graph chart. In particular the upper
interval equations become `M q = t`, while the lower equations become `dᵀ M = sᵀ`.
The right-hand sides are retained; none of these slices is required to be linear.
-/

namespace MaxCutGames.Inverse.MatrixChart

open Matrix

variable {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]

abbrev matrixGraph (M : Matrix ι κ K) : Submodule K ((ι → K) × (κ → K)) :=
  M.vecMulLinear.graph

omit [Fintype κ] in
@[simp] theorem mem_matrixGraph (M : Matrix ι κ K) (x : ι → K) (y : κ → K) :
    (x, y) ∈ matrixGraph M ↔ y = M.transpose *ᵥ x := by
  rw [Matrix.mulVec_transpose]
  rfl

omit [Fintype κ] in
theorem matrixGraph_injective : Function.Injective (matrixGraph (K := K) (ι := ι) (κ := κ)) := by
  classical
  intro M N h
  have hh : M.vecMulLinear = N.vecMulLinear := graph_injective h
  exact (LinearMap.toMatrixRight' (R := K)).symm.injective hh

/-- A coordinate vector as a linear functional, for the standard dot pairing. -/
abbrev dotFunctional (x : ι → K) : (ι → K) →ₗ[K] K := dotProductBilin K K x

theorem dotFunctional_injective : Function.Injective (dotFunctional (K := K) (ι := ι)) := by
  intro x y h
  apply dotProduct_eq x y
  intro z
  exact congrArg (fun f : (ι → K) →ₗ[K] K => f z) h

omit [Fintype κ] in
/-- The graph always has the row dimension, including degenerate zero dimensions. -/
theorem finrank_matrixGraph (M : Matrix ι κ K) :
    Module.finrank K (matrixGraph M) = Fintype.card ι := by
  rw [finrank_graph]
  simp

end MaxCutGames.Inverse.MatrixChart

/-! Transport the product-coordinate chart into the actual Grassmann vertices
used by the KMS boundary. The transport is a proved ambient linear equivalence.
-/

namespace MaxCutGames.Inverse.MatrixChart

open Matrix

/-- Concatenate the two coordinate blocks of the chart ambient space. -/
def coordinateJoin (K : Type*) [Field K] (ell m : Nat) :
    ((Fin ell → K) × (Fin m → K)) ≃ₗ[K] (Fin (ell + m) → K) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin ell) (Fin m) K K).symm.trans
    (LinearEquiv.funCongrLeft K K finSumFinEquiv.symm)

end MaxCutGames.Inverse.MatrixChart

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_RowErasure
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MaxCutGames.Inverse.RowErasure

section

open scoped BigOperators

/-- One independent replacement value per matrix entry, not per row fiber. -/
def replaceOn {X Y : Type*} (B : X → Prop) (f replacement : X → Y) : X → Y := by
  classical
  exact fun x => if B x then replacement x else f x

/-- A matrix belongs to the erased union exactly when at least one row map
provides good advice there. -/
def goodUnion {A X : Type*} (good : A → X → Prop) (x : X) : Prop :=
  ∃ a, good a x

open scoped BigOperators

end

open scoped BigOperators Classical

end MaxCutGames.Inverse.RowErasure

/-!
`InversePrinciple` concerns an arbitrary table function, full uniform factor
sampling, and an affine intercept.
-/

/-!
Fixed-length descriptions for the row-erasure union bound. Row and column
equation lists are padded with zero equations. Targets retain both the linear
coefficient and the affine intercept. Thus the finite description count is
exactly `2^((2r+1)(ell+m))`, including descriptions with empty solution sets.
-/

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_MatrixChartKMSNeighbors
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact full-neighbor count in the KMS vertex representation. -/

namespace MaxCutGames.Inverse.MatrixChart

open Module

/-- Ambient linear equivalence transports the actual neighbor subspaces. -/
noncomputable def grassmannNeighborsMapEquiv
    {E F : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [AddCommGroup F] [Module (ZMod 2) F]
    (e : E ≃ₗ[ZMod 2] F) (L : Submodule (ZMod 2) E) :
    GrassmannNeighbors L ≃ GrassmannNeighbors (L.map e.toLinearMap) := by
  refine Equiv.subtypeEquiv (Submodule.orderIsoMapComap e).toEquiv ?_
  intro W
  change (_ ∧ _) ↔
    (finrank (ZMod 2) (W.map e.toLinearMap) =
        finrank (ZMod 2) (L.map e.toLinearMap) ∧
      finrank (ZMod 2) (L.map e.toLinearMap ⊓ W.map e.toLinearMap :
        Submodule (ZMod 2) F) + 1 =
        finrank (ZMod 2) (L.map e.toLinearMap))
  rw [← Submodule.map_inf e.toLinearMap e.injective]
  simp only [LinearEquiv.finrank_map_eq]

end MaxCutGames.Inverse.MatrixChart

/-! Local ordered-basis retention in the precise KMS vertex representation. -/

/-!
# Ordered-basis retention versus Grassmann retention

This is the sampling comparison in KMS Lemma 2.7. The original experiment
uses all functionals and all directions, including zero. Its good event
induces exactly the full Grassmann-neighbor law; all other outcomes contribute
at most their explicit probability mass. Initial bases push forward uniformly
to the original Grassmann set.
-/

/-! The proved KMS Grassmann expansion principle. Its quantitative analytic
input is the actual basis-invariant fourth-moment theorem, whose proof uses
fixed-character and fixed-point inductions. No expansion, inverse,
rank-level, or missing-moment premise occurs in this theorem. -/

/-! Every Grassmann interval has a chart description with exactly `dim A`
lower equations and `codim B` upper equations. This supplies the quantitative
row/column budget used when the expansion theorem selects an interval.
-/

/-! Extract actual vector-valued row/column data from an arbitrary interval.
The equation counts are the dimension/codimension of that interval, and no
homogeneity is imposed on the equation right-hand sides.
-/

namespace MaxCutGames.Inverse.MatrixChart

open Matrix

variable {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]

theorem dotFunctional_surjective :
    Function.Surjective (dotFunctional (K := K) (ι := ι)) := by
  classical
  intro f
  refine ⟨fun i => f (Pi.single i 1), ?_⟩
  apply (Pi.basisFun K ι).ext
  intro i
  change (fun j => f (Pi.single j 1)) ⬝ᵥ (Pi.basisFun K ι i) =
    f (Pi.basisFun K ι i)
  simp

end MaxCutGames.Inverse.MatrixChart

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_MatrixChartShortcode
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete interface consumed by the shortcode assembly: an arbitrary
KMS interval becomes a `Shortcode.Slice`, with exact equation counts.
-/

namespace MaxCutGames.Inverse.ShortcodeFromGrassmann

noncomputable section
open scoped Classical
open MatrixChart

/-- The exact self-loop mass when independent uniform binary factors include
zero. The overlap of the two zero events is subtracted once. -/
def zeroFactorMass (ell m : ℕ) : ℝ :=
  ((2 : ℝ) ^ ell)⁻¹ + ((2 : ℝ) ^ m)⁻¹ - ((2 : ℝ) ^ (ell + m))⁻¹

end
end MaxCutGames.Inverse.ShortcodeFromGrassmann

/-!
The exact sampling bridge from the vector factors in the shortcode test
to actual KMS Grassmann vertices. Every nonzero vector pair is sent to the
matrix `M + rankOne a l`, and this is a bijection onto the chart neighbors.
-/

/-!
The exact finite sampling conversion in the shortcode proof. Independent
nonzero binary vector factors parametrize chart neighbors bijectively; the full
Grassmann degree is twice the chart degree. These identities imply the exact
factor one half, including its averaging over a nonempty output fiber.
-/

/-!
Finite equality-fiber extraction for the Grassmann-to-matrix route.

These elementary results do not assume a shortcode inverse theorem.  They
separate the equality test, the retention of a nonempty output fiber, and the
subsequent removal of zero perturbation factors.  The dimension-uniform
Grassmann expansion theorem remains a separate mathematical obligation.
-/

namespace MaxCutGames.Inverse.EqualityFiber

noncomputable section

open scoped BigOperators Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]

def fiberMass (p : X → ℝ) (f : X → Y) (y : Y) : ℝ := by
  classical
  exact ∑ x, if f x = y then p x else 0

def fiberFlow (p : X → ℝ) (k : X → X → ℝ) (f : X → Y) (y : Y) : ℝ := by
  classical
  exact ∑ x, p x * ∑ x', k x x' * if f x = y ∧ f x' = y then 1 else 0

def equalityAcceptance (p : X → ℝ) (k : X → X → ℝ) (f : X → Y) : ℝ := by
  classical
  exact ∑ x, p x * ∑ x', k x x' * if f x = f x' then 1 else 0

end
end MaxCutGames.Inverse.EqualityFiber

/-! The actual uniform matrix test supplies a positive-mass output fiber with
large retention. The transition kernel averages independent full vectors,
including zero, exactly as in the shortcode theorem. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_PartnerFullSampling
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Full slot indices and the actual partner law

Uniform indices at all positions restrict to uniform indices on an active set.
The explicit restriction/complement equivalence proves this sampling fact. The
dependent partner average then equals sampling the active set followed by all
slot indices, including unused indices outside the active set. Finally, the
coordinatewise occurrence/slot draw is related to that same law.
-/

namespace MaxCutGames.Soundness.PartnerFullSampling

open scoped BigOperators

noncomputable section

def restrictIndices {P X : Type*} (J : Finset P) (indices : P → X) : ↥J → X :=
  fun j => indices j.val

/-- The values inside and outside a finite set reconstruct the full tuple. -/
def restrictionProductEquiv {P X : Type*} [DecidableEq P] (J : Finset P) :
    (P → X) ≃ ((↥J → X) × ({j : P // j ∉ J} → X)) where
  toFun indices := (restrictIndices J indices, fun j => indices j.val)
  invFun parts := fun j =>
    if hj : j ∈ J then parts.1 ⟨j, hj⟩ else parts.2 ⟨j, hj⟩
  left_inv indices := by
    funext j
    by_cases hj : j ∈ J <;> simp [restrictIndices, hj]
  right_inv parts := by
    apply Prod.ext
    · funext j
      simp [restrictIndices, j.property]
    · funext j
      simp [j.property]

end

end MaxCutGames.Soundness.PartnerFullSampling

/-!
Uniform raw advice coefficients obtained by discarding unused flat coordinates.
The intercept, both full columns at every position, and one singleton column at
every position are independent. For a fixed singleton set, selecting the used
columns gives exactly the uniform law on the dynamic raw coefficient type.
The identity holds for every joint test function, not merely for marginals.
-/

/-!
Local randomized advice responses are bounded using complete independently
sampled response tables. The verifier questions are the actual weighted
pushforward of the occurrence/position draw, with the complete private row
input retained on each side. No response sees the opposite private question.

The outer mask and coefficient tuple may be fixed before selecting either
response kernel. Revealing these data only strengthens this upper bound; they
contain no clean question or agreement event. The quantitative game-repetition
rate is a separate input to the final averaging lemma.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_RowErasureSelection
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Visible selection of a row-erasure witness. The selected description depends
only on the fixed table function, the row map, and the observed row value.
The full sampled matrix enters only the later event testing its membership in
the already selected slice. Classical choice fixes one witness once and for all;
proof irrelevance makes the choice independent of the goodness proof.
-/

/-!
Finite partition estimates for a selector fixed by visible data. The observation
fibers need not have equal sizes. Each local counting inequality is summed over
the actual fibers, then divided by the size of the hidden sample space.
-/

namespace MaxCutGames.Inverse.RowErasure.SelectionPartition

open scoped BigOperators Classical

variable {X S : Type*} [Fintype X] [Fintype S]

def fiber (observe : X → S) (s : S) : Finset X :=
  Finset.univ.filter fun x => observe x = s

def event (observe : X → S) (good : S → Prop) (chosen : S → Finset X)
    (x : X) : Prop :=
  good (observe x) ∧ x ∈ chosen (observe x)

def matchEvent (observe : X → S) (good : S → Prop) (chosen : S → Finset X)
    (hit : S → X → Prop) (x : X) : Prop :=
  event observe good chosen x ∧ hit (observe x) x

end MaxCutGames.Inverse.RowErasure.SelectionPartition

/-!
Exact mass of a nonempty column slice within a fixed row-advice fiber. A
column span of dimension at most `r` costs at most `ell*r` binary degrees of
freedom. All inhomogeneous values are represented by the chosen base point.
-/

/-!
Exact uniform parametrization of the concrete row/column slice.  The quotient
parameter describes every point, not only a lower-bounding subfamily.  Affine
targets retain the base-point contribution and their original intercept.
-/

/-!
The actual finite matrix column event occupies at least `2^(-ell*r)` of its
row-advice fiber. This connects the intrinsic quotient-map count to the padded
descriptions used by the selector, without assuming independent equations.
-/

/-!
The selected column event under the actual uniform matrix and row-map samples.
The witness is fixed by visible row advice before testing the hidden matrix.
Fiber sizes are retained explicitly; no uniformity of row values is assumed.
The final averaging lemmas also allow arbitrary nonnegative context weights.
-/

end

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_FramedLen
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace OptimalMaxCut.CounterMachine
open scoped BigOperators

def frame : List Bool → List Bool
  | [] => [false]
  | b::s => true::b::frame s

end OptimalMaxCut.CounterMachine

end

end OAI
end


