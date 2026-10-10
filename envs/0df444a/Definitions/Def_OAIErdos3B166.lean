-- Prove2me | Definitions.Def_OAIErdos3B166
-- name    : OAIErdos3B166
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T02:18:33.928857+00:00
-- url     : https://prove2.me/theorems/dc53964e-b3a4-49c6-a17c-a1e5f91de327
-- title:
--   OpenAI Erdős-3 split, definitions bundle 167 of 177
-- statement:
--   Definitions bundle 167 of 177 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B165`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 167 available.
--
--   Modules: `OAI.Erdos3.RationalFilteredNilmanifold.FiniteMarkedRationalFactorFreezing`, `OAI.Erdos3.RationalFilteredNilmanifold.MarkedRationalFactorFreezing`, `OAI.Erdos3.RationalFilteredNilmanifold.MarkedRationalFactorFreezing.finite_enumeration`, `OAI.Erdos3.RationalFilteredNilmanifold.MarkedRationalFactorFreezing.mono`, `OAI.Erdos3.RationalFilteredNilmanifold.MarkedSlowFactorFreezing`, `OAI.Erdos3.RationalFilteredNilmanifold.MarkedSlowFactorFreezing.mono_bound`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_marked_rational_factor_freezing`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_native_marked_rational_factor_freezing_bound`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_uniform_finite_marked_factor_parameters`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_uniform_marked_factor_parameters`, `OAI.Erdos3.VectorPolynomial.lowJetAmbientSites`, `OAI.Erdos3.VectorPolynomial.lowJetAmbientSites_coefficient`, `OAI.Erdos3.VectorPolynomial.lowJetAmbientSites_lipschitz`, `OAI.Erdos3.jointExceptionalSpatialSize_polynomial`, `OAI.Erdos3.jointExceptionalSpatialWidthBudget`, `OAI.Erdos3.jointIntegerPhysicalSite_normalized_dist_of_slope_sum`, `OAI.Erdos3.narrowSpatial_jointPhysicalSite_normalized_dist`, `OAI.Erdos3.narrowSpatial_jointPhysicalSite_normalized_dist_le_cell`, `OAI.Erdos3.narrow_sampler_residue_width_exp`, `_private.Estimates.AllocatedZeroLayerCommonSideInitializationUniform.0.OAI.Erdos3.VectorPolynomial.UniformScalarCommonBoxSource`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B157
import Definitions.Def_OAIErdos3B159
import Definitions.Def_OAIErdos3B167

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NarrowSpatialSiteVariation
namespace OAI

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators

theorem jointIntegerPhysicalSite_normalized_dist_of_slope_sum
    {K X : Type*} [Fintype K] [Fintype X]
    (N : X → ℕ) (T : K → ℝ) (a : X → ℤ) (frame : Option K × X → ℤ)
    (u v : K → ℤ) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hslope : ∀ x, (∑ k, |(frame (some k, x) : ℝ) / N x| * T k) ≤ C)
    (hcell : ∀ k, |(u k : ℝ) - (v k : ℝ)| ≤ T k * δ) :
    dist (fun x => (jointIntegerPhysicalSite u (a, frame) x : ℝ) / N x)
      (fun x => (jointIntegerPhysicalSite v (a, frame) x : ℝ) / N x) ≤ C * δ := by
  apply (dist_pi_le_iff (mul_nonneg hC hδ)).mpr
  intro x
  rw [Real.dist_eq]
  have hraw : (jointIntegerPhysicalSite u (a, frame) x : ℝ) -
      (jointIntegerPhysicalSite v (a, frame) x : ℝ) =
      ∑ k, ((u k : ℝ) - (v k : ℝ)) * (frame (some k, x) : ℝ) := by
    calc
      _ = (∑ k, (u k : ℝ) * (frame (some k, x) : ℝ)) -
          ∑ k, (v k : ℝ) * (frame (some k, x) : ℝ) := by
        simp only [jointIntegerPhysicalSite, Pi.add_apply, integerPhysicalSite,
          Int.cast_add, Int.cast_sum, Int.cast_mul]
        ring
      _ = _ := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
  have heq : (jointIntegerPhysicalSite u (a, frame) x : ℝ) / N x -
      (jointIntegerPhysicalSite v (a, frame) x : ℝ) / N x =
      ∑ k, ((u k : ℝ) - (v k : ℝ)) * ((frame (some k, x) : ℝ) / N x) := by
    rw [← sub_div, hraw, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [heq]
  calc
    _ ≤ ∑ k, |((u k : ℝ) - (v k : ℝ)) * ((frame (some k, x) : ℝ) / N x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, (T k * δ) * |(frame (some k, x) : ℝ) / N x| := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hcell k) (abs_nonneg _)
    _ = (∑ k, |(frame (some k, x) : ℝ) / N x| * T k) * δ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hslope x) hδ

theorem narrowSpatial_jointPhysicalSite_normalized_dist
    {G J X : Type*} [Fintype G] [Fintype J] [Fintype X]
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : ξ ≤ 1)
    (N : X → ℕ) (hN : ∀ x, 0 < N x)
    (T : G ⊕ J → ℝ) (hT : ∀ k, 0 ≤ T k) (hsum : ∑ k, T k ≤ W)
    (a : X → ℤ) (frame : Option (G ⊕ J) × X → ℤ)
    (hframe : frame ∈ rectangularWeightIndices 0 (narrowTrimmedSpatialWidths W τ ξ N) 1)
    (u v : G ⊕ J → ℤ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcell : ∀ k, |(u k : ℝ) - (v k : ℝ)| ≤ T k * δ) :
    dist (fun x => (jointIntegerPhysicalSite u (a, frame) x : ℝ) / N x)
      (fun x => (jointIntegerPhysicalSite v (a, frame) x : ℝ) / N x) ≤ τ * δ / 8 := by
  have h := jointIntegerPhysicalSite_normalized_dist_of_slope_sum N T a frame u v
    (by positivity : 0 ≤ τ / 8) hδ
    (narrowSpatial_frame_normalized_slope_sum hW hτ hξ N hN T hT hsum frame hframe) hcell
  simpa only [div_mul_eq_mul_div] using h

theorem narrowSpatial_jointPhysicalSite_normalized_dist_le_cell
    {G J X : Type*} [Fintype G] [Fintype J] [Fintype X]
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hξ : ξ ≤ 1)
    (N : X → ℕ) (hN : ∀ x, 0 < N x)
    (T : G ⊕ J → ℝ) (hT : ∀ k, 0 ≤ T k) (hsum : ∑ k, T k ≤ W)
    (a : X → ℤ) (frame : Option (G ⊕ J) × X → ℤ)
    (hframe : frame ∈ rectangularWeightIndices 0 (narrowTrimmedSpatialWidths W τ ξ N) 1)
    (u v : G ⊕ J → ℤ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcell : ∀ k, |(u k : ℝ) - (v k : ℝ)| ≤ T k * δ) :
    dist (fun x => (jointIntegerPhysicalSite u (a, frame) x : ℝ) / N x)
      (fun x => (jointIntegerPhysicalSite v (a, frame) x : ℝ) / N x) ≤ δ := by
  apply (narrowSpatial_jointPhysicalSite_normalized_dist hW hτ hξ N hN T hT hsum
    a frame hframe u v hδ hcell).trans
  have h := mul_le_mul_of_nonneg_right hτ1 hδ
  nlinarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowJetAmbientReconstruction
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

variable {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]

noncomputable def lowJetAmbientSites
    (z : JetAmbientIndex (fun j : Fin m => BoundedBooleanJet α (j.val + 1)) J → UnitAddCircle) :
    JetAmbientIndex (fun _ : Fin m => Finset α) J → UnitAddCircle :=
  fun t => ∑ r, boundedBooleanReconstructionMatrix α (t.1.val + 1) t.2.1 r • z ⟨t.1, r, t.2.2⟩

theorem lowJetAmbientSites_lipschitz :
    LipschitzWith (∑ j : Fin m, (Fintype.card (BoundedBooleanJet α (j.val + 1)) : ℝ≥0))
      (lowJetAmbientSites (α := α) (J := J)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  apply (dist_pi_le_iff (by positivity)).mpr
  rintro ⟨j, s, i⟩
  have hterm (r : BoundedBooleanJet α (j.val + 1)) :
      dist (boundedBooleanReconstructionMatrix α (j.val + 1) s r • z ⟨j,r,i⟩)
        (boundedBooleanReconstructionMatrix α (j.val + 1) s r • w ⟨j,r,i⟩) ≤ dist z w := by
    simp only [boundedBooleanReconstructionMatrix]
    split_ifs
    · simpa only [one_zsmul] using dist_le_pi_dist z w ⟨j,r,i⟩
    · simpa only [zero_zsmul, dist_self] using (dist_nonneg : 0 ≤ dist z w)
  have hc : (Fintype.card (BoundedBooleanJet α (j.val + 1)) : ℝ≥0) ≤
      ∑ j : Fin m, (Fintype.card (BoundedBooleanJet α (j.val + 1)) : ℝ≥0) :=
    Finset.single_le_sum
      (f := fun j : Fin m => (Fintype.card (BoundedBooleanJet α (j.val + 1)) : ℝ≥0))
      (fun _ _ => zero_le) (Finset.mem_univ j)
  calc
    _ ≤ ∑ _r : BoundedBooleanJet α (j.val + 1), dist z w :=
      (dist_sum_sum_le _ _ _).trans (Finset.sum_le_sum (fun r _ => hterm r))
    _ = (Fintype.card (BoundedBooleanJet α (j.val + 1)) : ℝ) * dist z w := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) dist_nonneg

theorem lowJetAmbientSites_coefficient {K : Type*} [Fintype K]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (D : Matrix α K ℤ)
    (x : CoefficientTorus (K := K) U) :
    lowJetAmbientSites (coveredJetAmbientTorus U 1
      (euclideanCoefficientJetMap U root D (fun j =>
        (Subtype.val : BoundedBooleanJet α (j.val + 1) → Finset α)) x)) =
      coefficientAmbientSiteEvaluation (integerAffineCube root D) (coefficientAmbientTorus U x) := by
  funext t
  rcases t with ⟨j, s, i⟩
  simp only [lowJetAmbientSites, coveredJetAmbientTorus_coefficient, Nat.cast_one, one_mul,
    coefficientAmbientSiteEvaluation, Finset.smul_sum, ← mul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Finset.sum_smul]
  congr 1
  have h := boundedBooleanReconstruction_siteMatrix root D (j.val + 1)
  rw [Matrix.mul_assoc, booleanJetExtractionMatrix_mul_boundedSite] at h
  exact congrFun (congrFun h s) e

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.JointExceptionalSpatialWidthBudget
namespace OAI

section

namespace Erdos3

theorem narrow_sampler_residue_width_exp {G J X : Type*} {P W τ ξ : ℝ}
    (hP : 0 ≤ P) (hW : 0 ≤ W) (hWP : W ≤ Real.exp P)
    (hτ : 0 < τ) (hτP : τ⁻¹ ≤ Real.exp P)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hξP : ξ⁻¹ ≤ Real.exp P)
    (N q : X → ℕ) (hq : ∀ i, 0 < q i) (hqP : ∀ i, (q i : ℝ) ≤ Real.exp P)
    (hsize : ∀ i, Real.exp (10*P+128) ≤ (N i : ℝ)) :
    ∀ z : Option (G ⊕ J) × X, Real.exp P ≤
      residueProfileWidth q (narrowTrimmedSpatialWidths W τ ξ N) z := by
  have hN (i) : 0 < N i := by exact_mod_cast (Real.exp_pos _).trans_le (hsize i)
  obtain ⟨hf, hfInv, hfWidth⟩ := narrow_sampler_width_bounds (G := G) (J := J)
    hP hW hWP hτ hτP hξ hξ1 hξP N hN
  intro z
  have hproduct : Real.exp P * (q z.2 : ℝ) /
      spatialWidthFraction (2*P) (ξ*τ) ≤ (N z.2 : ℝ) := by
    calc
      _ = Real.exp P * (q z.2 : ℝ) *
          (1 / spatialWidthFraction (2*P) (ξ*τ)) := by ring
      _ ≤ Real.exp P * Real.exp P * Real.exp (spatialSamplingBudget (2*P)) := by
        gcongr
        exact hqP z.2
      _ = Real.exp (10*P+128) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        unfold spatialSamplingBudget
        ring
      _ ≤ _ := hsize z.2
  apply (le_div_iff₀ (show (0 : ℝ) < q z.2 by exact_mod_cast hq z.2)).mpr
  exact ((div_le_iff₀ hf).mp hproduct).trans
    (by simpa only [mul_comm] using hfWidth z)

theorem jointExceptionalSpatialSize_polynomial {P : ℝ} (hP : 0 ≤ P) :
    10*P+128 ≤ (P+4)^4 := by
  nlinarith only [hP, pow_nonneg hP 2, pow_nonneg hP 3, pow_nonneg hP 4]

theorem jointExceptionalSpatialWidthBudget {G J X : Type*} {P W τ ξ logwide : ℝ}
    (hP : 0 ≤ P) (hW : 0 ≤ W) (hWP : W ≤ Real.exp P)
    (hτ : 0 < τ) (hτP : τ⁻¹ ≤ Real.exp P)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hξP : ξ⁻¹ ≤ Real.exp P)
    (N q : X → ℕ) (hq : ∀ i, 0 < q i) (hqP : ∀ i, (q i : ℝ) ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hlog : logwide ≤ P)
    (hsize : ∀ i, Real.exp ((P+4)^4) ≤ (N i : ℝ))
    (e : Fin 2 × X ↪ G) :
    (∀ z : Option (G ⊕ J) × X, 8*(probabilityProfileLipschitz : ℝ) ≤
      residueProfileWidth q (narrowTrimmedSpatialWidths W τ ξ N) z) ∧
    ∀ i, Real.exp logwide ≤ spatialMatrixIndexWidth e q
      (narrowTrimmedSpatialWidths (J := J) W τ ξ N) i := by
  have hsize' (i) : Real.exp (10*P+128) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr (jointExceptionalSpatialSize_polynomial hP)).trans (hsize i)
  refine ⟨narrow_sampler_residue_scale hP hW hWP hτ hτP hξ hξ1 hξP
    N q hq hqP hprofile hsize', ?_⟩
  intro i
  exact (Real.exp_le_exp.mpr hlog).trans
    (narrow_sampler_residue_width_exp hP hW hWP hτ hτP hξ hξ1 hξP
      N q hq hqP hsize' (spatialMatrixBlockSlot e i))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedZeroLayerCommonSideInitializationUniform
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical NNReal

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin 0 → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin 0 → ℝ}
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]


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

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformFiniteMarkedFactorParameters
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

def MarkedRationalFactorFreezing
    {σ κ L T : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T) (φ : L →ₗ⁅ℚ⁆ T)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
    (w : σ → ℕ) (S : T →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j)
    (l : ℕ) (B : ℝ) : Prop :=
  ∃ M m : ℕ, 0 < M ∧ 0 < m ∧ (M : ℝ) ≤ B ∧ (m : ℝ) ≤ B ∧
    ∀ (R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
      (RF : (F.realification.adaptedPolynomialFiltration w).Group),
      D.filtration.PolynomialRationalGrid D.basis w l R →
      F.PolynomialRationalGrid c w l RF →
      D.filtration.realPolynomialGroupMap F φ hφ w R = RF →
      ∃ r : (σ → ZMod M) → D.RealGroup,
        (∀ a, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := F.lowerCentralSeries_eq_bot) φ (r a) = 1 ∧
          (∀ i, |(D.basis.baseChange ℝ).repr (r a).coord i| ≤ B) ∧
          (D.basis.baseChange ℝ).equivFun (r a).coord ∈ realDenominatorGrid m) ∧
        ∀ x : σ → ℤ, ∃ γ ∈ D.realLattice,
          D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ))
              ((D.filtration.filteredRealPolynomialSection F w S hS RF)⁻¹ * R) =
            r (fun j => (x j : ZMod M)) * γ ∧
          D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) R =
            D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ))
                (D.filtration.filteredRealPolynomialSection F w S hS RF) *
              r (fun j => (x j : ZMod M)) * γ

theorem exists_native_marked_rational_factor_freezing_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ κ L T : Type*} [Fintype σ] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d t : ℕ} (D : RationalFilteredNilmanifold L s d)
      (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T)
      (ω : Fin d → ℕ)
      (_hlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (φ : L →ₗ⁅ℚ⁆ T) (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
      (w : σ → ℕ), (∀ i, 0 < w i) → ∀ p : ℝ,
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p) →
      ∀ (S : T →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j),
      Function.RightInverse S φ →
      (∀ i j, RationalHeightLE (D.basis.repr (S (c j)) i)
        (rationalKernelHeight (Fintype.card κ) ⌈Real.exp p⌉₊)) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      D.MarkedRationalFactorFreezing F c φ hφ w S hS l (Real.exp ((p + C) ^ C)) := by
  obtain ⟨a, _, hgrid⟩ := NilpotentLieFiltration.exists_marked_kernel_rational_grid_bound s
  obtain ⟨b, _, hreps⟩ := exists_native_marked_kernel_residue_representatives s
  let U : Polynomial ℕ := (Polynomial.X + 3) ^ 11
  let V : Polynomial ℕ := (U + Polynomial.C a) ^ a + U
  let P : Polynomial ℕ := (V + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ κ L T _ _ _ _ _ _ _ _ _ _ d t D F c ω hlayers φ hφ w hw p hp hD hσ hκ hφb
    S hS hright hSb l hl hlp
  classical
  let p0 := p + 1
  let u := (p0 + 2) ^ 11
  let v := (u + a) ^ a + u
  let H := ⌈Real.exp p⌉₊
  have hp0 : 0 ≤ p0 := by dsimp [p0]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpu : p ≤ u := (show p ≤ p0 by dsimp [p0]; linarith).trans
    (le_power_budget hp0 (by decide : 1 ≤ 11))
  have huv : u ≤ v := le_add_of_nonneg_left (by positivity)
  have hpv : p ≤ v := hpu.trans huv
  have hv : 0 ≤ v := hu.trans huv
  have hd0 : (Fintype.card (Fin d) : ℝ) ≤ p0 := by
    simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p0 by dsimp [p0]; linarith)
  have hκ0 : (Fintype.card κ : ℝ) ≤ p0 := hκ.trans (by dsimp [p0]; linarith)
  have hH : (H : ℝ) ≤ Real.exp p0 := ceil_exp_le_exp_add_one hp
  have hφH : ∀ i j, RationalHeightLE (c.repr (φ (D.basis j)) i) H :=
    fun i j => rationalHeightLE_ceil_exp (hφb i j)
  have hden : ((matrixDenominator (LinearMap.toMatrix c D.basis S) * l : ℕ) : ℝ) ≤
      Real.exp u := by
    apply filtered_section_single_denominator_le_exp
      (LinearMap.toMatrix D.basis c φ.toLinearMap) (LinearMap.toMatrix c D.basis S) l
      hp0 hd0 hκ0 hH
    · intro i j
      rw [LinearMap.toMatrix_apply]
      exact hφH i j
    · simpa only [LinearMap.toMatrix_apply] using hSb
    · exact hlp.trans (Real.exp_le_exp.mpr (by dsimp [p0]; linarith))
  have hHpu : (H : ℝ) ≤ Real.exp u := hH.trans
    (Real.exp_le_exp.mpr (le_power_budget hp0 (by decide : 1 ≤ 11)))
  obtain ⟨q, hq, hqb, _, hqgrid⟩ := hgrid D.filtration F D.basis c ω hlayers w hw H u
    (one_le_ceil_exp p) hu (by simpa only [Fintype.card_fin] using hD.1.trans hpu)
    (hσ.trans hpu) hHpu (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
    S hS l hl hden
  have hqv : (q : ℝ) ≤ Real.exp v := hqb.trans
    (Real.exp_le_exp.mpr (le_add_of_nonneg_right hu))
  obtain ⟨M, m, hM, hm, hMb, hmb, hfreeze⟩ := hreps D F c φ w hw v hv
    (GeometryComplexityLE.mono D hD hpv) (hσ.trans hpv) (hκ.trans hpv)
    (fun i j => (hφb i j).trans hpv) q hq hqv
  have hb : (v + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, V, U, v, u, p0, Polynomial.eval₂_pow, add_assoc,
      show (1 : ℝ) + 2 = 3 by norm_num] using hbudget p hp
  refine ⟨M, m, hM, hm, hMb.trans (Real.exp_le_exp.mpr hb),
    hmb.trans (Real.exp_le_exp.mpr hb), ?_⟩
  intro R RF hR hRF hmark
  let KR := (D.filtration.filteredRealPolynomialSection F w S hS RF)⁻¹ * R
  have hKR : D.filtration.realPolynomialGroupMap F φ hφ w KR = 1 := by
    dsimp only [KR]
    rw [map_mul, map_inv, hmark,
      D.filtration.realPolynomialGroupMap_filteredSection F w φ hφ S hS hright RF,
      inv_mul_cancel]
  have hpoint (x : σ → ℤ) : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := F.lowerCentralSeries_eq_bot) φ
      (D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) KR) = 1 := by
    rw [← D.filtration.realPolynomialGroupMap_value F φ hφ w, hKR, map_one]
  obtain ⟨r, hr, hfac⟩ := hfreeze KR (hqgrid R RF hR hRF) hpoint
  refine ⟨r, fun z => ⟨(hr z).1, fun i => ((hr z).2.1 i).trans
    (Real.exp_le_exp.mpr hb), (hr z).2.2⟩, ?_⟩
  intro x
  obtain ⟨γ, hγ, heq⟩ := hfac x
  refine ⟨γ, hγ, heq, ?_⟩
  have heq' := heq
  dsimp only [KR] at heq'
  rw [map_mul, map_inv] at heq'
  calc
    _ = D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ))
        (D.filtration.filteredRealPolynomialSection F w S hS RF) *
        (r (fun j => (x j : ZMod M)) * γ) := by
      rw [← heq']
      group
    _ = _ := (mul_assoc _ _ _).symm

theorem exists_native_marked_rational_factor_freezing (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ κ L T : Type*} [Fintype σ] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d t : ℕ} (D : RationalFilteredNilmanifold L s d)
      (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T)
      (ω : Fin d → ℕ)
      (_hDlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (τ : κ → ℕ) (_hFlayers : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
      (φ : L →ₗ⁅ℚ⁆ T) (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j),
      (∀ j, ∀ y ∈ F.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
      ∀ w : σ → ℕ, (∀ i, 0 < w i) → ∀ p : ℝ,
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p) →
      ∃ (S : T →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j),
        Function.RightInverse S φ ∧
        (∀ i j, RationalHeightLE (D.basis.repr (S (c j)) i)
          (rationalKernelHeight (Fintype.card κ) ⌈Real.exp p⌉₊)) ∧
        ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
          D.MarkedRationalFactorFreezing F c φ hφ w S hS l (Real.exp ((p + C) ^ C)) := by
  obtain ⟨C, hC, hfreeze⟩ := exists_native_marked_rational_factor_freezing_bound s
  refine ⟨C, hC, ?_⟩
  intro σ κ L T _ _ _ _ _ _ _ _ _ _ d t D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  obtain ⟨S, hright, hS, hSb⟩ := D.filtration.exists_bounded_filtered_section F D.basis ω
    hDlayers c τ hFlayers φ.toLinearMap hsurj (one_le_ceil_exp p)
    (fun i j => rationalHeightLE_ceil_exp (hφb i j))
  exact ⟨S, hS, hright, hSb,
    hfreeze D F c ω hDlayers φ hφ w hw p hp hD hσ hκ hφb S hS hright hSb⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem MarkedRationalFactorFreezing.finite_enumeration
    {σ κ L T : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T) (φ : L →ₗ⁅ℚ⁆ T)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
    (w : σ → ℕ) (S : T →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j)
    (l : ℕ) {B p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hB : B ≤ Real.exp p)
    (hfreeze : D.MarkedRationalFactorFreezing F c φ hφ w S hS l B) :
    ∃ M m n : ℕ, 0 < M ∧ 0 < m ∧ 0 < n ∧
      (M : ℝ) ≤ B ∧ (m : ℝ) ≤ B ∧ (n : ℝ) ≤ Real.exp ((p + 2) ^ 3) ∧
      ∃ center : Fin n → D.RealGroup,
        (∀ a, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := F.lowerCentralSeries_eq_bot) φ (center a) = 1 ∧
          (∀ i, |(D.basis.baseChange ℝ).repr (center a).coord i| ≤ B) ∧
          (D.basis.baseChange ℝ).equivFun (center a).coord ∈ realDenominatorGrid m) ∧
        ∀ (R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
          (RF : (F.realification.adaptedPolynomialFiltration w).Group),
          D.filtration.PolynomialRationalGrid D.basis w l R →
          F.PolynomialRationalGrid c w l RF →
          D.filtration.realPolynomialGroupMap F φ hφ w R = RF →
          ∃ label : (σ → ZMod M) → Fin n,
            ∀ x : σ → ℤ, ∃ γ ∈ D.realLattice,
              D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ))
                  ((D.filtration.filteredRealPolynomialSection F w S hS RF)⁻¹ * R) =
                center (label (fun j => (x j : ZMod M))) * γ ∧
              D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) R =
                D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ))
                    (D.filtration.filteredRealPolynomialSection F w S hS RF) *
                  center (label (fun j => (x j : ZMod M))) * γ := by
  classical
  obtain ⟨M, m, hM, hm, hMb, hmb, hfactor⟩ := hfreeze
  have hB0 : 0 ≤ B := (Nat.cast_nonneg m).trans hmb
  obtain ⟨n, hn, hnb, center, hcenters, hcover⟩ :=
    exists_bounded_kernel_grid_enumeration_exp (D.basis.baseChange ℝ)
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) φ) m hm hp hB0
      (by simpa only [Fintype.card_fin] using hd) (hmb.trans hB) hB
  refine ⟨M, m, n, hM, hm, hn, hMb, hmb, hnb, center, hcenters, ?_⟩
  intro R RF hR hRF hmark
  obtain ⟨r, hr, hfac⟩ := hfactor R RF hR hRF hmark
  choose label hlabel using fun a => hcover (r a) (hr a).1 (hr a).2.1 (hr a).2.2
  refine ⟨label, ?_⟩
  intro x
  obtain ⟨γ, hγ, hKR, hRfac⟩ := hfac x
  refine ⟨γ, hγ, ?_, ?_⟩
  · simpa only [hlabel] using hKR
  · simpa only [hlabel] using hRfac

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module

theorem MarkedRationalFactorFreezing.mono
    {σ κ L T : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {F : NilpotentLieFiltration T t} {c : Basis κ ℚ T} {φ : L →ₗ⁅ℚ⁆ T}
    {hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j}
    {w : σ → ℕ} {S : T →ₗ[ℚ] L}
    {hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j}
    {l : ℕ} {B B' : ℝ}
    (h : D.MarkedRationalFactorFreezing F c φ hφ w S hS l B) (hBB' : B ≤ B') :
    D.MarkedRationalFactorFreezing F c φ hφ w S hS l B' := by
  obtain ⟨M, m, hM, hm, hMB, hmB, hfreeze⟩ := h
  refine ⟨M, m, hM, hm, hMB.trans hBB', hmB.trans hBB', ?_⟩
  intro R RF hR hRF hmark
  obtain ⟨r, hr, hfac⟩ := hfreeze R RF hR hRF hmark
  exact ⟨r, fun a => ⟨(hr a).1, fun i => ((hr a).2.1 i).trans hBB', (hr a).2.2⟩,
    hfac⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

def MarkedSlowFactorFreezing
    {σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T) (φ : L →ₗ⁅ℚ⁆ T)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
    (w : σ → ℕ) (S : T →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j)
    (Tbox : σ → ℝ) (A ε B : ℝ) : Prop :=
  letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  ∃ N Q : ℕ, 0 < N ∧ 0 < Q ∧
    (Fintype.card (Fin d → Fin (N + 1)) : ℝ) ≤ B ∧
    (Fintype.card (σ → Fin (Q + 1)) : ℝ) ≤ B ∧
    ∃ center : (Fin d → Fin (N + 1)) → D.RealGroup,
      (∀ j, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) φ (center j) = 1) ∧
      (∀ j i, |(D.basis.baseChange ℝ).repr (center j).coord i| ≤ B) ∧
      ∀ (E : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
        (EF : (F.realification.adaptedPolynomialFiltration w).Group),
        D.filtration.PolynomialSlowBound D.basis w Tbox A E →
        F.PolynomialSlowBound c w Tbox A EF →
        D.filtration.realPolynomialGroupMap F φ hφ w E = EF →
        ∃ label : (σ → Fin (Q + 1)) → (Fin d → Fin (N + 1)),
          ∀ j (v : σ → ℝ), (∀ i, |v i| ≤ Tbox i) →
            (∀ i, |v i - normalizedRealBoxGrid Tbox Q j i| ≤ Tbox i * (2 / Q)) →
            dist (D.filtration.adaptedPolynomialRealValueHom w v
              (E * (D.filtration.filteredRealPolynomialSection F w S hS EF)⁻¹))
              (center (label j)) ≤ ε

theorem exists_uniform_marked_factor_parameters (s a u : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d t : ℕ} (D : RationalFilteredNilmanifold L s d)
      (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T)
      (ω : Fin d → ℕ)
      (_hDlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (τ : κ → ℕ) (_hFlayers : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
      (φ : L →ₗ⁅ℚ⁆ T) (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j),
      (∀ j, ∀ y ∈ F.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
      ∀ w : σ → ℕ, (∀ i, 0 < w i) → ∀ p : ℝ,
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p) →
      ∃ (S : T →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j),
        Function.RightInverse S φ ∧
        (∀ i j, RationalHeightLE (D.basis.repr (S (c j)) i)
          (rationalKernelHeight (Fintype.card κ) ⌈Real.exp p⌉₊)) ∧
        ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
          ∀ Tbox : σ → ℝ, (∀ i, 0 < Tbox i) →
            D.MarkedRationalFactorFreezing F c φ hφ w S hS l (Real.exp ((p + C) ^ C)) ∧
            D.MarkedSlowFactorFreezing F c φ hφ w S hS Tbox
              (Real.exp ((p + 2) ^ a)) (Real.exp (-((p + 2) ^ u)))
              (Real.exp ((p + C) ^ C)) := by
  obtain ⟨A, _, hrat⟩ := exists_native_marked_rational_factor_freezing s
  obtain ⟨B, _, hslow⟩ := NilpotentLieFiltration.exists_actual_marked_slow_kernel_cells s (max a 7) u
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C A) ^ A +
    (Polynomial.X + 1 + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ κ L T _ _ _ _ _ _ _ _ _ _ _ d t D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  classical
  obtain ⟨S, hS, hright, hSb, hratS⟩ := hrat D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  have hsum : (p + A) ^ A + (p + 1 + B) ^ B ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  have hA : (p + A) ^ A ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (p + 1 + B) ^ B)).trans hsum
  have hB : (p + 1 + B) ^ B ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (by positivity : 0 ≤ (p + A) ^ A)).trans hsum
  refine ⟨S, hS, hright, hSb, ?_⟩
  intro l hl hlp Tbox hT
  refine ⟨(hratS l hl hlp).mono (Real.exp_le_exp.mpr hA), ?_⟩
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let H := ⌈Real.exp p⌉₊
  have hp1 : 0 ≤ p + 1 := by positivity
  have hp_le : p ≤ p + 1 := by linarith
  have hH : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hK := rationalKernelHeight_le_budget (Fintype.card κ) H hp1 (hκ.trans hp_le) hH
  have hentry : ∀ i j, |(D.basis.repr (S (c j)) i : ℝ)| ≤
      Real.exp (((p + 1) + 2) ^ max a 7) := by
    intro i j
    apply ((hSb i j).abs_real_le.trans hK).trans
    apply Real.exp_le_exp.mpr
    exact pow_le_pow_right₀ (by linarith : 1 ≤ (p + 1) + 2) (le_max_right _ _)
  obtain ⟨N, Q, hN, hQ, hNcard, hQcard, center, hmark, hcap, hfreeze⟩ :=
    hslow D.filtration F D.basis c ω hDlayers w hw φ hφ S hS hright H (p + 1)
      (one_le_ceil_exp p) hp1 (by simpa only [Fintype.card_fin] using hD.1.trans hp_le)
      (hκ.trans hp_le) (hσ.trans hp_le) hH
      (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)) hentry Tbox hT
  refine ⟨N, Q, hN, hQ, hNcard.trans (Real.exp_le_exp.mpr hB),
    hQcard.trans (Real.exp_le_exp.mpr hB), center, hmark,
    fun j i => (hcap j i).trans (Real.exp_le_exp.mpr hB), ?_⟩
  intro E EF hE hEF hproj
  have hinput : Real.exp ((p + 2) ^ a) ≤ Real.exp (((p + 1) + 2) ^ max a 7) := by
    apply Real.exp_le_exp.mpr
    exact (pow_le_pow_left₀ (by linarith : 0 ≤ p + 2)
      (by linarith : p + 2 ≤ (p + 1) + 2) a).trans
      (pow_le_pow_right₀ (by linarith : 1 ≤ (p + 1) + 2) (le_max_left _ _))
  obtain ⟨label, hlabel⟩ := hfreeze E EF
    (D.filtration.polynomialSlowBound_mono D.basis w Tbox hT hinput E hE)
    (F.polynomialSlowBound_mono c w Tbox hT hinput EF hEF) hproj
  refine ⟨label, ?_⟩
  intro j v hv hvj
  apply (hlabel j v hv hvj).trans
  apply Real.exp_le_exp.mpr
  exact neg_le_neg (pow_le_pow_left₀ (by linarith : 0 ≤ p + 2)
    (by linarith : p + 2 ≤ (p + 1) + 2) u)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

def FiniteMarkedRationalFactorFreezing
    {σ κ L T : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T) (φ : L →ₗ⁅ℚ⁆ T)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
    (w : σ → ℕ) (S : T →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j)
    (l : ℕ) (B : ℝ) : Prop :=
  ∃ M m n : ℕ, 0 < M ∧ 0 < m ∧ 0 < n ∧
    (M : ℝ) ≤ B ∧ (m : ℝ) ≤ B ∧ (n : ℝ) ≤ B ∧
    ∃ center : Fin n → D.RealGroup,
      (∀ a, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := F.lowerCentralSeries_eq_bot) φ (center a) = 1 ∧
        (∀ i, |(D.basis.baseChange ℝ).repr (center a).coord i| ≤ B) ∧
        (D.basis.baseChange ℝ).equivFun (center a).coord ∈ realDenominatorGrid m) ∧
      ∀ (R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
        (RF : (F.realification.adaptedPolynomialFiltration w).Group),
        D.filtration.PolynomialRationalGrid D.basis w l R →
        F.PolynomialRationalGrid c w l RF →
        D.filtration.realPolynomialGroupMap F φ hφ w R = RF →
        ∃ label : (σ → ZMod M) → Fin n,
          ∀ x : σ → ℤ, ∃ γ ∈ D.realLattice,
            D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ))
                ((D.filtration.filteredRealPolynomialSection F w S hS RF)⁻¹ * R) =
              center (label (fun j => (x j : ZMod M))) * γ ∧
            D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) R =
              D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ))
                  (D.filtration.filteredRealPolynomialSection F w S hS RF) *
                center (label (fun j => (x j : ZMod M))) * γ

theorem MarkedSlowFactorFreezing.mono_bound
    {σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {F : NilpotentLieFiltration T t} {c : Basis κ ℚ T} {φ : L →ₗ⁅ℚ⁆ T}
    {hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j}
    {w : σ → ℕ} {S : T →ₗ[ℚ] L}
    {hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j}
    {Tbox : σ → ℝ} {A ε B B' : ℝ}
    (h : D.MarkedSlowFactorFreezing F c φ hφ w S hS Tbox A ε B) (hBB' : B ≤ B') :
    D.MarkedSlowFactorFreezing F c φ hφ w S hS Tbox A ε B' := by
  obtain ⟨N, Q, hN, hQ, hNc, hQc, center, hmark, hcap, hfreeze⟩ := h
  exact ⟨N, Q, hN, hQ, hNc.trans hBB', hQc.trans hBB', center, hmark,
    fun j i => (hcap j i).trans hBB', hfreeze⟩

theorem exists_uniform_finite_marked_factor_parameters (s a u : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d t : ℕ} (D : RationalFilteredNilmanifold L s d)
      (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T)
      (ω : Fin d → ℕ)
      (_hDlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (τ : κ → ℕ) (_hFlayers : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
      (φ : L →ₗ⁅ℚ⁆ T) (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j),
      (∀ j, ∀ y ∈ F.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
      ∀ w : σ → ℕ, (∀ i, 0 < w i) → ∀ p : ℝ,
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p) →
      ∃ (S : T →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j),
        Function.RightInverse S φ ∧
        (∀ i j, RationalHeightLE (D.basis.repr (S (c j)) i)
          (rationalKernelHeight (Fintype.card κ) ⌈Real.exp p⌉₊)) ∧
        ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
          ∀ Tbox : σ → ℝ, (∀ i, 0 < Tbox i) →
            D.FiniteMarkedRationalFactorFreezing F c φ hφ w S hS l (Real.exp ((p + C) ^ C)) ∧
            D.MarkedSlowFactorFreezing F c φ hφ w S hS Tbox
              (Real.exp ((p + 2) ^ a)) (Real.exp (-((p + 2) ^ u)))
              (Real.exp ((p + C) ^ C)) := by
  obtain ⟨A, hA, hparams⟩ := exists_uniform_marked_factor_parameters s a u
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let P := U + (X + U + 2) ^ 3
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ κ L T _ _ _ _ _ _ _ _ _ _ _ d t D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  obtain ⟨S, hS, hright, hSb, hboth⟩ := hparams D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  refine ⟨S, hS, hright, hSb, ?_⟩
  intro l hl hlp Tbox hT
  obtain ⟨hrat, hslow⟩ := hboth l hl hlp Tbox hT
  let q := p + (p + A) ^ A
  have hAp : 0 ≤ (p + A) ^ A := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := le_add_of_nonneg_right hAp
  have hAq : (p + A) ^ A ≤ q := le_add_of_nonneg_left hp
  have hbud : (p + A) ^ A + (q + 2) ^ 3 ≤ (p + C) ^ C := by
    simpa [P, U, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hAcap : (p + A) ^ A ≤ (p + C) ^ C := by
    have : 0 ≤ (q + 2) ^ 3 := by positivity
    linarith
  have hqcap : (q + 2) ^ 3 ≤ (p + C) ^ C := by linarith
  have hBB : Real.exp ((p + A) ^ A) ≤ Real.exp ((p + C) ^ C) := Real.exp_le_exp.mpr hAcap
  refine ⟨?_, hslow.mono_bound hBB⟩
  obtain ⟨M, m, n, hM, hm, hn, hMb, hmb, hnb, center, hcenter, hfac⟩ :=
    MarkedRationalFactorFreezing.finite_enumeration D F c φ hφ w S hS l hq
      (hD.1.trans hpq) (Real.exp_le_exp.mpr hAq) hrat
  exact ⟨M, m, n, hM, hm, hn, hMb.trans hBB, hmb.trans hBB,
    hnb.trans (Real.exp_le_exp.mpr hqcap), center,
    fun j => ⟨(hcenter j).1, fun i => ((hcenter j).2.1 i).trans hBB, (hcenter j).2.2⟩, hfac⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI

end


