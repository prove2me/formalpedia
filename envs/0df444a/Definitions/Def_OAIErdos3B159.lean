-- Prove2me | Definitions.Def_OAIErdos3B159
-- name    : OAIErdos3B159
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T18:47:29.59467+00:00
-- url     : https://prove2.me/theorems/c520f303-3bc9-4d49-84e2-b789fe167718
-- title:
--   OpenAI Erdős-3 split, definitions bundle 160 of 161
-- statement:
--   Definitions bundle 160 of 161 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B158`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 160 available.
--
--   Modules: `OAI.Erdos3.BooleanCubeKernel.narrowTrimmedSpatialWidths_fit`, `OAI.Erdos3.BooleanCubeKernel.narrow_jointIntegerPhysicalSite_mem_box`, `OAI.Erdos3.BooleanCubeKernel.physicalSiteWidth_mono`, `OAI.Erdos3.BooleanCubeKernel.selectedResidue_positive_density_projection_error`, `OAI.Erdos3.VectorPolynomial.allocatedEarlyCoarseInput`, `OAI.Erdos3.VectorPolynomial.allocatedEarlyCoarseInput_bounds`, `OAI.Erdos3.VectorPolynomial.allocatedEarlyRecenteredMesh`, `OAI.Erdos3.VectorPolynomial.allocatedEarlyRecenteredMesh_partition_budget`, `OAI.Erdos3.VectorPolynomial.allocatedRecenteredCoarseMesh`, `OAI.Erdos3.VectorPolynomial.allocatedRecenteredProfileMass`, `OAI.Erdos3.VectorPolynomial.allocatedRecenteredProfileTerm`, `OAI.Erdos3.VectorPolynomial.allocatedResidueSpatialKernel`, `OAI.Erdos3.VectorPolynomial.allocatedSpatialCoefficientCap`, `OAI.Erdos3.VectorPolynomial.allocatedSpatialExpansionCoefficient`, `OAI.Erdos3.VectorPolynomial.allocatedWholeResidueReconstruction`, `OAI.Erdos3.VectorPolynomial.exists_allocatedEarlyCoarseLog_bound`, `OAI.Erdos3.VectorPolynomial.exists_allocatedEarlyRecenteredMesh_budget`, `OAI.Erdos3.exists_narrow_sampler_threshold`, `OAI.Erdos3.jointPhysicalBaseLog`, `OAI.Erdos3.jointPhysicalScalarBudget`, `OAI.Erdos3.narrow_sampler_residue_scale`, `OAI.Erdos3.narrow_sampler_width_bounds`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B054
import Definitions.Def_OAIErdos3B130

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.JointMeasureProductiveNarrowSampler
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem physicalSiteWidth_mono {K X : Type*} [Fintype K]
    (root : K → ℤ) {V W : Option K × X → ℝ} (h : ∀ z, V z ≤ W z) (x : X) :
    physicalSiteWidth root V x ≤ physicalSiteWidth root W x := by
  apply add_le_add (h (none,x))
  exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (h (some k,x)) (abs_nonneg _))

theorem narrowTrimmedSpatialWidths_fit {G J X : Type*} [Fintype G] [Fintype J]
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ1 : ξ ≤ 1)
    (root : G ⊕ J → ℤ) (hroot : (∑ k, |(root k : ℝ)|) ≤ W)
    (N : X → ℕ) (hN : ∀ x, 0 < N x) (x : X) :
    physicalSiteWidth root (narrowTrimmedSpatialWidths W τ ξ N) x ≤
      (spatialTrimMargin τ N x : ℝ) :=
  (physicalSiteWidth_mono root (narrowTrimmedSpatialWidths_le hW hτ hξ1 N hN) x).trans
    (spatialTrimMargin_fits hW hτ.le root hroot N x)

theorem narrow_jointIntegerPhysicalSite_mem_box {G J X : Type*}
    [Fintype G] [Fintype J] [Fintype X] [DecidableEq X]
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hτhalf : τ ≤ 1/2) (hξ1 : ξ ≤ 1)
    (root : G ⊕ J → ℤ) (hroot : (∑ k, |(root k : ℝ)|) ≤ W)
    (N : X → ℕ) (hN : ∀ x, 0 < N x) (hsize : ∀ x, 4 ≤ τ * (N x : ℝ))
    (z : trimmedIntegerBox N (spatialTrimMargin τ N) ×
      rectangularWeightIndices 0 (narrowTrimmedSpatialWidths (G := G) (J := J) W τ ξ N) 1) :
    jointIntegerPhysicalSite root (z.1.val,z.2.val) ∈ integerBox N :=
  jointIntegerPhysicalSite_mem_box root N (spatialTrimMargin τ N)
    (fun x => (spatialTrimMargin_proper hτhalf N hN hsize x).le) _
    (narrowTrimmedSpatialWidths_fit hW hτ hξ1 root hroot N hN) z

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_narrow_sampler_threshold (a b : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ P : ℝ, 0 ≤ P →
      (spatialSamplingBudget (2*P) + a)^a ≤ (P+A)^A ∧
      (spatialSamplingBudget (2*P) + b)^b ≤ (P+A)^A ∧
      10*P+128 ≤ (P+A)^A := by
  let base : Polynomial ℕ := 8*Polynomial.X+128
  let cost := (base+Polynomial.C a)^a+(base+Polynomial.C b)^b+10*Polynomial.X+128
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget cost
  refine ⟨A, hA, fun P hP => ?_⟩
  have h := hbudget P hP
  have he : spatialSamplingBudget (2*P) = 8*P+128 := by unfold spatialSamplingBudget; ring
  have hc : (spatialSamplingBudget (2*P)+a)^a + (spatialSamplingBudget (2*P)+b)^b +
      10*P+128 ≤ (P+A)^A := by
    rw [he]
    simpa [cost, base, Polynomial.eval₂_pow] using h
  have hQ : 0 ≤ spatialSamplingBudget (2*P) := by unfold spatialSamplingBudget; positivity
  have ha : 0 ≤ (spatialSamplingBudget (2*P)+a)^a := by positivity
  have hb : 0 ≤ (spatialSamplingBudget (2*P)+b)^b := by positivity
  constructor
  · linarith
  constructor <;> linarith

theorem narrow_sampler_width_bounds {G J X : Type*} {P W τ ξ : ℝ}
    (hP : 0 ≤ P) (hW : 0 ≤ W) (hWP : W ≤ Real.exp P)
    (hτ : 0 < τ) (hτP : τ⁻¹ ≤ Real.exp P)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (hN : ∀ i, 0 < N i) :
    0 < spatialWidthFraction (2*P) (ξ*τ) ∧
    1/spatialWidthFraction (2*P) (ξ*τ) ≤ Real.exp (spatialSamplingBudget (2*P)) ∧
    ∀ z : Option (G ⊕ J) × X,
      spatialWidthFraction (2*P) (ξ*τ) * (N z.2 : ℝ) ≤ narrowTrimmedSpatialWidths W τ ξ N z := by
  have h2P : 0 ≤ 2*P := by positivity
  have hτξ : 0 < ξ*τ := mul_pos hξ hτ
  have hτξP : (ξ*τ)⁻¹ ≤ Real.exp (2*P) := by
    rw [mul_inv_rev]
    calc
      _ ≤ Real.exp P * Real.exp P := mul_le_mul hτP hξP (inv_nonneg.mpr hξ.le) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  refine ⟨spatialWidthFraction_pos (2*P) hτξ,
    spatialWidthFraction_inv_le h2P hτξ hτξP, ?_⟩
  intro z
  exact (spatialWidthFraction_le_allocated_width h2P hW
    (hWP.trans (Real.exp_le_exp.mpr (by linarith))) hτξ.le N z).trans
    (narrowTrimmedSpatialWidths_lower hW hτ hξ1 N hN z)

theorem narrow_sampler_residue_scale {G J X : Type*} {P W τ ξ : ℝ}
    (hP : 0 ≤ P) (hW : 0 ≤ W) (hWP : W ≤ Real.exp P)
    (hτ : 0 < τ) (hτP : τ⁻¹ ≤ Real.exp P)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hξP : ξ⁻¹ ≤ Real.exp P)
    (N q : X → ℕ) (hq : ∀ i, 0 < q i) (hqP : ∀ i, (q i : ℝ) ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hsize : ∀ i, Real.exp (10*P+128) ≤ (N i : ℝ)) :
    ∀ z : Option (G ⊕ J) × X, 8*(probabilityProfileLipschitz : ℝ) ≤
      residueProfileWidth q (narrowTrimmedSpatialWidths W τ ξ N) z := by
  have h2P : 0 ≤ 2*P := by positivity
  have hτξ : 0 < ξ*τ := mul_pos hξ hτ
  have hτξP : (ξ*τ)⁻¹ ≤ Real.exp (2*P) := by
    rw [mul_inv_rev]
    calc
      _ ≤ Real.exp P * Real.exp P := mul_le_mul hτP hξP (inv_nonneg.mpr hξ.le) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hB4 : W ≤ Real.exp (2*(2*P)) := hWP.trans (Real.exp_le_exp.mpr (by linarith))
  have hN (i) : 0 < N i := by exact_mod_cast (Real.exp_pos _).trans_le (hsize i)
  have hsz (i) : 64*(probabilityProfileLipschitz : ℝ)*(q i : ℝ)*(1+W) ≤ (ξ*τ)*(N i : ℝ) := by
    calc
      _ ≤ 64*(probabilityProfileLipschitz : ℝ)*(q i : ℝ)*(1+Real.exp (2*(2*P))) :=
        mul_le_mul_of_nonneg_left (by linarith only [hB4]) (by positivity)
      _ ≤ _ := spatial_scale_of_exp_size h2P hτξ hτξP (Nat.cast_nonneg _)
        ((hqP i).trans (Real.exp_le_exp.mpr (by linarith)))
        (hprofile.trans (Real.exp_le_exp.mpr (by linarith)))
        (by convert hsize i using 1; congr 2; ring)
  intro z
  exact (trimmedSpatialWidths_scale hW q hq N hsz z).trans
    (div_le_div_of_nonneg_right (narrowTrimmedSpatialWidths_lower hW hτ hξ1 N hN z)
      (Nat.cast_nonneg _))

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped BigOperators NNReal

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped BigOperators NNReal Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped BigOperators NNReal Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped BigOperators NNReal Classical

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped BigOperators NNReal Classical

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedJointPhysicalScalarBudget
namespace OAI

section

namespace Erdos3

def jointPhysicalBaseLog (Pwidth E V : ℝ) : ℝ := 8 * Pwidth + V + 2 * E + 134

theorem jointPhysicalScalarBudget {G J X : Type*} {Pwidth W τ ξ E V : ℝ}
    (hP : 0 ≤ Pwidth) (hW : 0 ≤ W) (hWP : W ≤ Real.exp Pwidth)
    (hτ : 0 < τ) (hτP : τ⁻¹ ≤ Real.exp Pwidth)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hξP : ξ⁻¹ ≤ Real.exp Pwidth)
    (hE : 0 ≤ E) (hV : 0 ≤ V) (Q : ℕ)
    (hQexp : (Q : ℝ) ≤ Real.exp V) (stride : X → ℕ)
    (hstride : ∀ x, (stride x : ℝ) ≤ Real.exp Pwidth) :
    let ρ := spatialWidthFraction (2 * Pwidth) (ξ * τ)
    let Smax := Real.exp (Pwidth + V + 2 * E + 6)
    let Pbase := jointPhysicalBaseLog Pwidth E V
    0 ≤ Pbase ∧ Pwidth ≤ Pbase ∧ E ≤ Pbase ∧ V ≤ Pbase ∧
      0 < ρ ∧ 1 / ρ ≤ Real.exp Pbase ∧
      0 ≤ Smax ∧ Smax ≤ Real.exp Pbase ∧
      (∀ x, ((stride x * max Q (quantitativeBadPrimeRadius E ^ 2) : ℕ) : ℝ) ≤ Smax) ∧
      ∀ (N : X → ℕ), (∀ x, 0 < N x) →
        ∀ z : Option (G ⊕ J) × X, ρ * (N z.2 : ℝ) ≤ narrowTrimmedSpatialWidths W τ ξ N z := by
  intro ρ Smax Pbase
  have hbase : 0 ≤ Pbase := by dsimp [Pbase, jointPhysicalBaseLog]; positivity
  have hPbase : Pwidth ≤ Pbase := by dsimp [Pbase, jointPhysicalBaseLog]; linarith
  have hEbase : E ≤ Pbase := by dsimp [Pbase, jointPhysicalBaseLog]; linarith
  have hVbase : V ≤ Pbase := by dsimp [Pbase, jointPhysicalBaseLog]; linarith
  have hρ : 0 < ρ := spatialWidthFraction_pos _ (mul_pos hξ hτ)
  have hτξ : (ξ * τ)⁻¹ ≤ Real.exp (2 * Pwidth) := by
    rw [mul_inv_rev]
    calc
      _ ≤ Real.exp Pwidth * Real.exp Pwidth :=
        mul_le_mul hτP hξP (inv_nonneg.mpr hξ.le) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hρinv : 1 / ρ ≤ Real.exp Pbase :=
    (spatialWidthFraction_inv_le (by positivity : 0 ≤ 2 * Pwidth) (mul_pos hξ hτ) hτξ).trans
      (Real.exp_le_exp.mpr (by dsimp [Pbase, jointPhysicalBaseLog, spatialSamplingBudget]; linarith))
  have hcap := (quantitativeBadPrimeRadius_witness_budget hE hV Q hQexp).1
  refine ⟨hbase, hPbase, hEbase, hVbase, hρ, hρinv, (Real.exp_pos _).le,
    Real.exp_le_exp.mpr (by dsimp [Pbase, jointPhysicalBaseLog]; linarith), ?_, ?_⟩
  · intro x
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp Pwidth * Real.exp (V + 2 * E + 6) :=
        mul_le_mul (hstride x) hcap (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Smax := by dsimp [Smax]; rw [← Real.exp_add]; congr 1; ring
  · intro N hN
    exact (narrow_sampler_width_bounds hP hW hWP hτ hτP hξ hξ1 hξP N hN).2.2

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedLocalResidueReconstruction
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (X : Type*) [Fintype X]
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus] (H : X → ℝ)
variable {W : ℝ} (hW : 0 ≤ W) (mesh : ℝ)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod modulus)

noncomputable def allocatedResidueSpatialKernel
    (r : labels) (v : X → (Unit ⊕ Fin dim) → ℤ) : ℂ :=
  let ker := fun g => (0 : ℤ) + (x g none : ℤ)
  let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x ker
    (one_div_pos.mpr (Nat.cast_pos.mpr hM)) hx
  let f := canonicalSpatialSiteDensity selection ker (scalarCubeDifferenceMatrix x) hp W S.value
    hW (Nat.cast_pos.mpr S.positive)
  ∏ t, spatialSiteApprox (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
    (Matrix.fromCols (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection)
      (liftResidueMatrix (principalSpatialResidueColumns modulus (fun _ => (0 : ℤ)) id r)))
    modulus f (H t) 4 mesh (v t)

variable (q : X → ℕ) {τ : ℝ}
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
    (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
    (allocatedPrincipalSides B U b S))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical Matrix

noncomputable def allocatedSpatialCoefficientCap {G : Type*} [Fintype G] {dim : ℕ}
    (X : Type*) [Fintype X] (selection : Fin dim ↪ G) (M modulus : ℕ) (mesh : ℝ) : ℝ :=
  ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
    (intervalSiteCount 4 mesh : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
    ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ)))) ^ Fintype.card X

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (X : Type*) [Fintype X]
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus] {W : ℝ} (hW : 0 ≤ W) (mesh : ℝ)

local notation "labels" => PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod modulus
local notation "terms" => X → SpatialSiteLabel (Fin dim) modulus 4 mesh

noncomputable def allocatedSpatialExpansionCoefficient (r : labels) (t : terms) : ℂ :=
  let ker := fun g => (0 : ℤ) + (x g none : ℤ)
  let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x ker
    (one_div_pos.mpr (Nat.cast_pos.mpr hM)) hx
  let f := canonicalSpatialSiteDensity selection ker (scalarCubeDifferenceMatrix x) hp W S.value
    hW (Nat.cast_pos.mpr S.positive)
  ∏ z : X, spatialSiteCoefficient (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
    (Matrix.fromCols (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection)
      (liftResidueMatrix (principalSpatialResidueColumns modulus (fun _ => (0 : ℤ)) id r)))
    modulus f 4 mesh (t z)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (X : Type*) [Fintype X]
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus] (H : X → ℝ)

variable {W : ℝ} (hW : 0 ≤ W) (mesh : ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset (Fin dim))

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

variable (X : Type*) [Fintype X]

local notation "whole" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) sides (allocatedPrincipalSides_pos B U b S)

variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Module.Basis (Kcov j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) → EuclideanJetLayers U O → ℝ)
variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (C₀ ρ δ mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (Cg Z : ℝ)

local notation "frozenTuple" => PrincipalAxisTuples (α := Fin dim) grid sides
local notation "label" => (PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a))
  (fun a => layerSamplerDegree I n (Subtype.val a)) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q))
local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides
local notation "refined" => residueRefinedPeriod modulus q

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
    (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
    (allocatedPrincipalSides B U b S))
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)

noncomputable def allocatedWholeResidueReconstruction (base : X → ℤ)
    (r : labels) (a : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q) :=
  physicalResidueReconstruction
    (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference r))
    (allocatedPhysicalCubeDirections B U b S x (wholeReference r)) base
    (boundedColumnResidueRepresentative q a) q

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
    (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
    (allocatedPrincipalSides B U b S))
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedCoarseSource
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
    (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
    (allocatedPrincipalSides B U b S))
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
    (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
    (allocatedPrincipalSides B U b S))
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

end Erdos3.VectorPolynomial

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

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
    (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
    (allocatedPrincipalSides B U b S))
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

noncomputable def allocatedRecenteredProfileTerm
    (profile : fullTuple → EuclideanJetLayers U O → ℂ) (y : fullTuple) : ℂ :=
  let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
  let A := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
    (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i
  let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base
    (principalResidueLabel refined y)
  ∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
    ∑ v ∈ window,
      (allocatedResidueSpatialKernel B U b S x X hM selection hx modulus
        (trimmedSpatialRootScale τ N q) hW mesh (principalResidueLabel modulus y) v / (A : ℂ)) *
      test (reconstruct a.val v) * profile y (point (reconstruct a.val v))

noncomputable def allocatedRecenteredProfileMass
    (profile : fullTuple → EuclideanJetLayers U O → ℂ) (y : fullTuple) : ℝ :=
  let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
  let A := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
    (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i
  let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base
    (principalResidueLabel refined y)
  ∑ a : cells, selectedResidueCellWeight q cells V a *
    ((∑ v ∈ window, ‖profile y (point (reconstruct a.val v))‖) / A)

variable (hq : ∀ t, 0 < q t) (hN : ∀ t, 0 < N t) (hτ : 0 < τ)
variable (href : ∀ u r, principalResidueLabel (residueRefinedPeriod modulus q) (reference u r) = r)
variable (hwhole : ∀ r, principalResidueLabel (residueRefinedPeriod modulus q) (wholeReference r) = r)
variable (Q : ℝ≥0) (hQ : 1 ≤ Q) (hratio : (1 + W) / (S.value : ℝ) ≤ Q)
variable (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
variable (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
  pivotFullImage
    (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
    (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
variable (hmesh : 0 < mesh) {ε : ℝ} (hε : 0 ≤ ε) (hmargin : (3 + 2 * mesh) + 2 * ε ≤ 4)
variable (hsize : ∀ t, Fintype.card (Option (LayerSamplerVariables G I n B)) *
  (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ ε * trimmedSpatialRootScale τ N q t)
variable (htest : ∀ v, ‖test v‖ ≤ 1)

local notation "shiftError" => Fintype.card X *
  ((modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
    (anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * Q) * (8 * mesh + ε)) *
  (1 + (modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
    anisotropicSpatialDensityCap selection (1 / (M : ℝ)))^Fintype.card X

local notation "whole" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

variable (hq : ∀ t, 0 < q t) (hN : ∀ t, 0 < N t) (hτ : 0 < τ)

local notation "whole" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

variable (hq : ∀ t, 0 < q t) (hN : ∀ t, 0 < N t) (hτ : 0 < τ)

local notation "whole" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)

noncomputable def allocatedRecenteredCoarseMesh (Q : ℝ≥0) (V ε : ℝ) : ℝ :=
  spatialTupleCoarseMesh (Fintype.card X)
    ((modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) * anisotropicSpatialDensityCap selection (1 / (M : ℝ)))
    V ((modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
      (anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * Q)) ε

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped NNReal

noncomputable def allocatedEarlyRecenteredMesh {dim : ℕ} {G : Type*} [Fintype G]
    (X : Type*) [Fintype X] (selection : Fin dim ↪ G) (M modulus : ℕ) (p E : ℝ) : ℝ :=
  allocatedRecenteredCoarseMesh (M := M) X modulus selection (allocatedPrimitiveRootRatio (Real.exp p))
    (Real.exp (coefficientErrorVolumeLog p + 4)) (Real.exp (-E))

noncomputable def allocatedEarlyCoarseInput {A : Type*} [Semiring A] (m dim : ℕ) (s : A) : A :=
  let R := s + (m + dim + 2 : ℕ)
  2 * R + R ^ 3 + anisotropicSpatialCapLog R + spatialLipschitzEnvelope R +
    coefficientErrorVolumeLog R + 8

theorem allocatedEarlyCoarseInput_bounds (m dim : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    let R := s + (m + dim + 2 : ℕ)
    let T := allocatedEarlyCoarseInput m dim s
    0 ≤ T ∧ R ≤ T ∧ R ^ 3 ≤ T ∧
      R ^ 3 + anisotropicSpatialCapLog R ≤ T ∧
      R ^ 3 + spatialLipschitzEnvelope R + R ≤ T ∧
      coefficientErrorVolumeLog R + 4 ≤ T := by
  intro R T
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hcap := anisotropicSpatialCapLog_nonneg hR
  have hlip := (spatialCostEnvelopes_nonneg hR (le_refl (0 : ℝ))).2.2.2.2
  have hmass : 0 ≤ coefficientErrorVolumeLog R := by unfold coefficientErrorVolumeLog; positivity
  have hcube : 0 ≤ R ^ 3 := pow_nonneg hR _
  dsimp only [T, allocatedEarlyCoarseInput]
  change 0 ≤ 2 * R + R ^ 3 + anisotropicSpatialCapLog R + spatialLipschitzEnvelope R +
      coefficientErrorVolumeLog R + 8 ∧ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith only [hR, hcap, hlip, hmass, hcube]

theorem allocatedEarlyRecenteredMesh_partition_budget (m : ℕ) {dim : ℕ}
    {G : Type*} [Fintype G] (X : Type*) [Fintype X]
    (selection : Fin dim ↪ G) {M modulus : ℕ} {p E : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hM : 0 < M) (hMP : (M : ℝ) ≤ Real.exp p) (hmod : modulus ≤ M ^ (m + 1)) :
    let r := allocatedEarlyRecenteredMesh X selection M modulus p E
    let T := allocatedEarlyCoarseInput m dim (p + E)
    0 < r ∧ r ≤ 1 / 4 ∧ r⁻¹ ≤ Real.exp (coarseSpatialReciprocalLog T) ∧
      allocatedSpatialCoefficientCap X selection M modulus r ≤
        Real.exp (coarseSpatialPartitionLog T) := by
  let s := p + E
  let R := s + (m + dim + 2 : ℕ)
  let T := allocatedEarlyCoarseInput m dim s
  have hs : 0 ≤ s := add_nonneg hp hE
  have hR2 : 2 ≤ R := by
    dsimp [R]
    push_cast
    linarith only [hs, Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) dim]
  have hR : 0 ≤ R := by linarith only [hR2]
  obtain ⟨hT, hRT, hcubeT, hcapT, hlipT, hmassT⟩ := allocatedEarlyCoarseInput_bounds m dim hs
  change R ≤ T at hRT
  have hpR : p + 1 ≤ R := by
    dsimp [R, s]; push_cast
    linarith only [hE, Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) dim]
  have hpR' : p ≤ R := by linarith only [hpR]
  have hER : E ≤ R := by
    dsimp [R, s]; push_cast
    linarith only [hp, Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) dim]
  have hmR : ((m + 1 : ℕ) : ℝ) ≤ R := by
    dsimp [R]; push_cast
    linarith only [hs, Nat.cast_nonneg (α := ℝ) dim]
  have hnR : (Fintype.card (Unit ⊕ Fin dim) : ℝ) ≤ R := by
    simp only [Fintype.card_sum, Fintype.card_unique, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    dsimp [R]; push_cast
    linarith only [hs, Nat.cast_nonneg (α := ℝ) m]
  have hGR := hG.trans hpR'
  have hXR := hX.trans hpR'
  have hMR := hMP.trans (Real.exp_le_exp.mpr hpR')
  have hmodR := coefficientErrorPeriod_exp_sq hR hmR hMR hmod
  have hΓ : (modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) ≤ Real.exp (R ^ 3) :=
    (pow_le_exp_mul_of_le_exp (Nat.cast_nonneg _) hmodR (sq_nonneg R) _ hnR).trans_eq
      (congrArg Real.exp (by ring))
  have hκ : 0 ≤ 1 / (M : ℝ) := by positivity
  have hC0 := anisotropicSpatialDensityCap_nonneg selection hκ
  have hL0 := anisotropicSpatialDensityLip_nonneg selection hκ
  have hC := anisotropicSpatialDensityCap_exp_bound selection hR hM hMR hnR hGR
  have hfree : (Fintype.card (UnselectedColumn selection) : ℝ) ≤ 2 * R := by
    have hcard := selectedColumn_card selection
    have hb : (Fintype.card (UnselectedColumn selection) : ℝ) ≤ R :=
      (Nat.cast_le.mpr (by omega)).trans hGR
    linarith only [hb, hR]
  have hprofile := spatialProfileLog_le_fixedEnvelope _ _ hR hnR hfree
  have hL : anisotropicSpatialDensityLip selection (1 / (M : ℝ)) ≤
      Real.exp (spatialLipschitzEnvelope R) :=
    (anisotropicSpatialDensityLip_le_exp selection hR hM hMR hnR hGR).trans
      (Real.exp_le_exp.mpr (add_le_add le_rfl (mul_le_mul_of_nonneg_left hprofile (by norm_num))))
  have hQ : (allocatedPrimitiveRootRatio (Real.exp p) : ℝ) ≤ Real.exp R := by
    rw [(allocatedPrimitiveRootRatio_bounds (Real.exp_pos p).le).1, add_comm]
    exact (one_add_le_exp_succ hp (le_refl (Real.exp p))).trans (Real.exp_le_exp.mpr hpR)
  have hcapInput : (modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ)) ≤ Real.exp T := by
    calc
      _ ≤ Real.exp (R ^ 3) * Real.exp (anisotropicSpatialCapLog R) := by gcongr
      _ = Real.exp (R ^ 3 + anisotropicSpatialCapLog R) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hcapT
  have hlipInput : (modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      (anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * allocatedPrimitiveRootRatio (Real.exp p)) ≤
      Real.exp T := by
    calc
      _ ≤ Real.exp (R ^ 3) * (Real.exp (spatialLipschitzEnvelope R) * Real.exp R) := by gcongr
      _ = Real.exp (R ^ 3 + spatialLipschitzEnvelope R + R) := by
        rw [← Real.exp_add, ← Real.exp_add, add_assoc]
      _ ≤ _ := Real.exp_le_exp.mpr hlipT
  have hmassLog : coefficientErrorVolumeLog p ≤ coefficientErrorVolumeLog R := by
    unfold coefficientErrorVolumeLog
    gcongr
  have hmassInput : Real.exp (coefficientErrorVolumeLog p + 4) ≤ Real.exp T :=
    Real.exp_le_exp.mpr ((add_le_add hmassLog le_rfl).trans hmassT)
  have hε : 0 < Real.exp (-E) := Real.exp_pos _
  have hεInput : (Real.exp (-E))⁻¹ ≤ Real.exp T := by
    rw [← Real.exp_neg, neg_neg]
    exact Real.exp_le_exp.mpr (hER.trans hRT)
  have hsquare : R ^ 2 ≤ R ^ 3 := by
    calc
      R ^ 2 = R ^ 2 * 1 := (mul_one _).symm
      _ ≤ R ^ 2 * R := mul_le_mul_of_nonneg_left (by linarith only [hR2]) (sq_nonneg R)
      _ = R ^ 3 := by ring
  have hmodInput := hmodR.trans (Real.exp_le_exp.mpr (hsquare.trans hcubeT))
  have hΓInput := hΓ.trans (Real.exp_le_exp.mpr hcubeT)
  have hCInput := hC.trans (Real.exp_le_exp.mpr
    (show anisotropicSpatialCapLog R ≤ T from
      (le_add_of_nonneg_left (pow_nonneg hR 3)).trans hcapT))
  have hcap0 := mul_nonneg (pow_nonneg (Nat.cast_nonneg modulus (α := ℝ)) (Fintype.card (Unit ⊕ Fin dim))) hC0
  have hlip0 := mul_nonneg (pow_nonneg (Nat.cast_nonneg modulus (α := ℝ)) (Fintype.card (Unit ⊕ Fin dim)))
    (mul_nonneg hL0 (NNReal.coe_nonneg (allocatedPrimitiveRootRatio (Real.exp p))))
  have hspec := spatialTupleCoarseMesh_spec (Fintype.card X) hcap0
    (Real.exp_pos (coefficientErrorVolumeLog p + 4)).le hlip0 hε
  have hcost := spatialTupleCoarseMesh_partition_budget (Fintype.card X)
    (Fintype.card (Unit ⊕ Fin dim)) hcap0 (Real.exp_pos (coefficientErrorVolumeLog p + 4)).le hlip0
    (Nat.cast_nonneg _) hC0 hε hT (hXR.trans hRT) (hnR.trans hRT)
    hcapInput hmassInput hlipInput hεInput hmodInput hΓInput hCInput
  exact ⟨hspec.1, hspec.2.1, hcost.1, hcost.2⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem exists_allocatedEarlyCoarseLog_bound (m dim : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {s : ℝ}, 0 ≤ s →
      coarseSpatialReciprocalLog (allocatedEarlyCoarseInput m dim s) ≤ (s + a) ^ a ∧
      coarseSpatialPartitionLog (allocatedEarlyCoarseInput m dim s) ≤ (s + a) ^ a := by
  let poly : Polynomial ℕ :=
    coarseSpatialReciprocalLog (allocatedEarlyCoarseInput m dim Polynomial.X) +
      coarseSpatialPartitionLog (allocatedEarlyCoarseInput m dim Polynomial.X)
  obtain ⟨a, ha, hpoly⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro s hs
  have hsum : coarseSpatialReciprocalLog (allocatedEarlyCoarseInput m dim s) +
      coarseSpatialPartitionLog (allocatedEarlyCoarseInput m dim s) ≤ (s + a) ^ a := by
    simpa [poly, allocatedEarlyCoarseInput, coarseSpatialReciprocalLog, coarseSpatialPartitionLog,
      spatialTupleToleranceLog, spatialLipschitzEnvelope, spatialFixedProfileEnvelope,
      anisotropicSpatialCapLog, coefficientErrorVolumeLog, Polynomial.eval₂_pow] using hpoly s hs
  obtain ⟨hinv, hpartition⟩ := coarseSpatialLogs_nonneg (allocatedEarlyCoarseInput_bounds m dim hs).1
  exact ⟨(le_add_of_nonneg_right hpartition).trans hsum,
    (le_add_of_nonneg_left hinv).trans hsum⟩

theorem exists_allocatedEarlyRecenteredMesh_budget (m dim : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {G : Type*} [Fintype G] (X : Type*) [Fintype X]
      (selection : Fin dim ↪ G) {M modulus : ℕ} {p E : ℝ},
      0 ≤ p → 0 ≤ E → (Fintype.card G : ℝ) ≤ p → (Fintype.card X : ℝ) ≤ p →
      0 < M → (M : ℝ) ≤ Real.exp p → modulus ≤ M ^ (m + 1) →
      let r := allocatedEarlyRecenteredMesh X selection M modulus p E
      0 < r ∧ r ≤ 1 / 4 ∧ r⁻¹ ≤ Real.exp ((p + E + a) ^ a) ∧
        allocatedSpatialCoefficientCap X selection M modulus r ≤ Real.exp ((p + E + a) ^ a) := by
  obtain ⟨a, ha, hlogs⟩ := exists_allocatedEarlyCoarseLog_bound m dim
  refine ⟨a, ha, ?_⟩
  intro G _ X _ selection M modulus p E hp hE hG hX hM hMP hmod r
  have h := allocatedEarlyRecenteredMesh_partition_budget m X selection hp hE hG hX hM hMP hmod
  have hlog := hlogs (add_nonneg hp hE)
  exact ⟨h.1, h.2.1, h.2.2.1.trans (Real.exp_le_exp.mpr hlog.1),
    h.2.2.2.trans (Real.exp_le_exp.mpr hlog.2)⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (N : X → ℕ) {W τ ξ : ℝ} (hW : 0 ≤ W) (mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable {O : Fin m → Type*}
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ)

local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

variable (hq : ∀ t, 0 < q t) (hN : ∀ t, 0 < N t) (hτ : 0 < τ)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PositivePhysicalProjectionError
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

variable {I K F : Type*} [Fintype I] [Fintype K] [Fintype F] {m q : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (root : K → ℤ) (difference : Fin q → K → ℤ) (D : ℕ)
variable (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
variable (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
variable (hm : ∀ j d, coefficients (p j) d ∈ U j)
variable (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
variable (test : Finset (Fin q) → (I → ℝ) → ℂ) (htest : ∀ s v, ‖test s v‖ ≤ 1)
variable (base : I → ℤ) (modulus : I → ℕ)
variable (T : Finset (ColumnResiduePattern (Option K) I modulus))
variable (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z)

local notation "frame" => (fun z : Option K × I → ℤ => fun k i => (z (k, i) : ℝ))
local notation "output" => physicalCubeRootDifferences root (Matrix.of difference) base
local notation "law" => selectedResidueSmoothPMF modulus T V hV hZ

include hp htest in
theorem selectedResidue_positive_density_projection_error
    (density : CoefficientTorus (K := K) U → ℝ)
    (f : EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
    {η δ : ℝ} (hη : 0 ≤ η)
    (happrox : ∀ x, ‖(density x : ℂ) - coefficientTorusFourierSum U frequency c x‖ ≤ η) :
    let pa := fun j => translate (fun i => (base i : ℝ)) (p j)
    let hma := fun j => coefficients_translate_mem (U j) (fun i => (base i : ℝ)) (p j) (hm j)
    ∀ (_hpositive : ∀ z, ‖affineCubeFourierProjection U root difference frequency pa c (frame z) -
      (f (euclideanCoefficientJetMap U root (Matrix.of difference)
        (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
        (affineCoefficientCoverSample U pa hma D (frame z))) : ℂ)‖ ≤ η)
    (_hprojection :
      ‖(∑' z, ((law z).toReal : ℂ) * (physicalCubeSiteTest test (output z) *
        affineCubeFourierSum frequency pa c (frame z))) -
        ∑' z, ((law z).toReal : ℂ) * (physicalCubeSiteTest test (output z) *
          affineCubeFourierProjection U root difference frequency pa c (frame z))‖ ≤ δ),
    ‖(∑' z, ((law z).toReal : ℂ) * (physicalCubeSiteTest test (output z) *
      (density (affineSampleCoefficientTorus U pa hma (frame z)) : ℂ))) -
      ∑' z, ((law z).toReal : ℂ) * physicalCubePositiveTest U D p hm f test (output z)‖ ≤ 2 * η + δ := by
  intro pa hma hpositive hprojection
  have hpa (j) : DegreeLE (1 : I → ℕ) (j.val + 1) (pa j) :=
    degreeLE_translate (1 : I → ℕ) (fun _ => by norm_num) _ (p j) (hp j)
  have happ (z) : ‖(density (affineSampleCoefficientTorus U pa hma (frame z)) : ℂ) -
      affineCubeFourierSum frequency pa c (frame z)‖ ≤ η := by
    have h := happrox (affineSampleCoefficientTorus U pa hma (frame z))
    rw [coefficientTorusFourierSum_sample U frequency c pa hpa hma (frame z)] at h
    exact h
  have hpos (z) : ‖affineCubeFourierProjection U root difference frequency pa c (frame z) -
      (f (physicalCubeEuclideanSample U D p hm (output z)) : ℂ)‖ ≤ η := by
    have h := hpositive z
    rw [coefficientCoverSample_physicalJet U root difference D p hp hm base z] at h
    exact h
  exact selectedResidueSmoothPMF_projection_approximation modulus T V hV hZ
    (fun z => physicalCubeSiteTest test (output z))
    (fun z => (density (affineSampleCoefficientTorus U pa hma (frame z)) : ℂ))
    (fun z => affineCubeFourierSum frequency pa c (frame z))
    (fun z => affineCubeFourierProjection U root difference frequency pa c (frame z))
    (fun z => (f (physicalCubeEuclideanSample U D p hm (output z)) : ℂ))
    hη (fun z _ => physicalCubeSiteTest_norm_le test htest (output z))
    (fun z _ => happ z) (fun z _ => hpos z) hprojection

end Erdos3.BooleanCubeKernel

end

end OAI

end


