-- Prove2me | Definitions.Def_OAIE3v2B020
-- name    : OAIE3v2B020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:58:40.492984+00:00
-- url     : https://prove2.me/theorems/f3e3c49e-b23f-4421-92b9-a23e96d8a30f
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 21 of 311
-- statement:
--   Definitions bundle 21 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Estimates/CovolumeFactorBounds.lean`, `Estimates/DerivativeIndexBounds.lean`, `Estimates/GramCovolume.lean`, `Estimates/HorizontalPivotExclusion.lean`, `Estimates/IndependentColumnsMinor.lean`, `Estimates/LowerTriangularMinor.lean`, `Estimates/NormalizedMinorBounds.lean`, `Geometry/CoordinateMinorCovolume.lean`, `Geometry/NormalizedMinorCoordinates.lean`, `Lattices/FiniteLatticeBasis.lean`, `Lattices/IntegerMinorNormalization.lean`, `Lattices/LatticeCoordinateLifts.lean`, `Lattices/LatticeVoronoiPacking.lean`, `Lattices/PartitionedAffineLogEnvelope.lean`, `Linear/BasisImageSection.lean`, `Linear/EuclideanHorizontalProjection.lean`, `Linear/SpanSubsetBasis.lean`, `Sampling/GridNormalizationDenominator.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CovolumeFactorBounds
namespace OAI

section

namespace Erdos3

theorem covolume_index_graph_bounds {a I E C d : ℝ}
    (hd : 0 < d) (ha : 1 / d ≤ a) (hI : 1 ≤ I) (hE : 1 ≤ E)
    (hprod : a * I * E ≤ C) : a ≤ C ∧ I ≤ C * d ∧ E ≤ C * d := by
  have ha0 : 0 ≤ a := (one_div_pos.mpr hd).le.trans ha
  have hI0 : 0 ≤ I := zero_le_one.trans hI
  have hE0 : 0 ≤ E := zero_le_one.trans hE
  have haI : a * I ≤ C :=
    (le_mul_of_one_le_right (mul_nonneg ha0 hI0) hE).trans hprod
  have haE : a * E ≤ C := by
    calc
      a * E ≤ (a * I) * E := mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_right ha0 hI) hE0
      _ ≤ C := hprod
  refine ⟨(le_mul_of_one_le_right ha0 hI).trans haI, ?_, ?_⟩
  · apply (div_le_iff₀ hd).mp
    calc
      I / d = (1 / d) * I := by ring
      _ ≤ a * I := mul_le_mul_of_nonneg_right ha hI0
      _ ≤ C := haI
  · apply (div_le_iff₀ hd).mp
    calc
      E / d = (1 / d) * E := by ring
      _ ≤ a * E := mul_le_mul_of_nonneg_right ha hE0
      _ ≤ C := haE

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.HorizontalPivotExclusion
namespace OAI

section

namespace Erdos3

theorem pivots_lt_of_weighted_bound {m k : ℕ}
    (p : Fin k → Fin m) (hp : Function.Injective p)
    (w : Fin m → ℝ) (hw : ∀ i, 1 ≤ w i)
    (l : ℕ) (hl : 0 < l) (a : ℕ) (T C v : ℝ)
    (hfar : ∀ i, a ≤ i.val → T ≤ w i)
    (hlower : 1 / (l : ℝ) ^ k * (∏ i, w (p i)) ≤ v)
    (hupper : v ≤ C) (hlarge : C * (l : ℝ) ^ m < T) :
    ∀ i, (p i).val < a := by
  have hkm : k ≤ m := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective p hp
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  have hpow : 0 < (l : ℝ) ^ k := pow_pos hlr _
  have hprod : (∏ i, w (p i)) / (l : ℝ) ^ k ≤ C := by
    simpa only [one_div, div_eq_mul_inv, mul_one, mul_comm] using hlower.trans hupper
  have hC : 0 ≤ C := (div_nonneg
    (Finset.prod_nonneg (fun i _ => zero_le_one.trans (hw (p i)))) hpow.le).trans hprod
  have hprodm : (∏ i, w (p i)) ≤ C * (l : ℝ) ^ m := by
    apply ((div_le_iff₀ hpow).mp hprod).trans
    apply mul_le_mul_of_nonneg_left _ hC
    exact pow_le_pow_right₀ (by exact_mod_cast Nat.succ_le_iff.mpr hl) hkm
  intro j
  by_contra hj
  have hsingle : w (p j) ≤ ∏ i, w (p i) := by
    have h := Finset.prod_le_prod_of_subset_of_one_le
      (f := fun i => w (p i)) (Finset.subset_univ ({j} : Finset (Fin k)))
      (fun i _ => zero_le_one.trans (hw (p i))) (fun i _ _ => hw (p i))
    simpa only [Finset.prod_singleton] using h
  exact (not_le_of_gt hlarge) ((hfar (p j) (Nat.le_of_not_gt hj)).trans (hsingle.trans hprodm))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowerTriangularMinor
namespace OAI

section

namespace Erdos3

theorem nonzero_row_minor_injective {K ι : Type*} [Field K] {k : ℕ}
    (A : Matrix ι (Fin k) K) (p : Fin k → ι) (hp : (A.submatrix p id).det ≠ 0) :
    Function.Injective p := by
  have h := Matrix.linearIndependent_rows_of_det_ne_zero hp
  intro i j hij
  apply h.injective
  change A (p i) = A (p j)
  rw [hij]

end Erdos3

end

section

namespace Erdos3

theorem row_minor_update_det {K ι : Type*} [Field K] {k : ℕ}
    (A : Matrix ι (Fin k) K) (p : Fin k → ι)
    (C : Matrix ι (Fin k) K) (hC : C * A.submatrix p id = A)
    (i : ι) (j : Fin k) :
    (A.submatrix (Function.update p j i) id).det = C i j * (A.submatrix p id).det := by
  have he : A.submatrix (Function.update p j i) id =
      (A.submatrix p id).updateRow j (fun b => A i b) := by
    ext a b
    by_cases h : a = j
    · subst a
      simp only [Matrix.submatrix_apply, Function.update_self, id_eq, Matrix.updateRow_apply,
        ite_true]
    · simp only [Matrix.submatrix_apply, Function.update_of_ne h, id_eq, Matrix.updateRow_apply,
        if_neg h]
  have hr : (fun b => A i b) = ∑ a, C i a • (A.submatrix p id) a := by
    funext b
    simpa only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] using (congrArg (fun M : Matrix ι (Fin k) K => M i b) hC).symm
  rw [he, hr]
  simpa only [smul_eq_mul] using
    Matrix.det_updateRow_sum (A.submatrix p id) j (fun a => C i a)

theorem minimal_row_minor_coordinate_zero {K : Type*} [Field K] {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) K) (p : Fin k → Fin m)
    (hp : (A.submatrix p id).det ≠ 0)
    (hmin : ∀ q : Fin k → Fin m, (A.submatrix q id).det ≠ 0 →
      (∑ j, (p j).val) ≤ ∑ j, (q j).val)
    (C : Matrix (Fin m) (Fin k) K) (hC : C * A.submatrix p id = A)
    (i : Fin m) (j : Fin k) (hij : i < p j) : C i j = 0 := by
  classical
  by_contra hne
  have hdet : (A.submatrix (Function.update p j i) id).det ≠ 0 := by
    rw [row_minor_update_det A p C hC i j]
    exact mul_ne_zero hne hp
  have hle := hmin (Function.update p j i) hdet
  have hfun : (fun a => (Function.update p j i a).val) =
      Function.update (fun a => (p a).val) j i.val := by
    funext a
    by_cases h : a = j <;> simp [h]
  rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ j)] at hle
  have hsum : (∑ a, (p a).val) =
      (p j).val + ∑ a ∈ Finset.univ \ {j}, (p a).val := by
    simpa only [Function.update_eq_self] using
      (Finset.sum_update_of_mem (Finset.mem_univ j) (fun a => (p a).val) (p j).val)
  rw [hsum] at hle
  exact (not_le_of_gt hij) (Nat.le_of_add_le_add_right hle)

end Erdos3

end

section

namespace Erdos3

theorem det_eq_one_of_triangular_labels {K ι α : Type*} [CommRing K]
    [Fintype ι] [DecidableEq ι] [LinearOrder α]
    (B : Matrix ι ι K) (p : ι → α) (hp : Function.Injective p)
    (htri : ∀ i j, p i < p j → B i j = 0) (hdiag : ∀ i, B i i = 1) : B.det = 1 := by
  let : LinearOrder ι := LinearOrder.lift' p hp
  have hB : B.IsLowerTriangular := fun {i j} hij => htri i j hij
  rw [Matrix.det_of_isLowerTriangular B hB]
  simp only [hdiag, Finset.prod_const_one]

theorem lower_unitriangular_preserves_minimal_minor
    {K : Type*} [Field K] {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) K) (p : Fin k → Fin m)
    (hp : (A.submatrix p id).det ≠ 0)
    (hmin : ∀ q : Fin k → Fin m, (A.submatrix q id).det ≠ 0 →
      (∑ j, (p j).val) ≤ ∑ j, (q j).val)
    (M : Matrix (Fin m) (Fin m) K)
    (hM : ∀ i j, i < j → M i j = 0) (hdiag : ∀ i, M i i = 1) :
    ((M * A).submatrix p id).det = (A.submatrix p id).det := by
  classical
  let B := A.submatrix p id
  let C := A * B⁻¹
  have hB : IsUnit B.det := isUnit_iff_ne_zero.mpr hp
  have hC : C * B = A := Matrix.nonsing_inv_mul_cancel_right B A hB
  have hCp : C.submatrix p id = 1 := by
    change (A * B⁻¹).submatrix p id = 1
    rw [Matrix.submatrix_mul A B⁻¹ p id id Function.bijective_id, Matrix.submatrix_id_id]
    exact Matrix.mul_nonsing_inv B hB
  have hzero (a : Fin m) (j : Fin k) (haj : a < p j) : C a j = 0 :=
    minimal_row_minor_coordinate_zero A p hp hmin C hC a j haj
  let T := (M * C).submatrix p id
  have hTtri (i j : Fin k) (hij : p i < p j) : T i j = 0 := by
    change ∑ a, M (p i) a * C a j = 0
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : a ≤ p i
    · rw [hzero a j (lt_of_le_of_lt ha hij), mul_zero]
    · rw [hM (p i) a (lt_of_not_ge ha), zero_mul]
  have hTdiag (i : Fin k) : T i i = 1 := by
    change ∑ a, M (p i) a * C a i = 1
    rw [Finset.sum_eq_single (p i)]
    · have hc : C (p i) i = 1 := by
        simpa using congrArg (fun N : Matrix (Fin k) (Fin k) K => N i i) hCp
      rw [hdiag, hc, one_mul]
    · intro a _ hne
      by_cases ha : a < p i
      · rw [hzero a i ha, mul_zero]
      · have hi : p i < a := lt_of_le_of_ne (le_of_not_gt ha) (Ne.symm hne)
        rw [hM (p i) a hi, zero_mul]
    · simp
  have hT : T.det = 1 := det_eq_one_of_triangular_labels T p
    (nonzero_row_minor_injective A p hp) hTtri hTdiag
  have he : (M * A).submatrix p id = T * B := by
    rw [← hC, ← Matrix.mul_assoc]
    exact Matrix.submatrix_mul (M * C) B p id id Function.bijective_id
  rw [he, Matrix.det_mul, hT, one_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GramCovolume
namespace OAI

section

namespace Erdos3

open Module RealInnerProductSpace

theorem zspan_covolume_sq_eq_det_gram {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {r : ℕ} (b : Basis (Fin r) ℝ E) :
    ZLattice.covolume (Submodule.span ℤ (Set.range b)) ^ 2 = (Matrix.gram ℝ b).det := by
  let b₀ : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E := stdOrthonormalBasis ℝ E
  have hrank : Module.finrank ℝ E = r := by simpa using Module.finrank_eq_card_basis b
  let e : Fin (Module.finrank ℝ E) ≃ Fin r := Fin.castOrderIso hrank
  let o : OrthonormalBasis (Fin r) ℝ E := b₀.reindex e
  have hoVolume : MeasureTheory.volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
    rw [MeasureTheory.measureReal_def]
    have hfd : MeasureTheory.volume (ZSpan.fundamentalDomain o.toBasis) = 1 := by
      rw [MeasureTheory.measure_congr
        (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis MeasureTheory.volume)]
      exact o.volume_parallelepiped
    rw [hfd]
    simp
  have hcov : ZLattice.covolume (Submodule.span ℤ (Set.range b)) = |o.toBasis.det b| := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain
      (Submodule.span ℤ (Set.range b)) MeasureTheory.volume
      (ZSpan.isAddFundamentalDomain b MeasureTheory.volume),
      ZSpan.measureReal_fundamentalDomain b MeasureTheory.volume o.toBasis, hoVolume, mul_one]
  rw [hcov, sq_abs, o.toBasis.det_apply]
  rw [Matrix.gram_eq_conjTranspose_mul o b, Matrix.det_mul, Matrix.det_conjTranspose]
  have hm : o.toBasis.toMatrix b = Matrix.of fun i j => o.repr (b j) i := by
    ext i j
    rfl
  rw [hm]
  simp [pow_two]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BasisImageSection
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem basis_projection_injective_of_minor {K E ι : Type*} [Field K]
    [AddCommGroup E] [Module K E] {k : ℕ}
    (b : Module.Basis (Fin k) K E) (P : E →ₗ[K] (ι → K)) (p : Fin k → ι)
    (hdet : (Matrix.of (fun i j => P (b j) (p i))).det ≠ 0) : Function.Injective P := by
  let B := Matrix.of (fun i j => P (b j) (p i))
  have hB : IsUnit B := B.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hdet)
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  have hxP : P x = 0 := hx
  have hcoord : B *ᵥ (fun j => b.repr x j) = 0 := by
    funext i
    have hs := congrArg (fun y => P y (p i)) (b.sum_repr x)
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs
    change (∑ j, B i j * b.repr x j) = 0
    calc
      _ = P x (p i) := by simpa only [B, Matrix.of_apply, mul_comm] using hs
      _ = 0 := congrFun hxP (p i)
  have hz : (fun j => b.repr x j) = 0 := Matrix.mulVec_injective_of_isUnit hB
    (hcoord.trans (Matrix.mulVec_zero B).symm)
  apply b.repr.injective
  simp only [map_zero]
  exact Finsupp.ext (fun j => congrFun hz j)

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem basis_coordinate_matrix_mulVec {K E ι : Type*} [Field K]
    [AddCommGroup E] [Module K E] {k : ℕ}
    (b : Module.Basis (Fin k) K E) (f : E →ₗ[K] (ι → K)) (x : E) :
    Matrix.of (fun i j => f (b j) i) *ᵥ (fun j => b.repr x j) = f x := by
  funext i
  have hs := congrArg (fun y => f y i) (b.sum_repr x)
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs
  simpa only [Matrix.mulVec, dotProduct, Matrix.of_apply, mul_comm] using hs

theorem basis_image_reconstruct_from_minor {K E ι : Type*} [Field K]
    [AddCommGroup E] [Module K E] {k : ℕ}
    (b : Module.Basis (Fin k) K E) (f : E →ₗ[K] (ι → K)) (p : Fin k → ι)
    (hp : (Matrix.of (fun i j => f (b j) (p i))).det ≠ 0) (x : E) :
    let F := Matrix.of (fun i j => f (b j) i)
    (F * (F.submatrix p id)⁻¹) *ᵥ (fun j => f x (p j)) = f x := by
  let F := Matrix.of (fun i j => f (b j) i)
  have hF : F *ᵥ (fun j => b.repr x j) = f x := basis_coordinate_matrix_mulVec b f x
  have hsub : (F.submatrix p id) *ᵥ (fun j => b.repr x j) = fun j => f x (p j) := by
    funext i
    exact congrFun hF (p i)
  have hp' : (F.submatrix p id).det ≠ 0 := hp
  change (F * (F.submatrix p id)⁻¹) *ᵥ (fun j => f x (p j)) = f x
  rw [← hsub, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul (F.submatrix p id) (isUnit_iff_ne_zero.mpr hp'), Matrix.mul_one]
  exact hF

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SpanSubsetBasis
namespace OAI

section

namespace Erdos3

open Module

theorem exists_basis_of_span_subset {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (S : Set E) :
    ∃ d : ℕ, ∃ b : Basis (Fin d) ℝ (Submodule.span ℝ S),
      d = finrank ℝ (Submodule.span ℝ S) ∧ ∀ i, (b i).val ∈ S := by
  classical
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent ℝ S
  let : Fintype s := hli.setFinite.fintype
  have he : Submodule.span ℝ (Set.range ((↑) : s → E)) = Submodule.span ℝ S := by
    simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using hspan
  let b₀ : Basis s ℝ (Submodule.span ℝ S) := (Basis.span hli).map (LinearEquiv.ofEq _ _ he)
  let b := b₀.reindex (Fintype.equivFin s)
  refine ⟨Fintype.card s, b, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using (finrank_eq_card_basis b).symm
  intro i
  have hb : (b i).val = ((Fintype.equivFin s).symm i).val := by
    simp only [b, Basis.reindex_apply, b₀, Basis.map_apply]
    exact Basis.coe_span_apply hli _
  rw [hb]
  exact hs ((Fintype.equivFin s).symm i).property

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeVoronoiPacking
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (Λ : Submodule ℤ E)

def latticeVoronoi : Set E := {x : E | ∀ z : Λ, ‖x‖ ≤ ‖x - z.val‖}

theorem exists_sub_mem_latticeVoronoi [DiscreteTopology Λ] (x : E) :
    ∃ z : Λ, x - z.val ∈ latticeVoronoi Λ := by
  have hclosed : IsClosed (Λ : Set E) :=
    (AddSubgroup.isClosed_of_discrete : IsClosed (Λ.toAddSubgroup : Set E))
  obtain ⟨z, hz, he⟩ := hclosed.exists_infDist_eq_dist ⟨0, Λ.zero_mem⟩ x
  refine ⟨⟨z, hz⟩, ?_⟩
  intro w
  have hnear := Metric.infDist_le_dist_of_mem (x := x) (Λ.add_mem hz w.property)
  rw [he, dist_eq_norm, dist_eq_norm] at hnear
  simpa only [sub_add_eq_sub_sub] using hnear

end Erdos3

end

section

namespace Erdos3

open Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (Λ : Submodule ℤ E) (R : ℝ)

def shortVectorSpan : Submodule ℝ E :=
  Submodule.span ℝ {x : E | x ∈ Λ ∧ ‖x‖ ≤ R}

noncomputable def shortVectorLattice : Submodule ℤ (shortVectorSpan Λ R) :=
  ZLattice.comap ℝ Λ (shortVectorSpan Λ R).subtype

omit [FiniteDimensional ℝ E] in
theorem mem_shortVectorSpan {x : E} (hx : x ∈ Λ) (hR : ‖x‖ ≤ R) :
    x ∈ shortVectorSpan Λ R := Submodule.subset_span ⟨hx, hR⟩

theorem exists_shortVectorSpan_basis :
    ∃ d : ℕ, ∃ b : Basis (Fin d) ℝ (shortVectorSpan Λ R),
      d = finrank ℝ (shortVectorSpan Λ R) ∧
      ∀ i, b i ∈ shortVectorLattice Λ R ∧ ‖b i‖ ≤ R := by
  obtain ⟨d, b, hd, hb⟩ := exists_basis_of_span_subset {x : E | x ∈ Λ ∧ ‖x‖ ≤ R}
  exact ⟨d, b, hd, hb⟩

instance shortVectorLattice_discrete [DiscreteTopology Λ] :
    DiscreteTopology (shortVectorLattice Λ R) :=
  ZLattice.comap_discreteTopology ℝ Λ continuous_subtype_val Subtype.val_injective

instance shortVectorLattice_full [DiscreteTopology Λ] : IsZLattice ℝ (shortVectorLattice Λ R) := by
  obtain ⟨d, b, _, hb⟩ := exists_shortVectorSpan_basis Λ R
  constructor
  apply top_unique
  calc
    ⊤ = Submodule.span ℝ (Set.range b) := b.span_eq.symm
    _ ≤ Submodule.span ℝ (shortVectorLattice Λ R : Set (shortVectorSpan Λ R)) := by
      apply Submodule.span_mono
      rintro x ⟨i, rfl⟩
      exact (hb i).1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoordinateMinorCovolume
namespace OAI

section

namespace Erdos3

open RealInnerProductSpace

theorem exterior_norm_eq_sqrt_gram {r : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (v : Fin r → E) :
    ‖exteriorPower.ιMulti ℝ r v‖ = Real.sqrt (Matrix.gram ℝ v).det := by
  have hs : ‖exteriorPower.ιMulti ℝ r v‖ ^ 2 = (Matrix.gram ℝ v).det := by
    rw [← real_inner_self_eq_norm_sq]
    exact exteriorPower.inner_ιMulti_self v
  rw [← hs, Real.sqrt_sq (norm_nonneg _)]

theorem abs_coordinate_det_le_sqrt_gram {r : ℕ} {ι : Type*} [Fintype ι]
    (v : Fin r → EuclideanSpace ℝ ι) (p : Fin r → ι) (hp : Function.Injective p) :
    |(Matrix.of (fun i j => v i (p j))).det| ≤ Real.sqrt (Matrix.gram ℝ v).det := by
  classical
  let e : Fin r → EuclideanSpace ℝ ι := fun i => EuclideanSpace.single (p i) 1
  let u := exteriorPower.ιMulti ℝ r e
  let w := exteriorPower.ιMulti ℝ r v
  have he : Orthonormal ℝ e := EuclideanSpace.orthonormal_single.comp p hp
  have hgram : Matrix.gram ℝ e = 1 := Matrix.gram_eq_one_iff_orthonormal.mpr he
  have hu : ‖u‖ = 1 := by
    have hs : ‖u‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq]
      change inner ℝ (exteriorPower.ιMulti ℝ r e) (exteriorPower.ιMulti ℝ r e) = 1
      rw [exteriorPower.inner_ιMulti_self, hgram, Matrix.det_one]
    nlinarith [norm_nonneg u]
  have hi : inner ℝ u w = (Matrix.of (fun i j => v i (p j))).det := by
    change inner ℝ (exteriorPower.ιMulti ℝ r e) (exteriorPower.ιMulti ℝ r v) = _
    rw [exteriorPower.inner_ιMulti_ιMulti]
    congr 1
    ext i j
    simp [e, EuclideanSpace.inner_single_left]
  have h := abs_real_inner_le_norm u w
  rw [hi, hu, one_mul] at h
  exact h.trans_eq (exterior_norm_eq_sqrt_gram v)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FiniteLatticeBasis
namespace OAI

section

namespace Erdos3

noncomputable def finiteLatticeBasis {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    Module.Basis (Fin (Module.finrank ℝ E)) ℤ Λ :=
  (Module.Free.chooseBasis ℤ Λ).reindex (Fintype.equivOfCardEq
    (by rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ, Fintype.card_fin]))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeCoordinateLifts
namespace OAI

section

namespace Erdos3

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype ι]
  (Λ : Submodule ℤ E) (π : E →ₗ[ℝ] (ι → ℝ))

def latticeImage : Submodule ℤ (ι → ℝ) := Λ.map (π.restrictScalars ℤ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.EuclideanHorizontalProjection
namespace OAI

section

namespace Erdos3

def euclideanHorizontalProjection {σ : Type*} {m : ℕ} (a : ℕ) (ha : a ≤ m) :
    EuclideanSpace ℝ (σ ⊕ Fin m) →ₗ[ℝ] (Fin a → ℝ) where
  toFun x i := x (Sum.inr (Fin.castLE ha i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem euclideanHorizontalProjection_apply {σ : Type*} {m : ℕ}
    (a : ℕ) (ha : a ≤ m) (x : EuclideanSpace ℝ (σ ⊕ Fin m)) (i : Fin a) :
    euclideanHorizontalProjection a ha x i = x (Sum.inr (Fin.castLE ha i)) := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DerivativeIndexBounds
namespace OAI

section

namespace Erdos3

theorem weighted_row_minor_det {m k : ℕ} (N : Matrix (Fin m) (Fin k) ℝ)
    (w : Fin m → ℝ) (p : Fin k → Fin m) :
    (Matrix.of (fun i j => w (p i) * N (p i) j)).det =
      (∏ i, w (p i)) * (N.submatrix p id).det := by
  have he : Matrix.of (fun i j => w (p i) * N (p i) j) =
      Matrix.diagonal (fun i => w (p i)) * N.submatrix p id := by
    ext i j
    simp [Matrix.diagonal_mul]
  rw [he, Matrix.det_mul, Matrix.det_diagonal]

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem lower_triangular_horizontal_row {m a : ℕ}
    (M : Matrix (Fin m) (Fin m) ℝ)
    (hM : ∀ i j, i < j → M i j = 0)
    (hblock : ∀ i j, i.val < a → j.val < a → M i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j)
    (i : Fin m) (hi : i.val < a) (j : Fin m) :
    M i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j := by
  by_cases hj : j.val < a
  · exact hblock i j hi hj
  · have hij : i < j := by omega
    rw [hM i j hij, Matrix.one_apply, if_neg (ne_of_lt hij)]

theorem lower_triangular_horizontal_mulVec {m a : ℕ}
    (M : Matrix (Fin m) (Fin m) ℝ)
    (hM : ∀ i j, i < j → M i j = 0)
    (hblock : ∀ i j, i.val < a → j.val < a → M i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j)
    (x : Fin m → ℝ) (i : Fin m) (hi : i.val < a) : (M *ᵥ x) i = x i := by
  calc
    _ = ((1 : Matrix (Fin m) (Fin m) ℝ) *ᵥ x) i := by
      simp only [Matrix.mulVec, dotProduct, lower_triangular_horizontal_row M hM hblock i hi]
    _ = x i := congrFun (Matrix.one_mulVec x) i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndependentColumnsMinor
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem independent_columns_of_nonzero_row_minor {K ι : Type*} [Field K] {k : ℕ}
    (Q : Matrix ι (Fin k) K) (p : Fin k → ι) (hp : (Q.submatrix p id).det ≠ 0) :
    LinearIndependent K Q.col := by
  apply Matrix.mulVec_injective_iff.mp
  intro x y hxy
  apply Matrix.mulVec_injective_of_isUnit
    ((Q.submatrix p id).isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hp))
  funext i
  exact congrFun hxy (p i)

theorem independent_columns_of_identity_minor {K ι : Type*} [Field K] {k : ℕ}
    (Q : Matrix ι (Fin k) K) (p : Fin k → ι) (hp : Q.submatrix p id = 1) :
    LinearIndependent K Q.col := by
  apply independent_columns_of_nonzero_row_minor Q p
  rw [hp, Matrix.det_one]
  exact one_ne_zero

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.NormalizedMinorCoordinates
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem row_normalization_entry {K ι : Type*} [Field K] {k : ℕ}
    (H : Matrix ι (Fin k) K) (p : Fin k → ι) (hp : (H.submatrix p id).det ≠ 0)
    (i : ι) (j : Fin k) :
    (H * (H.submatrix p id)⁻¹) i j =
      (H.submatrix (Function.update p j i) id).det / (H.submatrix p id).det := by
  have h := row_minor_update_det H p (H * (H.submatrix p id)⁻¹)
    (Matrix.nonsing_inv_mul_cancel_right (H.submatrix p id) H (isUnit_iff_ne_zero.mpr hp)) i j
  exact (eq_div_iff hp).mpr h.symm

theorem row_normalization_submatrix {K ι : Type*} [Field K] {k : ℕ}
    (H : Matrix ι (Fin k) K) (p : Fin k → ι) (hp : (H.submatrix p id).det ≠ 0) :
    (H * (H.submatrix p id)⁻¹).submatrix p id = 1 := by
  rw [Matrix.submatrix_mul H (H.submatrix p id)⁻¹ p id id Function.bijective_id,
    Matrix.submatrix_id_id]
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hp)

theorem row_normalization_col_span {K ι : Type*} [Field K] {k : ℕ}
    (H : Matrix ι (Fin k) K) (p : Fin k → ι) (hp : (H.submatrix p id).det ≠ 0) :
    Submodule.span K (Set.range (H * (H.submatrix p id)⁻¹).col) =
      Submodule.span K (Set.range H.col) := by
  let B := H.submatrix p id
  have hsurj : Function.Surjective B⁻¹.mulVecLin := by
    intro x
    refine ⟨B *ᵥ x, ?_⟩
    change B⁻¹ *ᵥ (B *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hp),
      Matrix.one_mulVec]
  rw [← Matrix.range_mulVecLin, ← Matrix.range_mulVecLin, Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hsurj)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedMinorBounds
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem row_normalization_abs_le {ι : Type*} {k : ℕ}
    (M : Matrix ι (Fin k) ℝ) (p : Fin k → ι)
    (hp : (M.submatrix p id).det ≠ 0) (C D : ℝ) (hD : 0 < D)
    (hminor : ∀ q : Fin k → ι, |(M.submatrix q id).det| ≤ C)
    (hlower : 1 / D ≤ |(M.submatrix p id).det|) (i : ι) (j : Fin k) :
    |(M * (M.submatrix p id)⁻¹) i j| ≤ C * D := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hminor p)
  calc
    _ = |(M.submatrix (Function.update p j i) id).det| /
        |(M.submatrix p id).det| := by rw [row_normalization_entry M p hp i j, abs_div]
    _ ≤ C / |(M.submatrix p id).det| :=
      div_le_div_of_nonneg_right (hminor _) (abs_nonneg _)
    _ ≤ C / (1 / D) := div_le_div_of_nonneg_left hC (one_div_pos.mpr hD) hlower
    _ = C * D := by rw [one_div, div_inv_eq_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerMinorNormalization
namespace OAI

section

namespace Erdos3

theorem integer_row_normalization_entry {ι : Type*} {k : ℕ}
    (Z : Matrix ι (Fin k) ℤ) (p : Fin k → ι) (hp : (Z.submatrix p id).det ≠ 0)
    (i : ι) (j : Fin k) :
    let H := Z.map (Int.castRingHom ℚ)
    (H * (H.submatrix p id)⁻¹) i j =
      ((Z.submatrix (Function.update p j i) id).det : ℚ) / ((Z.submatrix p id).det : ℚ) := by
  let H := Z.map (Int.castRingHom ℚ)
  have hdet (q : Fin k → ι) : (H.submatrix q id).det = ((Z.submatrix q id).det : ℚ) := by
    change ((Z.submatrix q id).map (Int.castRingHom ℚ)).det = _
    exact ((Int.castRingHom ℚ).map_det _).symm
  have hp' : (H.submatrix p id).det ≠ 0 := by rw [hdet]; exact_mod_cast hp
  change (H * (H.submatrix p id)⁻¹) i j = _
  calc
    _ = (H.submatrix (Function.update p j i) id).det / (H.submatrix p id).det :=
      row_normalization_entry H p hp' i j
    _ = _ := by rw [hdet, hdet]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PartitionedAffineLogEnvelope
namespace OAI

section

namespace Erdos3

section Definitions
variable {A : Type*} [Semiring A]
def affineMinorVariableEnvelope (D : A) : A := D * (D * (D + 1))
end Definitions

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.GridNormalizationDenominator
namespace OAI

section

namespace Erdos3

theorem scaled_integer_minor_eq {ι : Type*} {k : ℕ}
    (Z : Matrix ι (Fin k) ℤ) (H : Matrix ι (Fin k) ℝ) (t : ℝ)
    (hZ : Z.map (Int.castRingHom ℝ) = t • H) (p : Fin k → ι) :
    ((Z.submatrix p id).det : ℝ) = t ^ k * (H.submatrix p id).det := by
  calc
    _ = ((Z.submatrix p id).map (Int.castRingHom ℝ)).det :=
      (Int.castRingHom ℝ).map_det _
    _ = (t • H.submatrix p id).det := by
      congr 1
      ext i j
      exact congrArg (fun M : Matrix ι (Fin k) ℝ => M (p i) j) hZ
    _ = _ := by rw [Matrix.det_smul, Fintype.card_fin]

theorem scaled_integer_minor_natAbs_bound {ι : Type*} {k : ℕ}
    (Z : Matrix ι (Fin k) ℤ) (H : Matrix ι (Fin k) ℝ) (t C : ℝ) (ht : 0 < t)
    (hZ : Z.map (Int.castRingHom ℝ) = t • H)
    (hminor : ∀ p : Fin k → ι, |(H.submatrix p id).det| ≤ C) :
    ∀ p : Fin k → ι, (Z.submatrix p id).det.natAbs ≤ Nat.ceil (C * t ^ k) := by
  intro p
  have h : |((Z.submatrix p id).det : ℝ)| ≤ C * t ^ k := by
    rw [scaled_integer_minor_eq Z H t hZ, abs_mul, abs_of_pos (pow_pos ht _)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hminor p) (pow_pos ht k).le
  have hc := h.trans (Nat.le_ceil (C * t ^ k))
  apply (Nat.cast_le (α := ℝ)).mp
  simpa only [Nat.cast_natAbs, Int.cast_abs] using hc

end Erdos3

end

section

namespace Erdos3

theorem scaled_integer_row_normalization_cast {ι : Type*} {k : ℕ}
    (Z : Matrix ι (Fin k) ℤ) (H : Matrix ι (Fin k) ℝ) (t : ℝ) (ht : t ≠ 0)
    (hZ : Z.map (Int.castRingHom ℝ) = t • H)
    (p : Fin k → ι) (hp : (H.submatrix p id).det ≠ 0)
    (hZp : (Z.submatrix p id).det ≠ 0) :
    let W := Z.map (Int.castRingHom ℚ)
    (W * (W.submatrix p id)⁻¹).map (Rat.castHom ℝ) = H * (H.submatrix p id)⁻¹ := by
  dsimp only
  ext i j
  have he := integer_row_normalization_entry Z p hZp i j
  change (((Z.map (Int.castRingHom ℚ) *
    ((Z.map (Int.castRingHom ℚ)).submatrix p id)⁻¹) i j : ℚ) : ℝ) = _
  rw [he]
  simp only [Rat.cast_div, Rat.cast_intCast]
  rw [scaled_integer_minor_eq Z H t hZ, scaled_integer_minor_eq Z H t hZ]
  rw [row_normalization_entry H p hp i j]
  field_simp

end Erdos3

end

end OAI
end


