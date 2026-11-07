-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
-- name    : QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:32:58.542926+00:00
-- url     : https://prove2.me/theorems/50bf11e0-b302-4d6a-a5a1-bd160a33c66e
-- title:
--   Universal Building Spectrum
-- statement:
--   Definitions and structural lemmas for Universal Building Spectrum, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/UniversalBuildingSpectrum.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.MetricSpace.Bounded
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_three
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalDoubleCoset_rankFour_one_inv
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalDoubleCoset_rankFour_three_inv
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalDoubleCoset_rankFour_two_inv
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalDoubleCoset_rankThree_one_inv
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalDoubleCoset_rankThree_two_inv
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourFundamentalHeckeAlgEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankThreeFundamentalHeckeAlgEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_three
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankFour_two
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankThree_one
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.HeckeFunction.star_fundamentalHeckeFunction_rankThree_two
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.coe_uniformizerUnit
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.diagonalGeneralLinear_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourFundamentalHeckeAlgEquiv_apply
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankFourSecondCompoundGeneralLinear_inv_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.SphericalHecke.rankThreeFundamentalHeckeAlgEquiv_apply


set_option autoImplicit false
noncomputable section
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups LocalTopology Pointwise lp ENNReal InnerProduct
open HeckeFunction MeasureTheory
universe u v
noncomputable def l2ReindexLinearIsometry {α : Type u} {β : Type v}
    (e : α ≃ β) :
    lp (fun _ : α ↦ ℂ) 2 →ₗᵢ[ℂ] lp (fun _ : β ↦ ℂ) 2 where
  toFun f := ⟨fun b ↦ f (e.symm b), by
    show Memℓp (fun b ↦ f (e.symm b)) 2
    rw [memℓp_gen_iff (by norm_num)]
    exact e.symm.summable_iff.mpr ((lp.memℓp f).summable (by norm_num))⟩
  map_add' f g := by
    apply lp.ext
    funext b
    rfl
  map_smul' c f := by
    apply lp.ext
    funext b
    rfl
  norm_map' f := by
    rw [lp.norm_eq_tsum_rpow (by norm_num),
      lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact e.symm.tsum_eq (fun a ↦ ‖f a‖ ^ ((2 : ℝ≥0∞).toReal))
@[simp]
theorem l2ReindexLinearIsometry_apply {α : Type u} {β : Type v}
    (e : α ≃ β) (f : lp (fun _ : α ↦ ℂ) 2) (b : β) :
    l2ReindexLinearIsometry e f b = f (e.symm b) :=
  rfl
abbrev BuildingL2 (k : Type u) [Field k] [Finite k] (d : ℕ) :=
  lp (fun _ : BuildingVertex k d ↦ ℂ) 2
noncomputable def buildingL2Translation
    (k : Type u) [Field k] [Finite k] (d : ℕ)
    (g : HeckeGroup k d) :
    BuildingL2 k d →ₗᵢ[ℂ] BuildingL2 k d :=
  l2ReindexLinearIsometry (MulAction.toPerm g)
@[simp]
theorem buildingL2Translation_apply
    (k : Type u) [Field k] [Finite k] (d : ℕ)
    (g : HeckeGroup k d) (f : BuildingL2 k d)
    (x : BuildingVertex k d) :
    buildingL2Translation k d g f x = f (g⁻¹ • x) := by
  rfl
@[simp]
theorem buildingVertex_out_smul_base
    (k : Type u) [Field k] [Finite k] (d : ℕ)
    (x : BuildingVertex k d) :
    x.out • (QuotientGroup.mk 1 : BuildingVertex k d) = x := by
  rw [MulAction.Quotient.smul_mk]
  change QuotientGroup.mk (x.out * 1) = x
  simpa only [mul_one] using x.out_eq'
noncomputable def fundamentalNeighborAdjacentEquiv
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (x : BuildingVertex k d) :
    {q // q ∈ fundamentalNeighborCosets k d r} ≃
      {y // ColoredBuildingAdjacent k d r x y} where
  toFun q := ⟨x.out • q.1, by
    have hbase := (fundamentalNeighborAdjacentBaseEquiv k d r q).2
    have hsmul := (coloredBuildingAdjacent_smul_iff k d r x.out
      (QuotientGroup.mk 1 : BuildingVertex k d) q.1).2 hbase
    simpa only [buildingVertex_out_smul_base] using hsmul⟩
  invFun y := ⟨x.out⁻¹ • y.1, by
    have hsmul := (coloredBuildingAdjacent_smul_iff k d r x.out⁻¹
      x y.1).2 y.2
    have hbase : x.out⁻¹ • x =
        (QuotientGroup.mk 1 : BuildingVertex k d) := by
      calc
        x.out⁻¹ • x = x.out⁻¹ •
            (x.out • (QuotientGroup.mk 1 : BuildingVertex k d)) := by
          exact congrArg (fun z : BuildingVertex k d ↦ x.out⁻¹ • z)
            (buildingVertex_out_smul_base k d x).symm
        _ = QuotientGroup.mk 1 :=
          inv_smul_smul x.out (QuotientGroup.mk 1 : BuildingVertex k d)
    have hadj : ColoredBuildingAdjacent k d r
        (QuotientGroup.mk 1) (x.out⁻¹ • y.1) := by
      exact hbase ▸ hsmul
    exact (fundamentalNeighborAdjacentBaseEquiv k d r).symm
      ⟨x.out⁻¹ • y.1, hadj⟩ |>.2⟩
  left_inv q := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp
noncomputable instance coloredBuildingNeighborFintype
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (x : BuildingVertex k d) :
    Fintype {y // ColoredBuildingAdjacent k d r x y} :=
  Fintype.ofEquiv {q // q ∈ fundamentalNeighborCosets k d r}
    (fundamentalNeighborAdjacentEquiv k d r x)
theorem card_coloredBuildingNeighbors
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (x : BuildingVertex k d) :
    Fintype.card {y // ColoredBuildingAdjacent k d r x y} =
      coloredAdjacencyDegree k d r := by
  rw [← Fintype.card_congr (fundamentalNeighborAdjacentEquiv k d r x)]
  simp [coloredAdjacencyDegree]
theorem coloredBuildingAdjacent_reverse_iff_of_inv
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s)
    (x y : BuildingVertex k d) :
    ColoredBuildingAdjacent k d r x y ↔
      ColoredBuildingAdjacent k d s y x := by
  constructor
  · rintro ⟨gx, gy, rfl, rfl, hxy⟩
    refine ⟨gy, gx, rfl, rfl, ?_⟩
    have hinv : (gx⁻¹ * gy)⁻¹ ∈
        (fundamentalDoubleCoset k d r)⁻¹ := by
      simpa
    rw [hset] at hinv
    simpa using hinv
  · rintro ⟨gy, gx, rfl, rfl, hyx⟩
    refine ⟨gx, gy, rfl, rfl, ?_⟩
    have hinv : (gy⁻¹ * gx)⁻¹ ∈
        (fundamentalDoubleCoset k d s)⁻¹ := by
      simpa
    have hsetInv : (fundamentalDoubleCoset k d s)⁻¹ =
        fundamentalDoubleCoset k d r := by
      rw [← hset]
      simp
    rw [hsetInv] at hinv
    simpa using hinv
noncomputable def buildingColoredNeighborSum
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (f : BuildingVertex k d → ℂ) (x : BuildingVertex k d) : ℂ :=
  ∑ y : {y // ColoredBuildingAdjacent k d r x y}, f y
abbrev ColoredBuildingEdge
    (k : Type u) [Field k] [Finite k] (d r : ℕ) :=
  Σ x : BuildingVertex k d,
    {y // ColoredBuildingAdjacent k d r x y}
noncomputable def coloredBuildingEdgeReverseEquiv
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s) :
    ColoredBuildingEdge k d r ≃ ColoredBuildingEdge k d s where
  toFun e := ⟨e.2.1, ⟨e.1,
    (coloredBuildingAdjacent_reverse_iff_of_inv
      k d r s hset e.1 e.2.1).1 e.2.2⟩⟩
  invFun e := ⟨e.2.1, ⟨e.1,
    (coloredBuildingAdjacent_reverse_iff_of_inv
      k d r s hset e.2.1 e.1).2 e.2.2⟩⟩
  left_inv e := by
    rcases e with ⟨x, ⟨y, hy⟩⟩
    rfl
  right_inv e := by
    rcases e with ⟨x, ⟨y, hy⟩⟩
    rfl
theorem summable_norm_sq_coloredBuildingEdge_source
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (f : BuildingL2 k d) :
    Summable (fun e : ColoredBuildingEdge k d r ↦ ‖f e.1‖ ^ 2) := by
  rw [summable_sigma_of_nonneg (fun _ ↦ sq_nonneg _)]
  constructor
  · intro x
    exact Summable.of_finite
  · have hf : Summable (fun x : BuildingVertex k d ↦ ‖f x‖ ^ 2) := by
      simpa using (lp.memℓp f).summable (by norm_num)
    have hfun : (fun x : BuildingVertex k d ↦
        ∑' _y : {y // ColoredBuildingAdjacent k d r x y}, ‖f x‖ ^ 2) =
        fun x ↦ (coloredAdjacencyDegree k d r : ℝ) * ‖f x‖ ^ 2 := by
      funext x
      rw [tsum_fintype]
      simp [card_coloredBuildingNeighbors]
    rw [hfun]
    exact hf.mul_left _
theorem tsum_norm_sq_coloredBuildingEdge_source
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (f : BuildingL2 k d) :
    (∑' e : ColoredBuildingEdge k d r, ‖f e.1‖ ^ 2) =
      (coloredAdjacencyDegree k d r : ℝ) * ‖f‖ ^ 2 := by
  rw [(summable_norm_sq_coloredBuildingEdge_source k d r f).tsum_sigma]
  simp_rw [tsum_fintype]
  have hinner : (fun x : BuildingVertex k d ↦
      ∑ _y : {y // ColoredBuildingAdjacent k d r x y}, ‖f x‖ ^ 2) =
      fun x ↦ (coloredAdjacencyDegree k d r : ℝ) * ‖f x‖ ^ 2 := by
    funext x
    simp [card_coloredBuildingNeighbors]
  rw [hinner, tsum_mul_left]
  congr 1
  simpa using (lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) f).symm
theorem summable_norm_sq_coloredBuildingEdge_target_of_inv
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s)
    (f : BuildingL2 k d) :
    Summable (fun e : ColoredBuildingEdge k d r ↦ ‖f e.2.1‖ ^ 2) := by
  let e := coloredBuildingEdgeReverseEquiv k d r s hset
  have hs := summable_norm_sq_coloredBuildingEdge_source k d s f
  exact (e.summable_iff.mpr hs).congr (fun _ => rfl)
theorem tsum_norm_sq_coloredBuildingEdge_target_of_inv
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s)
    (f : BuildingL2 k d) :
    (∑' e : ColoredBuildingEdge k d r, ‖f e.2.1‖ ^ 2) =
      (coloredAdjacencyDegree k d s : ℝ) * ‖f‖ ^ 2 := by
  let e := coloredBuildingEdgeReverseEquiv k d r s hset
  calc
    (∑' a : ColoredBuildingEdge k d r, ‖f a.2.1‖ ^ 2) =
        ∑' b : ColoredBuildingEdge k d s, ‖f b.1‖ ^ 2 := by
      simpa [e, coloredBuildingEdgeReverseEquiv] using
        (e.tsum_eq (fun b : ColoredBuildingEdge k d s ↦ ‖f b.1‖ ^ 2))
    _ = (coloredAdjacencyDegree k d s : ℝ) * ‖f‖ ^ 2 :=
      tsum_norm_sq_coloredBuildingEdge_source k d s f
theorem norm_buildingColoredNeighborSum_sq_le
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (f : BuildingVertex k d → ℂ) (x : BuildingVertex k d) :
    ‖buildingColoredNeighborSum k d r f x‖ ^ 2 ≤
      (coloredAdjacencyDegree k d r : ℝ) *
        ∑ y : {y // ColoredBuildingAdjacent k d r x y}, ‖f y‖ ^ 2 := by
  calc
    ‖buildingColoredNeighborSum k d r f x‖ ^ 2 ≤
        (∑ y : {y // ColoredBuildingAdjacent k d r x y}, ‖f y‖) ^ 2 := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (Fintype.card {y // ColoredBuildingAdjacent k d r x y} : ℝ) *
        ∑ y : {y // ColoredBuildingAdjacent k d r x y}, ‖f y‖ ^ 2 := by
      simpa using
        (sq_sum_le_card_mul_sum_sq
          (s := Finset.univ)
          (f := fun y : {y // ColoredBuildingAdjacent k d r x y} ↦ ‖f y‖))
    _ = (coloredAdjacencyDegree k d r : ℝ) *
        ∑ y : {y // ColoredBuildingAdjacent k d r x y}, ‖f y‖ ^ 2 := by
      rw [card_coloredBuildingNeighbors]
theorem buildingColoredNeighborSum_memLp_of_inv
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s)
    (f : BuildingL2 k d) :
    Memℓp (buildingColoredNeighborSum k d r f) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  have hedge :=
    summable_norm_sq_coloredBuildingEdge_target_of_inv k d r s hset f
  have houter : Summable (fun x : BuildingVertex k d ↦
      ∑ y : {y // ColoredBuildingAdjacent k d r x y}, ‖f y‖ ^ 2) := by
    have hsigma := (summable_sigma_of_nonneg
      (f := fun e : ColoredBuildingEdge k d r ↦ ‖f e.2.1‖ ^ 2)
      (fun _ ↦ sq_nonneg _)).mp hedge
    simpa only [tsum_fintype] using hsigma.2
  have hmajor : Summable (fun x : BuildingVertex k d ↦
      (coloredAdjacencyDegree k d r : ℝ) *
        ∑ y : {y // ColoredBuildingAdjacent k d r x y}, ‖f y‖ ^ 2) :=
    houter.mul_left _
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    hmajor.of_nonneg_of_le
    (fun x ↦ sq_nonneg _)
    (fun x ↦ norm_buildingColoredNeighborSum_sq_le k d r f x)
noncomputable def buildingColoredAdjacencyLinearMapOfInv
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s) :
    BuildingL2 k d →ₗ[ℂ] BuildingL2 k d where
  toFun f := ⟨buildingColoredNeighborSum k d r f,
    buildingColoredNeighborSum_memLp_of_inv k d r s hset f⟩
  map_add' f g := by
    apply lp.ext
    funext x
    change (∑ y : {y // ColoredBuildingAdjacent k d r x y},
      (f y + g y)) =
        (∑ y : {y // ColoredBuildingAdjacent k d r x y}, f y) +
          ∑ y : {y // ColoredBuildingAdjacent k d r x y}, g y
    exact Finset.sum_add_distrib
  map_smul' c f := by
    apply lp.ext
    funext x
    change (∑ y : {y // ColoredBuildingAdjacent k d r x y},
      c * f y) = c * ∑ y : {y // ColoredBuildingAdjacent k d r x y}, f y
    rw [Finset.mul_sum]
@[simp]
theorem buildingColoredAdjacencyLinearMapOfInv_apply_apply
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s)
    (f : BuildingL2 k d) (x : BuildingVertex k d) :
    buildingColoredAdjacencyLinearMapOfInv k d r s hset f x =
      ∑ y : {y // ColoredBuildingAdjacent k d r x y}, f y :=
  rfl
theorem norm_buildingColoredAdjacencyLinearMapOfInv_sq_le
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s)
    (f : BuildingL2 k d) :
    ‖buildingColoredAdjacencyLinearMapOfInv k d r s hset f‖ ^ 2 ≤
      (coloredAdjacencyDegree k d r : ℝ) *
        (coloredAdjacencyDegree k d s : ℝ) * ‖f‖ ^ 2 := by
  let A := buildingColoredAdjacencyLinearMapOfInv k d r s hset
  have hout : Summable (fun x : BuildingVertex k d ↦ ‖A f x‖ ^ 2) := by
    simpa using (lp.memℓp (A f)).summable (by norm_num)
  have hedge :=
    summable_norm_sq_coloredBuildingEdge_target_of_inv k d r s hset f
  have houter : Summable (fun x : BuildingVertex k d ↦
      ∑ y : {y // ColoredBuildingAdjacent k d r x y}, ‖f y‖ ^ 2) := by
    have hsigma := (summable_sigma_of_nonneg
      (f := fun e : ColoredBuildingEdge k d r ↦ ‖f e.2.1‖ ^ 2)
      (fun _ ↦ sq_nonneg _)).mp hedge
    simpa only [tsum_fintype] using hsigma.2
  have hmajor : Summable (fun x : BuildingVertex k d ↦
      (coloredAdjacencyDegree k d r : ℝ) *
        ∑ y : {y // ColoredBuildingAdjacent k d r x y}, ‖f y‖ ^ 2) :=
    houter.mul_left _
  calc
    ‖A f‖ ^ 2 = ∑' x : BuildingVertex k d, ‖A f x‖ ^ 2 := by
      simpa using lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (A f)
    _ ≤ ∑' x : BuildingVertex k d,
        (coloredAdjacencyDegree k d r : ℝ) *
          ∑ y : {y // ColoredBuildingAdjacent k d r x y}, ‖f y‖ ^ 2 := by
      exact hout.tsum_le_tsum
        (fun x ↦ norm_buildingColoredNeighborSum_sq_le k d r f x) hmajor
    _ = (coloredAdjacencyDegree k d r : ℝ) *
        ∑' e : ColoredBuildingEdge k d r, ‖f e.2.1‖ ^ 2 := by
      rw [tsum_mul_left]
      congr 1
      exact (hedge.tsum_sigma.trans (tsum_congr fun x ↦ by
        rw [tsum_fintype])).symm
    _ = (coloredAdjacencyDegree k d r : ℝ) *
        ((coloredAdjacencyDegree k d s : ℝ) * ‖f‖ ^ 2) := by
      rw [tsum_norm_sq_coloredBuildingEdge_target_of_inv k d r s hset f]
    _ = (coloredAdjacencyDegree k d r : ℝ) *
        (coloredAdjacencyDegree k d s : ℝ) * ‖f‖ ^ 2 := by ring
theorem norm_buildingColoredAdjacencyLinearMapOfInv_le
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s)
    (f : BuildingL2 k d) :
    ‖buildingColoredAdjacencyLinearMapOfInv k d r s hset f‖ ≤
      Real.sqrt ((coloredAdjacencyDegree k d r : ℝ) *
        coloredAdjacencyDegree k d s) * ‖f‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)), mul_pow,
    Real.sq_sqrt (mul_nonneg (by positivity) (by positivity))]
  exact norm_buildingColoredAdjacencyLinearMapOfInv_sq_le
    k d r s hset f
noncomputable def buildingColoredAdjacencyOperatorOfInv
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s) :
    BuildingL2 k d →L[ℂ] BuildingL2 k d :=
  (buildingColoredAdjacencyLinearMapOfInv k d r s hset).mkContinuous
    (Real.sqrt ((coloredAdjacencyDegree k d r : ℝ) *
      coloredAdjacencyDegree k d s))
    (norm_buildingColoredAdjacencyLinearMapOfInv_le k d r s hset)
@[simp]
theorem buildingColoredAdjacencyOperatorOfInv_apply_apply
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s)
    (f : BuildingL2 k d) (x : BuildingVertex k d) :
    buildingColoredAdjacencyOperatorOfInv k d r s hset f x =
      ∑ y : {y // ColoredBuildingAdjacent k d r x y}, f y :=
  rfl
noncomputable def rankThreeBuildingAdjacencyOne
    (k : Type u) [Field k] [Finite k] :
    BuildingL2 k 3 →L[ℂ] BuildingL2 k 3 :=
  buildingColoredAdjacencyOperatorOfInv k 3 1 2
    (fundamentalDoubleCoset_rankThree_one_inv k)
noncomputable def rankThreeBuildingAdjacencyTwo
    (k : Type u) [Field k] [Finite k] :
    BuildingL2 k 3 →L[ℂ] BuildingL2 k 3 :=
  buildingColoredAdjacencyOperatorOfInv k 3 2 1
    (fundamentalDoubleCoset_rankThree_two_inv k)
noncomputable def rankFourBuildingAdjacencyOne
    (k : Type u) [Field k] [Finite k] :
    BuildingL2 k 4 →L[ℂ] BuildingL2 k 4 :=
  buildingColoredAdjacencyOperatorOfInv k 4 1 3
    (fundamentalDoubleCoset_rankFour_one_inv k)
noncomputable def rankFourBuildingAdjacencyTwo
    (k : Type u) [Field k] [Finite k] :
    BuildingL2 k 4 →L[ℂ] BuildingL2 k 4 :=
  buildingColoredAdjacencyOperatorOfInv k 4 2 2
    (fundamentalDoubleCoset_rankFour_two_inv k)
noncomputable def rankFourBuildingAdjacencyThree
    (k : Type u) [Field k] [Finite k] :
    BuildingL2 k 4 →L[ℂ] BuildingL2 k 4 :=
  buildingColoredAdjacencyOperatorOfInv k 4 3 1
    (fundamentalDoubleCoset_rankFour_three_inv k)
@[simp]
theorem rankThreeBuildingAdjacencyOne_apply
    (k : Type u) [Field k] [Finite k]
    (f : BuildingL2 k 3) (x : BuildingVertex k 3) :
    rankThreeBuildingAdjacencyOne k f x =
      ∑ y : {y // ColoredBuildingAdjacent k 3 1 x y}, f y :=
  rfl
@[simp]
theorem rankThreeBuildingAdjacencyTwo_apply
    (k : Type u) [Field k] [Finite k]
    (f : BuildingL2 k 3) (x : BuildingVertex k 3) :
    rankThreeBuildingAdjacencyTwo k f x =
      ∑ y : {y // ColoredBuildingAdjacent k 3 2 x y}, f y :=
  rfl
@[simp]
theorem rankFourBuildingAdjacencyOne_apply
    (k : Type u) [Field k] [Finite k]
    (f : BuildingL2 k 4) (x : BuildingVertex k 4) :
    rankFourBuildingAdjacencyOne k f x =
      ∑ y : {y // ColoredBuildingAdjacent k 4 1 x y}, f y :=
  rfl
@[simp]
theorem rankFourBuildingAdjacencyTwo_apply
    (k : Type u) [Field k] [Finite k]
    (f : BuildingL2 k 4) (x : BuildingVertex k 4) :
    rankFourBuildingAdjacencyTwo k f x =
      ∑ y : {y // ColoredBuildingAdjacent k 4 2 x y}, f y :=
  rfl
@[simp]
theorem rankFourBuildingAdjacencyThree_apply
    (k : Type u) [Field k] [Finite k]
    (f : BuildingL2 k 4) (x : BuildingVertex k 4) :
    rankFourBuildingAdjacencyThree k f x =
      ∑ y : {y // ColoredBuildingAdjacent k 4 3 x y}, f y :=
  rfl
noncomputable def coloredBuildingEdgeSourceL2
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (f : BuildingL2 k d) :
  lp (fun _ : ColoredBuildingEdge k d r ↦ ℂ) 2 :=
  ⟨fun e ↦ f e.1, by
    show Memℓp (fun e : ColoredBuildingEdge k d r ↦ f e.1) 2
    rw [memℓp_gen_iff (by norm_num)]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      summable_norm_sq_coloredBuildingEdge_source k d r f⟩
noncomputable def coloredBuildingEdgeTargetL2OfInv
    (k : Type u) [Field k] [Finite k] (d r s : ℕ)
    (hset : (fundamentalDoubleCoset k d r)⁻¹ =
      fundamentalDoubleCoset k d s)
    (f : BuildingL2 k d) :
  lp (fun _ : ColoredBuildingEdge k d r ↦ ℂ) 2 :=
  ⟨fun e ↦ f e.2.1, by
    show Memℓp (fun e : ColoredBuildingEdge k d r ↦ f e.2.1) 2
    rw [memℓp_gen_iff (by norm_num)]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      summable_norm_sq_coloredBuildingEdge_target_of_inv k d r s hset f⟩
noncomputable def buildingVertexDelta
    (k : Type u) [Field k] [Finite k] (d : ℕ)
    (z : BuildingVertex k d) : BuildingL2 k d := by
  classical
  exact lp.single 2 z (1 : ℂ)
noncomputable def rankThreeBuildingAdjacencyFamily
    (k : Type u) [Field k] [Finite k] :
    Fin 2 → (BuildingL2 k 3 →L[ℂ] BuildingL2 k 3) :=
  ![rankThreeBuildingAdjacencyOne k, rankThreeBuildingAdjacencyTwo k]
noncomputable def rankFourBuildingAdjacencyFamily
    (k : Type u) [Field k] [Finite k] :
    Fin 3 → (BuildingL2 k 4 →L[ℂ] BuildingL2 k 4) :=
  ![rankFourBuildingAdjacencyOne k, rankFourBuildingAdjacencyTwo k,
    rankFourBuildingAdjacencyThree k]
def jointApproximatePointSpectrum
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ι → (E →L[ℂ] E)) : Set (ι → ℂ) :=
  {a | ∀ ε : ℝ, 0 < ε → ∃ v : E, ‖v‖ = 1 ∧
    ∀ i, ‖A i v - a i • v‖ < ε}
abbrev RankThreeBuildingJointApproximateSpectrum
    (k : Type u) [Field k] [Finite k] : Set (Fin 2 → ℂ) :=
  jointApproximatePointSpectrum (rankThreeBuildingAdjacencyFamily k)
abbrev RankFourBuildingJointApproximateSpectrum
    (k : Type u) [Field k] [Finite k] : Set (Fin 3 → ℂ) :=
  jointApproximatePointSpectrum (rankFourBuildingAdjacencyFamily k)
end QEC.Coding.HighDimensionalExpander.SphericalHecke


