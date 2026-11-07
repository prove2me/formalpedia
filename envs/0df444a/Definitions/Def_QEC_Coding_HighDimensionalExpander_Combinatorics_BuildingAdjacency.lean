-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
-- name    : QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T12:31:38.765581+00:00
-- url     : https://prove2.me/theorems/5b9f3075-906e-4eb9-abd9-89d0c92815cd
-- title:
--   Building Adjacency
-- statement:
--   Definitions and structural lemmas for Building Adjacency, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Combinatorics/BuildingAdjacency.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHeckeGenerators
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_three
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankFour_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_HeckeFunction_star_fundamentalHeckeFunction_rankThree_two
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_coe_uniformizerUnit
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_diagonalGeneralLinear_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalDoubleCoset_isCompact
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_fundamentalIntegralConjugate_det_localUnitOrder_eq_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_left_mul_mem_fundamentalDoubleCoset
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_maximalCompact_eq_range_powerSeriesProjectiveMap
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_mk_powerSeriesGeneralLinearToLocal_mem_maximalCompact
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_projective_mk_mem_maximalCompact_iff_integral
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourFundamentalHeckeAlgEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankFourSecondCompoundGeneralLinear_inv_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_rankThreeFundamentalHeckeAlgEquiv_apply
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_residueFundamentalPlane_eq_iff_integralConjugate
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_residueFundamentalPlane_surjective
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_SphericalHecke_right_mul_mem_fundamentalDoubleCoset
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
open scoped MatrixGroups LocalTopology Pointwise
open HeckeFunction
universe u
abbrev BuildingVertex (k : Type u) [Field k] [Finite k] (d : ℕ) :=
  HeckeGroup k d ⧸ maximalCompact k d
noncomputable instance buildingVertexDiscreteTopology
    (k : Type u) [Field k] [Finite k] (d : ℕ) :
    DiscreteTopology (BuildingVertex k d) :=
  QuotientGroup.discreteTopology_iff.mpr (maximalCompact_isOpen k d)
def ColoredBuildingAdjacent
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (x y : BuildingVertex k d) : Prop :=
  ∃ gx gy : HeckeGroup k d,
    QuotientGroup.mk gx = x ∧ QuotientGroup.mk gy = y ∧
      gx⁻¹ * gy ∈ fundamentalDoubleCoset k d r
theorem coloredBuildingAdjacent_mk_iff
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (gx gy : HeckeGroup k d) :
    ColoredBuildingAdjacent k d r (QuotientGroup.mk gx) (QuotientGroup.mk gy) ↔
      gx⁻¹ * gy ∈ fundamentalDoubleCoset k d r := by
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩
    have hka : a⁻¹ * gx ∈ maximalCompact k d := QuotientGroup.eq.mp ha
    have hkb : b⁻¹ * gy ∈ maximalCompact k d := QuotientGroup.eq.mp hb
    have hleft := left_mul_mem_fundamentalDoubleCoset k d r
      ((maximalCompact k d).inv_mem hka) hab
    have hboth := right_mul_mem_fundamentalDoubleCoset k d r hkb hleft
    simpa [mul_assoc] using hboth
  · intro h
    exact ⟨gx, gy, rfl, rfl, h⟩
theorem coloredBuildingAdjacent_smul_iff
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (g : HeckeGroup k d) (x y : BuildingVertex k d) :
    ColoredBuildingAdjacent k d r (g • x) (g • y) ↔
      ColoredBuildingAdjacent k d r x y := by
  induction x using QuotientGroup.induction_on with
  | _ a =>
      induction y using QuotientGroup.induction_on with
      | _ b =>
          rw [MulAction.Quotient.smul_mk,
            MulAction.Quotient.smul_mk,
            coloredBuildingAdjacent_mk_iff,
            coloredBuildingAdjacent_mk_iff]
          simp [smul_eq_mul, mul_assoc]
abbrev ColorOneReachable
    (k : Type u) [Field k] [Finite k] (d : ℕ)
    (x y : BuildingVertex k d) : Prop :=
  Relation.ReflTransGen (ColoredBuildingAdjacent k d 1) x y
def fundamentalNeighborCosetSet
    (k : Type u) [Field k] [Finite k] (d r : ℕ) :
    Set (BuildingVertex k d) :=
  QuotientGroup.mk '' fundamentalDoubleCoset k d r
theorem fundamentalNeighborCosetSet_finite
    (k : Type u) [Field k] [Finite k] (d r : ℕ) :
    (fundamentalNeighborCosetSet k d r).Finite := by
  apply IsCompact.finite_of_discrete
  exact (fundamentalDoubleCoset_isCompact k d r).image
    QuotientGroup.continuous_mk
noncomputable def fundamentalNeighborCosets
    (k : Type u) [Field k] [Finite k] (d r : ℕ) :
    Finset (BuildingVertex k d) :=
  (fundamentalNeighborCosetSet_finite k d r).toFinset
@[simp]
theorem mem_fundamentalNeighborCosets
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (x : BuildingVertex k d) :
    x ∈ fundamentalNeighborCosets k d r ↔
      x ∈ fundamentalNeighborCosetSet k d r := by
  simp [fundamentalNeighborCosets]
theorem mem_fundamentalNeighborCosetSet_iff_adjacent_base
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (x : BuildingVertex k d) :
    x ∈ fundamentalNeighborCosetSet k d r ↔
      ColoredBuildingAdjacent k d r (QuotientGroup.mk 1) x := by
  induction x using QuotientGroup.induction_on with
  | _ g =>
      rw [coloredBuildingAdjacent_mk_iff]
      simp only [inv_one, one_mul]
      constructor
      · rintro ⟨t, ht, htg⟩
        have hright : t⁻¹ * g ∈ maximalCompact k d :=
          QuotientGroup.eq.mp htg
        have hmem := right_mul_mem_fundamentalDoubleCoset k d r hright ht
        simpa [mul_assoc] using hmem
      · intro hg
        exact ⟨g, hg, rfl⟩
noncomputable def coloredNeighborSmuEquiv
    (k : Type u) [Field k] [Finite k] (d r : ℕ)
    (g : HeckeGroup k d) (x : BuildingVertex k d) :
    {q // ColoredBuildingAdjacent k d r x q} ≃
      {q // ColoredBuildingAdjacent k d r (g • x) q} where
  toFun q := ⟨g • q.1,
    (coloredBuildingAdjacent_smul_iff k d r g x q.1).2 q.2⟩
  invFun q := ⟨g⁻¹ • q.1, by
    have h := (coloredBuildingAdjacent_smul_iff
      k d r g⁻¹ (g • x) q.1).2 q.2
    simpa using h⟩
  left_inv q := by
    apply Subtype.ext
    simp
  right_inv q := by
    apply Subtype.ext
    simp
noncomputable def fundamentalNeighborAdjacentBaseEquiv
    (k : Type u) [Field k] [Finite k] (d r : ℕ) :
    {q // q ∈ fundamentalNeighborCosets k d r} ≃
      {q // ColoredBuildingAdjacent k d r (QuotientGroup.mk 1) q} where
  toFun q := ⟨q.1,
    (mem_fundamentalNeighborCosetSet_iff_adjacent_base k d r q.1).1
      ((mem_fundamentalNeighborCosets k d r q.1).1 q.2)⟩
  invFun q := ⟨q.1,
    (mem_fundamentalNeighborCosets k d r q.1).2
      ((mem_fundamentalNeighborCosetSet_iff_adjacent_base k d r q.1).2
        q.2)⟩
  left_inv q := by rfl
  right_inv q := by rfl
def coloredAdjacencyDegree
    (k : Type u) [Field k] [Finite k] (d r : ℕ) : ℕ :=
  (fundamentalNeighborCosets k d r).card
def integralFundamentalNeighbor
    (k : Type*) [Field k] [Finite k] (d r : ℕ)
    (g : GL (Fin d) (IntegerRing k)) : BuildingVertex k d :=
  QuotientGroup.mk
    (powerSeriesProjectiveMap k d g * fundamentalCoweight k d r)
theorem integralFundamentalNeighbor_mem
    (k : Type*) [Field k] [Finite k] (d r : ℕ)
    (g : GL (Fin d) (IntegerRing k)) :
    integralFundamentalNeighbor k d r g ∈
      fundamentalNeighborCosets k d r := by
  rw [mem_fundamentalNeighborCosets]
  refine ⟨powerSeriesProjectiveMap k d g * fundamentalCoweight k d r, ?_, rfl⟩
  rw [fundamentalDoubleCoset, Set.mem_mul]
  refine ⟨powerSeriesProjectiveMap k d g * fundamentalCoweight k d r, ?_,
    1, (maximalCompact k d).one_mem, mul_one _⟩
  rw [Set.mem_mul]
  exact ⟨powerSeriesProjectiveMap k d g,
    mk_powerSeriesGeneralLinearToLocal_mem_maximalCompact g,
    fundamentalCoweight k d r, Set.mem_singleton _, rfl⟩
theorem integralFundamentalNeighbor_surjective
    (k : Type*) [Field k] [Finite k] (d r : ℕ) :
    Function.Surjective (fun g : GL (Fin d) (IntegerRing k) ↦
      (⟨integralFundamentalNeighbor k d r g,
        integralFundamentalNeighbor_mem k d r g⟩ :
        {q // q ∈ fundamentalNeighborCosets k d r})) := by
  rintro ⟨q, hq⟩
  rw [mem_fundamentalNeighborCosets] at hq
  obtain ⟨t, ht, rfl⟩ := hq
  rw [fundamentalDoubleCoset, Set.mem_mul] at ht
  obtain ⟨y, hy, z, hz, rfl⟩ := ht
  rw [Set.mem_mul] at hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hy
  simp only [Set.mem_singleton_iff] at hb
  subst b
  rw [maximalCompact_eq_range_powerSeriesProjectiveMap] at ha
  obtain ⟨g, rfl⟩ := ha
  refine ⟨g, ?_⟩
  apply Subtype.ext
  apply QuotientGroup.eq.mpr
  simpa [integralFundamentalNeighbor, mul_assoc] using hz
theorem integralFundamentalNeighbor_eq_iff_projective
    (k : Type*) [Field k] [Finite k] (d r : ℕ)
    (g h : GL (Fin d) (IntegerRing k)) :
    integralFundamentalNeighbor k d r g =
        integralFundamentalNeighbor k d r h ↔
      Matrix.ProjGenLinGroup.mk
          (fundamentalIntegralConjugate k d r (g⁻¹ * h)) ∈
        maximalCompact k d := by
  change QuotientGroup.mk
      (powerSeriesProjectiveMap k d g * fundamentalCoweight k d r) =
      QuotientGroup.mk
        (powerSeriesProjectiveMap k d h * fundamentalCoweight k d r) ↔ _
  rw [QuotientGroup.eq]
  change (powerSeriesProjectiveMap k d g * fundamentalCoweight k d r)⁻¹ *
      (powerSeriesProjectiveMap k d h * fundamentalCoweight k d r) ∈
        maximalCompact k d ↔ _
  simp [fundamentalIntegralConjugate, fundamentalCoweight,
    powerSeriesProjectiveMap, map_mul, map_inv]
  group
theorem integralFundamentalNeighbor_eq_iff_residuePlane
    (k : Type*) [Field k] [Finite k] (d r : ℕ) (hd : 0 < d) (hr : r ≤ d)
    (g h : GL (Fin d) (IntegerRing k)) :
    integralFundamentalNeighbor k d r g =
        integralFundamentalNeighbor k d r h ↔
      residueFundamentalPlane k d r hr g =
        residueFundamentalPlane k d r hr h := by
  rw [integralFundamentalNeighbor_eq_iff_projective]
  rw [projective_mk_mem_maximalCompact_iff_integral k d hd
    (fundamentalIntegralConjugate k d r (g⁻¹ * h))
    (fundamentalIntegralConjugate_det_localUnitOrder_eq_zero k d r (g⁻¹ * h))]
  exact (residueFundamentalPlane_eq_iff_integralConjugate k d r hr g h).symm
noncomputable def equivOfSurjectiveOfEqFibers
    {α β γ : Type*} (f : α → β) (g : α → γ)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hfiber : ∀ x y, f x = f y ↔ g x = g y) : β ≃ γ where
  toFun b := g (Classical.choose (hf b))
  invFun c := f (Classical.choose (hg c))
  left_inv b := by
    calc
      f (Classical.choose (hg (g (Classical.choose (hf b))))) =
          f (Classical.choose (hf b)) := (hfiber _ _).mpr
            (Classical.choose_spec (hg (g (Classical.choose (hf b)))))
      _ = b := Classical.choose_spec (hf b)
  right_inv c := by
    calc
      g (Classical.choose (hf (f (Classical.choose (hg c))))) =
          g (Classical.choose (hg c)) := (hfiber _ _).mp
            (Classical.choose_spec (hf (f (Classical.choose (hg c)))))
      _ = c := Classical.choose_spec (hg c)
noncomputable def fundamentalNeighborGrassmannianEquiv
    (k : Type*) [Field k] [Finite k] (d r : ℕ) (hd : 0 < d) (hr : r ≤ d) :
    {q // q ∈ fundamentalNeighborCosets k d r} ≃
      QEC.Coding.HighDimensionalExpander.FiniteGeometry.FiniteGrassmannian
        k (Fin d → k) r :=
  equivOfSurjectiveOfEqFibers
    (fun g : GL (Fin d) (IntegerRing k) =>
      (⟨integralFundamentalNeighbor k d r g,
        integralFundamentalNeighbor_mem k d r g⟩ :
        {q // q ∈ fundamentalNeighborCosets k d r}))
    (residueFundamentalPlane k d r hr)
    (integralFundamentalNeighbor_surjective k d r)
    (residueFundamentalPlane_surjective k d r hr)
    (fun g h => by
      rw [Subtype.ext_iff]
      exact integralFundamentalNeighbor_eq_iff_residuePlane k d r hd hr g h)
def RankThreeAdjacent
    (k : Type u) [Field k] [Finite k] (color : RankThreeColor)
    (x y : BuildingVertex k 3) : Prop :=
  ColoredBuildingAdjacent k 3 (color.val + 1) x y
def RankFourAdjacent
    (k : Type u) [Field k] [Finite k] (color : RankFourColor)
    (x y : BuildingVertex k 4) : Prop :=
  ColoredBuildingAdjacent k 4 (color.val + 1) x y
end QEC.Coding.HighDimensionalExpander.SphericalHecke


