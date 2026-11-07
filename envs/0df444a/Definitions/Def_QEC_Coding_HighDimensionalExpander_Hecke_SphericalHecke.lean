-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
-- name    : QEC_Coding_HighDimensionalExpander_Hecke_SphericalHecke
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T10:27:35.143196+00:00
-- url     : https://prove2.me/theorems/5e5f089b-ae46-4633-9a37-747f4c112daa
-- title:
--   Spherical Hecke
-- statement:
--   Definitions and structural lemmas for Spherical Hecke, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Hecke/SphericalHecke.lean

import Mathlib.Algebra.Group.Pi.Units
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.MeasureTheory.Measure.Haar.Basic
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.HighDimensionalExpander.SphericalHecke
open scoped MatrixGroups Pointwise
universe u
abbrev LocalFunctionField (k : Type u) [Zero k] := LaurentSeries k
abbrev IntegerRing (k : Type u) [Zero k] := PowerSeries k
namespace LocalTopology
noncomputable scoped instance localFunctionFieldUniformSpace
    (k : Type u) [Field k] : UniformSpace (LocalFunctionField k) :=
  (LaurentSeries.valued k).toUniformSpace
scoped instance localFunctionFieldIsUniformAddGroup
    (k : Type u) [Field k] : IsUniformAddGroup (LocalFunctionField k) :=
  (LaurentSeries.valued k).toIsUniformAddGroup
scoped instance localFunctionFieldValued (k : Type u) [Field k] :
    Valued (LocalFunctionField k) (WithZero (Multiplicative Int)) :=
  LaurentSeries.valued k
open scoped LocalTopology Valued
theorem powerSeriesSubring_eq_integerSubring (k : Type u) [Field k] :
    LaurentSeries.powerSeries_as_subring k =
      (Valued.v : Valuation (LocalFunctionField k)
        (WithZero (Multiplicative Int))).valuationSubring.toSubring := by
  ext f
  change f ∈ Subring.map (HahnSeries.ofPowerSeries Int k) ⊤ ↔
    f ∈ (Valued.v : Valuation (LocalFunctionField k)
      (WithZero (Multiplicative Int))).valuationSubring
  rw [Valuation.mem_valuationSubring_iff]
  constructor
  · rintro ⟨F, _hF, rfl⟩
    exact (LaurentSeries.val_le_one_iff_eq_coe k _).2 ⟨F, rfl⟩
  · intro hf
    obtain ⟨F, hF⟩ := (LaurentSeries.val_le_one_iff_eq_coe k f).1 hf
    exact ⟨F, Subring.mem_top F, hF⟩
def powerSeriesIntegerEquiv (k : Type u) [Field k] :
    IntegerRing k ≃+* Valued.integer (LocalFunctionField k) :=
  (LaurentSeries.powerSeriesEquivSubring k).trans
    (RingEquiv.subringCongr (powerSeriesSubring_eq_integerSubring k))
noncomputable scoped instance localFunctionFieldIntegerIsDVR
    (k : Type u) [Field k] :
    IsDiscreteValuationRing (Valued.integer (LocalFunctionField k)) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (powerSeriesIntegerEquiv k)
noncomputable def residueFieldEquiv (k : Type u) [Field k] :
    IsLocalRing.ResidueField (Valued.integer (LocalFunctionField k)) ≃+* k :=
  (IsLocalRing.ResidueField.mapEquiv (powerSeriesIntegerEquiv k).symm).trans
    PowerSeries.residueFieldOfPowerSeries
noncomputable scoped instance localFunctionFieldFiniteResidue
    (k : Type u) [Field k] [Finite k] :
    Finite (IsLocalRing.ResidueField (Valued.integer (LocalFunctionField k))) :=
  Finite.of_equiv k (residueFieldEquiv k).symm.toEquiv
noncomputable scoped instance localFunctionFieldComplete
    (k : Type u) [Field k] : CompleteSpace (LocalFunctionField k) :=
  LaurentSeries.instLaurentSeriesComplete
noncomputable scoped instance localFunctionFieldRankOne
    (k : Type u) [Field k] :
    (Valued.v : Valuation (LocalFunctionField k)
      (WithZero (Multiplicative Int))).RankOne where
  hom' := (WithZeroMulInt.toNNReal (by norm_num : (2 : NNReal) ≠ 0)).comp
    MonoidWithZeroHom.ValueGroup₀.embedding
  strictMono' := (WithZeroMulInt.toNNReal_strictMono
    (by norm_num : (1 : NNReal) < 2)).comp
      MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
  exists_val_nontrivial := by
    refine ⟨HahnSeries.single (1 : Int) 1, ?_, ?_⟩ <;>
      simp [LaurentSeries.valuation_single_zpow]
noncomputable scoped instance localFunctionFieldProper
    (k : Type u) [Field k] [Finite k] :
    ProperSpace (LocalFunctionField k) := by
  rw [Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField]
  exact ⟨inferInstance, inferInstance, inferInstance⟩
noncomputable scoped instance localFunctionFieldSecondCountable
    (k : Type u) [Field k] [Finite k] :
    SecondCountableTopology (LocalFunctionField k) := by
  letI : NormedField (LocalFunctionField k) :=
    Valued.toNormedField (LocalFunctionField k)
      (WithZero (Multiplicative Int))
  infer_instance
noncomputable scoped instance matrixSecondCountable
    (k : Type u) [Field k] [Finite k] (d : ℕ) :
    SecondCountableTopology
      (Matrix (Fin d) (Fin d) (LocalFunctionField k)) := by
  exact inferInstanceAs
    (SecondCountableTopology
      (Fin d → Fin d → LocalFunctionField k))
noncomputable scoped instance localFunctionFieldLocallyCompact
    (k : Type u) [Field k] [Finite k] :
    LocallyCompactSpace (LocalFunctionField k) := by
  infer_instance
noncomputable scoped instance matrixLocallyCompact
    (k : Type u) [Field k] [Finite k] (d : ℕ) :
    LocallyCompactSpace (Matrix (Fin d) (Fin d) (LocalFunctionField k)) := by
  change LocallyCompactSpace (Fin d → Fin d → LocalFunctionField k)
  infer_instance
noncomputable scoped instance generalLinearLocallyCompact
    (k : Type u) [Field k] [Finite k] (d : ℕ) :
    LocallyCompactSpace (GL (Fin d) (LocalFunctionField k)) := by
  infer_instance
noncomputable scoped instance generalLinearSecondCountable
    (k : Type u) [Field k] [Finite k] (d : ℕ) :
    SecondCountableTopology (GL (Fin d) (LocalFunctionField k)) := by
  letI : SecondCountableTopology
      (MulOpposite (Matrix (Fin d) (Fin d) (LocalFunctionField k))) :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology
scoped instance generalLinearIsTopologicalGroup
    (k : Type u) [Field k] (d : ℕ) :
    IsTopologicalGroup (GL (Fin d) (LocalFunctionField k)) := by
  infer_instance
noncomputable scoped instance projectiveTopologicalSpace
    (k : Type u) [Field k] (d : ℕ) :
    TopologicalSpace PGL(Fin d, LocalFunctionField k) :=
  QuotientGroup.instTopologicalSpace
    (Subgroup.center (GL (Fin d) (LocalFunctionField k)))
scoped instance projectiveIsTopologicalGroup
    (k : Type u) [Field k] (d : ℕ) :
    IsTopologicalGroup PGL(Fin d, LocalFunctionField k) := by
  unfold Matrix.ProjGenLinGroup
  exact QuotientGroup.instIsTopologicalGroup
    (N := Subgroup.center (GL (Fin d) (LocalFunctionField k)))
noncomputable scoped instance projectiveT2Space
    (k : Type u) [Field k] (d : ℕ) :
    T2Space PGL(Fin d, LocalFunctionField k) := by
  letI : IsClosed
      (Subgroup.center (GL (Fin d) (LocalFunctionField k)) :
        Set (GL (Fin d) (LocalFunctionField k))) := by
    rw [← Subgroup.centralizer_univ]
    exact Set.isClosed_centralizer Set.univ
  unfold Matrix.ProjGenLinGroup
  infer_instance
noncomputable scoped instance projectiveLocallyCompactSpace
    (k : Type u) [Field k] [Finite k] (d : ℕ) :
    LocallyCompactSpace PGL(Fin d, LocalFunctionField k) := by
  unfold Matrix.ProjGenLinGroup
  exact QuotientGroup.instLocallyCompactSpace
    (Subgroup.center (GL (Fin d) (LocalFunctionField k)))
noncomputable scoped instance projectiveSecondCountable
    (k : Type u) [Field k] [Finite k] (d : ℕ) :
    SecondCountableTopology PGL(Fin d, LocalFunctionField k) := by
  unfold Matrix.ProjGenLinGroup
  let h := QuotientGroup.isOpenQuotientMap_mk
    (N := Subgroup.center (GL (Fin d) (LocalFunctionField k)))
  exact h.isQuotientMap.secondCountableTopology h.isOpenMap
noncomputable scoped instance projectiveMeasurableSpace
    (k : Type u) [Field k] (d : ℕ) :
    MeasurableSpace PGL(Fin d, LocalFunctionField k) :=
  borel PGL(Fin d, LocalFunctionField k)
scoped instance projectiveBorelSpace
    (k : Type u) [Field k] (d : ℕ) :
    BorelSpace PGL(Fin d, LocalFunctionField k) :=
  ⟨rfl⟩
noncomputable scoped instance integerRingCompact
    (k : Type u) [Field k] [Finite k] :
    CompactSpace (Valued.integer (LocalFunctionField k)) :=
  Valued.integer.properSpace_iff_compactSpace_integer.mp inferInstance
noncomputable scoped instance integerMatrixCompact
    (k : Type u) [Field k] [Finite k] (d : ℕ) :
    CompactSpace
      (Matrix (Fin d) (Fin d) (Valued.integer (LocalFunctionField k))) := by
  change CompactSpace
    (Fin d → Fin d → Valued.integer (LocalFunctionField k))
  infer_instance
noncomputable scoped instance integerGeneralLinearCompact
    (k : Type u) [Field k] [Finite k] (d : ℕ) :
    CompactSpace (GL (Fin d) (Valued.integer (LocalFunctionField k))) := by
  infer_instance
end LocalTopology
open scoped LocalTopology
open MeasureTheory
noncomputable def localHaarMeasure
    (k : Type u) [Field k] [Finite k] (d : ℕ) :
    Measure PGL(Fin d, LocalFunctionField k) :=
  Measure.haar
noncomputable instance localHaarMeasure_isHaar
    (k : Type u) [Field k] [Finite k] (d : ℕ) :
    Measure.IsHaarMeasure (localHaarMeasure k d) := by
  unfold localHaarMeasure
  infer_instance
def integerEmbedding (k : Type u) [CommRing k] :
    IntegerRing k →+* LocalFunctionField k :=
  HahnSeries.ofPowerSeries ℤ k
def powerSeriesGeneralLinearToLocal (k : Type u) [CommRing k] (d : ℕ) :
    GL (Fin d) (IntegerRing k) →* GL (Fin d) (LocalFunctionField k) :=
  Matrix.GeneralLinearGroup.map (integerEmbedding k)
def powerSeriesProjectiveMap (k : Type u) [CommRing k] (d : ℕ) :
    GL (Fin d) (IntegerRing k) →* PGL(Fin d, LocalFunctionField k) :=
  Matrix.ProjGenLinGroup.mk.comp (powerSeriesGeneralLinearToLocal k d)
def integralGeneralLinearToLocal (k : Type u) [Field k] (d : ℕ) :
    GL (Fin d) (Valued.integer (LocalFunctionField k)) →*
      GL (Fin d) (LocalFunctionField k) :=
  Matrix.GeneralLinearGroup.map
    (SubringClass.subtype (Valued.integer (LocalFunctionField k)))
def integralProjectiveMap (k : Type u) [Field k] (d : ℕ) :
    GL (Fin d) (Valued.integer (LocalFunctionField k)) →*
      PGL(Fin d, LocalFunctionField k) :=
  Matrix.ProjGenLinGroup.mk.comp (integralGeneralLinearToLocal k d)
theorem continuous_integralGeneralLinearToLocal
    (k : Type u) [Field k] [Finite k] (d : ℕ) :
    Continuous (integralGeneralLinearToLocal k d) :=
  Continuous.generalLinearGroup_map continuous_subtype_val
theorem continuous_integralProjectiveMap
    (k : Type u) [Field k] [Finite k] (d : ℕ) :
    Continuous (integralProjectiveMap k d) :=
  QuotientGroup.continuous_mk.comp
    (continuous_integralGeneralLinearToLocal k d)
def integralGeneralLinearSet (k : Type u) [Field k] (d : ℕ) :
    Set (GL (Fin d) (LocalFunctionField k)) :=
  {A | ∀ i j, A i j ∈ Valued.integer (LocalFunctionField k)} ∩
  {A | ∀ i j, A.inv i j ∈
    Valued.integer (LocalFunctionField k)}
theorem integralGeneralLinearSet_isOpen
    (k : Type u) [Field k] [Finite k] (d : ℕ) :
    IsOpen (integralGeneralLinearSet k d) := by
  let O : Set (LocalFunctionField k) :=
    Valued.integer (LocalFunctionField k)
  have hO : IsOpen O := Valued.isOpen_integer _
  have hMat : IsOpen (O.matrix : Set
      (Matrix (Fin d) (Fin d) (LocalFunctionField k))) := hO.matrix
  change IsOpen
    ((Units.val : GL (Fin d) (LocalFunctionField k) →
      Matrix (Fin d) (Fin d) (LocalFunctionField k)) ⁻¹' O.matrix ∩
    ((fun A : GL (Fin d) (LocalFunctionField k) ↦
      A.inv) ⁻¹' O.matrix))
  exact (hMat.preimage Units.continuous_val).inter
    (hMat.preimage Units.continuous_coe_inv)
theorem range_integralGeneralLinearToLocal
    (k : Type u) [Field k] [Finite k] (d : ℕ) :
    Set.range (integralGeneralLinearToLocal k d) =
      integralGeneralLinearSet k d := by
  ext A
  constructor
  · rintro ⟨B, rfl⟩
    constructor <;> intro i j
    · exact (B i j).property
    · exact (B⁻¹ i j).property
  · rintro ⟨hA, hAinv⟩
    let B : Matrix (Fin d) (Fin d)
        (Valued.integer (LocalFunctionField k)) :=
      fun i j ↦ ⟨A i j, hA i j⟩
    let C : Matrix (Fin d) (Fin d)
        (Valued.integer (LocalFunctionField k)) :=
      fun i j ↦
        ⟨A.inv i j,
          hAinv i j⟩
    have hBC : B * C = 1 := by
      apply Matrix.ext
      intro i j
      apply Subtype.ext
      rw [Matrix.mul_apply]
      push_cast
      dsimp only [B, C]
      have hone :
          (↑((1 : Matrix (Fin d) (Fin d)
            (Valued.integer (LocalFunctionField k))) i j) :
              LocalFunctionField k) =
            (1 : Matrix (Fin d) (Fin d) (LocalFunctionField k)) i j := by
        rw [Matrix.one_apply, Matrix.one_apply]
        split <;> rfl
      rw [hone]
      simpa only [Matrix.mul_apply] using
        congr_fun (congr_fun A.val_inv i) j
    have hCB : C * B = 1 := by
      apply Matrix.ext
      intro i j
      apply Subtype.ext
      rw [Matrix.mul_apply]
      push_cast
      dsimp only [B, C]
      have hone :
          (↑((1 : Matrix (Fin d) (Fin d)
            (Valued.integer (LocalFunctionField k))) i j) :
              LocalFunctionField k) =
            (1 : Matrix (Fin d) (Fin d) (LocalFunctionField k)) i j := by
        rw [Matrix.one_apply, Matrix.one_apply]
        split <;> rfl
      rw [hone]
      simpa only [Matrix.mul_apply] using
        congr_fun (congr_fun A.inv_val i) j
    let U : GL (Fin d) (Valued.integer (LocalFunctionField k)) :=
      ⟨B, C, hBC, hCB⟩
    refine ⟨U, ?_⟩
    apply Units.ext
    ext i j
    rfl
def maximalCompact (k : Type u) [Field k] (d : ℕ) :
    Subgroup PGL(Fin d, LocalFunctionField k) :=
  (integralProjectiveMap k d).range
@[simp]
theorem mem_maximalCompact_iff (k : Type u) [Field k] (d : ℕ)
    (g : PGL(Fin d, LocalFunctionField k)) :
    g ∈ maximalCompact k d ↔
      ∃ h : GL (Fin d) (Valued.integer (LocalFunctionField k)),
        integralProjectiveMap k d h = g :=
  MonoidHom.mem_range
theorem maximalCompact_isCompact
    (k : Type u) [Field k] [Finite k] (d : ℕ) :
    IsCompact (maximalCompact k d : Set PGL(Fin d, LocalFunctionField k)) := by
  rw [maximalCompact, MonoidHom.coe_range]
  simpa only [Set.image_univ] using
    isCompact_univ.image (continuous_integralProjectiveMap k d)
theorem maximalCompact_isOpen
    (k : Type u) [Field k] [Finite k] (d : ℕ) :
    IsOpen (maximalCompact k d : Set PGL(Fin d, LocalFunctionField k)) := by
  have hGL : IsOpen (Set.range (integralGeneralLinearToLocal k d)) := by
    rw [range_integralGeneralLinearToLocal]
    exact integralGeneralLinearSet_isOpen k d
  have hImage : IsOpen
      (QuotientGroup.mk '' Set.range (integralGeneralLinearToLocal k d) :
        Set PGL(Fin d, LocalFunctionField k)) :=
    (QuotientGroup.isOpenQuotientMap_mk
      (N := Subgroup.center (GL (Fin d) (LocalFunctionField k)))).isOpenMap
        (Set.range (integralGeneralLinearToLocal k d)) hGL
  rw [maximalCompact, MonoidHom.coe_range]
  change IsOpen (Set.range (fun a ↦
    QuotientGroup.mk (integralGeneralLinearToLocal k d a)))
  rw [Set.range_comp']
  exact hImage
noncomputable def maximalCompactPositiveCompacts
    (k : Type u) [Field k] [Finite k] (d : ℕ) :
    TopologicalSpace.PositiveCompacts
      PGL(Fin d, LocalFunctionField k) where
  carrier := maximalCompact k d
  isCompact' := maximalCompact_isCompact k d
  interior_nonempty' := by
    rw [(maximalCompact_isOpen k d).interior_eq]
    exact ⟨1, (maximalCompact k d).one_mem⟩
noncomputable def normalizedLocalHaarMeasure
    (k : Type u) [Field k] [Finite k] (d : ℕ) :
    Measure PGL(Fin d, LocalFunctionField k) :=
  Measure.haarMeasure (maximalCompactPositiveCompacts k d)
noncomputable instance normalizedLocalHaarMeasure_isHaar
    (k : Type u) [Field k] [Finite k] (d : ℕ) :
    Measure.IsHaarMeasure (normalizedLocalHaarMeasure k d) := by
  unfold normalizedLocalHaarMeasure
  infer_instance
@[simp]
theorem normalizedLocalHaarMeasure_maximalCompact
    (k : Type u) [Field k] [Finite k] (d : ℕ) :
    normalizedLocalHaarMeasure k d (maximalCompact k d) = 1 := by
  exact Measure.haarMeasure_self
def uniformizerUnit (k : Type u) [Field k] :
    Units (LocalFunctionField k) where
  val := HahnSeries.single (1 : Int) 1
  inv := HahnSeries.single (-1 : Int) 1
  val_inv := by simp
  inv_val := by simp
def fundamentalDiagonalUnits (k : Type u) [Field k] (d r : ℕ) :
    Fin d → Units (LocalFunctionField k) :=
  fun i => if i.val < r then uniformizerUnit k else 1
def diagonalGeneralLinear (R : Type u) [CommRing R] (d : ℕ)
    (u : Fin d → Units R) : GL (Fin d) R :=
  Units.map (Matrix.diagonalRingHom (Fin d) R).toMonoidHom
    ((MulEquiv.piUnits).symm u)
def fundamentalDiagonal (k : Type u) [Field k] (d r : ℕ) :
    GL (Fin d) (LocalFunctionField k) :=
  diagonalGeneralLinear (LocalFunctionField k) d
    (fundamentalDiagonalUnits k d r)
def fundamentalCoweight (k : Type u) [Field k] (d r : ℕ) :
    PGL(Fin d, LocalFunctionField k) :=
  Matrix.ProjGenLinGroup.mk (fundamentalDiagonal k d r)
def fundamentalDoubleCoset (k : Type u) [Field k] (d r : ℕ) :
    Set PGL(Fin d, LocalFunctionField k) :=
  (maximalCompact k d : Set PGL(Fin d, LocalFunctionField k)) *
    ({fundamentalCoweight k d r} :
      Set PGL(Fin d, LocalFunctionField k)) *
    (maximalCompact k d : Set PGL(Fin d, LocalFunctionField k))
abbrev RankThreeGroup (k : Type u) [CommRing k] :=
  PGL(Fin 3, LocalFunctionField k)
abbrev RankFourGroup (k : Type u) [CommRing k] :=
  PGL(Fin 4, LocalFunctionField k)
abbrev RankThreeColor := Fin 2
abbrev RankFourColor := Fin 3
def rankThreeCoweight (k : Type u) [Field k] (color : RankThreeColor) :
    RankThreeGroup k :=
  fundamentalCoweight k 3 (color.val + 1)
def rankFourCoweight (k : Type u) [Field k] (color : RankFourColor) :
    RankFourGroup k :=
  fundamentalCoweight k 4 (color.val + 1)
def rankThreeDoubleCoset (k : Type u) [Field k] (color : RankThreeColor) :
    Set (RankThreeGroup k) :=
  fundamentalDoubleCoset k 3 (color.val + 1)
def rankFourDoubleCoset (k : Type u) [Field k] (color : RankFourColor) :
    Set (RankFourGroup k) :=
  fundamentalDoubleCoset k 4 (color.val + 1)
end QEC.Coding.HighDimensionalExpander.SphericalHecke


