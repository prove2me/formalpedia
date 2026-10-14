-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0255_parallel1
-- name    : PNT_ZeroFree_433_0255_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:23:57.331419+00:00
-- url     : https://prove2.me/theorems/3888898f-5864-4657-9d2c-f520f560a4e1
-- title:
--   Zero-free region foundations: Eisenstein.CubeEigenrelation [0255_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.CubeEigenrelation
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CubeEigenrelation.lean#L84-L554

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0017
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0074
import Definitions.Def_PNT_ZeroFree_433_0075
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0123_parallel1
import Definitions.Def_PNT_ZeroFree_433_0131_parallel1
import Definitions.Def_PNT_ZeroFree_433_0147_parallel1
import Definitions.Def_PNT_ZeroFree_433_0151_parallel2
import Definitions.Def_PNT_ZeroFree_433_0155_parallel1
import Definitions.Def_PNT_ZeroFree_433_0238_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0238_parallel2

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CubeEigenrelation.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace CubicEisenstein

section

open scoped Classical MatrixGroups BigOperators
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma positive_cube_cpow_third (r:ℝ) (hr:0<r) :
    ((r^3:ℝ):ℂ)^(1/3:ℂ)=(r:ℂ) := by
  calc
    _=(((r^3)^(1/3:ℝ):ℝ):ℂ):=by
      simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using
        (Complex.ofReal_cpow (pow_nonneg hr.le 3) (1/3)).symm
    _=_:=by
      congr 1
      rw [←Real.rpow_natCast_mul hr.le 3]
      norm_num


lemma eisenstein_norm_eq_sqrt_norm (p:Eis) :
    ‖eisEmbedding p‖=Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ) := by
  rw [←eisEmbedding_norm_sq_eq_absNorm_span,Real.sqrt_sq (norm_nonneg _)]


end

open MeasureTheory
open scoped Classical MatrixGroups BigOperators
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota EisensteinCuspModThree
local notation "Eis" => ActualEisensteinCubic.O


end CubicEisenstein

open scoped Classical

namespace FiniteAutomorphismCover

variable {G : Type*} [Group G] {ι : Type*}

def common (K R : Subgroup G) (a : ι → G ≃* G) : Subgroup G :=
  K ⊓ ⨅i, R.comap (a i).toMonoidHom

lemma common_le (K R : Subgroup G) (a : ι → G ≃* G) : common K R a ≤ K :=
  inf_le_left

lemma common_le_preimage (K R : Subgroup G) (a : ι → G ≃* G) (i : ι) :
    common K R a ≤ R.comap (a i).toMonoidHom :=
  inf_le_right.trans (iInf_le _ i)

instance common_finiteIndex [Finite ι] (K R : Subgroup G) (a : ι → G ≃* G)
    [K.FiniteIndex] [R.FiniteIndex] : (common K R a).FiniteIndex := by
  let : (⨅i, R.comap (a i).toMonoidHom).FiniteIndex :=
    Subgroup.finiteIndex_iInf (fun i => inferInstance)
  unfold common
  infer_instance

def toSource (K R : Subgroup G) (a : ι → G ≃* G) (i : ι) : common K R a →* R where
  toFun h := ⟨a i (h : G), common_le_preimage K R a i h.property⟩
  map_one' := Subtype.ext (map_one (a i))
  map_mul' x y := Subtype.ext (map_mul (a i) (x : G) (y : G))

@[simp] lemma toSource_coe (K R : Subgroup G) (a : ι → G ≃* G) (i : ι)
    (h : common K R a) : (toSource K R a i h : G) = a i (h : G) := rfl

lemma toSource_injective (K R : Subgroup G) (a : ι → G ≃* G) (i : ι) :
    Function.Injective (toSource K R a i) := by
  intro x y hxy
  apply Subtype.ext
  exact (a i).injective (congrArg (fun r : R => (r : G)) hxy)

lemma toSource_range (K R : Subgroup G) (a : ι → G ≃* G) (i : ι) :
    (toSource K R a i).range =
      (common K R a).comap ((a i).symm.toMonoidHom.comp R.subtype) := by
  ext r
  constructor
  · rintro ⟨h,rfl⟩
    change (a i).symm (a i (h : G)) ∈ common K R a
    simpa only [MulEquiv.symm_apply_apply] using h.property
  · intro hr
    refine ⟨⟨(a i).symm (r : G),hr⟩,?_⟩
    apply Subtype.ext
    exact (a i).apply_symm_apply (r : G)

instance toSource_range_finiteIndex [Finite ι] (K R : Subgroup G) (a : ι → G ≃* G)
    [K.FiniteIndex] [R.FiniteIndex] (i : ι) : (toSource K R a i).range.FiniteIndex := by
  rw [toSource_range]
  infer_instance

def hom (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale) (i : ι) :
    common K R a →* G :=
  lengthScale.subtype.comp (e.toMonoidHom.comp (toSource K R a i))

@[simp] lemma hom_apply (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale)
    (i : ι) (h : common K R a) :
    hom K R lengthScale a e i h = (e (toSource K R a i h) : G) := rfl

lemma hom_injective (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale) (i : ι) :
    Function.Injective (hom K R lengthScale a e i) :=
  lengthScale.subtype_injective.comp (e.injective.comp (toSource_injective K R a i))

def target (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale) (i : ι) : Subgroup G :=
  (hom K R lengthScale a e i).range

lemma target_le (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale) (i : ι) :
    target K R lengthScale a e i ≤ lengthScale := by
  rintro x ⟨h,rfl⟩
  exact (e (toSource K R a i h)).property

lemma target_le_common_ambient (K R lengthScale : Subgroup G) (a : ι → G ≃* G)
    (e : R ≃* lengthScale) (hLK : lengthScale ≤ K) (i : ι) : target K R lengthScale a e i ≤ K :=
  (target_le K R lengthScale a e i).trans hLK

lemma target_eq_map (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale) (i : ι) :
    target K R lengthScale a e i = ((toSource K R a i).range.map e.toMonoidHom).map lengthScale.subtype := by
  rw [target,hom,MonoidHom.range_comp,MonoidHom.range_comp]

instance target_finiteIndex [Finite ι] (K R lengthScale : Subgroup G) (a : ι → G ≃* G)
    (e : R ≃* lengthScale) [K.FiniteIndex] [R.FiniteIndex] [lengthScale.FiniteIndex] (i : ι) :
    (target K R lengthScale a e i).FiniteIndex := by
  let : ((toSource K R a i).range.map e.toMonoidHom).FiniteIndex :=
    by
      constructor
      rw [Subgroup.index_map_of_bijective e.bijective]
      exact Subgroup.FiniteIndex.index_ne_zero
  constructor
  rw [target_eq_map,Subgroup.index_map_subtype]
  exact mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Subgroup.FiniteIndex.index_ne_zero

def equiv (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale) (i : ι) :
    common K R a ≃* target K R lengthScale a e i :=
  MonoidHom.ofInjective (hom_injective K R lengthScale a e i)

@[simp] lemma equiv_coe (K R lengthScale : Subgroup G) (a : ι → G ≃* G) (e : R ≃* lengthScale)
    (i : ι) (h : common K R a) :
    (equiv K R lengthScale a e i h : G) = (e (toSource K R a i h) : G) := rfl

end FiniteAutomorphismCover

namespace CubicKubota
open scoped BigOperators Classical MatrixGroups

open CubicEisenstein ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O


lemma cubeTranslation_complex (q : ActualEisensteinCubic.O) :
    integralComplexMatrix (upperTranslation q:SL(2,ActualEisensteinCubic.O))=complexTranslation (3*eisEmbedding q) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [integralComplexMatrix_apply]
  fin_cases i <;> fin_cases j <;> simp [upperTranslation, complexTranslation, map_ofNat]


end CubicKubota


open scoped Classical MatrixGroups BigOperators

namespace CubicKubota
open CubicEisenstein ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

abbrev CubeResidues (p : ActualEisensteinCubic.O) := ActualEisensteinCubic.O ⧸ Ideal.span {p^3}

def cubeCommonAutomorphism (p : ActualEisensteinCubic.O) (r : CubeResidues p) : SL(2,ActualEisensteinCubic.O) ≃* SL(2,ActualEisensteinCubic.O) :=
  MulAut.conj (upperTranslation (GaussianShiftedPartition.representative (p^3) r):SL(2,ActualEisensteinCubic.O))

def cubeCommonCover (p : ActualEisensteinCubic.O) (hp : p≠0) : Subgroup (SL(2,ActualEisensteinCubic.O)) :=
  FiniteAutomorphismCover.common globalKubotaKernel
    (cubeKernelRightGlobal p hp).range (cubeCommonAutomorphism p)

lemma cubeCommonCover_le (p : ActualEisensteinCubic.O) (hp : p≠0) : cubeCommonCover p hp≤globalKubotaKernel :=
  FiniteAutomorphismCover.common_le _ _ _


end CubicKubota

end

end OAI

end


