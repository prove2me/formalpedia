-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Objects
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Objects
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T01:17:55.91173+00:00
-- url     : https://prove2.me/theorems/5a78684a-871a-4f91-8ab9-a34012ac7a4d
-- title:
--   Objects
-- statement:
--   Definitions and structural lemmas for Objects, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Objects.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups
import Theorems.Thm_GroundTheory_Automorphic_add_conj
import Theorems.Thm_GroundTheory_Automorphic_conj_algebraMap
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_finiteAdeleUnitaryEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_mul_conj
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.finiteAdeleUnitaryEquiv_apply
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk


set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal
noncomputable section
section Conj
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
theorem embedding_conj [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E]
    (σ : E →+* ℂ) (x : E) : σ (conj F E x) = starRingEnd ℂ (σ x) := by
  have hF : ∀ c : F, starRingEnd ℂ (σ (algebraMap F E c)) = σ (algebraMap F E c) := by
    intro c
    have h1 := ComplexEmbedding.isReal_iff.mp
      (IsTotallyReal.complexEmbedding_isReal (σ.comp (algebraMap F E)))
    have h2 := congrArg (fun ψ : F →+* ℂ => ψ c) h1
    simpa [ComplexEmbedding.conjugate_coe_eq] using h2
  by_cases hx : x ∈ Set.range (algebraMap F E)
  · obtain ⟨c, rfl⟩ := hx
    rw [conj_algebraMap, hF]
  · have hs : σ x + σ (conj F E x) = σ (algebraMap F E (Algebra.trace F E x)) := by
      rw [← map_add, add_conj]
    have hp : σ x * σ (conj F E x) = σ (algebraMap F E (Algebra.norm F x)) := by
      rw [← map_mul, mul_conj]
    have e1 : starRingEnd ℂ (σ x) + starRingEnd ℂ (σ (conj F E x)) = σ x + σ (conj F E x) := by
      rw [← map_add, hs, hF]
    have e2 : starRingEnd ℂ (σ x) * starRingEnd ℂ (σ (conj F E x)) =
        σ x * σ (conj F E x) := by
      rw [← map_mul, hp, hF]
    have key : (starRingEnd ℂ (σ x) - σ x) * (starRingEnd ℂ (σ x) - σ (conj F E x)) = 0 := by
      linear_combination (starRingEnd ℂ (σ x)) * e1 - e2
    rcases mul_eq_zero.mp key with h1 | h1
    · exfalso
      have hz : starRingEnd ℂ (σ x) = σ x := sub_eq_zero.mp h1
      apply IsTotallyComplex.complexEmbedding_not_isReal σ
      rw [ComplexEmbedding.isReal_iff]
      ext y
      have hy := (basisOneOf hx).sum_repr y
      rw [Fin.sum_univ_two, basisOneOf_zero, basisOneOf_one] at hy
      rw [← hy]
      simp only [ComplexEmbedding.conjugate_coe_eq, Algebra.smul_def,
        map_add, map_mul, mul_one, hF, hz]
    · exact (sub_eq_zero.mp h1).symm
end Conj
section Real
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
def gramAt (h : HermitianForm F E W) (v : Basis ι E W) (w : InfinitePlace E) : Matrix ι ι ℂ :=
  (gram h.toSesq v).map w.embedding
def archUnitary (h : HermitianForm F E W) (v : Basis ι E W) :
    Subgroup (InfinitePlace E → GL ι ℂ) :=
  Subgroup.pi Set.univ fun w => unitaryGroupMatrix (starRingEnd ℂ) (gramAt h v w)
instance locallyCompactSpace_matrix_complex : LocallyCompactSpace (Matrix ι ι ℂ) :=
  inferInstanceAs (LocallyCompactSpace (ι → ι → ℂ))
theorem isClosed_archUnitary (h : HermitianForm F E W) (v : Basis ι E W) :
    IsClosed (archUnitary h v : Set (InfinitePlace E → GL ι ℂ)) := by
  have : (archUnitary h v : Set (InfinitePlace E → GL ι ℂ)) = Set.pi Set.univ fun w =>
      {g : GL ι ℂ | ((g : Matrix ι ι ℂ).map (starRingEnd ℂ))ᵀ * gramAt h v w *
        (g : Matrix ι ι ℂ) = gramAt h v w} := by
    ext g
    simp [archUnitary, Subgroup.mem_pi, mem_unitaryGroupMatrix]
  rw [this]
  refine isClosed_set_pi fun w _ => isClosed_eq ?_ continuous_const
  exact ((Units.continuous_val.matrix_map Complex.continuous_conj).matrix_transpose.matrix_mul
    continuous_const).matrix_mul Units.continuous_val
variable [NumberField E]
instance locallyCompactSpace_archUnitary (h : HermitianForm F E W) (v : Basis ι E W) :
    LocallyCompactSpace (archUnitary h v) :=
  (isClosed_archUnitary h v).isClosedEmbedding_subtypeVal.locallyCompactSpace
instance measurableSpace_archUnitary (h : HermitianForm F E W) (v : Basis ι E W) :
    MeasurableSpace (archUnitary h v) :=
  borel _
instance borelSpace_archUnitary (h : HermitianForm F E W) (v : Basis ι E W) :
    BorelSpace (archUnitary h v) :=
  ⟨rfl⟩
def vecAt (v : Basis ι E W) (x : W) : InfinitePlace E → ι → ℂ :=
  fun w i => w.embedding (v.repr x i)
def invApply {h : HermitianForm F E W} {v : Basis ι E W} (g : archUnitary h v)
    (y : InfinitePlace E → ι → ℂ) : InfinitePlace E → ι → ℂ :=
  fun w => (((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ y w
structure Majorant (h : HermitianForm F E W) (v : Basis ι E W) where

  P : InfinitePlace E → Matrix ι ι ℂ

  posDef : ∀ w, (P w).PosDef

  siegel : ∀ w, P w * (gramAt h v w)⁻¹ * P w = gramAt h v w
namespace Majorant
variable {h : HermitianForm F E W} {v : Basis ι E W}
def len (M : Majorant h v) (y : InfinitePlace E → ι → ℂ) : ℝ :=
  Real.sqrt (∑ w, (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re)
def stab (M : Majorant h v) : Subgroup (archUnitary h v) :=
  (Subgroup.pi Set.univ fun w => unitaryGroupMatrix (starRingEnd ℂ) (M.P w)).subgroupOf
    (archUnitary h v)
end Majorant
variable (E) in

structure IsLattice (La : AddSubgroup W) : Prop where

  smul_mem : ∀ (a : 𝓞 E) (x : W), x ∈ La → (a : E) • x ∈ La

  fg : La.FG

  span_eq_top : Submodule.span E (La : Set W) = ⊤
def dualLattice (h : HermitianForm F E W) (La : AddSubgroup W) : AddSubgroup W where
  carrier := {y | ∀ x ∈ La, h.toSesq y x ∈ integralClosure ℤ E}
  add_mem' {a b} ha hb x hx := by
    rw [map_add, LinearMap.add_apply]
    exact add_mem (ha x hx) (hb x hx)
  zero_mem' x _ := by
    rw [map_zero, LinearMap.zero_apply]
    exact zero_mem _
  neg_mem' {a} ha x hx := by
    rw [map_neg, LinearMap.neg_apply]
    exact neg_mem (ha x hx)
def IsIntegralOn (h : HermitianForm F E W) (La : AddSubgroup W) : Prop :=
  ∀ x ∈ La, ∀ y ∈ La, h.toSesq x y ∈ integralClosure ℤ E
structure IsDIntegral (h : HermitianForm F E W) (D : ℕ) (La : AddSubgroup W) : Prop where

  isLattice : IsLattice E La

  integral : IsIntegralOn h La

  index_ne_zero : La.relIndex (dualLattice h La) ≠ 0

  index_le : La.relIndex (dualLattice h La) ≤ D
def latticeStab (h : HermitianForm F E W) (La : AddSubgroup W) : Subgroup h.unitaryGroup :=
  MulAction.stabilizer h.unitaryGroup La
def IsIsotropicLine (h : HermitianForm F E W) (l : Submodule E W) : Prop :=
  finrank E l = 1 ∧ ∀ x ∈ l, ∀ y ∈ l, h.toSesq x y = 0
variable (E) in

def ringMultiples (x : W) : AddSubgroup W :=
  (((smulAddHom E W).flip x).comp (algebraMap (𝓞 E) E).toAddMonoidHom).range
variable (E) in

def lineIndex (La : AddSubgroup W) (x : W) : ℕ :=
  (ringMultiples E x).relIndex (La ⊓ (Submodule.span E {x}).toAddSubgroup)
variable [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]
def archEmbed (h : HermitianForm F E W) (v : Basis ι E W) : h.unitaryGroup →* archUnitary h v :=
  MonoidHom.codRestrict
    (MonoidHom.pi fun w : InfinitePlace E =>
      (Matrix.GeneralLinearGroup.map (n := ι) w.embedding).comp
        ((unitaryGroupMatrix (conjHom F E) (gram h.toSesq v)).subtype.comp
          (unitaryGroupEquivMatrix h v).toMonoidHom))
    (archUnitary h v)
    (fun g => (Subgroup.mem_pi _).2 fun w _ => map_mem_unitaryGroupMatrix w.embedding
      (fun x => by simpa using embedding_conj w.embedding x) rfl (unitaryGroupEquivMatrix h v g).2)
def archLatticeGroup (h : HermitianForm F E W) (v : Basis ι E W) (La : AddSubgroup W) :
    Subgroup (archUnitary h v) :=
  (latticeStab h La).map (archEmbed h v)
variable {h : HermitianForm F E W} {v : Basis ι E W} in

def countBelow (M : Majorant h v) (VV : Set W) (g : archUnitary h v) (t : ℝ) : ℝ≥0∞ :=
  (({x ∈ VV | M.len (invApply g (vecAt v x)) < t}.encard : ℕ∞) : ℝ≥0∞)
variable {h : HermitianForm F E W} {v : Basis ι E W} in

def massBelow (M : Majorant h v) (μ : Measure (archUnitary h v)) (FD : Set (archUnitary h v))
    (VV : Set W) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ g in FD, countBelow M VV g t ∂μ
def vecStabGroup (h : HermitianForm F E W) (v : Basis ι E W) (La : AddSubgroup W) (x : W) :
    Subgroup (archUnitary h v) :=
  (MulAction.stabilizer (latticeStab h La) x).map ((archEmbed h v).comp (latticeStab h La).subtype)
end Real
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


