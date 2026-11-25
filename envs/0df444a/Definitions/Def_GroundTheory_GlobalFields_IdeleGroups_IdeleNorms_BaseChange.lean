-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
-- name    : GroundTheory_GlobalFields_IdeleGroups_IdeleNorms_BaseChange
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T09:08:30.034066+00:00
-- url     : https://prove2.me/theorems/39953e47-62d2-4d1c-8b56-466d9d60409d
-- title:
--   Base Change
-- statement:
--   Definitions and structural lemmas for Base Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/IdeleNorms/BaseChange.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_BaseChange
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_adeleMap_algebraMap
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_adeleTensorEquiv_tmul
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_algebraMap_adeleRing
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_finiteAdeleMap_apply
import Theorems.Thm_GroundTheory_Global_AdeleBaseChange_finiteTensorHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_InfinitePlace_infiniteAdeleRingMap_apply
import Theorems.Thm_GroundTheory_Global_InfinitePlace_piPlacesOverEquiv_apply
import Theorems.Thm_GroundTheory_Global_InfinitePlace_tensorInfiniteAdeleRingHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_SemiLocal_tensorHomeomorph_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.AdeleBaseChange.finiteAdeleMap_apply
attribute [local simp] GroundTheory.Global.AdeleBaseChange.finiteTensorHomeomorph_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_apply
attribute [local simp] GroundTheory.Global.InfinitePlace.piPlacesOverEquiv_apply
attribute [local simp] GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingHomeomorph_apply
attribute [local simp] GroundTheory.Global.SemiLocal.tensorHomeomorph_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] P2M_GroundTheory_Global_SemiLocal_tensorEquiv__tmul_7bea2d8929c7


set_option autoImplicit false
namespace GroundTheory.Global
open IsDedekindDomain NumberField TensorProduct Module Topology
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
section NormMap
variable {A B A' B' ι : Type*} [CommRing A] [CommRing B] [Algebra A B] [CommRing A']
  [CommRing B'] [Algebra A' B'] [Fintype ι] [DecidableEq ι]
theorem norm_map_of_repr (φ : A →+* A') (ψ : B →+* B') (b : Basis ι A B) (b' : Basis ι A' B')
    (h : ∀ y i, b'.repr (ψ y) i = φ (b.repr y i)) (y : B) :
    Algebra.norm A' (ψ y) = φ (Algebra.norm A y) := by
  have hb : ∀ j, ψ (b j) = b' j := fun j ↦ b'.repr.injective <| Finsupp.ext fun i ↦ by
    rw [h, b.repr_self, b'.repr_self, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs <;> simp
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b', RingHom.map_det]
  congr 1
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, RingHom.mapMatrix_apply, Matrix.map_apply,
    Algebra.leftMulMatrix_eq_repr_mul, ← hb, ← map_mul, h]
end NormMap
namespace AdeleBaseChange
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (K L) in

def adeleTensorAlgEquivLeft : 𝔸[K] ⊗[K] L ≃ₐ[𝔸[K]] 𝔸[L] :=
  AlgEquiv.ofRingEquiv
    (f := (Algebra.TensorProduct.comm K 𝔸[K] L).toRingEquiv.trans
      (adeleTensorEquiv K L).toRingEquiv) fun a ↦ by
    change adeleTensorEquiv K L (Algebra.TensorProduct.comm K 𝔸[K] L (a ⊗ₜ 1)) = adeleMap K L a
    rw [Algebra.TensorProduct.comm_tmul, adeleTensorEquiv_tmul, map_one, one_mul]
theorem adeleTensorAlgEquivLeft_tmul (a : 𝔸[K]) (l : L) :
    adeleTensorAlgEquivLeft K L (a ⊗ₜ l) = algebraMap L 𝔸[L] l * adeleMap K L a := by
  change adeleTensorEquiv K L (Algebra.TensorProduct.comm K 𝔸[K] L (a ⊗ₜ l)) = _
  rw [Algebra.TensorProduct.comm_tmul, adeleTensorEquiv_tmul]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)
def adeleBasis : Basis ι 𝔸[K] 𝔸[L] :=
  (Algebra.TensorProduct.basis 𝔸[K] b).map (adeleTensorAlgEquivLeft K L).toLinearEquiv
omit [Fintype ι] [DecidableEq ι] in
theorem adeleBasis_apply (i : ι) : adeleBasis b i = algebraMap L 𝔸[L] (b i) := by
  rw [adeleBasis, Basis.map_apply, Algebra.TensorProduct.basis_apply]
  change adeleTensorAlgEquivLeft K L (1 ⊗ₜ b i) = _
  rw [adeleTensorAlgEquivLeft_tmul, map_one, mul_one]
omit [DecidableEq ι] in

theorem adeleBasis_repr_algebraMap (l : L) (i : ι) :
    (adeleBasis b).repr (algebraMap L 𝔸[L] l) i = algebraMap K 𝔸[K] (b.repr l i) := by
  classical
  have hl : algebraMap L 𝔸[L] l = ∑ j, algebraMap K 𝔸[K] (b.repr l j) • adeleBasis b j := by
    conv_lhs => rw [← b.sum_repr l]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [adeleBasis_apply, Algebra.smul_def, map_mul, Algebra.smul_def, algebraMap_adeleRing,
      adeleMap_algebraMap]
  rw [hl, Basis.repr_sum_self]
variable (K) in

scoped instance nontrivial_adeleRing : Nontrivial 𝔸[K] :=
  (AdeleRing.algebraMap_injective (𝓞 K) K).nontrivial
variable (K L) in
scoped instance : Module.Free 𝔸[K] 𝔸[L] := .of_basis (adeleBasis (Module.finBasis K L))
variable (K L) in
scoped instance : Module.Finite 𝔸[K] 𝔸[L] := .of_basis (adeleBasis (Module.finBasis K L))
theorem norm_adeleRing_algebraMap (l : L) :
    Algebra.norm 𝔸[K] (algebraMap L 𝔸[L] l) = algebraMap K 𝔸[K] (Algebra.norm K l) := by
  classical
  exact norm_map_of_repr (algebraMap K 𝔸[K]) (algebraMap L 𝔸[L]) (Module.finBasis K L)
    (adeleBasis (Module.finBasis K L)) (fun y i ↦ adeleBasis_repr_algebraMap _ y i) l
end AdeleBaseChange
open AdeleBaseChange
variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
def ideleEmbedding : IdeleGroup K →* IdeleGroup L :=
  Units.map (adeleMap K L).toMonoidHom
variable {K L}
@[simp]
theorem coe_ideleEmbedding (x : IdeleGroup K) :
    ((ideleEmbedding K L x : IdeleGroup L) : 𝔸[L]) = adeleMap K L x :=
  rfl
theorem ideleEmbedding_diagonal (k : Kˣ) :
    ideleEmbedding K L (IdeleGroup.diagonal K k) =
      IdeleGroup.diagonal L (Units.map (algebraMap K L).toMonoidHom k) :=
  Units.ext (adeleMap_algebraMap (k : K))
variable (K L) in

def ideleNorm : IdeleGroup L →* IdeleGroup K :=
  Units.map (Algebra.norm 𝔸[K] : 𝔸[L] →* 𝔸[K])
@[simp]
theorem coe_ideleNorm (x : IdeleGroup L) :
    ((ideleNorm K L x : IdeleGroup K) : 𝔸[K]) = Algebra.norm 𝔸[K] (x : 𝔸[L]) :=
  rfl
theorem ideleNorm_diagonal (l : Lˣ) :
    ideleNorm K L (IdeleGroup.diagonal L l) =
      IdeleGroup.diagonal K (Units.map (Algebra.norm K : L →* K) l) :=
  Units.ext (norm_adeleRing_algebraMap (l : L))
theorem diagonal_range_le_comap_ideleEmbedding :
    (IdeleGroup.diagonal K).range ≤ (IdeleGroup.diagonal L).range.comap (ideleEmbedding K L) := by
  rintro _ ⟨k, rfl⟩
  exact ⟨Units.map (algebraMap K L).toMonoidHom k, (ideleEmbedding_diagonal k).symm⟩
theorem diagonal_range_le_comap_ideleNorm :
    (IdeleGroup.diagonal L).range ≤ (IdeleGroup.diagonal K).range.comap (ideleNorm K L) := by
  rintro _ ⟨l, rfl⟩
  exact ⟨Units.map (Algebra.norm K : L →* K) l, (ideleNorm_diagonal l).symm⟩
variable (K L) in

def ideleClassMap : IdeleClassGroup K →* IdeleClassGroup L :=
  QuotientGroup.map _ _ (ideleEmbedding K L) diagonal_range_le_comap_ideleEmbedding
variable (K L) in

def ideleClassNorm : IdeleClassGroup L →* IdeleClassGroup K :=
  QuotientGroup.map _ _ (ideleNorm K L) diagonal_range_le_comap_ideleNorm
end
end GroundTheory.Global


