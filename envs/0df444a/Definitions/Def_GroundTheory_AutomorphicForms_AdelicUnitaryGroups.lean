-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups
-- name    : GroundTheory_AutomorphicForms_AdelicUnitaryGroups
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T01:08:35.897883+00:00
-- url     : https://prove2.me/theorems/861e1619-6efd-452f-a252-9696f78ec007
-- title:
--   Adelic Unitary Groups
-- statement:
--   Definitions and structural lemmas for Adelic Unitary Groups, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Restricted
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_LatticeCompact
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Anisotropic
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_finiteAdeleUnitaryEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_isUnit_det_gram
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
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
namespace GroundTheory.Automorphic
open Module Matrix TensorProduct Topology Filter IsDedekindDomain NumberField
open scoped RestrictedProduct NumberField.AdeleRing
noncomputable section
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
section Congr
variable {R S : Type*} [CommRing R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing S] [Algebra K S] [TopologicalSpace S] [IsTopologicalRing S]
def unitaryCongr (e : R ≃ₐ[K] S) (he : Continuous e) (he' : Continuous e.symm) :
    unitaryPoints K E H R ≃ₜ* unitaryPoints K E H S where
  toFun := unitaryMap K E H (e : R →ₐ[K] S)
  invFun := unitaryMap K E H (e.symm : S →ₐ[K] R)
  left_inv g := by
    let b := Module.finBasis K E
    apply unitaryCoords_injective H R b
    rw [unitaryCoords_unitaryMap, unitaryCoords_unitaryMap]
    funext p
    simp
  right_inv g := by
    let b := Module.finBasis K E
    apply unitaryCoords_injective H S b
    rw [unitaryCoords_unitaryMap, unitaryCoords_unitaryMap]
    funext p
    simp
  map_mul' := map_mul _
  continuous_toFun := continuous_unitaryMap _ he
  continuous_invFun := continuous_unitaryMap _ he'
end Congr
variable [NumberField K]
variable (K) in

def adeleRingEquivProd : 𝔸[K] ≃ₐ[K] InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K :=
  AlgEquiv.refl
variable (K) in

def infiniteAdeleRingEquivPi : InfiniteAdeleRing K ≃ₐ[K] ∀ w : InfinitePlace K, w.Completion :=
  AlgEquiv.refl
variable (K) in

def adeleInfiniteEval (w : InfinitePlace K) : 𝔸[K] →ₐ[K] w.Completion :=
  ((Pi.evalAlgHom K (fun w : InfinitePlace K => w.Completion) w).comp
    (infiniteAdeleRingEquivPi K).toAlgHom).comp
    ((AlgHom.fst K _ _).comp (adeleRingEquivProd K).toAlgHom)
variable (K) in

def adeleFiniteEval (v : HeightOneSpectrum (𝓞 K)) : 𝔸[K] →ₐ[K] v.adicCompletion K :=
  (finiteAdeleEval K v).comp ((AlgHom.snd K _ _).comp (adeleRingEquivProd K).toAlgHom)
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)
def adeleUnitaryEquiv (hH : IsUnit H.det) :
    unitaryPoints K E H 𝔸[K] ≃ₜ*
      (∀ w : InfinitePlace K, unitaryPoints K E H w.Completion) ×
        Πʳ v : HeightOneSpectrum (𝓞 K),
          [unitaryPoints K E H (v.adicCompletion K), localIntegral H b v] :=
  (unitaryCongr H (adeleRingEquivProd K) (by exact continuous_id) (by exact continuous_id)).trans
    ((unitaryProdEquiv K H _ _ hH).trans
      { toMulEquiv := MulEquiv.prodCongr
          ((unitaryCongr H (infiniteAdeleRingEquivPi K) (by exact continuous_id) (by exact continuous_id)).trans
            (unitaryPiEquiv K H (fun w : InfinitePlace K => w.Completion) hH)).toMulEquiv
          (finiteAdeleUnitaryEquiv H b hH).toMulEquiv
        continuous_toFun :=
          (((unitaryCongr H (infiniteAdeleRingEquivPi K) (by exact continuous_id) (by exact continuous_id)).trans
            (unitaryPiEquiv K H (fun w : InfinitePlace K => w.Completion) hH)).continuous.comp
              continuous_fst).prodMk
            ((finiteAdeleUnitaryEquiv H b hH).continuous.comp continuous_snd)
        continuous_invFun :=
          (((unitaryCongr H (infiniteAdeleRingEquivPi K) (by exact continuous_id) (by exact continuous_id)).trans
            (unitaryPiEquiv K H (fun w : InfinitePlace K => w.Completion) hH)).symm.continuous.comp
              continuous_fst).prodMk
            ((finiteAdeleUnitaryEquiv H b hH).symm.continuous.comp continuous_snd) })
variable (K) in

def unitaryDiagonal : unitaryPoints K E H K →* unitaryPoints K E H 𝔸[K] :=
  unitaryMap K E H (Algebra.ofId K 𝔸[K])
section Hermitian
variable {V : Type*} [AddCommGroup V] [Module E V] (h : HermitianForm K E V) (v : Basis ι E V)
def adeleUnitaryEquivHermitian :
    unitaryPoints K E (gram h.toSesq v) 𝔸[K] ≃ₜ*
      (∀ w : InfinitePlace K, unitaryPoints K E (gram h.toSesq v) w.Completion) ×
        Πʳ w : HeightOneSpectrum (𝓞 K),
          [unitaryPoints K E (gram h.toSesq v) (w.adicCompletion K),
            localIntegral (gram h.toSesq v) b w] :=
  adeleUnitaryEquiv (gram h.toSesq v) b (isUnit_det_gram h v)
def hermitianDiagonal : h.unitaryGroup →* unitaryPoints K E (gram h.toSesq v) 𝔸[K] :=
  (unitaryDiagonal K (gram h.toSesq v)).comp
    (unitaryPointsRationalEquivHermitian K E h v).symm.toMonoidHom
end Hermitian
end
end GroundTheory.Automorphic


