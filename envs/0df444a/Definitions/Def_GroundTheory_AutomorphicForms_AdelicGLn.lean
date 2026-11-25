-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
-- name    : GroundTheory_AutomorphicForms_AdelicGLn
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:52:50.450087+00:00
-- url     : https://prove2.me/theorems/5cfa935a-3395-4a8b-bad6-16a2bdaaddb0
-- title:
--   Adelic GLn
-- statement:
--   Definitions and structural lemmas for Adelic GLn, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicGLn.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_RestrictedProductMatrix
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_integralGL_eq_units
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_mem_integralMatrices
import Theorems.Thm_GroundTheory_Automorphic_RestrictedProduct_matrixUnitsEquiv_apply
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
import Theorems.Thm_GroundTheory_Global_isOpen_integralFiniteAdeles
import Theorems.Thm_GroundTheory_Global_mem_valuationInteger_iff
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.RestrictedProduct.matrixUnitsEquiv_apply
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
open NumberField IsDedekindDomain Topology Filter Set
open scoped NumberField.AdeleRing RestrictedProduct
namespace GroundTheory.Automorphic
noncomputable section
instance locallyCompactSpace_matrix {m R : Type*} [Finite m] [TopologicalSpace R]
    [LocallyCompactSpace R] : LocallyCompactSpace (Matrix m m R) :=
  inferInstanceAs (LocallyCompactSpace (m → m → R))
namespace AdelicGLn
variable (K : Type*) [Field K] [NumberField K] (n : ℕ)
abbrev AdelicMatrix : Type _ := Matrix (Fin n) (Fin n) 𝔸[K]
abbrev AdelicGL : Type _ := GL (Fin n) 𝔸[K]
abbrev InfiniteAdelicGL : Type _ := GL (Fin n) (InfiniteAdeleRing K)
abbrev FiniteAdelicGL : Type _ := GL (Fin n) (FiniteAdeleRing (𝓞 K) K)
def det : AdelicGL K n →* (𝔸[K])ˣ :=
  Matrix.GeneralLinearGroup.det
@[simp]
theorem coe_det (g : AdelicGL K n) : (det K n g : 𝔸[K]) = (g : AdelicMatrix K n).det :=
  rfl
def prodEquiv : AdelicGL K n ≃ₜ* InfiniteAdelicGL K n × FiniteAdelicGL K n :=
  glProdEquiv (Fin n) (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)
@[simp]
theorem prodEquiv_apply_fst (g : AdelicGL K n) (a b : Fin n) :
    (prodEquiv K n g).1 a b = (g a b).1 :=
  rfl
@[simp]
theorem prodEquiv_apply_snd (g : AdelicGL K n) (a b : Fin n) :
    (prodEquiv K n g).2 a b = (g a b).2 :=
  rfl
def infiniteEquiv : InfiniteAdelicGL K n ≃ₜ* Π w : InfinitePlace K, GL (Fin n) w.Completion :=
  glPiEquiv (Fin n) fun w : InfinitePlace K => w.Completion
omit [NumberField K] in
@[simp]
theorem infiniteEquiv_apply (g : InfiniteAdelicGL K n) (w : InfinitePlace K) (a b : Fin n) :
    infiniteEquiv K n g w a b = g a b w :=
  rfl
theorem mem_integralMatrices_adicCompletion (v : HeightOneSpectrum (𝓞 K))
    (M : Matrix (Fin n) (Fin n) (v.adicCompletion K)) :
    M ∈ GLnLocal.integralMatrices (v.adicCompletion K) n ↔
      ∀ a b, M a b ∈ v.adicCompletionIntegers K := by
  rw [GLnLocal.mem_integralMatrices]
  simp only [GroundTheory.Global.mem_valuationInteger_iff]
def finiteRestrictedEquiv :
    FiniteAdelicGL K n ≃ₜ* Πʳ v : HeightOneSpectrum (𝓞 K),
      [GL (Fin n) (v.adicCompletion K), GLnLocal.integralGL (v.adicCompletion K) n] :=
  (RestrictedProduct.matrixUnitsEquiv (Fin n)
    (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (B := fun v => v.adicCompletionIntegers K)
    (C := fun v => GLnLocal.integralMatrices (v.adicCompletion K) n)
    (mem_integralMatrices_adicCompletion K n)
    (fun v => Valued.isOpen_valuationSubring (v.adicCompletion K))).trans
    (RestrictedProduct.congrSetsMul fun v => by
      rw [GLnLocal.integralGL_eq_units]
      rfl)
@[simp]
theorem finiteRestrictedEquiv_apply (g : FiniteAdelicGL K n) (v : HeightOneSpectrum (𝓞 K))
    (a b : Fin n) :
    (finiteRestrictedEquiv K n g v : GL (Fin n) (v.adicCompletion K)) a b = g a b v :=
  rfl
def restrictedProductEquiv :
    AdelicGL K n ≃ₜ* (Π w : InfinitePlace K, GL (Fin n) w.Completion) ×
      Πʳ v : HeightOneSpectrum (𝓞 K),
        [GL (Fin n) (v.adicCompletion K), GLnLocal.integralGL (v.adicCompletion K) n] :=
  (prodEquiv K n).trans
    { toMulEquiv := MulEquiv.prodCongr (infiniteEquiv K n).toMulEquiv
        (finiteRestrictedEquiv K n).toMulEquiv
      continuous_toFun := ((infiniteEquiv K n).continuous.comp continuous_fst).prodMk
        ((finiteRestrictedEquiv K n).continuous.comp continuous_snd)
      continuous_invFun := ((infiniteEquiv K n).symm.continuous.comp continuous_fst).prodMk
        ((finiteRestrictedEquiv K n).symm.continuous.comp continuous_snd) }
@[simp]
theorem restrictedProductEquiv_apply_fst (g : AdelicGL K n) (w : InfinitePlace K) (a b : Fin n) :
    (restrictedProductEquiv K n g).1 w a b = (g a b).1 w :=
  rfl
@[simp]
theorem restrictedProductEquiv_apply_snd (g : AdelicGL K n) (v : HeightOneSpectrum (𝓞 K))
    (a b : Fin n) :
    ((restrictedProductEquiv K n g).2 v : GL (Fin n) (v.adicCompletion K)) a b = (g a b).2 v :=
  rfl
def integralFiniteMatrices : Subring (Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K)) :=
  (RingHom.mapMatrix (GroundTheory.Global.integralFiniteAdeles (𝓞 K) K).subtype).range
theorem mem_integralFiniteMatrices {M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K)} :
    M ∈ integralFiniteMatrices K n ↔
      ∀ a b, M a b ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K := by
  constructor
  · rintro ⟨N, rfl⟩ a b
    exact (N a b).2
  · intro h
    exact ⟨Matrix.of fun a b => ⟨M a b, h a b⟩, rfl⟩
def integralFiniteGL : Subgroup (FiniteAdelicGL K n) :=
  (integralFiniteMatrices K n).toSubmonoid.units
theorem isOpen_integralFiniteMatrices :
    IsOpen (integralFiniteMatrices K n : Set (Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K))) := by
  have : (integralFiniteMatrices K n : Set (Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K))) =
      ⋂ a, ⋂ b, (fun M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K) => M a b) ⁻¹'
        (GroundTheory.Global.integralFiniteAdeles (𝓞 K) K) := by
    ext M
    simp [mem_integralFiniteMatrices]
  rw [this]
  exact isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b =>
    GroundTheory.Global.isOpen_integralFiniteAdeles.preimage (continuous_apply_apply a b)
theorem isOpen_integralFiniteGL : IsOpen (integralFiniteGL K n : Set (FiniteAdelicGL K n)) :=
  Submonoid.isOpen_units (isOpen_integralFiniteMatrices K n)
def integralFiniteOpenSubgroup : OpenSubgroup (FiniteAdelicGL K n) where
  toSubgroup := integralFiniteGL K n
  isOpen' := isOpen_integralFiniteGL K n
theorem totallyDisconnectedSpace_of_injective {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TotallyDisconnectedSpace Y] {f : X → Y} (hf : Continuous f)
    (hinj : Function.Injective f) : TotallyDisconnectedSpace X :=
  ⟨fun s _ hs => Set.subsingleton_of_image hinj s
    (isTotallyDisconnected_of_totallyDisconnectedSpace _ _ (Set.subset_univ _)
      (hs.image f hf.continuousOn))⟩
instance totallyDisconnectedSpace_finite : TotallyDisconnectedSpace (FiniteAdelicGL K n) :=
  totallyDisconnectedSpace_of_injective
    (f := fun g v => finiteRestrictedEquiv K n g v)
    (continuous_pi fun v =>
      (_root_.RestrictedProduct.continuous_eval v).comp (finiteRestrictedEquiv K n).continuous)
    fun _ _ hgh => (finiteRestrictedEquiv K n).injective
      (Subtype.ext (funext fun v => congrFun hgh v))
def diagonal : GL (Fin n) K →* AdelicGL K n :=
  Units.map (algebraMap K 𝔸[K]).mapMatrix.toMonoidHom
def rationalGL : Subgroup (AdelicGL K n) :=
  (diagonal K n).range
end AdelicGLn
end
end GroundTheory.Automorphic


