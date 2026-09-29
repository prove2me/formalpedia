-- Prove2me | solution 1 for AutomorphicForm.isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/7ebcb210-24f2-5695-bda4-60d4805b5dc2

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import Definitions.Def_M4aHerbrand_ArchSemilocal
import Theorems.Thm_AutomorphicForm_exists_mulEquiv_generalLinearGroup_tensorProduct_infiniteAdeleRing_pi
import Theorems.Thm_AutomorphicForm_exists_ringEquiv_tensorProduct_infiniteAdeleRing_pi_forall_tmul
import Theorems.Thm_Matrix_GeneralLinearGroup_isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two
import Theorems.Thm_AutomorphicForm_isInvInvariant_twistedCentralizer_completion_of_isNormConjugator_scalar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar

set_option autoImplicit false

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf toTensorGL sigmaTensor sigmaGL normString IsNormConjugator twistedCentralizer twistedCentralizerBorel IsRegularSemisimple sigmaCentralizer mem_sigmaCentralizer_iff exists_mulEquiv_generalLinearGroup_tensorProduct_infiniteAdeleRing_pi exists_ringEquiv_tensorProduct_infiniteAdeleRing_pi_forall_tmul isInvInvariant_twistedCentralizer_completion_of_isNormConjugator_scalar"
namespace CentAsmLocal
p2m_open "AutomorphicForm"

open MeasureTheory

section Generic

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

theorem map_mem_centralizer (e : G ≃ₜ* H) (γ : G) (t : Subgroup.centralizer ({γ} : Set G)) :
    e (t : G) ∈ Subgroup.centralizer ({e γ} : Set H) := by
  have ht : (t : G) * γ = γ * t := Subgroup.mem_centralizer_singleton_iff.1 t.2
  have h : e ((t : G) * γ) = e (γ * t) := congrArg e ht
  rw [map_mul, map_mul] at h
  exact Subgroup.mem_centralizer_singleton_iff.2 h

theorem symm_map_mem_centralizer (e : G ≃ₜ* H) (γ : G) (t' : Subgroup.centralizer ({e γ} : Set H)) :
    e.symm (t' : H) ∈ Subgroup.centralizer ({γ} : Set G) := by
  have ht : (t' : H) * e γ = e γ * t' := Subgroup.mem_centralizer_singleton_iff.1 t'.2
  have h : e.symm ((t' : H) * e γ) = e.symm (e γ * t') := congrArg e.symm ht
  rw [map_mul, map_mul, e.symm_apply_apply] at h
  exact Subgroup.mem_centralizer_singleton_iff.2 h

def centralizerCongr (e : G ≃ₜ* H) (γ : G) :
    Subgroup.centralizer ({γ} : Set G) ≃ₜ* Subgroup.centralizer ({e γ} : Set H) where
  toFun t := ⟨e t, map_mem_centralizer e γ t⟩
  invFun t' := ⟨e.symm t', symm_map_mem_centralizer e γ t'⟩
  left_inv _ := Subtype.ext (e.symm_apply_apply _)
  right_inv _ := Subtype.ext (e.apply_symm_apply _)
  map_mul' _ _ := Subtype.ext (map_mul e _ _)
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk (map_mem_centralizer e γ)
  continuous_invFun :=
    (e.symm.continuous.comp continuous_subtype_val).subtype_mk (symm_map_mem_centralizer e γ)

@[scoped simp] theorem coe_centralizerCongr_apply (e : G ≃ₜ* H) (γ : G)
    (t : Subgroup.centralizer ({γ} : Set G)) : ((centralizerCongr e γ t : _) : H) = e t := rfl

@[scoped simp] theorem coe_centralizerCongr_symm_apply (e : G ≃ₜ* H) (γ : G)
    (t' : Subgroup.centralizer ({e γ} : Set H)) :
    (((centralizerCongr e γ).symm t' : _) : G) = e.symm t' := rfl

theorem map_mem_sigmaCentralizer (e : G ≃ₜ* H) (θ : G →* G) (θ' : H →* H)
    (hθ : ∀ g, e (θ g) = θ' (e g)) (δ : G) (t : sigmaCentralizer θ δ) :
    e (t : G) ∈ sigmaCentralizer θ' (e δ) := by
  have ht : (t : G) * δ * (θ t)⁻¹ = δ := mem_sigmaCentralizer_iff.1 t.2
  have h : e ((t : G) * δ * (θ t)⁻¹) = e δ := congrArg e ht
  rw [map_mul, map_mul, map_inv, hθ] at h
  exact mem_sigmaCentralizer_iff.2 h

theorem symm_map_mem_sigmaCentralizer (e : G ≃ₜ* H) (θ : G →* G) (θ' : H →* H)
    (hθ : ∀ g, e (θ g) = θ' (e g)) (δ : G) (t' : sigmaCentralizer θ' (e δ)) :
    e.symm (t' : H) ∈ sigmaCentralizer θ δ := by
  have hθ' : ∀ h, e.symm (θ' h) = θ (e.symm h) := fun h => by
    apply e.injective
    rw [e.apply_symm_apply, hθ, e.apply_symm_apply]
  have ht : (t' : H) * e δ * (θ' t')⁻¹ = e δ := mem_sigmaCentralizer_iff.1 t'.2
  have h : e.symm ((t' : H) * e δ * (θ' t')⁻¹) = e.symm (e δ) := congrArg e.symm ht
  rw [map_mul, map_mul, map_inv, hθ', e.symm_apply_apply] at h
  exact mem_sigmaCentralizer_iff.2 h

def sigmaCentralizerCongr (e : G ≃ₜ* H) (θ : G →* G) (θ' : H →* H)
    (hθ : ∀ g, e (θ g) = θ' (e g)) (δ : G) :
    sigmaCentralizer θ δ ≃ₜ* sigmaCentralizer θ' (e δ) where
  toFun t := ⟨e t, map_mem_sigmaCentralizer e θ θ' hθ δ t⟩
  invFun t' := ⟨e.symm t', symm_map_mem_sigmaCentralizer e θ θ' hθ δ t'⟩
  left_inv _ := Subtype.ext (e.symm_apply_apply _)
  right_inv _ := Subtype.ext (e.apply_symm_apply _)
  map_mul' _ _ := Subtype.ext (map_mul e _ _)
  continuous_toFun :=
    (e.continuous.comp continuous_subtype_val).subtype_mk (map_mem_sigmaCentralizer e θ θ' hθ δ)
  continuous_invFun :=
    (e.symm.continuous.comp continuous_subtype_val).subtype_mk (symm_map_mem_sigmaCentralizer e θ θ' hθ δ)

@[scoped simp] theorem coe_sigmaCentralizerCongr_apply (e : G ≃ₜ* H) (θ : G →* G) (θ' : H →* H)
    (hθ : ∀ g, e (θ g) = θ' (e g)) (δ : G) (t : sigmaCentralizer θ δ) :
    ((sigmaCentralizerCongr e θ θ' hθ δ t : _) : H) = e t := rfl

@[scoped simp] theorem coe_sigmaCentralizerCongr_symm_apply (e : G ≃ₜ* H) (θ : G →* G) (θ' : H →* H)
    (hθ : ∀ g, e (θ g) = θ' (e g)) (δ : G) (t' : sigmaCentralizer θ' (e δ)) :
    (((sigmaCentralizerCongr e θ θ' hθ δ).symm t' : _) : G) = e.symm t' := rfl

end Generic

end AutomorphicForm.CentAsmLocal
p2m_reactivate "P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm.CentAsmLocal"
p2m_reactivate "P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm.CentAsmLocal"

set_option autoImplicit false

p2m_open "MeasureTheory NumberField AutomorphicForm P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm"
open scoped TensorProduct
open scoped TensorProduct.RightActions

namespace FDTEF

p2m_open "NumberField AutomorphicForm P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm"
open scoped TensorProduct TensorProduct.RightActions

variable (K : Type) [Field K] [NumberField K]

noncomputable def XiK : InfiniteAdeleRing K ≃+* ((v : InfinitePlace K) → v.Completion) := RingEquiv.refl _

theorem XiK_apply (a : InfiniteAdeleRing K) (v : InfinitePlace K) : XiK K a v = a v := rfl

theorem continuous_XiK : Continuous (XiK K) := continuous_id
theorem continuous_XiK_symm : Continuous (XiK K).symm := continuous_id

noncomputable def thetaK :
    GL (Fin 2) (InfiniteAdeleRing K) ≃* ((v : InfinitePlace K) → GL (Fin 2) v.Completion) :=
  ((Units.mapEquiv (RingEquiv.mapMatrix (m := Fin 2) (XiK K)).toMulEquiv).trans
    (Units.mapEquiv (Matrix.piRingEquiv :
      Matrix (Fin 2) (Fin 2) ((v : InfinitePlace K) → v.Completion) ≃+*
        ((v : InfinitePlace K) → Matrix (Fin 2) (Fin 2) v.Completion)).toMulEquiv)).trans MulEquiv.piUnits

theorem thetaK_val (g : GL (Fin 2) (InfiniteAdeleRing K)) (v : InfinitePlace K) (i j : Fin 2) :
    ((thetaK K g v : GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion) i j =
      (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j v := rfl

theorem thetaK_apply (g : GL (Fin 2) (InfiniteAdeleRing K)) (v : InfinitePlace K) :
    thetaK K g v = Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun v : InfinitePlace K => v.Completion) v) g :=
  Units.ext (Matrix.ext fun i j => by rw [thetaK_val]; rfl)

theorem thetaK_symm_apply (F : (v : InfinitePlace K) → GL (Fin 2) v.Completion) :
    (thetaK K).symm F = (Units.mapEquiv (RingEquiv.mapMatrix (m := Fin 2) (XiK K)).toMulEquiv).symm
      ((Units.mapEquiv (Matrix.piRingEquiv :
        Matrix (Fin 2) (Fin 2) ((v : InfinitePlace K) → v.Completion) ≃+*
          ((v : InfinitePlace K) → Matrix (Fin 2) (Fin 2) v.Completion)).toMulEquiv).symm (MulEquiv.piUnits.symm F)) :=
  rfl

theorem continuous_thetaK : Continuous (thetaK K) := by
  refine continuous_pi fun v => ?_
  have hfun : (fun g => thetaK K g v) =
      Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun v : InfinitePlace K => v.Completion) v) :=
    funext fun g => thetaK_apply K g v
  rw [hfun]
  exact Continuous.units_map _ (continuous_id.matrix_map (continuous_apply v))

theorem continuous_thetaK_symm : Continuous (thetaK K).symm := by
  have h1 : Continuous (MulEquiv.piUnits (M := fun v : InfinitePlace K => Matrix (Fin 2) (Fin 2) v.Completion)).symm := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · exact continuous_pi fun v => Units.continuous_val.comp (continuous_apply v)
    · exact continuous_pi fun v => Units.continuous_coe_inv.comp (continuous_apply v)
  have h2 : Continuous (Units.mapEquiv (Matrix.piRingEquiv :
        Matrix (Fin 2) (Fin 2) ((v : InfinitePlace K) → v.Completion) ≃+*
          ((v : InfinitePlace K) → Matrix (Fin 2) (Fin 2) v.Completion)).toMulEquiv).symm := by
    refine Continuous.units_map _ ?_
    refine continuous_matrix fun i j => continuous_pi fun v => ?_
    exact ((continuous_apply j).comp ((continuous_apply i).comp (continuous_apply v)))
  have h3 : Continuous (Units.mapEquiv (RingEquiv.mapMatrix (m := Fin 2) (XiK K)).toMulEquiv).symm :=
    Continuous.units_map _ (continuous_id.matrix_map (continuous_XiK_symm K))
  have hfun := funext (thetaK_symm_apply K)
  rw [show ⇑(thetaK K).symm = _ from hfun]
  exact h3.comp (h2.comp h1)

variable (L : Type) [Field L] [NumberField L] [Algebra K L]

theorem exists_thetaL :
    ∃ (Ξ : L ⊗[K] InfiniteAdeleRing K ≃+* ((v : InfinitePlace K) → L ⊗[K] v.Completion))
      (Θ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) ≃* ((v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion))),
      Continuous Ξ ∧ Continuous Ξ.symm ∧ (∀ (x : L) (a : InfiniteAdeleRing K) (v : InfinitePlace K), Ξ (x ⊗ₜ a) v = x ⊗ₜ (a v)) ∧
      Continuous Θ ∧ Continuous Θ.symm ∧
      (∀ (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (v : InfinitePlace K),
        Θ g v = Matrix.GeneralLinearGroup.map
          ((Pi.evalRingHom (fun v : InfinitePlace K => L ⊗[K] v.Completion) v).comp Ξ.toRingHom) g) ∧
      (∀ (σ : L ≃ₐ[K] L) (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (v : InfinitePlace K),
        Θ (sigmaGL K L (InfiniteAdeleRing K) σ g) v = sigmaGL K L v.Completion σ (Θ g v)) ∧
      (∀ (g : GL (Fin 2) (InfiniteAdeleRing K)) (v : InfinitePlace K),
        Θ (toTensorGL K L (InfiniteAdeleRing K) g) v = toTensorGL K L v.Completion (thetaK K g v)) := by
  obtain ⟨Ξ, hΞ, hΞ', hΞt⟩ := AutomorphicForm.exists_ringEquiv_tensorProduct_infiniteAdeleRing_pi_forall_tmul K L
  obtain ⟨Θ, hΘ, hΘ', hΘapp, hΘσ, hΘι⟩ :=
    AutomorphicForm.exists_mulEquiv_generalLinearGroup_tensorProduct_infiniteAdeleRing_pi K L Ξ hΞ hΞ' hΞt
  refine ⟨Ξ, Θ, hΞ, hΞ', hΞt, hΘ, hΘ', hΘapp, hΘσ, fun g v => ?_⟩
  rw [hΘι, thetaK_apply]

section Instances

variable (v : InfinitePlace K)

theorem secondCountableTopology_completion : SecondCountableTopology v.Completion := by
  letI : NontriviallyNormedField v.Completion := M4aHerbrand.ArchSemilocal.nontriviallyNormedCompletion v
  haveI : ProperSpace v.Completion := ProperSpace.of_locallyCompactSpace v.Completion
  infer_instance

attribute [local instance 10000] AutomorphicForm.glBorelOf

theorem borelSpace_gl (R : Type) [CommRing R] [TopologicalSpace R] : BorelSpace (GL (Fin 2) R) := ⟨rfl⟩

attribute [local instance] borelSpace_gl

theorem locallyCompactSpace_gl (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [T2Space R] [LocallyCompactSpace R] : LocallyCompactSpace (GL (Fin 2) R) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) R) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → R))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) R) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → R))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem secondCountableTopology_gl (R : Type) [CommRing R] [TopologicalSpace R]
    [SecondCountableTopology R] : SecondCountableTopology (GL (Fin 2) R) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) R) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → R))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem t2Space_gl (R : Type) [CommRing R] [TopologicalSpace R] [T2Space R] : T2Space (GL (Fin 2) R) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) R) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → R))
  exact Units.isEmbedding_embedProduct.t2Space

attribute [local instance] secondCountableTopology_completion locallyCompactSpace_gl
  secondCountableTopology_gl t2Space_gl

theorem isMulRightInvariant_haar_completion :
    (Measure.haar : Measure (GL (Fin 2) v.Completion)).IsMulRightInvariant := by
  exact (Matrix.GeneralLinearGroup.isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two
    (Measure.haar : Measure (GL (Fin 2) v.Completion))).1

end Instances
p2m_reactivate "P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm.CentAsmLocal"

end FDTEF
p2m_reactivate "P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm.CentAsmLocal"

namespace FDTEF

section ProductData

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]

noncomputable def thetaKC :
    GL (Fin 2) (InfiniteAdeleRing K) ≃ₜ* ((v : InfinitePlace K) → GL (Fin 2) v.Completion) :=
  { thetaK K with
    continuous_toFun := continuous_thetaK K
    continuous_invFun := continuous_thetaK_symm K }

@[scoped simp] theorem thetaKC_apply (g : GL (Fin 2) (InfiniteAdeleRing K)) : thetaKC K g = thetaK K g := rfl

@[scoped simp] theorem thetaKC_symm_apply (g : (v : InfinitePlace K) → GL (Fin 2) v.Completion) :
    (thetaKC K).symm g = (thetaK K).symm g := rfl

omit [NumberField K] in
theorem disc_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (g : GL (Fin 2) R) :
    Matrix.trace ((Matrix.GeneralLinearGroup.map f g : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) ^ 2 -
      4 * Matrix.det ((Matrix.GeneralLinearGroup.map f g : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) =
    f (Matrix.trace (g : Matrix (Fin 2) (Fin 2) R) ^ 2 - 4 * Matrix.det (g : Matrix (Fin 2) (Fin 2) R)) := by
  simp [Matrix.trace_fin_two, Matrix.det_fin_two, map_sub, map_mul, map_pow, map_add, map_ofNat]

omit [NumberField K] in
theorem isRegularSemisimple_map_iff_of_injective_isUnit {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : ∀ x : R, IsUnit (f x) → IsUnit x) (g : GL (Fin 2) R) :
    IsRegularSemisimple (Matrix.GeneralLinearGroup.map f g) ↔ IsRegularSemisimple g := by
  unfold IsRegularSemisimple
  rw [disc_map]
  exact ⟨hf _, fun h => h.map f⟩

omit [NumberField K] in
theorem map_scalar' {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (c : Rˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (f : R →* S) c) := by
  ext i j
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem isUnit_infiniteAdeleRing_iff (x : InfiniteAdeleRing K) : IsUnit x ↔ ∀ v : InfinitePlace K, IsUnit (x v) :=
  Pi.isUnit_iff

theorem isRegularSemisimple_iff_forall_thetaK (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    IsRegularSemisimple g ↔ ∀ v, IsRegularSemisimple (thetaK K g v) := by
  unfold IsRegularSemisimple
  rw [isUnit_infiniteAdeleRing_iff]
  refine forall_congr' fun v => ?_
  rw [thetaK_apply, disc_map]
  rfl

noncomputable def unitAt (c : (InfiniteAdeleRing K)ˣ) (v : InfinitePlace K) : (v.Completion)ˣ :=
  Units.map (Pi.evalMonoidHom (fun v : InfinitePlace K => v.Completion) v) c

@[scoped simp] theorem val_unitAt (c : (InfiniteAdeleRing K)ˣ) (v : InfinitePlace K) :
    ((unitAt K c v : (v.Completion)ˣ) : v.Completion) = (c : InfiniteAdeleRing K) v := rfl

theorem thetaK_scalar (c : (InfiniteAdeleRing K)ˣ) :
    thetaK K (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      fun v => Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c v) := by
  funext v
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [thetaK_val]
  simp only [Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
    Matrix.scalar_apply, Matrix.diagonal_apply, val_unitAt]
  split_ifs <;> rfl

variable {K L} in
omit [NumberField K] [NumberField L] in

theorem map_normString {A B : Type} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B] (σ : L ≃ₐ[K] L)
    (h : GL (Fin 2) (L ⊗[K] A) →* GL (Fin 2) (L ⊗[K] B))
    (hσ : ∀ g, h (sigmaGL K L A σ g) = sigmaGL K L B σ (h g)) (δ : GL (Fin 2) (L ⊗[K] A)) :
    h (normString K L A σ δ) = normString K L B σ (h δ) := by
  unfold normString
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  have hs : Function.Semiconj (⇑h) (⇑(sigmaGL K L A σ)) (⇑(sigmaGL K L B σ)) := hσ
  exact (hs.iterate_right i) δ

variable (σ : L ≃ₐ[K] L)
  (Ξ : L ⊗[K] InfiniteAdeleRing K ≃+* ((v : InfinitePlace K) → L ⊗[K] v.Completion))
  (Θ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) ≃* ((v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion)))
  (hΘapp : ∀ (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (v : InfinitePlace K),
    Θ g v = Matrix.GeneralLinearGroup.map
      ((Pi.evalRingHom (fun v : InfinitePlace K => L ⊗[K] v.Completion) v).comp Ξ.toRingHom) g)
  (hΘσ : ∀ (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (v : InfinitePlace K),
    Θ (sigmaGL K L (InfiniteAdeleRing K) σ g) v = sigmaGL K L v.Completion σ (Θ g v))
  (hΘι : ∀ (g : GL (Fin 2) (InfiniteAdeleRing K)) (v : InfinitePlace K),
    Θ (toTensorGL K L (InfiniteAdeleRing K) g) v = toTensorGL K L v.Completion (thetaK K g v))

noncomputable def thetaAt (v : InfinitePlace K) :
    GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) →* GL (Fin 2) (L ⊗[K] v.Completion) :=
  (Pi.evalMonoidHom (fun v : InfinitePlace K => GL (Fin 2) (L ⊗[K] v.Completion)) v).comp Θ.toMonoidHom

omit [NumberField L] in
@[scoped simp] theorem thetaAt_apply (v : InfinitePlace K) (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
    thetaAt K L Θ v g = Θ g v := rfl

include hΘσ in
omit [NumberField L] in
theorem theta_normString (δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (v : InfinitePlace K) :
    Θ (normString K L (InfiniteAdeleRing K) σ δ) v = normString K L v.Completion σ (Θ δ v) := by
  have := map_normString σ (thetaAt K L Θ v) (fun g => hΘσ g v) δ
  simpa only [thetaAt_apply] using this

include hΘapp in
omit [NumberField L] in

theorem isRegularSemisimple_iff_forall_theta (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
    IsRegularSemisimple g ↔ ∀ v, IsRegularSemisimple (Θ g v) := by
  have key : ∀ v, IsRegularSemisimple (Θ g v) ↔
      IsUnit (Ξ (Matrix.trace (g : Matrix (Fin 2) (Fin 2) _) ^ 2 - 4 * Matrix.det (g : Matrix (Fin 2) (Fin 2) _)) v) := by
    intro v
    unfold IsRegularSemisimple
    rw [hΘapp, disc_map]
    rfl
  simp_rw [key]
  rw [← Pi.isUnit_iff]
  unfold IsRegularSemisimple
  exact (MulEquiv.isUnit_map Ξ.toMulEquiv).symm

include hΘσ hΘι in
omit [NumberField L] in

theorem isNormConjugator_iff_forall (γ : GL (Fin 2) (InfiniteAdeleRing K))
    (δ y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
    IsNormConjugator K L (InfiniteAdeleRing K) σ γ δ y ↔
      ∀ v, IsNormConjugator K L v.Completion σ (thetaK K γ v) (Θ δ v) (Θ y v) := by
  unfold IsNormConjugator
  rw [← Θ.injective.eq_iff, funext_iff]
  refine forall_congr' fun v => ?_
  rw [hΘι, map_mul, map_mul, map_inv, Pi.mul_apply, Pi.mul_apply, Pi.inv_apply, theta_normString K L σ Θ hΘσ]

end ProductData
p2m_reactivate "P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm.CentAsmLocal"

section HReg

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]

attribute [local instance 10000] AutomorphicForm.glBorelOf
attribute [local instance] borelSpace_gl locallyCompactSpace_gl secondCountableTopology_gl t2Space_gl
  secondCountableTopology_completion

variable (σ : L ≃ₐ[K] L)
  (Ξ : L ⊗[K] InfiniteAdeleRing K ≃+* ((v : InfinitePlace K) → L ⊗[K] v.Completion))
  (Θ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) ≃ₜ* ((v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion)))
  (hΘapp : ∀ (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (v : InfinitePlace K),
    Θ g v = Matrix.GeneralLinearGroup.map
      ((Pi.evalRingHom (fun v : InfinitePlace K => L ⊗[K] v.Completion) v).comp Ξ.toRingHom) g)
  (hΘσ : ∀ (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (v : InfinitePlace K),
    Θ (sigmaGL K L (InfiniteAdeleRing K) σ g) v = sigmaGL K L v.Completion σ (Θ g v))
  (hΘι : ∀ (g : GL (Fin 2) (InfiniteAdeleRing K)) (v : InfinitePlace K),
    Θ (toTensorGL K L (InfiniteAdeleRing K) g) v = toTensorGL K L v.Completion (thetaK K g v))
  (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)

noncomputable abbrev piTwist : ((v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion)) →*
    ((v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion)) :=
  MonoidHom.pi fun i : InfinitePlace K =>
    (sigmaGL K L i.Completion σ).comp (Pi.evalMonoidHom (fun i : InfinitePlace K => GL (Fin 2) (L ⊗[K] i.Completion)) i)

noncomputable abbrev piEmb : ((v : InfinitePlace K) → GL (Fin 2) v.Completion) →*
    ((v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion)) :=
  MonoidHom.pi fun i : InfinitePlace K =>
    (toTensorGL K L i.Completion).comp (Pi.evalMonoidHom (fun i : InfinitePlace K => GL (Fin 2) i.Completion) i)

include hΘσ in
theorem theta_twist (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
    Θ (sigmaGL K L (InfiniteAdeleRing K) σ g) = piTwist K L σ (Θ g) := by
  funext v
  exact hΘσ g v

include hΘσ in
theorem theta_symm_twist (g : (v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion)) :
    Θ.symm (piTwist K L σ g) = sigmaGL K L (InfiniteAdeleRing K) σ (Θ.symm g) := by
  apply Θ.injective
  rw [Θ.apply_symm_apply, theta_twist K L σ Θ hΘσ, Θ.apply_symm_apply]

include hΘι in
theorem theta_emb (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    Θ (toTensorGL K L (InfiniteAdeleRing K) g) = piEmb K L (thetaKC K g) := by
  funext v
  exact hΘι g v

include hΘι in
theorem theta_symm_emb (g : (v : InfinitePlace K) → GL (Fin 2) v.Completion) :
    Θ.symm (piEmb K L g) = toTensorGL K L (InfiniteAdeleRing K) ((thetaKC K).symm g) := by
  apply Θ.injective
  rw [Θ.apply_symm_apply, theta_emb K L Θ hΘι, ContinuousMulEquiv.apply_symm_apply]

variable {K L} in
theorem continuous_toTensorGL (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (toTensorGL K L A) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  have h : Continuous (algebraMap A (L ⊗[K] A)) := by
    have heq : (algebraMap A (L ⊗[K] A) : A → L ⊗[K] A) = fun a => a • (1 : L ⊗[K] A) :=
      funext fun a => Algebra.algebraMap_eq_smul_one a
    rw [heq]
    exact continuous_id.fun_smul continuous_const
  have h' : Continuous (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) := by
    convert h using 1
    all_goals first | rfl | skip
  exact Continuous.units_map _ (continuous_id.matrix_map h')

theorem continuous_piEmb : Continuous (piEmb K L) :=
  continuous_pi fun v => (continuous_toTensorGL v.Completion).comp (continuous_apply v)

end HReg
p2m_reactivate "P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm.CentAsmLocal"

end FDTEF
p2m_reactivate "P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.FDTEF"

p2m_open "MeasureTheory NumberField AutomorphicForm P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.FDTEF"
open scoped TensorProduct
open scoped TensorProduct.RightActions

noncomputable section

namespace Ws46
namespace InvTC

section Transport

variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace H] [BorelSpace H]

theorem isInvInvariant_map_equiv (e : G ≃ₜ* H) (ν : Measure H) [ν.IsInvInvariant] :
    (ν.map e.symm).IsInvInvariant := by
  have hms : Measurable e.symm := e.symm.continuous.measurable
  constructor
  show Measure.map Inv.inv (Measure.map e.symm ν) = Measure.map e.symm ν
  rw [Measure.map_map measurable_inv hms,
    show (Inv.inv ∘ e.symm) = (e.symm ∘ Inv.inv) from funext fun x => (map_inv e.symm x).symm,
    ← Measure.map_map hms measurable_inv, Measure.map_inv_eq_self]

theorem isInvInvariant_of_continuousMulEquiv (e : G ≃ₜ* H)
    (hH : ∀ ν : Measure H, ν.IsHaarMeasure → ν.IsInvInvariant) (μ : Measure G) [μ.IsHaarMeasure] :
    μ.IsInvInvariant := by
  have hme : Measurable e := e.continuous.measurable
  have hms : Measurable e.symm := e.symm.continuous.measurable
  haveI : (μ.map e).IsHaarMeasure := e.isHaarMeasure_map μ
  haveI := hH (μ.map e) inferInstance
  have hback : (μ.map e).map e.symm = μ := by
    rw [Measure.map_map hms hme, show (e.symm ∘ e : G → G) = id from funext fun x => e.symm_apply_apply x,
      Measure.map_id]
  rw [← hback]
  exact isInvInvariant_map_equiv e _

end Transport
p2m_reactivate "P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.FDTEF"

section Pi

variable {ι : Type*} [Fintype ι] {G : ι → Type*} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  [∀ i, IsTopologicalGroup (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
  [∀ i, LocallyCompactSpace (G i)] [∀ i, SecondCountableTopology (G i)]

theorem isInvInvariant_pi (ν : ∀ i, Measure (G i)) [∀ i, SigmaFinite (ν i)] [∀ i, (ν i).IsInvInvariant] :
    (Measure.pi ν).IsInvInvariant := by
  constructor
  show Measure.map Inv.inv (Measure.pi ν) = Measure.pi ν
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply measurable_inv (MeasurableSet.univ_pi hs)]
  have hpre : (Inv.inv ⁻¹' Set.pi Set.univ s : Set (Π i, G i)) = Set.pi Set.univ fun i => (s i)⁻¹ := by
    ext x
    simp [Set.mem_pi]
  rw [hpre, Measure.pi_pi]
  exact Finset.prod_congr rfl fun i _ => Measure.measure_inv (ν i) (s i)

theorem isInvInvariant_of_pi (h : ∀ i, ∀ ν : Measure (G i), ν.IsHaarMeasure → ν.IsInvInvariant)
    (μ : Measure (Π i, G i)) [μ.IsHaarMeasure] : μ.IsInvInvariant := by
  haveI : ∀ i, (Measure.haar : Measure (G i)).IsInvInvariant := fun i => h i _ inferInstance
  have hν : (Measure.pi fun i => (Measure.haar : Measure (G i))).IsInvInvariant := isInvInvariant_pi _
  rw [Measure.isMulLeftInvariant_eq_smul_of_regular μ (Measure.pi fun i => (Measure.haar : Measure (G i)))]
  constructor
  show Measure.map Inv.inv _ = _
  rw [Measure.map_smul, Measure.map_inv_eq_self]

end Pi
p2m_reactivate "P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.FDTEF"

section SigmaPi

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]

def piTwistHom (θ : ∀ i, G i →* G i) : (Π i, G i) →* (Π i, G i) :=
  MonoidHom.pi fun i => (θ i).comp (Pi.evalMonoidHom G i)

@[scoped simp] theorem piTwistHom_apply (θ : ∀ i, G i →* G i) (g : Π i, G i) (i : ι) :
    piTwistHom θ g i = θ i (g i) := rfl

theorem mem_sigmaCentralizer_pi_iff (θ : ∀ i, G i →* G i) (δ t : Π i, G i) :
    t ∈ sigmaCentralizer (piTwistHom θ) δ ↔ ∀ i, t i ∈ sigmaCentralizer (θ i) (δ i) := by
  simp only [mem_sigmaCentralizer_iff, funext_iff, Pi.mul_apply, Pi.inv_apply, piTwistHom_apply]

variable [∀ i, TopologicalSpace (G i)]

def sigmaCentralizerPiEquiv (θ : ∀ i, G i →* G i) (δ : Π i, G i) :
    sigmaCentralizer (piTwistHom θ) δ ≃ₜ* Π i, sigmaCentralizer (θ i) (δ i) where
  toFun t := fun i => ⟨(t : Π i, G i) i, (mem_sigmaCentralizer_pi_iff θ δ t).1 t.2 i⟩
  invFun f := ⟨fun i => (f i : G i), (mem_sigmaCentralizer_pi_iff θ δ _).2 fun i => (f i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_pi fun i =>
    ((continuous_apply i).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_pi fun i =>
    continuous_subtype_val.comp (continuous_apply i)).subtype_mk _

end SigmaPi
p2m_reactivate "P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.FDTEF"

section Combined

variable {ι : Type*} [Fintype ι] {G : ι → Type*} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  [∀ i, IsTopologicalGroup (G i)] [∀ i, SecondCountableTopology (G i)]

theorem isInvInvariant_sigmaCentralizer_pi (θ : ∀ i, G i →* G i) (δ : Π i, G i)
    [∀ i, LocallyCompactSpace (sigmaCentralizer (θ i) (δ i))]
    (h : ∀ i, ∀ ν : @Measure (sigmaCentralizer (θ i) (δ i)) (borel _),
      @Measure.IsHaarMeasure _ _ _ (borel _) ν → @Measure.IsInvInvariant _ (borel _) _ ν)
    (μ : @Measure (sigmaCentralizer (piTwistHom θ) δ) (borel _))
    (hμ : @Measure.IsHaarMeasure _ _ _ (borel _) μ) :
    @Measure.IsInvInvariant _ (borel _) _ μ := by
  haveI : ∀ i, SecondCountableTopology (sigmaCentralizer (θ i) (δ i)) := fun i =>
    TopologicalSpace.Subtype.secondCountableTopology (sigmaCentralizer (θ i) (δ i) : Set (G i))
  letI : ∀ i, MeasurableSpace (sigmaCentralizer (θ i) (δ i)) := fun i => borel _
  haveI : ∀ i, BorelSpace (sigmaCentralizer (θ i) (δ i)) := fun i => ⟨rfl⟩
  letI : MeasurableSpace (sigmaCentralizer (piTwistHom θ) δ) := borel _
  haveI : BorelSpace (sigmaCentralizer (piTwistHom θ) δ) := ⟨rfl⟩
  exact isInvInvariant_of_continuousMulEquiv (sigmaCentralizerPiEquiv θ δ)
    (fun ν hν => isInvInvariant_of_pi (fun i ν' hν' => h i ν' hν') ν) μ

end Combined
p2m_reactivate "P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.FDTEF"

end Ws46.InvTC
p2m_reactivate "P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.FDTEF P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.Ws46 P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.Ws46.InvTC"
p2m_reactivate "P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.FDTEF P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.Ws46"

end
p2m_reactivate "P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.FDTEF P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.Ws46 P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.Ws46.InvTC"

noncomputable section

namespace Ws46
namespace InvTC

section Closed

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] (σ : L ≃ₐ[K] L)

theorem continuous_sigmaGL : Continuous (sigmaGL K L A σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  have h : Continuous (sigmaTensor K L A σ) := by
    have := IsModuleTopology.continuous_of_linearMap
      (TensorProduct.RightActions.AlgebraMap.baseChange K L L A σ.toAlgHom).toLinearMap
    exact this
  exact Continuous.units_map _ (continuous_id.matrix_map h)

theorem isClosed_twistedCentralizer [T2Space A] (δ : GL (Fin 2) (L ⊗[K] A)) :
    IsClosed (twistedCentralizer K L A σ δ : Set (GL (Fin 2) (L ⊗[K] A))) := by
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  haveI := AutomorphicForm.t2Space_tensorGL K L A
  have hc : Continuous fun t : GL (Fin 2) (L ⊗[K] A) => t * δ * (sigmaGL K L A σ t)⁻¹ :=
    (continuous_id.mul continuous_const).mul ((continuous_sigmaGL K L A σ).inv)
  have : (twistedCentralizer K L A σ δ : Set (GL (Fin 2) (L ⊗[K] A))) =
      (fun t : GL (Fin 2) (L ⊗[K] A) => t * δ * (sigmaGL K L A σ t)⁻¹) ⁻¹' {δ} := by
    ext t; exact mem_sigmaCentralizer_iff
  rw [this]
  exact (isClosed_singleton).preimage hc

theorem locallyCompactSpace_twistedCentralizer [T2Space A] [LocallyCompactSpace A] (δ : GL (Fin 2) (L ⊗[K] A)) :
    LocallyCompactSpace (twistedCentralizer K L A σ δ) := by
  haveI := AutomorphicForm.locallyCompactSpace_tensorGL K L A
  haveI := AutomorphicForm.t2Space_tensorGL K L A
  exact (isClosed_twistedCentralizer K L A σ δ).isClosedEmbedding_subtypeVal.locallyCompactSpace

end Closed
p2m_reactivate "P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.FDTEF P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.Ws46 P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.Ws46.InvTC"

section Reduction

variable (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]

attribute [local instance 10000] AutomorphicForm.glBorelOf
attribute [local instance] FDTEF.borelSpace_gl FDTEF.locallyCompactSpace_gl FDTEF.secondCountableTopology_gl
  FDTEF.t2Space_gl FDTEF.secondCountableTopology_completion
theorem locallyCompactSpace_tensorGL_completion'' (v : InfinitePlace K) :
    LocallyCompactSpace (GL (Fin 2) (L ⊗[K] v.Completion)) :=
  AutomorphicForm.locallyCompactSpace_tensorGL K L _

theorem isTopologicalGroup_tensorGL_completion'' (v : InfinitePlace K) :
    IsTopologicalGroup (GL (Fin 2) (L ⊗[K] v.Completion)) :=
  AutomorphicForm.isTopologicalGroup_tensorGL K L _

attribute [local instance] locallyCompactSpace_tensorGL_completion'' isTopologicalGroup_tensorGL_completion''

set_option maxHeartbeats 4000000 in

theorem isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_forall_completion (σ : L ≃ₐ[K] L)
    (hloc : ∀ (v : InfinitePlace K) (cv : (v.Completion)ˣ) (δv yv : GL (Fin 2) (L ⊗[K] v.Completion)),
      IsNormConjugator K L v.Completion σ (Matrix.GeneralLinearGroup.scalar (Fin 2) cv) δv yv →
      ∀ τv : @Measure (twistedCentralizer K L v.Completion σ δv) (twistedCentralizerBorel K L v.Completion σ δv),
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L v.Completion σ δv) τv →
        @Measure.IsInvInvariant _ (twistedCentralizerBorel K L v.Completion σ δv) _ τv)
    (c : (InfiniteAdeleRing K)ˣ) (δ y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (hδ : IsNormConjugator K L (InfiniteAdeleRing K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ' : @Measure (twistedCentralizer K L (InfiniteAdeleRing K) σ δ)
      (twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ) τ') :
    @Measure.IsInvInvariant _ (twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ) _ τ' := by
  classical
  obtain ⟨Ξ, Θ0, hΞ, hΞ', hΞt, hΘ, hΘ', hΘapp, hΘσ, hΘι⟩ := exists_thetaL K L
  let Θ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) ≃ₜ* ((v : InfinitePlace K) → GL (Fin 2) (L ⊗[K] v.Completion)) :=
    { Θ0 with continuous_toFun := hΘ, continuous_invFun := hΘ' }
  have hΘσ' : ∀ (g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (v : InfinitePlace K),
      Θ (sigmaGL K L (InfiniteAdeleRing K) σ g) v = sigmaGL K L v.Completion σ (Θ g v) := hΘσ σ
  have hΘι' : ∀ (g : GL (Fin 2) (InfiniteAdeleRing K)) (v : InfinitePlace K),
      Θ (toTensorGL K L (InfiniteAdeleRing K) g) v = toTensorGL K L v.Completion (thetaK K g v) := hΘι

  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (InfiniteAdeleRing K)
  haveI := AutomorphicForm.t2Space_tensorGL K L (InfiniteAdeleRing K)

  have hN' : ∀ v, IsNormConjugator K L v.Completion σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c v))
      (Θ δ v) (Θ y v) := by
    have h := (isNormConjugator_iff_forall K L σ Θ.toMulEquiv hΘσ' hΘι' _ δ y).1 hδ
    intro v
    have hv := h v
    rwa [show thetaK K (Matrix.GeneralLinearGroup.scalar (Fin 2) c) v =
        Matrix.GeneralLinearGroup.scalar (Fin 2) (unitAt K c v) from congrFun (thetaK_scalar K c) v] at hv

  letI mT : MeasurableSpace (twistedCentralizer K L (InfiniteAdeleRing K) σ δ) := twistedCentralizerBorel _ _ _ _ _
  haveI : BorelSpace (twistedCentralizer K L (InfiniteAdeleRing K) σ δ) := ⟨rfl⟩
  letI mT' : MeasurableSpace (sigmaCentralizer (piTwist K L σ) (Θ δ)) := borel _
  haveI : BorelSpace (sigmaCentralizer (piTwist K L σ) (Θ δ)) := ⟨rfl⟩
  haveI : τ'.IsHaarMeasure := hτ'

  let eT := CentAsmLocal.sigmaCentralizerCongr Θ (sigmaGL K L (InfiniteAdeleRing K) σ) (piTwist K L σ)
    (theta_twist K L σ Θ hΘσ') δ
  refine isInvInvariant_of_continuousMulEquiv eT (fun ν hν => ?_) τ'

  haveI : ∀ i : InfinitePlace K, LocallyCompactSpace
      (sigmaCentralizer (sigmaGL K L (InfinitePlace.Completion i) σ) (Θ δ i)) := fun i =>
    locallyCompactSpace_twistedCentralizer K L (InfinitePlace.Completion i) σ (Θ δ i)
  haveI : ∀ i : InfinitePlace K, SecondCountableTopology (L ⊗[K] InfinitePlace.Completion i) := fun i =>
    Module.Finite.secondCountabletopology (InfinitePlace.Completion i) (L ⊗[K] InfinitePlace.Completion i)
  haveI : ∀ i : InfinitePlace K, SecondCountableTopology (GL (Fin 2) (L ⊗[K] InfinitePlace.Completion i)) :=
    fun i => FDTEF.secondCountableTopology_gl _
  exact isInvInvariant_sigmaCentralizer_pi (G := fun i : InfinitePlace K => GL (Fin 2) (L ⊗[K] i.Completion))
    (fun i : InfinitePlace K => sigmaGL K L i.Completion σ) (Θ δ)
    (fun i τv hτv => hloc i (unitAt K c i) (Θ δ i) (Θ y i) (hN' i) τv hτv) ν hν

theorem solution_aux
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (c : (InfiniteAdeleRing K)ˣ)
    (δ y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (hδ : AutomorphicForm.IsNormConjugator K L (InfiniteAdeleRing K) σ
      (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ) τ') :
    @Measure.IsInvInvariant _ (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ) _ τ' :=
  isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_forall_completion K L σ
    (fun v cv δv yv hv τv hτv =>
      AutomorphicForm.isInvInvariant_twistedCentralizer_completion_of_isNormConjugator_scalar K L hprime σ hgen
        v cv δv yv hv τv hτv)
    c δ y hδ τ' hτ'

end Reduction
p2m_reactivate "P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.FDTEF P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.Ws46 P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.Ws46.InvTC"

end Ws46.InvTC
p2m_reactivate "P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.FDTEF P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.Ws46 P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.Ws46.InvTC"
p2m_reactivate "P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.FDTEF P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.Ws46 P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.Ws46.InvTC"

end
p2m_reactivate "P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm.CentAsmLocal P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.FDTEF P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.Ws46 P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.Ws46.InvTC"

p2m_open "MeasureTheory NumberField AutomorphicForm P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar.AutomorphicForm"
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (c : (InfiniteAdeleRing K)ˣ)
    (δ y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (hδ : AutomorphicForm.IsNormConjugator K L (InfiniteAdeleRing K) σ
      (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ) τ') :
    @Measure.IsInvInvariant _ (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ) _ τ' :=
  Ws46.InvTC.solution_aux K L hprime σ hgen c δ y hδ τ' hτ'

end S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar
end P2MW
export P2MW.S_AutomorphicForm_isInvInvariant_twistedCentralizer_infiniteAdeleRing_of_isNormConjugator_scalar (solution)
