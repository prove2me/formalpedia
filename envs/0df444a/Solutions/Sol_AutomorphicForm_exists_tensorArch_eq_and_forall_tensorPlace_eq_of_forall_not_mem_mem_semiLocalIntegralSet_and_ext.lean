-- Prove2me | solution 1 for AutomorphicForm.exists_tensorArch_eq_and_forall_tensorPlace_eq_of_forall_not_mem_mem_semiLocalIntegralSet_and_ext
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/394c33aa-e543-5e99-9c87-03c6b6ab8c51

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_tensorArch_eq_and_forall_tensorPlace_eq_of_forall_not_mem_mem_semiLocalIntegralSet_and_ext

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace K58ASM

open AdelicDock

section Arch

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

def archMat (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (AdeleRing R K) :=
  Matrix.of fun i j => ((g i j, (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)) i j) : AdeleRing R K)

theorem mapMatrix_arch_archMat (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :
    (AdelicLevel.adeleArch R K).mapMatrix (archMat R K g) = g := by
  ext i j
  simp [archMat, RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply]

theorem mapMatrix_fin_archMat (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :
    (AdelicLevel.adeleFin R K).mapMatrix (archMat R K g) = 1 := by
  ext i j
  simp [archMat, RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleFin_apply]

theorem archMat_one : archMat R K 1 = 1 :=
  matrix_eq_of_mapMatrix_arch_fin_eq R K (by rw [mapMatrix_arch_archMat, map_one])
    (by rw [mapMatrix_fin_archMat, map_one])

theorem archMat_mul (g h : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :
    archMat R K (g * h) = archMat R K g * archMat R K h :=
  matrix_eq_of_mapMatrix_arch_fin_eq R K
    (by rw [map_mul, mapMatrix_arch_archMat, mapMatrix_arch_archMat, mapMatrix_arch_archMat])
    (by rw [map_mul, mapMatrix_fin_archMat, mapMatrix_fin_archMat, mapMatrix_fin_archMat, mul_one])

def archEmbed : GL (Fin 2) (InfiniteAdeleRing K) →* GL (Fin 2) (AdeleRing R K) where
  toFun g :=
    { val := archMat R K g
      inv := archMat R K ((g⁻¹ : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix _ _ _)
      val_inv := by rw [← archMat_mul, Units.mul_inv, archMat_one]
      inv_val := by rw [← archMat_mul, Units.inv_mul, archMat_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact archMat_one R K)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact archMat_mul R K _ _)

theorem coe_archEmbed (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    ((archEmbed R K g : GL (Fin 2) (AdeleRing R K)) : Matrix _ _ _) = archMat R K g := rfl

theorem glArch_archEmbed (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    AdelicLevel.glArch R K (archEmbed R K g) = g := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicLevel.glArch_apply, coe_archEmbed]
  rfl

theorem glFin_archEmbed (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    AdelicLevel.glFin R K (archEmbed R K g) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicLevel.glFin_apply, coe_archEmbed, Units.val_one]
  rfl

def splice2 (a : GL (Fin 2) (InfiniteAdeleRing K)) (h : GL (Fin 2) (FiniteAdeleRing R K)) :
    GL (Fin 2) (AdeleRing R K) :=
  archEmbed R K a * finEmbed R K h

theorem glArch_splice2 (a : GL (Fin 2) (InfiniteAdeleRing K)) (h : GL (Fin 2) (FiniteAdeleRing R K)) :
    AdelicLevel.glArch R K (splice2 R K a h) = a := by
  rw [splice2, map_mul, glArch_archEmbed, glArch_finEmbed, mul_one]

theorem glFin_splice2 (a : GL (Fin 2) (InfiniteAdeleRing K)) (h : GL (Fin 2) (FiniteAdeleRing R K)) :
    AdelicLevel.glFin R K (splice2 R K a h) = h := by
  rw [splice2, map_mul, glFin_archEmbed, glFin_finEmbed, one_mul]

end Arch

section Assemble

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem semiLocalEval_apply (v : HeightOneSpectrum (𝓞 K)) (a : FiniteAdeleRing (𝓞 L) L) :
    AutomorphicForm.semiLocalEval K L v a =
      (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).symm
        (fun w : v.Extension (𝓞 L) => a w.1) :=
  rfl

theorem mem_semiLocalIntegers_iff_forall (v : HeightOneSpectrum (𝓞 K)) (x : L ⊗[K] v.adicCompletion K) :
    x ∈ AutomorphicForm.semiLocalIntegers K L v ↔
      ∀ w : v.Extension (𝓞 L),
        HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w ∈ w.1.adicCompletionIntegers L := by
  rw [AutomorphicForm.semiLocalIntegers_eq_preimage, Set.mem_preimage, AutomorphicForm.piIntegers,
    Set.mem_univ_pi]
  rfl

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

def assemble (y : ∀ v : HeightOneSpectrum (𝓞 K), L ⊗[K] v.adicCompletion K)
    (hy : ∀ v ∉ S, y v ∈ AutomorphicForm.semiLocalIntegers K L v) : FiniteAdeleRing (𝓞 L) L :=
  ⟨fun w => (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) (HeightOneSpectrum.under (𝓞 K) w)
      (y (HeightOneSpectrum.under (𝓞 K) w)) ⟨w, rfl⟩ : w.adicCompletion L),
    by
      refine Filter.eventually_cofinite.mpr ?_
      refine ((S.finite_toSet.preimage' (f := fun w : HeightOneSpectrum (𝓞 L) => HeightOneSpectrum.under (𝓞 K) w)
        fun v _ => ?_).subset ?_)
      · haveI := HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
        refine (Set.finite_range fun w : v.Extension (𝓞 L) => (w.1 : HeightOneSpectrum (𝓞 L))).subset ?_
        intro w hw
        exact ⟨⟨w, hw⟩, rfl⟩
      · intro w hw
        by_contra hS
        exact hw ((mem_semiLocalIntegers_iff_forall K L _ _).1 (hy _ hS) ⟨w, rfl⟩)⟩

theorem semiLocalEval_assemble (y : ∀ v : HeightOneSpectrum (𝓞 K), L ⊗[K] v.adicCompletion K)
    (hy : ∀ v ∉ S, y v ∈ AutomorphicForm.semiLocalIntegers K L v) (v : HeightOneSpectrum (𝓞 K)) :
    AutomorphicForm.semiLocalEval K L v (assemble K L S y hy) = y v := by
  rw [semiLocalEval_apply, AlgEquiv.symm_apply_eq]
  funext w
  obtain ⟨w, hw⟩ := w
  subst hw
  rfl

def assembleMat (M : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hM : ∀ v ∉ S, ∀ i j, M v i j ∈ AutomorphicForm.semiLocalIntegers K L v) :
    Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L) :=
  Matrix.of fun i j => assemble K L S (fun v => M v i j) (fun v hv => hM v hv i j)

theorem mapMatrix_assembleMat (M : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hM : ∀ v ∉ S, ∀ i j, M v i j ∈ AutomorphicForm.semiLocalIntegers K L v) (v : HeightOneSpectrum (𝓞 K)) :
    (AutomorphicForm.semiLocalEval K L v).mapMatrix (assembleMat K L S M hM) = M v := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, assembleMat, Matrix.of_apply, semiLocalEval_assemble]

def assembleGL (x : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hx : ∀ v ∉ S, x v ∈ AutomorphicForm.semiLocalIntegralSet K L v) : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) where
  val := assembleMat K L S (fun v => ((x v : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix _ _ _))
    (fun v hv => (AutomorphicForm.mem_integralUnitsSet.1 (hx v hv)).1)
  inv := assembleMat K L S (fun v => ((x v)⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) )
    (fun v hv => (AutomorphicForm.mem_integralUnitsSet.1 (hx v hv)).2)
  val_inv := AutomorphicForm.matrix_eq_of_forall_semiLocalEval_mapMatrix_eq K L fun v => by
    rw [map_mul, mapMatrix_assembleMat, mapMatrix_assembleMat, map_one, ← Units.val_mul, mul_inv_cancel,
      Units.val_one]
  inv_val := AutomorphicForm.matrix_eq_of_forall_semiLocalEval_mapMatrix_eq K L fun v => by
    rw [map_mul, mapMatrix_assembleMat, mapMatrix_assembleMat, map_one, ← Units.val_mul, inv_mul_cancel,
      Units.val_one]

theorem semiLocalComponent_assembleGL (x : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hx : ∀ v ∉ S, x v ∈ AutomorphicForm.semiLocalIntegralSet K L v) (v : HeightOneSpectrum (𝓞 K)) :
    AutomorphicForm.semiLocalComponent K L v (assembleGL K L S x hx) = x v := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have := congrFun (congrFun (mapMatrix_assembleMat K L S
    (fun v => ((x v : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix _ _ _))
    (fun v hv => (AutomorphicForm.mem_integralUnitsSet.1 (hx v hv)).1) v) i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at this
  exact this

open scoped TensorProduct.RightActions in

theorem exists_tensorArch_eq_and_forall_tensorPlace_eq
    (xa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (xv : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hxv : ∀ v ∉ S, xv v ∈ AutomorphicForm.semiLocalIntegralSet K L v) :
    ∃ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      AutomorphicForm.tensorArch K L x = xa ∧
      ∀ v : HeightOneSpectrum (𝓞 K), AutomorphicForm.tensorPlace K L v x = xv v := by
  let y : GL (Fin 2) (AdeleRing (𝓞 L) L) :=
    archEmbed (𝓞 L) L (AutomorphicForm.archIdentGLEquiv K L xa) * finEmbed (𝓞 L) L (assembleGL K L S xv hxv)
  refine ⟨(AutomorphicForm.baseChangeGLEquiv K L).symm y, ?_, fun v => ?_⟩
  · apply (AutomorphicForm.archIdentGLEquiv K L).injective
    rw [AutomorphicForm.archIdentGLEquiv_apply K L (AutomorphicForm.tensorArch K L _),
      ← AutomorphicForm.glArch_baseChangeGL, ← AutomorphicForm.baseChangeGLEquiv_apply,
      ContinuousMulEquiv.apply_symm_apply, map_mul, glArch_archEmbed, glArch_finEmbed, mul_one]
  · rw [← AutomorphicForm.semiLocalComponent_glFin_baseChangeGL, ← AutomorphicForm.baseChangeGLEquiv_apply,
      ContinuousMulEquiv.apply_symm_apply, map_mul, glFin_archEmbed, glFin_finEmbed, one_mul,
      semiLocalComponent_assembleGL]

end Assemble

end K58ASM

end

open scoped TensorProduct.RightActions in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    (∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (xa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
        (xv : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
        (∀ v ∉ S, xv v ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
        ∃ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
          AutomorphicForm.tensorArch K L x = xa ∧
          ∀ v : HeightOneSpectrum (𝓞 K), AutomorphicForm.tensorPlace K L v x = xv v) ∧
    (∀ x x' : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
        AutomorphicForm.tensorArch K L x = AutomorphicForm.tensorArch K L x' →
        (∀ v : HeightOneSpectrum (𝓞 K), AutomorphicForm.tensorPlace K L v x = AutomorphicForm.tensorPlace K L v x') →
          x = x') := by
  refine ⟨fun S xa xv hxv => ?_, fun x x' h₁ h₂ => ?_⟩
  · exact K58ASM.exists_tensorArch_eq_and_forall_tensorPlace_eq K L S xa xv hxv
  · exact AutomorphicForm.eq_of_tensorArch_eq_of_forall_tensorPlace_eq K L h₁ h₂

end S_AutomorphicForm_exists_tensorArch_eq_and_forall_tensorPlace_eq_of_forall_not_mem_mem_semiLocalIntegralSet_and_ext
end P2MW
export P2MW.S_AutomorphicForm_exists_tensorArch_eq_and_forall_tensorPlace_eq_of_forall_not_mem_mem_semiLocalIntegralSet_and_ext (solution)
