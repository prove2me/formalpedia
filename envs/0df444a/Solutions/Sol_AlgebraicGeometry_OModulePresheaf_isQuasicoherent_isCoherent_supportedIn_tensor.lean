-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.isQuasicoherent_isCoherent_supportedIn_tensor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/8b1e8541-90f3-5488-a0a6-0c547f3e9654

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_isCoherent_supportedIn_tensor

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace P2mTensorStableSol

section Alg

variable {A : Type*} [CommRing A] (S : Submonoid A) (A' : Type*) [CommRing A'] [Algebra A A']
  [IsLocalization S A']
variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
variable {M' N' : Type*} [AddCommGroup M'] [Module A' M'] [Module A M'] [IsScalarTower A A' M']
  [AddCommGroup N'] [Module A' N'] [Module A N'] [IsScalarTower A A' N']
variable (lM : M →ₗ[A] M') (lN : N →ₗ[A] N')

noncomputable def diag : M ⊗[A] N →ₗ[A] M' ⊗[A'] N' :=
  TensorProduct.lift
    (LinearMap.mk₂ A (fun x y => lM x ⊗ₜ[A'] lN y)
      (fun x₁ x₂ y => by simp only [map_add, add_tmul])
      (fun a x y => by simp only [map_smul, smul_tmul'])
      (fun x y₁ y₂ => by simp only [map_add, tmul_add])
      (fun a x y => by simp only [map_smul, tmul_smul]))

theorem diag_tmul (x : M) (y : N) : diag A' lM lN (x ⊗ₜ y) = lM x ⊗ₜ[A'] lN y := rfl

include S in
theorem isLocalizedModule_diag [IsLocalizedModule S lM] [IsLocalizedModule S lN] :
    IsLocalizedModule S (diag A' lM lN) := by
  let e : M' ⊗[A'] N' ≃ₗ[A] M' ⊗[A] N' := (IsLocalization.moduleTensorEquiv S A' M' N').restrictScalars A
  have he : ∀ (x : M') (y : N'), e (x ⊗ₜ[A'] y) = x ⊗ₜ[A] y := fun x y => rfl
  have hcomp : (e.symm : M' ⊗[A] N' →ₗ[A] M' ⊗[A'] N') ∘ₗ TensorProduct.map lM lN = diag A' lM lN := by
    refine TensorProduct.ext' fun x y => ?_
    rw [LinearMap.comp_apply, TensorProduct.map_tmul, diag_tmul, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_eq, he]
  rw [← hcomp]
  infer_instance

end Alg

section Datum

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}

@[reducible] noncomputable def modBO (F : OModulePresheaf π) (U : V.Opens) (f : Γ(V, U)) :
    Module Γ(V, U) (F.obj (V.basicOpen f)) :=
  Module.compHom (F.obj (V.basicOpen f)) (algebraMap Γ(V, U) Γ(V, V.basicOpen f))

theorem isScalarTower_modBO (F : OModulePresheaf π) (U : V.Opens) (f : Γ(V, U)) :
    letI := modBO F U f
    IsScalarTower Γ(V, U) Γ(V, V.basicOpen f) (F.obj (V.basicOpen f)) :=
  letI := modBO F U f
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

noncomputable def resBO (F : OModulePresheaf π) (U : V.Opens) (f : Γ(V, U)) :
    letI := modBO F U f
    F.obj U →ₗ[Γ(V, U)] F.obj (V.basicOpen f) :=
  letI := modBO F U f
  { toFun := F.res (V.basicOpen_le f)
    map_add' := fun x y => map_add _ x y
    map_smul' := fun a x => F.res_smul (V.basicOpen_le f) a x }

theorem resBO_apply (F : OModulePresheaf π) (U : V.Opens) (f : Γ(V, U)) (x : F.obj U) :
    letI := modBO F U f
    resBO F U f x = F.res (V.basicOpen_le f) x := rfl

theorem isLocalizedModule_resBO (F : OModulePresheaf π) (hF : F.IsQuasicoherent) (U : V.affineOpens)
    (f : Γ(V, U.1)) :
    letI := modBO F U.1 f
    IsLocalizedModule (Submonoid.powers f) (resBO F U.1 f) := by
  letI := modBO F U.1 f
  haveI := isScalarTower_modBO F U.1 f
  haveI : IsLocalization.Away f Γ(V, V.basicOpen f) := U.2.isLocalization_basicOpen f
  obtain ⟨h1, h2⟩ := hF U f
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, n, rfl⟩
    rw [Module.End.isUnit_iff]
    have hu : IsUnit (algebraMap Γ(V, U.1) Γ(V, V.basicOpen f) (f ^ n)) := by
      rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit f).pow n
    have := hu.smul_bijective (β := F.obj (V.basicOpen f))
    exact this
  · intro y
    obtain ⟨n, x, hx⟩ := h1 y
    exact ⟨⟨x, ⟨f ^ n, n, rfl⟩⟩, hx.symm⟩
  · intro x₁ x₂ h
    have h0 : F.res (V.basicOpen_le f) (x₁ - x₂) = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr h
    obtain ⟨n, hn⟩ := h2 (x₁ - x₂) h0
    refine ⟨⟨f ^ n, n, rfl⟩, ?_⟩
    rw [Submonoid.smul_def, Submonoid.smul_def, ← sub_eq_zero, ← smul_sub]
    exact hn

theorem qcAt_of_isLocalizedModule (F : OModulePresheaf π) (U : V.affineOpens) (f : Γ(V, U.1))
    (h : letI := modBO F U.1 f; IsLocalizedModule (Submonoid.powers f) (resBO F U.1 f)) :
    (∀ x : F.obj (V.basicOpen f), ∃ (n : ℕ) (y : F.obj U.1),
        F.res (V.basicOpen_le f) y = (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ n) • x)
      ∧ (∀ y : F.obj U.1, F.res (V.basicOpen_le f) y = 0 → ∃ n : ℕ, (f ^ n : Γ(V, U.1)) • y = 0) := by
  letI := modBO F U.1 f
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · obtain ⟨⟨y, ⟨s, n, rfl⟩⟩, hs⟩ := h.surj x
    exact ⟨n, y, hs.symm⟩
  · have h0 : resBO F U.1 f y = resBO F U.1 f 0 := by rw [map_zero]; exact hy
    obtain ⟨⟨s, n, rfl⟩, hs⟩ := h.exists_of_eq h0
    refine ⟨n, ?_⟩
    simpa [Submonoid.smul_def] using hs

end Datum

section Card

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} (F G : OModulePresheaf π)

theorem isQuasicoherent_tensor (hF : F.IsQuasicoherent) (hG : G.IsQuasicoherent) :
    (F.tensor G).IsQuasicoherent := by
  intro U f

  letI := modBO F U.1 f; letI := modBO G U.1 f
  haveI := isScalarTower_modBO F U.1 f; haveI := isScalarTower_modBO G U.1 f
  haveI : IsLocalization.Away f Γ(V, V.basicOpen f) := U.2.isLocalization_basicOpen f
  haveI := isLocalizedModule_resBO F hF U f
  haveI := isLocalizedModule_resBO G hG U f
  have hdiag := isLocalizedModule_diag (Submonoid.powers f) Γ(V, V.basicOpen f) (resBO F U.1 f) (resBO G U.1 f)

  letI := modBO (F.tensor G) U.1 f
  have key : IsLocalizedModule (Submonoid.powers f) (resBO (F.tensor G) U.1 f) := by
    have hfun : ∀ t, resBO (F.tensor G) U.1 f t
        = diag Γ(V, V.basicOpen f) (resBO F U.1 f) (resBO G U.1 f) t := fun t => rfl
    refine ⟨fun s => ?_, fun y => ?_, fun {x₁ x₂} h => ?_⟩
    · have := hdiag.map_units s
      rw [Module.End.isUnit_iff] at this ⊢
      exact this
    · obtain ⟨p, hp⟩ := hdiag.surj y
      exact ⟨p, by rw [hfun]; exact hp⟩
    · rw [hfun, hfun] at h
      exact hdiag.exists_of_eq h
  exact qcAt_of_isLocalizedModule (F.tensor G) U f key

theorem isCoherent_tensor (hF : F.IsCoherent) (hG : G.IsCoherent) : (F.tensor G).IsCoherent := by
  intro U
  haveI := hF U; haveI := hG U
  show Module.Finite Γ(V, U.1) (F.obj U.1 ⊗[Γ(V, U.1)] G.obj U.1)
  infer_instance

theorem supportedIn_tensor (Y : TopologicalSpace.Closeds V) (h : F.SupportedIn Y ∨ G.SupportedIn Y) :
    (F.tensor G).SupportedIn Y := by
  intro U hU
  show Subsingleton (F.obj U.1 ⊗[Γ(V, U.1)] G.obj U.1)
  rcases h with h | h
  · haveI := h U hU; infer_instance
  · haveI := h U hU; infer_instance

theorem main :
    (F.IsQuasicoherent → G.IsQuasicoherent → (F.tensor G).IsQuasicoherent) ∧
    (F.IsCoherent → G.IsCoherent → (F.tensor G).IsCoherent) ∧
    (∀ Y : TopologicalSpace.Closeds V, F.SupportedIn Y ∨ G.SupportedIn Y → (F.tensor G).SupportedIn Y) :=
  ⟨isQuasicoherent_tensor F G, isCoherent_tensor F G, supportedIn_tensor F G⟩

end Card

end P2mTensorStableSol

theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} (F G : OModulePresheaf π) :
    (F.IsQuasicoherent → G.IsQuasicoherent → (F.tensor G).IsQuasicoherent) ∧
    (F.IsCoherent → G.IsCoherent → (F.tensor G).IsCoherent) ∧
    (∀ Y : TopologicalSpace.Closeds V, F.SupportedIn Y ∨ G.SupportedIn Y → (F.tensor G).SupportedIn Y) :=
  P2mTensorStableSol.main F G

end S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_isCoherent_supportedIn_tensor
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_isCoherent_supportedIn_tensor (solution)
