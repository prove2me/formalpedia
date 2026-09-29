-- Prove2me | solution 1 for AlgebraicGeometry.FramedPolarisedAbelianScheme.iso_of_isReframe_inter_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/5060fbf0-84e1-55ab-90e3-fc6759efab38

import Definitions.Def_AlgebraicGeometry_ThetaReframe
import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_ThetaLevel_exists_eq_smul_one_of_forall_mul_schrodMat_eq_schrodMat_mul
import Theorems.Thm_AlgebraicGeometry_ThetaLevel_exists_isIntertwiner_of_mem_gam
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_toProj_eq_of_forall_sections_eq_univ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_of_isReframe_inter_mul

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

universe u

namespace K79Engine

open AlgebraicGeometry.Scheme.Modules

noncomputable def smulPresentation {R : Type u} [CommRing R] {X : Scheme.{u}} {M : X.Modules}
    {f : X ⟶ Spec (CommRingCat.of R)} {N : ℕ}
    (P : M.ProjPresentation f N) (c : Γ(X, ⊤)) (hc : IsUnit c) : M.ProjPresentation f N where
  σ := fun i => c • P.σ i
  toProj := P.toProj
  toProj_π := P.toProj_π
  frame := fun i V hV => by
    have key : (fun g : Γ(X, V) => g • M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (c • P.σ i)) =
        (fun g : Γ(X, V) => g • M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (P.σ i)) ∘
          (fun g : Γ(X, V) => g * X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op c) := by
      funext g
      simp only [Function.comp_apply, Scheme.Modules.map_smul, smul_smul]
    rw [key]
    exact (P.frame i V hV).comp
      (Units.mulRight (hc.map (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom).unit).bijective
  app_ratio_smul := fun i j => by
    rw [Scheme.Modules.map_smul, Scheme.Modules.map_smul, smul_comm, P.app_ratio_smul i j]

theorem smulPresentation_σ {R : Type u} [CommRing R] {X : Scheme.{u}} {M : X.Modules}
    {f : X ⟶ Spec (CommRingCat.of R)} {N : ℕ}
    (P : M.ProjPresentation f N) (c : Γ(X, ⊤)) (hc : IsUnit c) (i : Fin (N + 1)) :
    (smulPresentation P c hc).σ i = c • P.σ i := rfl

theorem smulPresentation_toProj {R : Type u} [CommRing R] {X : Scheme.{u}} {M : X.Modules}
    {f : X ⟶ Spec (CommRingCat.of R)} {N : ℕ}
    (P : M.ProjPresentation f N) (c : Γ(X, ⊤)) (hc : IsUnit c) :
    (smulPresentation P c hc).toProj = P.toProj := rfl

end K79Engine

namespace K79CL3

open AlgebraicGeometry.FramedPolarisedAbelianScheme

theorem iso_mk_mk_of_toProj_eq {g N n : ℕ} {S : Type} [CommRing S] (X : FramedPolarisedAbelianScheme g N n S)
    (P : Scheme.Modules.ProjPresentation X.pol X.f N) (h₁ : IsClosedImmersion P.toProj)
    (h₂ : Scheme.Modules.IsSectionBasis X.f X.pol P.σ)
    (P' : Scheme.Modules.ProjPresentation X.pol X.f N) (h₁' : IsClosedImmersion P'.toProj)
    (h₂' : Scheme.Modules.IsSectionBasis X.f X.pol P'.σ) (h : P.toProj = P'.toProj) :
    FramedPolarisedAbelianScheme.Iso (⟨X.toPolarisedAbelianScheme, P, h₁, h₂⟩ : FramedPolarisedAbelianScheme g N n S)
      ⟨X.toPolarisedAbelianScheme, P', h₁', h₂'⟩ := by
  refine ⟨Iso.refl _, Category.id_comp _, ?_, ?_, ?_, ?_⟩
  · change 𝟙 _ ≫ P'.toProj = P.toProj
    rw [Category.id_comp, h]
  · intro T t x y
    change (X.L.mul t x y).1 ≫ 𝟙 _ = (X.L.mul t ⟨x.1 ≫ 𝟙 _, _⟩ ⟨y.1 ≫ 𝟙 _, _⟩).1
    rw [Category.comp_id]
    congr 1
  · intro i
    exact Category.comp_id _
  · intro s
    refine ⟨⊤, trivial, ⟨?_⟩⟩
    exact (Scheme.Modules.pullback (X.f ⁻¹ᵁ ⊤).ι).mapIso ((Scheme.Modules.pullbackId X.A).app X.pol)

noncomputable def ψ {g N n : ℕ} {S : Type} [CommRing S] (X : FramedPolarisedAbelianScheme g N n S) : S →+* Γ(X.A, ⊤) :=
  (X.f.appLE ⊤ ⊤ le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom

theorem ψ_apply {g N n : ℕ} {S : Type} [CommRing S] (X : FramedPolarisedAbelianScheme g N n S) (s : S) :
    ψ X s = (X.f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom s) := rfl

theorem sum_smul_sum_smul {g N n : ℕ} {S : Type} [CommRing S] (X : FramedPolarisedAbelianScheme g N n S)
    (A C : Matrix (Fin (N + 1)) (Fin (N + 1)) S) (σ : Fin (N + 1) → Γ(X.pol, ⊤)) (i : Fin (N + 1)) :
    ∑ j, ψ X (A i j) • ∑ k, ψ X (C j k) • σ k = ∑ k, ψ X ((A * C) i k) • σ k := by
  simp only [Finset.smul_sum, smul_smul, ← map_mul, Matrix.mul_apply, map_sum, Finset.sum_smul]
  rw [Finset.sum_comm]

end K79CL3

open AlgebraicGeometry.ThetaLevel K79CL3 in
theorem solution
    (g N n : ℕ) (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (hδd : ∏ i, δ i = N + 1)
    (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    (B : Type) [CommRing B] (hd : IsUnit ((N + 1 : ℕ) : B))
    (ζ : B) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (ω : B) (hω : ω ^ 2 = ζ)
    {S : Type} [CommRing S] (φB : B →+* S) (γ γ' : (ThetaLevel.Heis.Gam (δ := δ) (d := N + 1)))
    (X X₁ X₂ X₃ : FramedPolarisedAbelianScheme g N n S)
    (h₁ : X.IsReframe ((Matrix.transpose (ThetaLevel.inter δ (N + 1) B ω e ((γ * γ')⁻¹).1)).map φB) X₁)
    (h₂ : X.IsReframe ((Matrix.transpose (ThetaLevel.inter δ (N + 1) B ω e ((γ')⁻¹).1)).map φB) X₂) (h₃ : X₂.IsReframe ((Matrix.transpose (ThetaLevel.inter δ (N + 1) B ω e ((γ)⁻¹).1)).map φB) X₃) :
    FramedPolarisedAbelianScheme.Iso X₁ X₃ := by
  classical

  set a : MulAut (Heis δ (N + 1)) := (γ⁻¹).1 with ha
  set b : MulAut (Heis δ (N + 1)) := (γ'⁻¹).1 with hb
  have hba : ((γ * γ')⁻¹).1 = b * a := by rw [mul_inv_rev]; rfl
  rw [hba] at h₁
  set Ia := inter δ (N + 1) B ω e a with hIa
  set Ib := inter δ (N + 1) B ω e b with hIb
  set Iba := inter δ (N + 1) B ω e (b * a) with hIba

  obtain ⟨hau, haz⟩ := isIntertwiner_inter δ (N + 1) B ω e a
    (exists_isIntertwiner_of_mem_gam δ (N + 1) hδd B hd ζ ω hζ hζu hω e a (γ⁻¹).2)
  obtain ⟨hbu, hbz⟩ := isIntertwiner_inter δ (N + 1) B ω e b
    (exists_isIntertwiner_of_mem_gam δ (N + 1) hδd B hd ζ ω hζ hζu hω e b (γ'⁻¹).2)
  obtain ⟨hbau, hbaz⟩ := isIntertwiner_inter δ (N + 1) B ω e (b * a)
    (exists_isIntertwiner_of_mem_gam δ (N + 1) hδd B hd ζ ω hζ hζu hω e (b * a) (γ'⁻¹ * γ⁻¹).2)

  have hT : ∀ z, (Ib * Ia) * schrodMat δ (N + 1) B ω e z = schrodMat δ (N + 1) B ω e ((b * a) z) * (Ib * Ia) := by
    intro z
    rw [Matrix.mul_assoc, haz, ← Matrix.mul_assoc, hbz, MulAut.mul_apply, Matrix.mul_assoc]
  have hTu : IsUnit (Ib * Ia) := hbu.mul hau

  obtain ⟨Ti, hTi₁, hTi₂, hTiu⟩ : ∃ Ti : Matrix (Fin (N + 1)) (Fin (N + 1)) B,
      Ti * (Ib * Ia) = 1 ∧ (Ib * Ia) * Ti = 1 ∧ IsUnit Ti := by
    refine ⟨((hTu.unit⁻¹ : (Matrix (Fin (N + 1)) (Fin (N + 1)) B)ˣ) : Matrix (Fin (N + 1)) (Fin (N + 1)) B), ?_, ?_,
      Units.isUnit _⟩
    · have h := hTu.unit.inv_mul
      rwa [hTu.unit_spec] at h
    · have h := hTu.unit.mul_inv
      rwa [hTu.unit_spec] at h

  have hD : ∀ z, (Ti * Iba) * schrodMat δ (N + 1) B ω e z = schrodMat δ (N + 1) B ω e z * (Ti * Iba) := by
    intro z
    have hinv : Ti * schrodMat δ (N + 1) B ω e ((b * a) z) = schrodMat δ (N + 1) B ω e z * Ti := by
      have e1 : Ti * schrodMat δ (N + 1) B ω e ((b * a) z) =
          Ti * schrodMat δ (N + 1) B ω e ((b * a) z) * ((Ib * Ia) * Ti) := by rw [hTi₂, mul_one]
      have e2 : Ti * schrodMat δ (N + 1) B ω e ((b * a) z) * ((Ib * Ia) * Ti) =
          Ti * ((Ib * Ia) * schrodMat δ (N + 1) B ω e z) * Ti := by
        rw [hT z]; simp only [mul_assoc]
      have e3 : Ti * ((Ib * Ia) * schrodMat δ (N + 1) B ω e z) * Ti = schrodMat δ (N + 1) B ω e z * Ti := by
        rw [← mul_assoc Ti, hTi₁, one_mul]
      rw [e1, e2, e3]
    rw [mul_assoc, hbaz, ← mul_assoc, hinv, mul_assoc]
  obtain ⟨c, hc⟩ := exists_eq_smul_one_of_forall_mul_schrodMat_eq_schrodMat_mul δ (N + 1) hδd B ζ ω hζ hζu hω e
    (Ti * Iba) hD

  have hIba : Iba = c • (Ib * Ia) := by
    calc Iba = ((Ib * Ia) * Ti) * Iba := by rw [hTi₂, one_mul]
      _ = (Ib * Ia) * (c • 1) := by rw [mul_assoc, hc]
      _ = c • (Ib * Ia) := by rw [Matrix.mul_smul, mul_one]
  have hcu : IsUnit c := by
    have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (hTiu.mul hbau)
    rw [hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
    exact isUnit_pow_succ_iff.mp hdet

  obtain ⟨P₁, hP₁, hP₁', rfl, hσ₁⟩ := h₁
  obtain ⟨P₂, hP₂, hP₂', rfl, hσ₂⟩ := h₂
  obtain ⟨P₃, hP₃, hP₃', rfl, hσ₃⟩ := h₃

  set u : Γ(X.A, ⊤) := ψ X (φB c) with hu
  have huu : IsUnit u := (hcu.map φB).map (ψ X)
  have hentry : ∀ i k, ((Matrix.transpose Iba).map φB) i k =
      φB c * (((Matrix.transpose Ia).map φB) * ((Matrix.transpose Ib).map φB)) i k := by
    intro i k
    simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.mul_apply, hIba, Matrix.smul_apply, smul_eq_mul,
      map_mul, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hσ₃' : ∀ i, P₃.σ i = ∑ k, ψ X ((((Matrix.transpose Ia).map φB) * ((Matrix.transpose Ib).map φB)) i k) • X.frame.σ k := by
    intro i
    rw [hσ₃ i]
    change ∑ j, ψ X _ • P₂.σ j = _
    simp_rw [hσ₂]
    change ∑ j, ψ X _ • ∑ k, ψ X _ • X.frame.σ k = _
    exact sum_smul_sum_smul X _ _ X.frame.σ i
  have hσ' : ∀ i, P₁.σ i = u • P₃.σ i := by
    intro i
    rw [hσ₁ i, hσ₃' i, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    change ψ X _ • X.frame.σ k = _
    rw [hentry, map_mul, smul_smul]
  have htp : P₁.toProj = P₃.toProj :=
    AlgebraicGeometry.Scheme.Modules.ProjPresentation.toProj_eq_of_forall_sections_eq_univ P₁
      (K79Engine.smulPresentation P₃ u huu) hσ'
  exact iso_mk_mk_of_toProj_eq X P₁ hP₁ hP₁' P₃ hP₃ hP₃' htp

end S_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_of_isReframe_inter_mul
end P2MW
export P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_iso_of_isReframe_inter_mul (solution)
