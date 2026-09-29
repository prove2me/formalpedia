-- Prove2me | solution 1 for AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_isReframe
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/c03aceba-c2d3-5941-a911-e8d6436facef

import Definitions.Def_AlgebraicGeometry_ThetaReframe
import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isClosedImmersion_toProj_of_isSectionBasis_of_closedImmersionBySections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_sum_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_mem_isFrameOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_smul_of_forall_exists_bijective_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_isReframe

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

noncomputable section

namespace Reframe31

universe u

variable {g N n : ℕ} {S : Type u} [CommRing S] (X : FramedPolarisedAbelianScheme g N n S)

abbrev cst (s : S) : Γ(X.A, ⊤) :=
  (X.f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom s)

theorem cst_mul (s s' : S) : cst X (s * s') = cst X s * cst X s' := by
  simp only [cst, map_mul]

theorem cst_sum {ι : Type} (T : Finset ι) (s : ι → S) : cst X (∑ i ∈ T, s i) = ∑ i ∈ T, cst X (s i) := by
  simp only [cst, map_sum]

abbrev σ' (U : Matrix (Fin (N + 1)) (Fin (N + 1)) S) (i : Fin (N + 1)) : Γ(X.pol, ⊤) :=
  ∑ j : Fin (N + 1), cst X (U i j) • X.frame.σ j

theorem sum_cst_smul_σ' (U : Matrix (Fin (N + 1)) (Fin (N + 1)) S) (c : Fin (N + 1) → S) :
    ∑ i, cst X (c i) • σ' X U i = ∑ j, cst X ((Matrix.vecMul c U) j) • X.frame.σ j := by
  simp only [σ', Finset.smul_sum, smul_smul, ← cst_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul, ← cst_sum]
  rfl

theorem isSectionBasis_σ' (U : Matrix (Fin (N + 1)) (Fin (N + 1)) S) (hU : IsUnit U) :
    Scheme.Modules.IsSectionBasis X.f X.pol (σ' X U) := by
  obtain ⟨u, rfl⟩ := hU
  have hb := X.frame_basis
  unfold Scheme.Modules.IsSectionBasis Scheme.Modules.IsSectionBasisOn at hb ⊢
  have hcomp : (fun c : Fin (N + 1) → S => ∑ i, cst X (c i) • σ' X (u : Matrix (Fin (N + 1)) (Fin (N + 1)) S) i) =
      (fun c : Fin (N + 1) → S => ∑ j, cst X (c j) • X.frame.σ j) ∘ (fun c => Matrix.vecMul c (u : Matrix (Fin (N + 1)) (Fin (N + 1)) S)) := by
    funext c; exact sum_cst_smul_σ' X _ c
  change Function.Bijective (fun c : Fin (N + 1) → S => ∑ i, cst X (c i) • σ' X (u : Matrix (Fin (N + 1)) (Fin (N + 1)) S) i)
  rw [hcomp]
  refine Function.Bijective.comp hb ?_
  refine Function.bijective_iff_has_inverse.mpr ⟨fun c => Matrix.vecMul c (↑u⁻¹ : Matrix (Fin (N + 1)) (Fin (N + 1)) S), fun c => ?_, fun c => ?_⟩
  · simp [Matrix.vecMul_vecMul]
  · simp [Matrix.vecMul_vecMul]

abbrev RawFrame (s : Γ(X.pol, ⊤)) (W : X.A.Opens) : Prop :=
  ∀ V : X.A.Opens, V ≤ W →
    Function.Bijective fun g : Γ(X.A, V) => g • (X.pol.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s : Γ(X.pol, V))

theorem rawFrame_of_isFrameOn {s : Γ(X.pol, ⊤)} {W : X.A.Opens} (h : Scheme.Modules.IsFrameOn s W) :
    RawFrame X s W :=
  fun V hV => h le_top hV

theorem σ_eq_sum (u : (Matrix (Fin (N + 1)) (Fin (N + 1)) S)ˣ) (k : Fin (N + 1)) :
    X.frame.σ k = ∑ j, cst X ((↑u⁻¹ : Matrix (Fin (N + 1)) (Fin (N + 1)) S) k j) • σ' X ↑u j := by
  rw [sum_cst_smul_σ']
  have h1 : ∀ j', Matrix.vecMul (fun j => (↑u⁻¹ : Matrix (Fin (N + 1)) (Fin (N + 1)) S) k j)
      (↑u : Matrix (Fin (N + 1)) (Fin (N + 1)) S) j' = if k = j' then 1 else 0 := by
    intro j'
    have h : Matrix.vecMul ((↑u⁻¹ : Matrix (Fin (N + 1)) (Fin (N + 1)) S) k)
        (↑u : Matrix (Fin (N + 1)) (Fin (N + 1)) S) j' =
        ((↑u⁻¹ : Matrix (Fin (N + 1)) (Fin (N + 1)) S) * (↑u : Matrix (Fin (N + 1)) (Fin (N + 1)) S)) k j' := by
      rw [Matrix.mul_apply']; rfl
    rw [Units.inv_mul, Matrix.one_apply] at h
    exact h
  have h2 : ∀ j', cst X (Matrix.vecMul (fun j => (↑u⁻¹ : Matrix (Fin (N + 1)) (Fin (N + 1)) S) k j)
      (↑u : Matrix (Fin (N + 1)) (Fin (N + 1)) S) j') • X.frame.σ j' = if k = j' then X.frame.σ j' else 0 := by
    intro j'
    rw [h1]
    split_ifs
    · simp only [cst, map_one, one_smul]
    · simp only [cst, map_zero, zero_smul]
  rw [Finset.sum_congr rfl fun j' _ => h2 j', Finset.sum_ite_eq]
  simp

theorem exists_cover (u : (Matrix (Fin (N + 1)) (Fin (N + 1)) S)ˣ) :
    ∃ W : Fin (N + 1) → X.A.Opens, iSup W = ⊤ ∧ ∀ (i : Fin (N + 1)) (V : X.A.Opens), V ≤ W i →
      Function.Bijective fun g : Γ(X.A, V) =>
        g • (X.pol.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (σ' X ↑u i) : Γ(X.pol, V)) := by
  refine ⟨fun i => ⨆ (W : X.A.Opens) (_ : RawFrame X (σ' X ↑u i) W), W, ?_, ?_⟩
  · refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨k, U₀, hxU₀, hk⟩ := X.frame.exists_mem_isFrameOn x
    have hk' := rawFrame_of_isFrameOn X hk
    rw [σ_eq_sum X u k] at hk'
    obtain ⟨j, W, hxW, hW⟩ := Scheme.Modules.exists_frame_of_frame_sum_smul X.pol
      (fun j => cst X ((↑u⁻¹ : Matrix (Fin (N + 1)) (Fin (N + 1)) S) k j)) (σ' X ↑u) x ⟨U₀, hxU₀, hk'⟩
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, TopologicalSpace.Opens.mem_iSup.2 ⟨W, TopologicalSpace.Opens.mem_iSup.2 ⟨hW, hxW⟩⟩⟩
  · intro i V hV
    apply Scheme.Modules.bijective_smul_of_forall_exists_bijective_smul X.pol (σ' X ↑u i) V
    intro x hx
    obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.1 (hV hx)
    obtain ⟨hPW, hxW⟩ := TopologicalSpace.Opens.mem_iSup.1 hW
    exact ⟨W, hxW, hPW⟩

theorem exists_isReframe (U : Matrix (Fin (N + 1)) (Fin (N + 1)) S) (hU : IsUnit U) :
    ∃ X' : FramedPolarisedAbelianScheme g N n S, X.IsReframe U X' := by
  obtain ⟨u, rfl⟩ := hU
  obtain ⟨W, hW, hfr⟩ := exists_cover X u
  obtain ⟨P', hPσ, -⟩ :=
    Scheme.Modules.exists_projPresentation_of_iSup_eq_top X.f X.pol N (σ' X ↑u) W hW hfr
  have h₂ : Scheme.Modules.IsSectionBasis X.f X.pol P'.σ := by
    rw [hPσ]; exact isSectionBasis_σ' X ↑u (Units.isUnit u)
  have h₁ : IsClosedImmersion P'.toProj :=
    Scheme.Modules.ProjPresentation.isClosedImmersion_toProj_of_isSectionBasis_of_closedImmersionBySections
      ⟨N, X.frame, X.frame_isClosedImmersion⟩ P' h₂
  exact ⟨⟨X.toPolarisedAbelianScheme, P', h₁, h₂⟩, P', h₁, h₂, rfl, fun i => by rw [hPσ]⟩

end Reframe31

end

theorem solution
    {g N n : ℕ} {S : Type} [CommRing S] (X : FramedPolarisedAbelianScheme g N n S)
    (U : Matrix (Fin (N + 1)) (Fin (N + 1)) S) (hU : IsUnit U) :
    ∃ X' : FramedPolarisedAbelianScheme g N n S, X.IsReframe U X' :=
  Reframe31.exists_isReframe X U hU

end S_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_isReframe
end P2MW
export P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_exists_isReframe (solution)
