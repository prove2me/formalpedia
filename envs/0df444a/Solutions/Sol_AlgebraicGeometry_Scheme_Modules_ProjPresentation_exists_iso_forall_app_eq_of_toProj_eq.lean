-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_iso_forall_app_eq_of_toProj_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/f16355a8-a9a7-5676-8bca-7ca4b87e835c

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_existsUnique_hom_app_eq_of_iSup_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_iso_forall_app_eq_of_toProj_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

p2m_open "CategoryTheory.MonoidalCategory Opposite"

attribute [local instance] MvPolynomial.gradedAlgebra

namespace TwoPresSol

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules} {N : ℕ}
  (𝔓 : Scheme.Modules.ProjPresentation M f N)

noncomputable abbrev D (R : Type u) [CommRing R] (N : ℕ) (i : Fin (N + 1)) :
    (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)).Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)

noncomputable abbrev U (i : Fin (N + 1)) : X.Opens := 𝔓.toProj ⁻¹ᵁ D R N i

noncomputable def r (i j : Fin (N + 1)) : Γ(X, U 𝔓 i) :=
  𝔓.toProj.app (D R N i) (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio R N i j))

noncomputable def a (i : Fin (N + 1)) (W : X.Opens) : Γ(M, W) :=
  M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (𝔓.σ i)

theorem map_a (i : Fin (N + 1)) {W W' : X.Opens} (h : W' ≤ W) :
    M.presheaf.map (homOfLE h).op (a 𝔓 i W) = a 𝔓 i W' := by
  unfold a
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  rfl

theorem bijective_smul_a (i : Fin (N + 1)) (W : X.Opens) (hW : W ≤ U 𝔓 i) :
    Function.Bijective fun g : Γ(X, W) => g • a 𝔓 i W :=
  𝔓.frame i W hW

theorem isFrameOn_a (i : Fin (N + 1)) (W : X.Opens) : Scheme.Modules.IsFrameOn (a 𝔓 i W) (U 𝔓 i) := by
  intro W' hW'W hW'U
  have hb := bijective_smul_a 𝔓 i W' hW'U
  have heq : (fun g : Γ(X, W') => g • M.presheaf.map (homOfLE hW'W).op (a 𝔓 i W)) = fun g => g • a 𝔓 i W' := by
    funext g; rw [map_a]
  rw [heq]; exact hb

noncomputable def uu (i j : Fin (N + 1)) (W : X.Opens) (hW : W ≤ U 𝔓 i) : Γ(X, W) :=
  X.presheaf.map (homOfLE hW).op (r 𝔓 i j)

theorem a_eq_uu_smul (i j : Fin (N + 1)) (W : X.Opens) (hW : W ≤ U 𝔓 i) :
    a 𝔓 j W = uu 𝔓 i j W hW • a 𝔓 i W := by
  have h0 := 𝔓.app_ratio_smul i j
  have h1 := congrArg (M.presheaf.map (homOfLE hW).op) h0
  rw [Scheme.Modules.map_smul] at h1
  change X.presheaf.map (homOfLE hW).op (r 𝔓 i j) • M.presheaf.map (homOfLE hW).op (a 𝔓 i (U 𝔓 i)) =
    M.presheaf.map (homOfLE hW).op (a 𝔓 j (U 𝔓 i)) at h1
  rw [map_a, map_a] at h1
  exact h1.symm

theorem uu_eq {M' : X.Modules} (𝔔 : Scheme.Modules.ProjPresentation M' f N) (h : 𝔓.toProj = 𝔔.toProj)
    (i j : Fin (N + 1)) (W : X.Opens) (hWP : W ≤ U 𝔓 i) (hWQ : W ≤ U 𝔔 i) :
    uu 𝔓 i j W hWP = uu 𝔔 i j W hWQ := by
  have key : ∀ (G G' : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)) (e : G = G')
      (hG : W ≤ G ⁻¹ᵁ D R N i) (hG' : W ≤ G' ⁻¹ᵁ D R N i),
      X.presheaf.map (homOfLE hG).op (G.app (D R N i) (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio R N i j))) =
      X.presheaf.map (homOfLE hG').op (G'.app (D R N i) (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio R N i j))) := by
    rintro G _ rfl _ _; rfl
  exact key _ _ h _ _

theorem iSup_U : ⨆ i, U 𝔓 i = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  let y := 𝔓.toProj.base x
  let j : Fin (N + 1) := (ProjSpace.affineOpenCover R N).openCover.idx y
  have hc : y ∈ Set.range ((ProjSpace.affineOpenCover R N).openCover.f j).base :=
    (ProjSpace.affineOpenCover R N).openCover.covers y
  have h2 : y ∈ (Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
      (MvPolynomial.X j) (ProjSpace.X_mem_one R N j) one_pos).opensRange :=
    Scheme.Hom.mem_opensRange.mpr hc
  rw [Proj.opensRange_awayι] at h2
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, h2⟩

noncomputable def coeff (i : Fin (N + 1)) (W : X.Opens) (hW : W ≤ U 𝔓 i) :
    Γ(M, W) →ₗ[Γ(X, W)] Γ(X, W) :=
  (LinearEquiv.ofBijective (LinearMap.toSpanSingleton Γ(X, W) _ (a 𝔓 i W)) (bijective_smul_a 𝔓 i W hW)).symm.toLinearMap

theorem coeff_smul (i : Fin (N + 1)) (W : X.Opens) (hW : W ≤ U 𝔓 i) (g : Γ(X, W)) :
    coeff 𝔓 i W hW (g • a 𝔓 i W) = g := by
  unfold coeff
  apply (bijective_smul_a 𝔓 i W hW).1
  change (LinearMap.toSpanSingleton Γ(X, W) _ (a 𝔓 i W))
    ((LinearEquiv.ofBijective (LinearMap.toSpanSingleton Γ(X, W) _ (a 𝔓 i W)) (bijective_smul_a 𝔓 i W hW)).symm
      (g • a 𝔓 i W)) = g • a 𝔓 i W
  rw [← LinearEquiv.ofBijective_apply (hf := bijective_smul_a 𝔓 i W hW), LinearEquiv.apply_symm_apply]

variable {M' : X.Modules} (𝔔 : Scheme.Modules.ProjPresentation M' f N) (h : 𝔓.toProj = 𝔔.toProj)

include h in
theorem U_eq (i : Fin (N + 1)) : U 𝔓 i = U 𝔔 i := by
  change 𝔓.toProj ⁻¹ᵁ D R N i = 𝔔.toProj ⁻¹ᵁ D R N i
  rw [h]

noncomputable def floc (W : X.Opens) (hW : ∃ i, W ≤ U 𝔓 i) : Γ(M, W) →ₗ[Γ(X, W)] Γ(M', W) :=
  (LinearMap.toSpanSingleton Γ(X, W) _ (a 𝔔 hW.choose W)).comp (coeff 𝔓 hW.choose W hW.choose_spec)

include h in

theorem floc_smul_a (W : X.Opens) (hW : ∃ i, W ≤ U 𝔓 i) (j : Fin (N + 1)) (hj : W ≤ U 𝔓 j) (g : Γ(X, W)) :
    floc 𝔓 𝔔 W hW (g • a 𝔓 j W) = g • a 𝔔 j W := by
  set i := hW.choose with hi
  have hiW : W ≤ U 𝔓 i := hW.choose_spec
  have hiWQ : W ≤ U 𝔔 i := (U_eq 𝔓 𝔔 h i) ▸ hiW
  unfold floc
  rw [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
  rw [a_eq_uu_smul 𝔓 i j W hiW, smul_smul, coeff_smul 𝔓, a_eq_uu_smul 𝔔 i j W hiWQ, smul_smul,
    uu_eq 𝔓 𝔔 h i j W hiW hiWQ]

include h in
theorem floc_a (W : X.Opens) (hW : ∃ i, W ≤ U 𝔓 i) (j : Fin (N + 1)) (hj : W ≤ U 𝔓 j) :
    floc 𝔓 𝔔 W hW (a 𝔓 j W) = a 𝔔 j W := by
  have := floc_smul_a 𝔓 𝔔 h W hW j hj 1
  rwa [one_smul, one_smul] at this

include h in

theorem map_floc (W W' : X.Opens) (hW : ∃ i, W ≤ U 𝔓 i) (hle : W' ≤ W) (x : Γ(M, W)) :
    M'.presheaf.map (homOfLE hle).op (floc 𝔓 𝔔 W hW x) =
      floc 𝔓 𝔔 W' (hW.imp fun _ hi => hle.trans hi) (M.presheaf.map (homOfLE hle).op x) := by
  obtain ⟨i, hi⟩ := hW
  obtain ⟨g, rfl⟩ := (bijective_smul_a 𝔓 i W hi).2 x
  simp only []
  rw [floc_smul_a 𝔓 𝔔 h W ⟨i, hi⟩ i hi g, Scheme.Modules.map_smul, Scheme.Modules.map_smul, map_a 𝔓, map_a 𝔔,
    floc_smul_a 𝔓 𝔔 h W' _ i (hle.trans hi)]

include h in

theorem floc_a_any (W : X.Opens) (hW : ∃ i, W ≤ U 𝔓 i) (i j : Fin (N + 1)) (hj : W ≤ U 𝔓 j) :
    floc 𝔓 𝔔 W hW (a 𝔓 i W) = a 𝔔 i W := by
  have hjQ : W ≤ U 𝔔 j := (U_eq 𝔓 𝔔 h j) ▸ hj
  rw [a_eq_uu_smul 𝔓 j i W hj, floc_smul_a 𝔓 𝔔 h W hW j hj, uu_eq 𝔓 𝔔 h j i W hj hjQ, ← a_eq_uu_smul 𝔔 j i W hjQ]

theorem app_map {P Q : X.Modules} (φ : P ⟶ Q) {V V' : X.Opens} (hle : V' ≤ V) (x : Γ(P, V)) :
    Q.presheaf.map (homOfLE hle).op (φ.app V x) = φ.app V' (P.presheaf.map (homOfLE hle).op x) := by
  have := φ.mapPresheaf.naturality (homOfLE hle).op
  have e := congrArg (fun f => f x) this
  simpa using e.symm

end TwoPresSol

open TwoPresSol in
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {M M' : X.Modules} {N : ℕ}
    (P : M.ProjPresentation f N) (Q : M'.ProjPresentation f N) (h : P.toProj = Q.toProj) :
    ∃ φ : M ≅ M', ∀ i : Fin (N + 1), φ.hom.app ⊤ (P.σ i) = Q.σ i := by
  obtain ⟨F, hF, -⟩ := AlgebraicGeometry.Scheme.Modules.existsUnique_hom_app_eq_of_iSup_eq_top
    M M' (U P) (iSup_U P)
    (fun W hW => floc P Q W hW) (fun W W' hW hle x => map_floc P Q h W W' hW hle x)
  haveI : IsIso F :=
    AlgebraicGeometry.Scheme.Modules.isIso_of_isFrameOn_of_iSup_eq_top_monoidalV2 F (U P) (iSup_U P)
      (fun i => a P i (U P i)) (fun i => a Q i (U P i))
      (fun i => isFrameOn_a P i _) (fun i => (isFrameOn_a Q i (U P i)).mono (U_eq P Q h i).le)
      (fun i => by rw [hF (U P i) ⟨i, le_rfl⟩]; exact floc_a P Q h _ ⟨i, le_rfl⟩ i le_rfl)
  refine ⟨asIso F, fun i => ?_⟩
  show F.app ⊤ (P.σ i) = Q.σ i
  apply TopCat.Sheaf.eq_of_locally_eq' (⟨M'.presheaf, M'.isSheaf⟩ : TopCat.Sheaf Ab X) (U P) ⊤
    (fun j => homOfLE le_top) (by rw [iSup_U P])
  intro j
  show M'.presheaf.map (homOfLE (le_top : U P j ≤ ⊤)).op (F.app ⊤ (P.σ i)) =
    M'.presheaf.map (homOfLE (le_top : U P j ≤ ⊤)).op (Q.σ i)
  rw [app_map F (le_top : U P j ≤ ⊤), hF (U P j) ⟨j, le_rfl⟩]
  exact floc_a_any P Q h (U P j) ⟨j, le_rfl⟩ i j le_rfl

end S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_iso_forall_app_eq_of_toProj_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_iso_forall_app_eq_of_toProj_eq (solution)
