-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_unit_smul_eq_of_toProj_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/b81d1a8e-e8c7-5e60-b80c-eda08f995ff1

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_unit_smul_eq_of_toProj_eq

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

end TwoPresSol

namespace C2Sol
open TwoPresSol

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules} {N : ℕ}
  (P P' : Scheme.Modules.ProjPresentation M f N) (h : P.toProj = P'.toProj)

theorem smul_a_inj (j : Fin (N + 1)) (W : X.Opens) (hW : W ≤ U P j) {g g' : Γ(X, W)}
    (e : g • a P j W = g' • a P j W) : g = g' :=
  (bijective_smul_a P j W hW).1 e

include h in

theorem exists_c (j : Fin (N + 1)) : ∃ c : Γ(X, U P j), c • a P j (U P j) = a P' j (U P j) :=
  (bijective_smul_a P j (U P j) le_rfl).2 _

include h in
theorem exists_c' (j : Fin (N + 1)) : ∃ c' : Γ(X, U P j), c' • a P' j (U P j) = a P j (U P j) :=
  (bijective_smul_a P' j (U P j) ((U_eq P P' h j).le)).2 _

theorem res_smul_a {j : Fin (N + 1)} {W W' : X.Opens} (hle : W' ≤ W) (c : Γ(X, W)) (Q : Scheme.Modules.ProjPresentation M f N) :
    M.presheaf.map (homOfLE hle).op (c • a Q j W) = X.presheaf.map (homOfLE hle).op c • a Q j W' := by
  rw [Scheme.Modules.map_smul, map_a]

include h in
theorem main : ∃ u : (Γ(X, ⊤))ˣ, ∀ i : Fin (N + 1), P'.σ i = (u : Γ(X, ⊤)) • P.σ i := by
  classical
  choose c hc using exists_c P P' h
  choose c' hc' using exists_c' P P' h

  have hcompat : ∀ (j l : Fin (N + 1)) (W : X.Opens) (hj : W ≤ U P j) (hl : W ≤ U P l),
      X.presheaf.map (homOfLE hj).op (c j) = X.presheaf.map (homOfLE hl).op (c l) := by
    intro j l W hj hl
    have hl' : W ≤ U P' l := (U_eq P P' h l) ▸ hl
    apply smul_a_inj P j W hj
    have e1 := congrArg (M.presheaf.map (homOfLE hj).op) (hc j)
    rw [res_smul_a, map_a] at e1
    have e2 := congrArg (M.presheaf.map (homOfLE hl).op) (hc l)
    rw [res_smul_a, map_a] at e2
    rw [e1, a_eq_uu_smul P' l j W hl', ← e2, smul_smul, a_eq_uu_smul P l j W hl, smul_smul,
      uu_eq P P' h l j W hl hl', mul_comm]
  have hcompat' : ∀ (j l : Fin (N + 1)) (W : X.Opens) (hj : W ≤ U P j) (hl : W ≤ U P l),
      X.presheaf.map (homOfLE hj).op (c' j) = X.presheaf.map (homOfLE hl).op (c' l) := by
    intro j l W hj hl
    have hj' : W ≤ U P' j := (U_eq P P' h j) ▸ hj
    have hl' : W ≤ U P' l := (U_eq P P' h l) ▸ hl
    apply smul_a_inj P' j W hj'
    have e1 := congrArg (M.presheaf.map (homOfLE hj).op) (hc' j)
    rw [res_smul_a, map_a] at e1
    have e2 := congrArg (M.presheaf.map (homOfLE hl).op) (hc' l)
    rw [res_smul_a, map_a] at e2
    rw [e1, a_eq_uu_smul P l j W hl, ← e2, smul_smul, a_eq_uu_smul P' l j W hl', smul_smul,
      uu_eq P P' h l j W hl hl', mul_comm]

  obtain ⟨u, hu⟩ : ∃ u : Γ(X, ⊤), ∀ j, X.presheaf.map (homOfLE (le_top : U P j ≤ ⊤)).op u = c j :=
    (TopCat.Sheaf.existsUnique_gluing' X.sheaf (U P) ⊤ (fun j => homOfLE le_top)
      (by rw [iSup_U P]) c (fun j l => hcompat j l _ inf_le_left inf_le_right)).exists
  obtain ⟨u', hu'⟩ : ∃ u' : Γ(X, ⊤), ∀ j, X.presheaf.map (homOfLE (le_top : U P j ≤ ⊤)).op u' = c' j :=
    (TopCat.Sheaf.existsUnique_gluing' X.sheaf (U P) ⊤ (fun j => homOfLE le_top)
      (by rw [iSup_U P]) c' (fun j l => hcompat' j l _ inf_le_left inf_le_right)).exists

  have huu' : u * u' = 1 := by
    apply TopCat.Sheaf.eq_of_locally_eq' X.sheaf (U P) ⊤ (fun j => homOfLE le_top) (by rw [iSup_U P])
    intro j
    show X.presheaf.map (homOfLE (le_top : U P j ≤ ⊤)).op (u * u') =
      X.presheaf.map (homOfLE (le_top : U P j ≤ ⊤)).op 1
    rw [show X.presheaf.map (homOfLE (le_top : U P j ≤ ⊤)).op (u * u') =
        X.presheaf.map (homOfLE (le_top : U P j ≤ ⊤)).op u * X.presheaf.map (homOfLE (le_top : U P j ≤ ⊤)).op u' from
        map_mul _ _ _,
      show X.presheaf.map (homOfLE (le_top : U P j ≤ ⊤)).op (1 : Γ(X, ⊤)) = 1 from map_one _, hu j, hu' j]
    apply smul_a_inj P j (U P j) le_rfl
    rw [one_smul, mul_comm, ← smul_smul, hc, hc']
  refine ⟨Units.mkOfMulEqOne u u' huu', fun i => ?_⟩

  apply TopCat.Sheaf.eq_of_locally_eq' (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X) (U P) ⊤
    (fun j => homOfLE le_top) (by rw [iSup_U P])
  intro j
  have hj' : U P j ≤ U P' j := (U_eq P P' h j).le
  show M.presheaf.map (homOfLE (le_top : U P j ≤ ⊤)).op (P'.σ i) =
    M.presheaf.map (homOfLE (le_top : U P j ≤ ⊤)).op ((u : Γ(X, ⊤)) • P.σ i)
  rw [Scheme.Modules.map_smul, hu j]
  change a P' i (U P j) = c j • a P i (U P j)
  rw [a_eq_uu_smul P' j i (U P j) hj', ← hc j, smul_smul, a_eq_uu_smul P j i (U P j) le_rfl, smul_smul,
    uu_eq P P' h j i (U P j) le_rfl hj', mul_comm]

end C2Sol

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} {M : X.Modules} {f : X ⟶ Spec (.of R)} {N : ℕ}
    (P P' : M.ProjPresentation f N) (h : P.toProj = P'.toProj) :
    ∃ u : (Γ(X, ⊤))ˣ, ∀ i : Fin (N + 1), P'.σ i = (u : Γ(X, ⊤)) • P.σ i :=
  C2Sol.main P P' h

end S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_unit_smul_eq_of_toProj_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_unit_smul_eq_of_toProj_eq (solution)
