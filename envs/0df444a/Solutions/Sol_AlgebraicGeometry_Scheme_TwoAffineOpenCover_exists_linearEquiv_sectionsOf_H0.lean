-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/95790957-0329-559e-a986-1ad6a18775d0

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0.AlgebraicGeometry TopologicalSpace Opposite"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective Spec Scheme Scheme.TwoAffineOpenCover.moduleSectionsOfHom Scheme.TwoAffineOpenCover"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Γ Modules Opens TwoAffineOpenCover.moduleSectionsOfHom TwoAffineOpenCover"
namespace TwoAffineOpenCover
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "moduleSectionsOfHom restrictSections sectionsOf restrict_mem_H0 U1 U0 sup_eq_top"
namespace ModH0
p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
  (M : X.Modules)

noncomputable abbrev rM {V W : X.Opens} (h : V ≤ W) : Γ(M, W) → Γ(M, V) := fun y => M.presheaf.map (homOfLE h).op y

omit [CommRing R] in
theorem rM_rM {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (y : Γ(M, V₁)) :
    rM M h₃₂ (rM M h₂₁ y) = rM M (h₃₂.trans h₂₁) y := by
  show (M.presheaf.map (homOfLE h₂₁).op ≫ M.presheaf.map (homOfLE h₃₂).op) y = _
  rw [← Functor.map_comp]; rfl

omit [CommRing R] in
theorem map_eq_rM {V W : X.Opens} (i : V ⟶ W) (y : Γ(M, W)) :
    M.presheaf.map i.op y = rM M (leOfHom i) y := by
  rw [Subsingleton.elim i (homOfLE (leOfHom i))]

noncomputable def F : TopCat.Sheaf Ab X.carrier := ⟨M.presheaf, M.isSheaf⟩

theorem restrict_mem_H0 (s : Γ(M, ⊤)) :
    ((show (𝒱.sectionsOf c M).M0 from rM M (le_top : 𝒱.U0 ≤ ⊤) s),
      (show (𝒱.sectionsOf c M).M1 from rM M (le_top : 𝒱.U1 ≤ ⊤) s)) ∈ (𝒱.sectionsOf c M).H0 := by
  rw [TwoChartCech.Sections.mem_H0_iff]
  show rM M inf_le_left (rM M le_top s) = rM M inf_le_right (rM M le_top s)
  rw [rM_rM, rM_rM]

noncomputable def toH0M : letI := moduleSectionsOfHom c M ⊤; Γ(M, ⊤) →ₗ[R] (𝒱.sectionsOf c M).H0 :=
  letI := moduleSectionsOfHom c M ⊤
  letI := moduleSectionsOfHom c M 𝒱.U0
  letI := moduleSectionsOfHom c M 𝒱.U1
  LinearMap.codRestrict ((𝒱.sectionsOf c M).H0)
    ((show Γ(M, ⊤) →ₗ[R] (𝒱.sectionsOf c M).M0 from restrictSections c M (le_top : 𝒱.U0 ≤ ⊤)).prod
      (show Γ(M, ⊤) →ₗ[R] (𝒱.sectionsOf c M).M1 from restrictSections c M (le_top : 𝒱.U1 ≤ ⊤)))
    (fun s => restrict_mem_H0 𝒱 c M s)

theorem toH0M_apply_coe (s : Γ(M, ⊤)) :
    letI := moduleSectionsOfHom c M ⊤
    ((toH0M 𝒱 c M s : (𝒱.sectionsOf c M).M0 × (𝒱.sectionsOf c M).M1)) =
      (M.presheaf.map (homOfLE (le_top : 𝒱.U0 ≤ ⊤)).op s,
        M.presheaf.map (homOfLE (le_top : 𝒱.U1 ≤ ⊤)).op s) := rfl

theorem toH0M_injective : letI := moduleSectionsOfHom c M ⊤; Function.Injective (toH0M 𝒱 c M) := by
  letI := moduleSectionsOfHom c M ⊤
  intro s t hst
  have h := congrArg Subtype.val hst
  rw [toH0M_apply_coe, toH0M_apply_coe] at h
  exact TopCat.Sheaf.eq_of_locally_eq₂ (F M) (homOfLE (le_top : 𝒱.U0 ≤ ⊤)) (homOfLE (le_top : 𝒱.U1 ≤ ⊤))
    𝒱.sup_eq_top.ge s t (congrArg Prod.fst h) (congrArg Prod.snd h)

def U2 : Bool → X.Opens := fun b => cond b 𝒱.U1 𝒱.U0

omit [CommRing R] in
theorem iSup_U2 : iSup (U2 𝒱) = ⊤ := by
  rw [← 𝒱.sup_eq_top]
  apply le_antisymm
  · exact iSup_le fun b => by cases b <;> simp [U2]
  · exact sup_le (le_iSup (U2 𝒱) false) (le_iSup (U2 𝒱) true)

theorem toH0M_surjective : letI := moduleSectionsOfHom c M ⊤; Function.Surjective (toH0M 𝒱 c M) := by
  letI := moduleSectionsOfHom c M ⊤
  rintro ⟨⟨p0, p1⟩, hp⟩
  have hp' : rM M inf_le_left p0 = rM M inf_le_right p1 :=
    (TwoChartCech.Sections.mem_H0_iff _ _).mp hp

  let sf : ∀ b : Bool, (F M).1.obj (op (U2 𝒱 b)) := fun b => match b with
    | false => p0
    | true => p1
  have hcomp : TopCat.Presheaf.IsCompatible (F M).1 (U2 𝒱) sf := by
    intro i j
    show M.presheaf.map _ (sf i) = M.presheaf.map _ (sf j)
    rw [map_eq_rM, map_eq_rM]
    cases i <;> cases j
    · rfl
    ·
      exact hp'
    ·
      show rM M (inf_le_left : 𝒱.U1 ⊓ 𝒱.U0 ≤ 𝒱.U1) p1 = rM M (inf_le_right : 𝒱.U1 ⊓ 𝒱.U0 ≤ 𝒱.U0) p0
      have h10 : 𝒱.U1 ⊓ 𝒱.U0 ≤ 𝒱.U0 ⊓ 𝒱.U1 := le_of_eq (inf_comm _ _)
      rw [← rM_rM M inf_le_right h10, ← rM_rM M inf_le_left h10, hp']
    · rfl
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F M) (U2 𝒱) ⊤ (fun b => homOfLE le_top)
    (iSup_U2 𝒱).ge sf hcomp
  refine ⟨s, Subtype.ext ?_⟩
  rw [toH0M_apply_coe]
  exact Prod.ext (hs false) (hs true)

theorem exists_linearEquiv :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c M ⊤
    ∃ e : Γ(M, ⊤) ≃ₗ[R] (𝒱.sectionsOf c M).H0, ∀ s : Γ(M, ⊤),
      ((e s : (𝒱.sectionsOf c M).M0 × (𝒱.sectionsOf c M).M1)) =
        (M.presheaf.map (homOfLE (le_top : 𝒱.U0 ≤ ⊤)).op s,
          M.presheaf.map (homOfLE (le_top : 𝒱.U1 ≤ ⊤)).op s) := by
  letI := moduleSectionsOfHom c M ⊤
  exact ⟨LinearEquiv.ofBijective (toH0M 𝒱 c M) ⟨toH0M_injective 𝒱 c M, toH0M_surjective 𝒱 c M⟩,
    fun s => toH0M_apply_coe 𝒱 c M s⟩

end AlgebraicGeometry.Scheme.TwoAffineOpenCover.ModH0

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (M : X.Modules) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c M ⊤
    ∃ e : Γ(M, ⊤) ≃ₗ[R] (𝒱.sectionsOf c M).H0, ∀ s : Γ(M, ⊤),
      ((e s : (𝒱.sectionsOf c M).M0 × (𝒱.sectionsOf c M).M1)) =
        (M.presheaf.map (homOfLE (le_top : 𝒱.U0 ≤ ⊤)).op s,
          M.presheaf.map (homOfLE (le_top : 𝒱.U1 ≤ ⊤)).op s) :=
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.ModH0.exists_linearEquiv 𝒱 c M

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0 (solution)
