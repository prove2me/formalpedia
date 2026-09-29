-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.app_injective_and_exists_of_forall_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/8a8dba13-5876-56ae-9acc-77fb77a8cfe3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_app_injective_and_exists_of_forall_isAffineOpen

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Hom_app_injective_and_exists_of_forall_isAffineOpen.AlgebraicGeometry"

universe u

open TopologicalSpace Opposite

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom Scheme exists_isAffineOpen_mem_and_subset IsAffineOpen Scheme.Hom.preimage_iSup Scheme.Hom.comp_preimage"
p2m_open "AlgebraicGeometry"

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Hom mk Γ mk.injEq Hom.preimage_iSup Opens Hom.comp_preimage" end Scheme
p2m_open_scoped "AlgebraicGeometry.Scheme" in

theorem Scheme.iSup_affineOpens_le {X : Scheme.{u}} (U : X.Opens) :
    ⨆ (V : {V : X.Opens // IsAffineOpen V ∧ V ≤ U}), (V : X.Opens) = U := by
  apply le_antisymm
  · exact iSup_le fun V => V.2.2
  · intro x hx
    obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := U) hx
    exact Opens.mem_iSup.mpr ⟨⟨W, hW, hWU⟩, hxW⟩

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Hom mk Γ mk.injEq Hom.preimage_iSup Opens Hom.comp_preimage" namespace Hom p2m_export "AlgebraicGeometry.Scheme.Hom" "app mk naturality preimage_mono mk.injEq cover preimage_iSup comp_preimage comp_apply" end Scheme.Hom
p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

theorem Scheme.Hom.app_apply_map_homOfLE {X Y : Scheme.{u}} (f : Y ⟶ X) {U V : X.Opens} (e : V ≤ U)
    (s : Γ(X, U)) :
    f.app V (X.presheaf.map (homOfLE e).op s) =
      Y.presheaf.map (homOfLE (show f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U from fun _ hx => e hx)).op (f.app U s) := by
  have h := CategoryTheory.ConcreteCategory.congr_hom (f.naturality (homOfLE e).op) s
  rw [CategoryTheory.ConcreteCategory.comp_apply, CategoryTheory.ConcreteCategory.comp_apply] at h
  rw [h]
  rfl

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

theorem Scheme.Hom.app_prod_injective_of_forall_isAffineOpen {X Y₁ Y₂ : Scheme.{u}} (i₁ : Y₁ ⟶ X)
    (i₂ : Y₂ ⟶ X) (U : X.Opens)
    (h : ∀ V : X.Opens, IsAffineOpen V → V ≤ U →
      Function.Injective (fun f : Γ(X, V) => ((i₁.app V) f, (i₂.app V) f)))
    {W : X.Opens} (hW : W ≤ U) :
    Function.Injective (fun f : Γ(X, W) => ((i₁.app W) f, (i₂.app W) f)) := by
  intro f f' hff'
  simp only [Prod.mk.injEq] at hff'
  fapply X.sheaf.eq_of_locally_eq' (fun V : {V : X.Opens // IsAffineOpen V ∧ V ≤ W} => (V : X.Opens)) W
    (fun V => homOfLE V.2.2) (le_of_eq (Scheme.iSup_affineOpens_le W).symm)
  intro V
  change X.presheaf.map (homOfLE V.2.2).op f = X.presheaf.map (homOfLE V.2.2).op f'
  apply h V.1 V.2.1 (V.2.2.trans hW)
  simp only [Prod.mk.injEq]
  constructor
  · rw [Scheme.Hom.app_apply_map_homOfLE, Scheme.Hom.app_apply_map_homOfLE, hff'.1]
  · rw [Scheme.Hom.app_apply_map_homOfLE, Scheme.Hom.app_apply_map_homOfLE, hff'.2]

p2m_open_scoped "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom" in

theorem Scheme.Hom.app_apply_map_op {X Y : Scheme.{u}} (f : Y ⟶ X) {U V : X.Opens} (ι : V ⟶ U)
    (s : Γ(X, U)) :
    f.app V (X.presheaf.map ι.op s) =
      Y.presheaf.map ((Opens.map f.base).map ι).op (f.app U s) := by
  have h := CategoryTheory.ConcreteCategory.congr_hom (f.naturality ι.op) s
  rw [CategoryTheory.ConcreteCategory.comp_apply, CategoryTheory.ConcreteCategory.comp_apply] at h
  exact h

end AlgebraicGeometry

theorem solution
    {X Y₁ Y₂ : Scheme.{u}} (i₁ : Y₁ ⟶ X) (i₂ : Y₂ ⟶ X) (U : X.Opens)
    (h : ∀ (V : X.Opens), IsAffineOpen V → V ≤ U →
      Function.Injective (fun f : Γ(X, V) => ((i₁.app V) f, (i₂.app V) f)) ∧
        ∀ (g₁ : Γ(Y₁, i₁ ⁻¹ᵁ V)) (g₂ : Γ(Y₂, i₂ ⁻¹ᵁ V)),
          (pullback i₁ i₂).presheaf.map
              (eqToHom (show (pullback.snd i₁ i₂) ⁻¹ᵁ (i₂ ⁻¹ᵁ V) = (pullback.fst i₁ i₂) ⁻¹ᵁ (i₁ ⁻¹ᵁ V) by
                rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition])).op
            ((pullback.fst i₁ i₂).app (i₁ ⁻¹ᵁ V) g₁) =
            (pullback.snd i₁ i₂).app (i₂ ⁻¹ᵁ V) g₂ →
          ∃ f : Γ(X, V), (i₁.app V) f = g₁ ∧ (i₂.app V) f = g₂) :
    Function.Injective (fun f : Γ(X, U) => ((i₁.app U) f, (i₂.app U) f)) ∧
      ∀ (g₁ : Γ(Y₁, i₁ ⁻¹ᵁ U)) (g₂ : Γ(Y₂, i₂ ⁻¹ᵁ U)),
        (pullback i₁ i₂).presheaf.map
            (eqToHom (show (pullback.snd i₁ i₂) ⁻¹ᵁ (i₂ ⁻¹ᵁ U) = (pullback.fst i₁ i₂) ⁻¹ᵁ (i₁ ⁻¹ᵁ U) by
              rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition])).op
          ((pullback.fst i₁ i₂).app (i₁ ⁻¹ᵁ U) g₁) =
          (pullback.snd i₁ i₂).app (i₂ ⁻¹ᵁ U) g₂ →
        ∃ f : Γ(X, U), (i₁.app U) f = g₁ ∧ (i₂.app U) f = g₂ := by
  classical

  have hinj : ∀ W : X.Opens, W ≤ U →
      Function.Injective (fun f : Γ(X, W) => ((i₁.app W) f, (i₂.app W) f)) :=
    fun W hW => Scheme.Hom.app_prod_injective_of_forall_isAffineOpen i₁ i₂ U
      (fun V hV hVU => (h V hV hVU).1) hW
  refine ⟨hinj U le_rfl, ?_⟩
  intro g₁ g₂ hagree

  let ι : Type u := {V : X.Opens // IsAffineOpen V ∧ V ≤ U}
  let V : ι → X.Opens := fun j => j.1

  let r₁ : ∀ j : ι, Γ(Y₁, i₁ ⁻¹ᵁ V j) := fun j =>
    Y₁.presheaf.map (homOfLE (i₁.preimage_mono j.2.2)).op g₁
  let r₂ : ∀ j : ι, Γ(Y₂, i₂ ⁻¹ᵁ V j) := fun j =>
    Y₂.presheaf.map (homOfLE (i₂.preimage_mono j.2.2)).op g₂

  have hagreeV : ∀ j : ι,
      (pullback i₁ i₂).presheaf.map
          (eqToHom (show (pullback.snd i₁ i₂) ⁻¹ᵁ (i₂ ⁻¹ᵁ V j) =
              (pullback.fst i₁ i₂) ⁻¹ᵁ (i₁ ⁻¹ᵁ V j) by
            rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
              pullback.condition])).op
        ((pullback.fst i₁ i₂).app (i₁ ⁻¹ᵁ V j) (r₁ j)) =
        (pullback.snd i₁ i₂).app (i₂ ⁻¹ᵁ V j) (r₂ j) := by
    intro j
    simp only [r₁, r₂]
    rw [Scheme.Hom.app_apply_map_op, Scheme.Hom.app_apply_map_op, ← hagree]
    generalize (pullback.fst i₁ i₂).app (i₁ ⁻¹ᵁ U) g₁ = t
    simp only [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    rfl

  choose fV hfV₁ hfV₂ using fun j : ι => (h (V j) j.2.1 j.2.2).2 (r₁ j) (r₂ j) (hagreeV j)

  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 V fV := by
    intro j j'
    apply hinj (V j ⊓ V j') (inf_le_left.trans j.2.2)
    change ((i₁.app _) (X.presheaf.map _ (fV j)), (i₂.app _) (X.presheaf.map _ (fV j))) =
      ((i₁.app _) (X.presheaf.map _ (fV j')), (i₂.app _) (X.presheaf.map _ (fV j')))
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [Scheme.Hom.app_apply_map_op, Scheme.Hom.app_apply_map_op, hfV₁, hfV₁]
      simp only [r₁, ← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      rfl
    · rw [Scheme.Hom.app_apply_map_op, Scheme.Hom.app_apply_map_op, hfV₂, hfV₂]
      simp only [r₂, ← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      rfl

  obtain ⟨f, hf, -⟩ := X.sheaf.existsUnique_gluing' V U (fun j => homOfLE j.2.2)
    (le_of_eq (Scheme.iSup_affineOpens_le U).symm) fV hcompat
  refine ⟨f, ?_, ?_⟩
  ·
    fapply Y₁.sheaf.eq_of_locally_eq' (fun j : ι => i₁ ⁻¹ᵁ V j) (i₁ ⁻¹ᵁ U)
      (fun j => homOfLE (i₁.preimage_mono j.2.2))
    · rw [← Scheme.Hom.preimage_iSup]
      exact i₁.preimage_mono (le_of_eq (Scheme.iSup_affineOpens_le U).symm)
    · intro j
      have e1 : (i₁.app (V j)) (X.presheaf.map (homOfLE j.2.2).op f) = r₁ j := by
        have := hf j
        change X.presheaf.map (homOfLE j.2.2).op f = fV j at this
        rw [this, hfV₁]
      rw [Scheme.Hom.app_apply_map_op] at e1
      exact e1
  ·
    fapply Y₂.sheaf.eq_of_locally_eq' (fun j : ι => i₂ ⁻¹ᵁ V j) (i₂ ⁻¹ᵁ U)
      (fun j => homOfLE (i₂.preimage_mono j.2.2))
    · rw [← Scheme.Hom.preimage_iSup]
      exact i₂.preimage_mono (le_of_eq (Scheme.iSup_affineOpens_le U).symm)
    · intro j
      have e2 : (i₂.app (V j)) (X.presheaf.map (homOfLE j.2.2).op f) = r₂ j := by
        have := hf j
        change X.presheaf.map (homOfLE j.2.2).op f = fV j at this
        rw [this, hfV₂]
      rw [Scheme.Hom.app_apply_map_op] at e2
      exact e2

end S_AlgebraicGeometry_Scheme_Hom_app_injective_and_exists_of_forall_isAffineOpen
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Hom_app_injective_and_exists_of_forall_isAffineOpen (solution)
