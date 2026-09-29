-- Prove2me | solution 1 for AlgebraicGeometry.exists_fg_subalgebra_comp_eq_pullback_fst_comp_of_comp_eq_of_locallyOfFinitePresentation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/fb5953f7-0810-52f3-8f4c-5d190e2ef2d5

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Theorems.Thm_AlgebraicGeometry_exists_eq_comp_hom_pullback_specMap_of_isDirectLimit_of_locallyOfFinitePresentation
import Theorems.Thm_AlgebraicGeometry_exists_pullback_fst_comp_eq_of_isDirectLimit_of_locallyOfFiniteType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_comp_eq_pullback_fst_comp_of_comp_eq_of_locallyOfFinitePresentation

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FGStagesP1

variable {A₀ : Type} [CommRing A₀] {A : Type} [CommRing A] [Algebra A₀ A] (B : Subalgebra A₀ A)

abbrev Idx : Type := {T : Subalgebra A₀ A // T.FG ∧ B ≤ T}

abbrev G (i : Idx B) : Type := ↥i.1

abbrev φ (i j : Idx B) (h : i ≤ j) : G B i →+* G B j := (Subalgebra.inclusion (show i.1 ≤ j.1 from h)).toRingHom

abbrev g (i : Idx B) : G B i →+* A := (i.1).val.toRingHom

@[scoped simp] theorem φ_apply (i j : Idx B) (h : i ≤ j) (x : G B i) : (φ B i j h x : A) = (x : A) := rfl
@[scoped simp] theorem g_apply (i : Idx B) (x : G B i) : g B i x = (x : A) := rfl

scoped instance : DirectedSystem (G B) (fun i j h => ⇑(φ B i j h)) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

private def _root_.FGStagesP1.sup (i j : Idx B) : Idx B := ⟨i.1 ⊔ j.1, i.2.1.sup j.2.1, le_sup_of_le_left i.2.2⟩

p2m_export "FGStagesP1" "sup"
scoped instance : IsDirected (Idx B) (· ≤ ·) :=
  ⟨fun i j => ⟨sup B i j, (le_sup_left : i.1 ≤ i.1 ⊔ j.1), (le_sup_right : j.1 ≤ i.1 ⊔ j.1)⟩⟩

theorem nonempty (hB : B.FG) : Nonempty (Idx B) := ⟨⟨B, hB, le_rfl⟩⟩

theorem isDirectLimit (hB : B.FG) : IsDirectLimit (fun i j h => ⇑(φ B i j h)) (fun i => ⇑(g B i)) where
  surj m := by
    refine ⟨⟨B ⊔ Algebra.adjoin A₀ {m}, hB.sup ⟨{m}, by rw [Finset.coe_singleton]⟩, le_sup_left⟩, ⟨m, ?_⟩, rfl⟩
    exact Algebra.mem_sup_right (Algebra.self_mem_adjoin_singleton A₀ m)
  inj i j mi mj h := ⟨sup B i j, (le_sup_left : i.1 ≤ i.1 ⊔ j.1), (le_sup_right : j.1 ≤ i.1 ⊔ j.1), Subtype.ext h⟩
  compatibility _ _ _ _ := rfl

theorem specMap_g_comp_specMap_φ (i j : Idx B) (h : i ≤ j) :
    Spec.map (CommRingCat.ofHom (g B j)) ≫ Spec.map (CommRingCat.ofHom (φ B i j h)) =
      Spec.map (CommRingCat.ofHom (g B i)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl

theorem specMap_φ_comp_specMap_φ (i j k : Idx B) (hij : i ≤ j) (hjk : j ≤ k) :
    Spec.map (CommRingCat.ofHom (φ B j k hjk)) ≫ Spec.map (CommRingCat.ofHom (φ B i j hij)) =
      Spec.map (CommRingCat.ofHom (φ B i k (le_trans hij hjk))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl

end FGStagesP1
p2m_reactivate "P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_comp_eq_pullback_fst_comp_of_comp_eq_of_locallyOfFinitePresentation.FGStagesP1"

open FGStagesP1 in

theorem solution
    {A₀ : Type} [CommRing A₀] {A : Type} [CommRing A] [Algebra A₀ A] (B : Subalgebra A₀ A) (hB : B.FG)
    {X W V : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of ↥B)) [LocallyOfFiniteType f]
    (w : W ⟶ X) [QuasiCompact (w ≫ f)] [QuasiSeparated (w ≫ f)]
    (v : V ⟶ X) [LocallyOfFinitePresentation (v ≫ f)]
    (a : pullback (w ≫ f) (Spec.map (CommRingCat.ofHom B.val.toRingHom)) ⟶ V)
    (ha : a ≫ v = pullback.fst (w ≫ f) (Spec.map (CommRingCat.ofHom B.val.toRingHom)) ≫ w) :
    ∃ (T : Subalgebra A₀ A) (_ : T.FG) (hle : B ≤ T)
      (aT : pullback (w ≫ f) (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom)) ⟶ V),
      aT ≫ v = pullback.fst (w ≫ f) (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom)) ≫ w := by
  haveI : Nonempty (Idx B) := FGStagesP1.nonempty B hB
  have ha' : a ≫ (v ≫ f) =
      pullback.fst (w ≫ f) (Spec.map (CommRingCat.ofHom (g B (⟨B, hB, le_rfl⟩ : Idx B)))) ≫ (w ≫ f) := by
    simpa only [Category.assoc] using congrArg (· ≫ f) ha

  obtain ⟨j, hij, aj, haj, huniq⟩ :=
    AlgebraicGeometry.exists_eq_comp_hom_pullback_specMap_of_isDirectLimit_of_locallyOfFinitePresentation
      (φ B) (g B) (isDirectLimit B hB) (⟨B, hB, le_rfl⟩ : Idx B) (w ≫ f) (v ≫ f) a ha'

  obtain ⟨κ₀, hκ₁, hκ₂⟩ : ∃ κ₀ : pullback (w ≫ f) (Spec.map (CommRingCat.ofHom (g B (⟨B, hB, le_rfl⟩ : Idx B)))) ⟶
      pullback (w ≫ f) (Spec.map (CommRingCat.ofHom (φ B (⟨B, hB, le_rfl⟩ : Idx B) j hij))),
      κ₀ ≫ pullback.fst _ _ = pullback.fst _ _ ∧
        κ₀ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (g B j)) :=
    ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (g B j)))
      (by rw [Category.assoc, specMap_g_comp_specMap_φ]; exact pullback.condition),
     pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have haκ : a = κ₀ ≫ aj := huniq κ₀ hκ₁ hκ₂

  obtain ⟨a', ha'₁, ha'₂⟩ : ∃ a' : pullback (w ≫ f) (Spec.map (CommRingCat.ofHom (φ B (⟨B, hB, le_rfl⟩ : Idx B) j hij))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (φ B (⟨B, hB, le_rfl⟩ : Idx B) j hij))),
      a' ≫ pullback.fst _ _ = aj ≫ v ∧ a' ≫ pullback.snd _ _ = pullback.snd _ _ :=
    ⟨pullback.lift (aj ≫ v) (pullback.snd _ _) (by rw [Category.assoc, haj]; exact pullback.condition),
     pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨b', hb'₁, hb'₂⟩ : ∃ b' : pullback (w ≫ f) (Spec.map (CommRingCat.ofHom (φ B (⟨B, hB, le_rfl⟩ : Idx B) j hij))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (φ B (⟨B, hB, le_rfl⟩ : Idx B) j hij))),
      b' ≫ pullback.fst _ _ = pullback.fst _ _ ≫ w ∧ b' ≫ pullback.snd _ _ = pullback.snd _ _ :=
    ⟨pullback.lift (pullback.fst _ _ ≫ w) (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition),
     pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

  obtain ⟨θ, hθ₁, hθ₂⟩ : ∃ θ : pullback (pullback.snd (w ≫ f) (Spec.map (CommRingCat.ofHom (φ B (⟨B, hB, le_rfl⟩ : Idx B) j hij))))
        (Spec.map (CommRingCat.ofHom (g B j))) ⟶ pullback (w ≫ f) (Spec.map (CommRingCat.ofHom (g B (⟨B, hB, le_rfl⟩ : Idx B)))),
      θ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ ∧ θ ≫ pullback.snd _ _ = pullback.snd _ _ :=
    ⟨pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _)
      (by
        have h1 := pullback.condition (f := w ≫ f) (g := Spec.map (CommRingCat.ofHom (φ B (⟨B, hB, le_rfl⟩ : Idx B) j hij)))
        have h2 := pullback.condition (f := pullback.snd (w ≫ f) (Spec.map (CommRingCat.ofHom (φ B (⟨B, hB, le_rfl⟩ : Idx B) j hij))))
          (g := Spec.map (CommRingCat.ofHom (g B j)))
        rw [Category.assoc, h1, ← Category.assoc, h2, Category.assoc, specMap_g_comp_specMap_φ]),
     pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hθκ : pullback.fst (pullback.snd (w ≫ f) (Spec.map (CommRingCat.ofHom (φ B (⟨B, hB, le_rfl⟩ : Idx B) j hij))))
      (Spec.map (CommRingCat.ofHom (g B j))) = θ ≫ κ₀ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hκ₁, hθ₁]
    · rw [Category.assoc, hκ₂, ← Category.assoc, hθ₂]
      exact pullback.condition
  have haκv : κ₀ ≫ aj ≫ v = pullback.fst _ _ ≫ w := by rw [← Category.assoc, ← haκ, ha]
  have hκw : κ₀ ≫ pullback.fst _ _ ≫ w =
      pullback.fst (w ≫ f) (Spec.map (CommRingCat.ofHom (g B (⟨B, hB, le_rfl⟩ : Idx B)))) ≫ w := by rw [← Category.assoc, hκ₁]
  have hab : pullback.fst (pullback.snd (w ≫ f) (Spec.map (CommRingCat.ofHom (φ B (⟨B, hB, le_rfl⟩ : Idx B) j hij))))
        (Spec.map (CommRingCat.ofHom (g B j))) ≫ a' =
      pullback.fst (pullback.snd (w ≫ f) (Spec.map (CommRingCat.ofHom (φ B (⟨B, hB, le_rfl⟩ : Idx B) j hij))))
        (Spec.map (CommRingCat.ofHom (g B j))) ≫ b' := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, ha'₁, hb'₁, hθκ, Category.assoc, Category.assoc, haκv, hκw]
    · rw [Category.assoc, Category.assoc, ha'₂, hb'₂]

  obtain ⟨k, hjk, hk⟩ :=
    AlgebraicGeometry.exists_pullback_fst_comp_eq_of_isDirectLimit_of_locallyOfFiniteType
      (φ B) (g B) (isDirectLimit B hB) j
      (pullback.snd (w ≫ f) (Spec.map (CommRingCat.ofHom (φ B (⟨B, hB, le_rfl⟩ : Idx B) j hij))))
      (pullback.snd f (Spec.map (CommRingCat.ofHom (φ B (⟨B, hB, le_rfl⟩ : Idx B) j hij))))
      a' b' ha'₂ hb'₂ hab

  have hik : (⟨B, hB, le_rfl⟩ : Idx B) ≤ k := le_trans hij hjk
  obtain ⟨μ, hμ₁, hμ₂⟩ : ∃ μ : pullback (w ≫ f) (Spec.map (CommRingCat.ofHom (φ B (⟨B, hB, le_rfl⟩ : Idx B) k hik))) ⟶
      pullback (w ≫ f) (Spec.map (CommRingCat.ofHom (φ B (⟨B, hB, le_rfl⟩ : Idx B) j hij))),
      μ ≫ pullback.fst _ _ = pullback.fst _ _ ∧
        μ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (φ B j k hjk)) :=
    ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (φ B j k hjk)))
      (by rw [Category.assoc, specMap_φ_comp_specMap_φ]; exact pullback.condition),
     pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨lam, hlam⟩ : ∃ lam : pullback (w ≫ f) (Spec.map (CommRingCat.ofHom (φ B (⟨B, hB, le_rfl⟩ : Idx B) k hik))) ⟶
      pullback (pullback.snd (w ≫ f) (Spec.map (CommRingCat.ofHom (φ B (⟨B, hB, le_rfl⟩ : Idx B) j hij))))
        (Spec.map (CommRingCat.ofHom (φ B j k hjk))),
      lam ≫ pullback.fst _ _ = μ :=
    ⟨pullback.lift μ (pullback.snd _ _) hμ₂, pullback.lift_fst _ _ _⟩
  have e3 : μ ≫ a' = μ ≫ b' := by
    rw [← hlam, Category.assoc, Category.assoc, hk]
  refine ⟨k.1, k.2.1, hik, μ ≫ aj, ?_⟩
  calc (μ ≫ aj) ≫ v = μ ≫ (aj ≫ v) := Category.assoc _ _ _
    _ = μ ≫ (a' ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (φ B (⟨B, hB, le_rfl⟩ : Idx B) j hij)))) := by rw [ha'₁]
    _ = (μ ≫ a') ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (φ B (⟨B, hB, le_rfl⟩ : Idx B) j hij))) := (Category.assoc _ _ _).symm
    _ = (μ ≫ b') ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (φ B (⟨B, hB, le_rfl⟩ : Idx B) j hij))) := by rw [e3]
    _ = μ ≫ (pullback.fst (w ≫ f) (Spec.map (CommRingCat.ofHom (φ B (⟨B, hB, le_rfl⟩ : Idx B) j hij))) ≫ w) := by
        rw [Category.assoc, hb'₁]
    _ = pullback.fst (w ≫ f) (Spec.map (CommRingCat.ofHom (φ B (⟨B, hB, le_rfl⟩ : Idx B) k hik))) ≫ w := by
        rw [← Category.assoc, hμ₁]

end S_AlgebraicGeometry_exists_fg_subalgebra_comp_eq_pullback_fst_comp_of_comp_eq_of_locallyOfFinitePresentation
end P2MW
export P2MW.S_AlgebraicGeometry_exists_fg_subalgebra_comp_eq_pullback_fst_comp_of_comp_eq_of_locallyOfFinitePresentation (solution)
