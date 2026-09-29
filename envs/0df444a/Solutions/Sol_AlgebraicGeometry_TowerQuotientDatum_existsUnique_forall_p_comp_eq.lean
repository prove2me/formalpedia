-- Prove2me | solution 1 for AlgebraicGeometry.TowerQuotientDatum.existsUnique_forall_p_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/271ae969-f06d-5298-bdef-84f8762baa4f

import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_TowerQuotientDatum_existsUnique_forall_p_comp_eq

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem solution
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪)
    (X : ℕ → Scheme.{0}) (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
    (G : Type) [Group G] (a : ∀ n : ℕ, G →* Aut (X n))
    (D : TowerQuotientDatum 𝒪 π X xb xt G a)
    (T : Scheme.{0}) (w : ∀ n : ℕ, X n ⟶ T)
    (hinv : ∀ (n : ℕ) (g : G), (a n g).hom ≫ w n = w n)
    (hxt : ∀ n : ℕ, xt n ≫ w (n + 1) = w n) :
    ∃! u : ∀ n : ℕ, D.Y n ⟶ T, ∀ n : ℕ, D.p n ≫ u n = w n := by
  have hepi : ∀ n : ℕ, Epi (D.p n) := by
    intro n
    haveI : Epi ((D.p n) ∣_ (⊤ : (D.Y n).Opens)) := D.p_epi_loc n ⊤
    haveI : IsIso (⊤ : (D.Y n).Opens).ι := by rw [← Scheme.topIso_hom]; infer_instance
    have h : Epi (((D.p n) ∣_ (⊤ : (D.Y n).Opens)) ≫ (⊤ : (D.Y n).Opens).ι) := epi_comp _ _
    rw [morphismRestrict_ι] at h
    exact epi_of_epi ((D.p n) ⁻¹ᵁ (⊤ : (D.Y n).Opens)).ι (D.p n)
  obtain ⟨v, hv⟩ := D.univ_loc T (fun n => ⊤) (fun n => Scheme.Hom.preimage_top _)
    (fun n => ((D.p n) ⁻¹ᵁ (⊤ : (D.Y n).Opens)).ι ≫ w n)
    (fun n g => by rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hinv])
    (fun n => by rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hxt])
  have hex : ∀ n : ℕ, D.p n ≫ ((D.Y n).topIso.inv ≫ v n) = w n := by
    intro n
    haveI : IsIso ((D.p n) ⁻¹ᵁ (⊤ : (D.Y n).Opens)).ι := by
      rw [Scheme.Hom.preimage_top, ← Scheme.topIso_hom]; infer_instance
    rw [← cancel_epi ((D.p n) ⁻¹ᵁ (⊤ : (D.Y n).Opens)).ι, ← hv n, ← Category.assoc, ← morphismRestrict_ι,
      Category.assoc, ← Category.assoc (⊤ : (D.Y n).Opens).ι, Scheme.ι_toIso_inv, Category.id_comp]
  refine ⟨fun n => (D.Y n).topIso.inv ≫ v n, hex, fun u' hu' => funext fun n => ?_⟩
  exact (cancel_epi (D.p n)).mp ((hu' n).trans (hex n).symm)

end S_AlgebraicGeometry_TowerQuotientDatum_existsUnique_forall_p_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_TowerQuotientDatum_existsUnique_forall_p_comp_eq (solution)
