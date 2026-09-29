-- Prove2me | solution 1 for AlgebraicGeometry.prodKerGraph_comap_fst_eq_prodKerGraph_comap_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/69ca7b38-ecff-5351-aebb-8bc9cc836205

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Theorems.Thm_AlgebraicGeometry_prodKerGraph_comap_mapOnProdOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_prodKerGraph_comap_fst_eq_prodKerGraph_comap_of_isPullback

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace PKCAux

p2m_open "AlgebraicGeometry.Scheme.IdealSheafData"

variable {X Y : Scheme.{u}}

theorem comap_eq_map_inv (I : Y.IdealSheafData) (ε : X ⟶ Y) [IsIso ε] :
    I.comap ε = I.map (inv ε) := by
  apply le_antisymm
  · rw [Scheme.IdealSheafData.le_map_iff_comap_le, ← Scheme.IdealSheafData.comap_comp, IsIso.inv_hom_id,
      Scheme.IdealSheafData.comap_id]
  · calc I.map (inv ε) ≤ ((I.comap ε).map ε).map (inv ε) :=
          Scheme.IdealSheafData.map_mono _ (Scheme.IdealSheafData.le_map_comap I ε)
      _ = I.comap ε := by rw [← Scheme.IdealSheafData.map_comp, IsIso.hom_inv_id, Scheme.IdealSheafData.map_id]

theorem ker_comap_of_comp_eq {T : Scheme.{u}} (γ' : T ⟶ X) (γ : T ⟶ Y) (ε : X ⟶ Y) [IsIso ε]
    (h : γ' ≫ ε = γ) : γ.ker.comap ε = γ'.ker := by
  rw [comap_eq_map_inv, Scheme.IdealSheafData.map_ker, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

theorem comap_mul_of_isIso (I J : Y.IdealSheafData) (ε : X ⟶ Y) [IsIso ε] :
    (I * J).comap ε = I.comap ε * J.comap ε := by
  ext U : 2
  rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
  set e := (ε.appIso U)

  have key : ∀ K : Ideal _, K.comap e.inv.hom = K.map e.hom.hom := by
    intro K
    have : (e.hom.hom : _ →+* _) = (e.commRingCatIsoToRingEquiv : _ ≃+* _) := rfl
    rw [this, Ideal.map_comap_of_equiv]
    rfl
  rw [key, key, key, Ideal.map_mul]

end PKCAux

theorem solution
    {𝒞 𝒞' S S' : Scheme.{u}} (f : 𝒞 ⟶ S) (f' : 𝒞' ⟶ S') [IsSeparated f] [IsSeparated f']
    (h : S' ⟶ S) (g' : 𝒞' ⟶ 𝒞) (H : IsPullback g' f' f h)
    {r : ℕ} (a : Fin r → (S ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = 𝟙 S)
    (b : Fin r → (S' ⟶ 𝒞')) (hb : ∀ i, b i ≫ f' = 𝟙 S')
    (hab : ∀ i, b i ≫ g' = h ≫ a i)
    (θ : pullback (pullback.snd f (𝟙 S)) h ⟶ pullback f' (𝟙 S'))
    (hθ₁ : θ ≫ pullback.fst f' (𝟙 S') ≫ g' = pullback.fst (pullback.snd f (𝟙 S)) h ≫ pullback.fst f (𝟙 S))
    (hθ₂ : θ ≫ pullback.snd f' (𝟙 S') = pullback.snd (pullback.snd f (𝟙 S)) h) :
    (prodKerGraph f a ha).comap (pullback.fst (pullback.snd f (𝟙 S)) h) =
      (prodKerGraph f' b hb).comap θ := by

  have c1 : pullback.fst f (𝟙 S) ≫ f = pullback.snd f (𝟙 S) ≫ 𝟙 S := pullback.condition
  have c2 : pullback.fst (pullback.snd f (𝟙 S)) h ≫ pullback.snd f (𝟙 S) = pullback.snd (pullback.snd f (𝟙 S)) h ≫ h :=
    pullback.condition
  let e : pullback (pullback.snd f (𝟙 S)) h ⟶ pullback f h :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst f (𝟙 S)) (pullback.snd _ _)
      (by rw [Category.assoc, c1, ← Category.assoc, c2, Category.assoc, Category.comp_id])
  have hpr : pullback.fst (pullback.snd f (𝟙 S)) h = e ≫ mapOnProdOver f h (Category.comp_id h) := by
    apply pullback.hom_ext
    · rw [Category.assoc, mapOnProdOver_fst, pullback.lift_fst]
    · rw [Category.assoc, mapOnProdOver_snd, ← Category.assoc, pullback.lift_snd, c2]
  rw [hpr, Scheme.IdealSheafData.comap_comp, AlgebraicGeometry.prodKerGraph_comap_mapOnProdOver]

  have HP : IsPullback (pullback.fst f' (𝟙 S') ≫ g') (pullback.snd f' (𝟙 S')) f h := by
    have := (IsPullback.of_hasPullback f' (𝟙 S')).paste_horiz H
    simpa using this
  have hθ : θ ≫ HP.isoPullback.hom = e := by
    apply pullback.hom_ext
    · rw [Category.assoc, IsPullback.isoPullback_hom_fst, pullback.lift_fst]
      exact hθ₁
    · rw [Category.assoc, IsPullback.isoPullback_hom_snd, pullback.lift_snd]
      exact hθ₂
  rw [← hθ, Scheme.IdealSheafData.comap_comp]
  congr 1

  have hgraph : ∀ i, graphOver f' (b i) (hb i) ≫ HP.isoPullback.hom =
      graphOver f (h ≫ a i) (by rw [Category.assoc, ha, Category.comp_id]) := by
    intro i
    apply pullback.hom_ext
    · rw [Category.assoc, IsPullback.isoPullback_hom_fst, ← Category.assoc, graphOver_fst, graphOver_fst, hab]
    · rw [Category.assoc, IsPullback.isoPullback_hom_snd, graphOver_snd, graphOver_snd]
  rw [prodKerGraph_eq_prod, prodKerGraph_eq_prod]
  let Φ : (pullback f h).IdealSheafData →* (pullback f' (𝟙 S')).IdealSheafData :=
    { toFun := fun I => I.comap HP.isoPullback.hom
      map_one' := Scheme.IdealSheafData.comap_top _
      map_mul' := fun I J => PKCAux.comap_mul_of_isIso I J _ }
  change Φ (∏ i, (graphOver f (h ≫ a i) _).ker) = _
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact PKCAux.ker_comap_of_comp_eq _ _ _ (hgraph i)

end S_AlgebraicGeometry_prodKerGraph_comap_fst_eq_prodKerGraph_comap_of_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_prodKerGraph_comap_fst_eq_prodKerGraph_comap_of_isPullback (solution)
