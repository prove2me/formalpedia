-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.Leray.exists_levelwise_equiv_transpose_id
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/37f0b5c3-27e9-5179-b368-75a868f1835f

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_levelwise_equiv_transpose_id

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

open AlgebraicGeometry.OModulePresheaf AlgebraicGeometry.OModulePresheaf.Leray

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R))
    (𝔓 𝒲 : X.OrderedAffineCover) :
    ∃ e : ∀ p q : ℕ, (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).C p q ≃ₗ[R]
        (DoubleComplex.transpose (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲)).C p q,
      (∀ (p q : ℕ) (x : (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).C p q),
        e (p + 1) q ((OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).dH p q x) =
          (DoubleComplex.transpose (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲)).dH p q (e p q x)) ∧
      (∀ (p q : ℕ) (x : (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).C p q),
        e p (q + 1) ((OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).dV p q x) =
          (DoubleComplex.transpose (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝔓 𝒲)).dV p q (e p q x)) ∧
      ∀ (p q : ℕ) (x : (OModulePresheaf.Leray.LerayDblCpx (𝟙 X) π 𝒲 𝔓).C p q) (σ : 𝔓.Idx q) (τ : 𝒲.Idx p),
        (e p q x : OModulePresheaf.Leray.biC (𝟙 X) π 𝔓 𝒲 q p) (σ, τ) =
          (X.presheaf.map (homOfLE (le_inf
              (inf_le_right.trans (Scheme.Hom.id_preimage (𝔓.inter σ)).le)
              ((Scheme.Hom.id_preimage (𝒲.inter τ)).ge.trans' inf_le_left) :
            OModulePresheaf.Leray.biOpen (𝟙 X) 𝔓 𝒲 q p σ τ ≤ OModulePresheaf.Leray.biOpen (𝟙 X) 𝒲 𝔓 p q τ σ)).op).hom
            (x (τ, σ)) := by
  have h₁ : ∀ {p q : ℕ} (σ : 𝔓.Idx q) (τ : 𝒲.Idx p),
      biOpen (𝟙 X) 𝔓 𝒲 q p σ τ ≤ biOpen (𝟙 X) 𝒲 𝔓 p q τ σ := fun σ τ =>
    le_inf (inf_le_right.trans (Scheme.Hom.id_preimage _).le) (inf_le_left.trans (Scheme.Hom.id_preimage _).ge)
  have h₂ : ∀ {p q : ℕ} (τ : 𝒲.Idx p) (σ : 𝔓.Idx q),
      biOpen (𝟙 X) 𝒲 𝔓 p q τ σ ≤ biOpen (𝟙 X) 𝔓 𝒲 q p σ τ := fun τ σ =>
    le_inf (inf_le_right.trans (Scheme.Hom.id_preimage _).le) (inf_le_left.trans (Scheme.Hom.id_preimage _).ge)
  refine ⟨fun p q =>
    { toFun := fun x στ => (OModulePresheaf.unit (𝟙 X ≫ π)).res (h₁ στ.1 στ.2) (x (στ.2, στ.1))
      map_add' := fun x y => funext fun στ => map_add _ _ _
      map_smul' := fun r x => funext fun στ => by
        show (OModulePresheaf.unit (𝟙 X ≫ π)).res (h₁ στ.1 στ.2) (r • x (στ.2, στ.1)) = r • (OModulePresheaf.unit (𝟙 X ≫ π)).res (h₁ στ.1 στ.2) (x (στ.2, στ.1))
        exact map_smul _ _ _
      invFun := fun y τσ => (OModulePresheaf.unit (𝟙 X ≫ π)).res (h₂ τσ.1 τσ.2) (y (τσ.2, τσ.1))
      left_inv := fun x => funext fun τσ => by
        show (OModulePresheaf.unit (𝟙 X ≫ π)).res _ ((OModulePresheaf.unit (𝟙 X ≫ π)).res _ (x (τσ.1, τσ.2))) = x τσ
        rw [OModulePresheaf.res_res]
        exact (OModulePresheaf.unit (𝟙 X ≫ π)).res_refl_apply _ _
      right_inv := fun y => funext fun στ => by
        show (OModulePresheaf.unit (𝟙 X ≫ π)).res _ ((OModulePresheaf.unit (𝟙 X ≫ π)).res _ (y (στ.1, στ.2))) = y στ
        rw [OModulePresheaf.res_res]
        exact (OModulePresheaf.unit (𝟙 X ≫ π)).res_refl_apply _ _ }, ?_, ?_, ?_⟩
  · intro p q x
    funext στ
    obtain ⟨σ, τ'⟩ := στ
    show (X.presheaf.map (homOfLE (h₁ σ τ')).op).hom (dH (𝟙 X) π 𝒲 𝔓 p q x (τ', σ)) =
      dV (𝟙 X) π 𝔓 𝒲 q p
        (fun στ : BiIdx 𝔓 𝒲 q p => (X.presheaf.map (homOfLE (h₁ στ.1 στ.2)).op).hom (x (στ.2, στ.1))) (σ, τ')
    rw [dH_apply', dV_apply', map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul]
    congr 1
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
    rfl
  · intro p q x
    funext στ
    obtain ⟨σ', τ⟩ := στ
    show (X.presheaf.map (homOfLE (h₁ σ' τ)).op).hom (dV (𝟙 X) π 𝒲 𝔓 p q x (τ, σ')) =
      dH (𝟙 X) π 𝔓 𝒲 q p
        (fun στ : BiIdx 𝔓 𝒲 q p => (X.presheaf.map (homOfLE (h₁ στ.1 στ.2)).op).hom (x (στ.2, στ.1))) (σ', τ)
    rw [dH_apply', dV_apply', map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul]
    congr 1
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
    rfl
  · intro p q x σ τ
    rfl

end S_AlgebraicGeometry_OModulePresheaf_Leray_exists_levelwise_equiv_transpose_id
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_levelwise_equiv_transpose_id (solution)
