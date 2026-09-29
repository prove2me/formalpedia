-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.ores_ounitPullback_oext
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/38e6f1b3-573a-5791-8984-884e23126c1b

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_ores_ounitPullback_oext

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace DORDProofs
open AlgebraicGeometry.OModulePresheaf AlgebraicGeometry.Scheme.OrderedAffineCover

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)}

theorem ores_od (F : OModulePresheaf π) (K : V.OrderedAffineCover) (n : ℕ) (c : F.ocochain K n) :
    F.ores K (n + 1) (F.od K n c) = F.d K n (F.ores K n c) := by
  funext s
  rw [ores_apply, od_apply, d_apply]
  rfl

theorem ores_oext (F : OModulePresheaf π) (K : V.OrderedAffineCover) (n : ℕ) (z : F.cochain K n) :
    F.ores K n (F.oext K n z) = z := by
  funext s
  have hinj : Function.Injective s.1 := s.2.injective
  have hsort : Tuple.sort s.1 = Equiv.refl _ := (Tuple.sort_eq_refl_iff_monotone).2 s.2.monotone
  have hs : K.osort s.1 hinj = s := Subtype.ext (by rw [osort_val, hsort]; rfl)
  have key : ∀ (s' : K.Idx n) (e : s' = s) (h₁ : K.ointer s.1 ≤ K.inter s'),
      F.res h₁ (z s') = (show F.obj (K.ointer s.1) from z s) := by
    intro s' e h₁; subst e; exact F.res_refl_apply _ _
  rw [ores_apply, oext_apply_of_injective _ _ _ _ _ hinj, key _ hs, hsort, Equiv.Perm.sign_refl, Units.val_one,
    one_smul]

theorem ores_ocup (F : OModulePresheaf π) (K : V.OrderedAffineCover) (a b n : ℕ) (hn : a + b = n)
    (α : (OModulePresheaf.unit π).ocochain K a) (β : F.ocochain K b) :
    F.ores K n (F.ocup K a b n hn α β) = F.cup K a b n hn ((OModulePresheaf.unit π).ores K a α) (F.ores K b β) := by
  funext s
  rfl

variable {R' : Type u} [CommRing R'] {X Y : Scheme.{u}}

theorem ores_ounitPullback_oext
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) (z : (OModulePresheaf.unit πY).cochain 𝒦 n) :
    (OModulePresheaf.unit πX).ores 𝒲 n
        (OModulePresheaf.ounitPullback (πX := πX) h 𝒲 𝒦 lam hlam n ((OModulePresheaf.unit πY).oext 𝒦 n z)) =
      OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z := by
  classical
  funext s
  rw [ores_apply, ounitPullback_apply]
  by_cases hinj : Function.Injective (lam ∘ s.1)
  · rw [oext_apply_of_injective _ _ _ _ _ hinj, unitPullback_apply_of_injective _ _ _ _ _ _ _ _ hinj]
    change (X.presheaf.map (homOfLE (𝒲.ointer_le_preimage_ointer_comp h 𝒦 lam hlam s.1)).op).hom
        ((h.app (𝒦.ointer (lam ∘ s.1))).hom
          (((Equiv.Perm.sign (Tuple.sort (lam ∘ s.1)) : ℤˣ) : ℤ) •
            (show Γ(Y, 𝒦.ointer (lam ∘ s.1)) from
              (Y.presheaf.map (homOfLE (𝒦.ointer_le_inter_osort (lam ∘ s.1) hinj)).op).hom (z (𝒦.osort (lam ∘ s.1) hinj))))) = _
    rw [map_zsmul, map_zsmul]
    congr 1
    change ((Y.presheaf.map (homOfLE (𝒦.ointer_le_inter_osort (lam ∘ s.1) hinj)).op ≫
        h.appLE (𝒦.ointer (lam ∘ s.1)) (𝒲.ointer s.1) (𝒲.ointer_le_preimage_ointer_comp h 𝒦 lam hlam s.1))).hom
        (z (𝒦.osort (lam ∘ s.1) hinj)) =
      (h.appLE (𝒦.inter (𝒲.sortIdx 𝒦 lam s hinj)) (𝒲.inter s) (𝒲.inter_le_preimage_inter_sortIdx h 𝒦 lam hlam s hinj)).hom
        (z (𝒲.sortIdx 𝒦 lam s hinj))
    rw [Scheme.Hom.map_appLE]
    rfl
  · rw [oext_apply_of_not_injective _ _ _ _ _ hinj, unitPullback_apply_of_not_injective _ _ _ _ _ _ _ _ hinj]
    change (X.presheaf.map _).hom ((h.app _).hom (0 : Γ(Y, 𝒦.ointer (lam ∘ s.1)))) = (0 : Γ(X, 𝒲.inter s))
    rw [map_zero, map_zero]

theorem od_ounitPullback
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) (c : (OModulePresheaf.unit πY).ocochain 𝒦 n) :
    (OModulePresheaf.unit πX).od 𝒲 n (OModulePresheaf.ounitPullback (πX := πX) h 𝒲 𝒦 lam hlam n c) =
      OModulePresheaf.ounitPullback (πX := πX) h 𝒲 𝒦 lam hlam (n + 1) ((OModulePresheaf.unit πY).od 𝒦 n c) := by
  funext t
  rw [od_apply, ounitPullback_apply, od_apply]
  change _ = (X.presheaf.map _).hom ((h.app _).hom (∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      (show Γ(Y, 𝒦.ointer (lam ∘ t)) from (OModulePresheaf.unit πY).res (𝒦.ointer_le_ointer_oface (lam ∘ t) j) (c (𝒦.oface (lam ∘ t) j)))))
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, map_zsmul, ounitPullback_apply]
  change ((-1 : ℤ) ^ (j : ℕ)) • ((h.appLE _ _ (𝒲.ointer_le_preimage_ointer_comp h 𝒦 lam hlam (𝒲.oface t j)) ≫
      X.presheaf.map (homOfLE (𝒲.ointer_le_ointer_oface t j)).op).hom (c (lam ∘ 𝒲.oface t j))) =
    ((-1 : ℤ) ^ (j : ℕ)) • ((Y.presheaf.map (homOfLE (𝒦.ointer_le_ointer_oface (lam ∘ t) j)).op ≫
      h.appLE _ _ (𝒲.ointer_le_preimage_ointer_comp h 𝒦 lam hlam t))).hom (c (𝒦.oface (lam ∘ t) j))
  rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  rfl

theorem ounitPullback_ocup
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (a b n : ℕ) (hn : a + b = n)
    (α : (OModulePresheaf.unit πY).ocochain 𝒦 a) (β : (OModulePresheaf.unit πY).ocochain 𝒦 b) :
    OModulePresheaf.ounitPullback (πX := πX) h 𝒲 𝒦 lam hlam n ((OModulePresheaf.unit πY).ocup 𝒦 a b n hn α β) =
      (OModulePresheaf.unit πX).ocup 𝒲 a b n hn
        (OModulePresheaf.ounitPullback (πX := πX) h 𝒲 𝒦 lam hlam a α)
        (OModulePresheaf.ounitPullback (πX := πX) h 𝒲 𝒦 lam hlam b β) := by
  funext t
  rw [ounitPullback_apply, ocup_apply, ocup_apply, ounitPullback_apply, ounitPullback_apply]
  change (h.appLE _ _ (𝒲.ointer_le_preimage_ointer_comp h 𝒦 lam hlam t)).hom
      ((Y.presheaf.map (homOfLE (𝒦.ointer_le_ointer_ofrontFace a b n hn (lam ∘ t))).op).hom (α (𝒦.ofrontFace a b n hn (lam ∘ t))) *
        (Y.presheaf.map (homOfLE (𝒦.ointer_le_ointer_obackFace a b n hn (lam ∘ t))).op).hom (β (𝒦.obackFace a b n hn (lam ∘ t)))) =
    (X.presheaf.map (homOfLE (𝒲.ointer_le_ointer_ofrontFace a b n hn t)).op).hom
        ((h.appLE _ _ (𝒲.ointer_le_preimage_ointer_comp h 𝒦 lam hlam (𝒲.ofrontFace a b n hn t))).hom (α (lam ∘ 𝒲.ofrontFace a b n hn t))) *
      (X.presheaf.map (homOfLE (𝒲.ointer_le_ointer_obackFace a b n hn t)).op).hom
        ((h.appLE _ _ (𝒲.ointer_le_preimage_ointer_comp h 𝒦 lam hlam (𝒲.obackFace a b n hn t))).hom (β (lam ∘ 𝒲.obackFace a b n hn t)))
  rw [map_mul, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.map_appLE, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map, Scheme.Hom.appLE_map]
  rfl

end DORDProofs

theorem solution
    {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) (z : (OModulePresheaf.unit πY).cochain 𝒦 n) :
    (OModulePresheaf.unit πX).ores 𝒲 n
        (OModulePresheaf.ounitPullback (πX := πX) h 𝒲 𝒦 lam hlam n ((OModulePresheaf.unit πY).oext 𝒦 n z)) =
      OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z :=
  DORDProofs.ores_ounitPullback_oext πX πY h 𝒲 𝒦 lam hlam n z

end S_AlgebraicGeometry_OModulePresheaf_ores_ounitPullback_oext
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_ores_ounitPullback_oext (solution)
