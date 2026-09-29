-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.unitPullback_prodCover_cup_sub_cup_unitPullback_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/64a8a3d1-487d-5f44-a06f-aea36805dc53

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_DoubleComplex
import Definitions.Def_AlgebraicGeometry_BiCech
import Definitions.Def_AlgebraicGeometry_BoundedCochainTensor
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d

import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_unitPullback_cup_sub_cup_unitPullback_mem_of_mem_ker
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_unitPullback_unitPullback_sub_mem_of_d_eq_zero
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_cup
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_unitPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_unitPullback_prodCover_cup_sub_cup_unitPullback_mem
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableOSub"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TensorProduct AlgebraicGeometry

universe u

namespace RefineCupAux

open AlgebraicGeometry.OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (CommRingCat.of R)} (K : V.OrderedAffineCover)

theorem cup_sub_left (a b n : ℕ) (h : a + b = n) (α α' : (unit π).cochain K a) (β : (unit π).cochain K b) :
    (unit π).cup K a b n h (α - α') β = (unit π).cup K a b n h α β - (unit π).cup K a b n h α' β := by
  funext s
  rw [Pi.sub_apply, cup_apply, cup_apply, cup_apply, Pi.sub_apply]
  erw [map_sub]
  rw [sub_smul]

theorem cup_sub_right (a b n : ℕ) (h : a + b = n) (α : (unit π).cochain K a) (β β' : (unit π).cochain K b) :
    (unit π).cup K a b n h α (β - β') = (unit π).cup K a b n h α β - (unit π).cup K a b n h α β' := by
  funext s
  rw [Pi.sub_apply, cup_apply, cup_apply, cup_apply, Pi.sub_apply, map_sub, smul_sub]

theorem cup_zero_left (a b n : ℕ) (h : a + b = n) (β : (unit π).cochain K b) :
    (unit π).cup K a b n h 0 β = 0 := by
  have := cup_sub_left K a b n h 0 0 β
  rwa [sub_self, sub_self] at this

theorem cup_zero_right (a b n : ℕ) (h : a + b = n) (α : (unit π).cochain K a) :
    (unit π).cup K a b n h α 0 = 0 := by
  have := cup_sub_right K a b n h α 0 0
  rwa [sub_self, sub_self] at this

theorem cup_d_left (a' b m : ℕ) (h : a' + b = m) (h' : a' + 1 + b = m + 1)
    (u : (unit π).cochain K a') (y : (unit π).cochain K b) (hy : (unit π).d K b y = 0) :
    (unit π).cup K (a' + 1) b (m + 1) h' ((unit π).d K a' u) y = (unit π).d K m ((unit π).cup K a' b m h u y) := by
  rw [d_cup, hy, cup_zero_right, smul_zero, add_zero]

theorem cup_d_right (a b' m : ℕ) (h : a + b' = m) (h' : a + (b' + 1) = m + 1)
    (x : (unit π).cochain K a) (hx : (unit π).d K a x = 0) (v : (unit π).cochain K b') :
    (unit π).cup K a (b' + 1) (m + 1) h' x ((unit π).d K b' v) = (unit π).d K m (((-1 : ℤ) ^ a) • (unit π).cup K a b' m h x v) := by
  rw [map_zsmul, d_cup, hx, cup_zero_left, zero_add, smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]

theorem unitPullback_zero {R' : Type u} [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w)) (n : ℕ) :
    OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n (0 : (OModulePresheaf.unit πY).cochain 𝒦 n) = 0 := by
  classical
  funext s
  rw [Pi.zero_apply]
  by_cases hinj : Function.Injective (lam ∘ s.1)
  · rw [OModulePresheaf.unitPullback_apply_of_injective (πX := πX) h 𝒲 𝒦 lam hlam n 0 s hinj]
    change _ • (X.presheaf.map _).hom ((h.app _).hom (0 : Γ(Y, _))) = (0 : Γ(X, _))
    rw [map_zero, map_zero, smul_zero]
  · exact OModulePresheaf.unitPullback_apply_of_not_injective (πX := πX) h 𝒲 𝒦 lam hlam n 0 s hinj

end RefineCupAux

open RefineCupAux

theorem solution
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of k)) (πY : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated πX] [IsSeparated πY]
    (𝔘 : X.OrderedAffineCover) (𝔙 : Y.OrderedAffineCover)
    (haff : ∀ i j, IsAffineOpen ((𝔘.preimageFamily (pullback.fst πX πY)).U i ⊓ (𝔙.preimageFamily (pullback.snd πX πY)).U j))
    (hcov : ⨆ ij : 𝔘.ι × 𝔙.ι,
      (𝔘.preimageFamily (pullback.fst πX πY)).U ij.1 ⊓ (𝔙.preimageFamily (pullback.snd πX πY)).U ij.2 = ⊤)

    (𝒲 : (pullback πX πY).OrderedAffineCover) (lam₁ : 𝒲.ι → 𝔘.ι) (lam₂ : 𝒲.ι → 𝔙.ι)
    (h₁ : ∀ w, 𝒲.U w ≤ pullback.fst πX πY ⁻¹ᵁ 𝔘.U (lam₁ w))
    (h₂ : ∀ w, 𝒲.U w ≤ pullback.snd πX πY ⁻¹ᵁ 𝔙.U (lam₂ w))
    (hμ : ∀ w, 𝒲.U w ≤ (𝟙 (pullback πX πY)) ⁻¹ᵁ
      ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov).U
        (toLex (lam₁ w, lam₂ w)))
    (p q n : ℕ) (hn : p + q = n)
    (α : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝔘 p))) (β : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝔙 q))) :
    (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (𝟙 (pullback πX πY)) 𝒲
        ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov)
        (fun w => toLex (lam₁ w, lam₂ w)) hμ n
        ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).cup
          ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) p q n hn
          (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.fst πX πY)
            ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) 𝔘
            (fun ij => (ofLex ij).1) (fun ij => inf_le_left) p α.1)
          (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.snd πX πY)
            ((𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov) 𝔙
            (fun ij => (ofLex ij).2) (fun ij => inf_le_right) q β.1)) -
      (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).cup 𝒲 p q n hn
        (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.fst πX πY) 𝒲 𝔘 lam₁ h₁ p α.1)
        (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.snd πX πY) 𝒲 𝔙 lam₂ h₂ q β.1))
      ∈ (show Submodule k ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).cochain 𝒲 n) from
          match n with
          | 0 => ⊥
          | m + 1 => LinearMap.range ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).d 𝒲 m)) := by
  classical

  set 𝔓 := (𝔘.preimageFamily (pullback.fst πX πY)).prodCover (𝔙.preimageFamily (pullback.snd πX πY)) haff hcov with h𝔓
  set μ : 𝒲.ι → 𝔓.ι := fun w => toLex (lam₁ w, lam₂ w) with hμdef
  set A := OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.fst πX πY) 𝔓 𝔘
    (fun ij => (ofLex ij).1) (fun ij => inf_le_left) p α.1 with hA
  set B := OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.snd πX πY) 𝔓 𝔙
    (fun ij => (ofLex ij).2) (fun ij => inf_le_right) q β.1 with hB

  have hAz : (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).d 𝔓 p A = 0 := by
    rw [hA, OModulePresheaf.d_unitPullback, show (OModulePresheaf.unit πX).d 𝔘 p α.1 = 0 from α.2, unitPullback_zero]
  have hBz : (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).d 𝔓 q B = 0 := by
    rw [hB, OModulePresheaf.d_unitPullback, show (OModulePresheaf.unit πY).d 𝔙 q β.1 = 0 from β.2, unitPullback_zero]

  have hU2 := AlgebraicGeometry.OModulePresheaf.unitPullback_cup_sub_cup_unitPullback_mem_of_mem_ker
    (pullback.fst πX πY ≫ πX) (pullback.fst πX πY ≫ πX) (𝟙 (pullback πX πY)) 𝒲 𝔓 μ hμ p q n hn ⟨A, hAz⟩ ⟨B, hBz⟩

  have hFA := AlgebraicGeometry.OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero
    (pullback.fst πX πY ≫ πX) (pullback.fst πX πY ≫ πX) πX (𝟙 (pullback πX πY)) (pullback.fst πX πY) (pullback.fst πX πY)
    (by rw [Category.id_comp]) 𝒲 𝔓 𝔘 μ (fun ij => (ofLex ij).1) lam₁ (funext fun w => rfl) hμ (fun ij => inf_le_left) h₁ p α.1 α.2
  have hFB := AlgebraicGeometry.OModulePresheaf.unitPullback_unitPullback_sub_mem_of_d_eq_zero
    (pullback.fst πX πY ≫ πX) (pullback.fst πX πY ≫ πX) πY (𝟙 (pullback πX πY)) (pullback.snd πX πY) (pullback.snd πX πY)
    (by rw [Category.id_comp]) 𝒲 𝔓 𝔙 μ (fun ij => (ofLex ij).2) lam₂ (funext fun w => rfl) hμ (fun ij => inf_le_right) h₂ q β.1 β.2

  have hA'z : (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).d 𝒲 p
      (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.fst πX πY) 𝒲 𝔘 lam₁ h₁ p α.1) = 0 := by
    rw [OModulePresheaf.d_unitPullback, show (OModulePresheaf.unit πX).d 𝔘 p α.1 = 0 from α.2, unitPullback_zero]
  have hμBz : (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).d 𝒲 q
      (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (𝟙 (pullback πX πY)) 𝒲 𝔓 μ hμ q B) = 0 := by
    rw [OModulePresheaf.d_unitPullback, hBz, unitPullback_zero]

  set μA := OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (𝟙 (pullback πX πY)) 𝒲 𝔓 μ hμ p A with hμA
  set μB := OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (𝟙 (pullback πX πY)) 𝒲 𝔓 μ hμ q B with hμB
  set A' := OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.fst πX πY) 𝒲 𝔘 lam₁ h₁ p α.1 with hA'
  set B' := OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (pullback.snd πX πY) 𝒲 𝔙 lam₂ h₂ q β.1 with hB'
  set C := (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).cup 𝔓 p q n hn A B with hC
  have hsplit : OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (𝟙 (pullback πX πY)) 𝒲 𝔓 μ hμ n C -
      (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).cup 𝒲 p q n hn A' B' =
      (OModulePresheaf.unitPullback (πX := pullback.fst πX πY ≫ πX) (𝟙 (pullback πX πY)) 𝒲 𝔓 μ hμ n C -
        (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).cup 𝒲 p q n hn μA μB) +
      ((OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).cup 𝒲 p q n hn (μA - A') μB +
        (OModulePresheaf.unit (pullback.fst πX πY ≫ πX)).cup 𝒲 p q n hn A' (μB - B')) := by
    rw [cup_sub_left, cup_sub_right]; abel
  rw [hsplit]
  cases p with
  | zero =>
    cases q with
    | zero =>
      obtain rfl : n = 0 := by omega
      change _ ∈ (⊥ : Submodule k _) at hU2 hFA hFB ⊢
      rw [Submodule.mem_bot] at hU2 hFA hFB ⊢
      rw [hU2, hFA, hFB, cup_zero_left, cup_zero_right, add_zero, add_zero]
    | succ q' =>
      obtain rfl : n = q' + 1 := by omega
      change _ ∈ LinearMap.range _ at hU2 hFB ⊢
      change _ ∈ (⊥ : Submodule k _) at hFA
      rw [Submodule.mem_bot] at hFA
      obtain ⟨v, hv⟩ := hFB
      rw [hFA, cup_zero_left, zero_add, ← hv, cup_d_right 𝒲 0 q' q' (by omega) hn A' hA'z v]
      exact Submodule.add_mem _ hU2 ⟨_, rfl⟩
  | succ p' =>
    cases q with
    | zero =>
      obtain rfl : n = p' + 1 := by omega
      change _ ∈ LinearMap.range _ at hU2 hFA ⊢
      change _ ∈ (⊥ : Submodule k _) at hFB
      rw [Submodule.mem_bot] at hFB
      obtain ⟨u, hu⟩ := hFA
      rw [hFB, cup_zero_right, add_zero, ← hu, cup_d_left 𝒲 p' 0 p' (by omega) hn u μB hμBz]
      exact Submodule.add_mem _ hU2 ⟨_, rfl⟩
    | succ q' =>
      obtain rfl : n = (p' + q' + 1) + 1 := by omega
      change _ ∈ LinearMap.range _ at hU2 hFA hFB ⊢
      obtain ⟨u, hu⟩ := hFA
      obtain ⟨v, hv⟩ := hFB
      rw [← hu, ← hv, cup_d_left 𝒲 p' (q' + 1) (p' + q' + 1) (by omega) hn u μB hμBz,
        cup_d_right 𝒲 (p' + 1) q' (p' + q' + 1) (by omega) hn A' hA'z v]
      exact Submodule.add_mem _ hU2 (Submodule.add_mem _ ⟨_, rfl⟩ ⟨_, rfl⟩)

end S_AlgebraicGeometry_OModulePresheaf_unitPullback_prodCover_cup_sub_cup_unitPullback_mem
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_unitPullback_prodCover_cup_sub_cup_unitPullback_mem (solution)
