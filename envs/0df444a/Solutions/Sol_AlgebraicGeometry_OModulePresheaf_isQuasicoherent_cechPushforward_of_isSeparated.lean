-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.isQuasicoherent_cechPushforward_of_isSeparated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/fc9942a7-7772-5850-927e-6b0133e9cc23

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_cechPushforward_of_isSeparated

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace C2QC

open AlgebraicGeometry.OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} (G : OModulePresheaf π)

theorem res_eq_zero_of_eq {W W₁ W₂ : V.Opens} (e : W₁ = W₂) (h₁ : W₁ ≤ W) (h₂ : W₂ ≤ W) (x : G.obj W)
    (hx : G.res h₁ x = 0) : G.res h₂ x = 0 := by
  subst e; exact hx

theorem res_via {W₀ W₁ W : V.Opens} (h₀₁ : W₀ ≤ W₁) (h₁ : W₁ ≤ W) (h₀ : W₀ ≤ W) (x : G.obj W) :
    G.res h₀ x = G.res h₀₁ (G.res h₁ x) := by
  rw [G.res_res]

theorem res_res_of_eq {W₁ W₂ : V.Opens} (h₁₂ : W₁ ≤ W₂) (h₂₁ : W₂ ≤ W₁) (x : G.obj W₁) :
    G.res h₁₂ (G.res h₂₁ x) = x := by
  rw [G.res_res, G.res_refl_apply]

theorem res_smul' {W W' : V.Opens} (h : W ≤ W') (a : Γ(V, W')) (x : G.obj W') :
    G.res h (a • x) = (V.presheaf.map (homOfLE h).op).hom a • G.res h x := G.res_smul h a x

end C2QC

open C2QC in
theorem solution
    {A : Type u} [CommRing A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsSeparated q]
    {V' : Scheme.{u}} (p : V' ⟶ P) [IsSeparated p]
    (K' : V'.OrderedAffineCover) (G : OModulePresheaf (p ≫ q)) (hqc : G.IsQuasicoherent) :
    (OModulePresheaf.cechPushforward p q K' G).IsQuasicoherent := by
  classical
  haveI : IsSeparated (p ≫ q) := inferInstance
  rw [OModulePresheaf.isQuasicoherent_iff]
  intro U f

  have hD : P.basicOpen f ≤ U.1 := P.basicOpen_le f
  have hpre : p ⁻¹ᵁ P.basicOpen f ≤ p ⁻¹ᵁ U.1 := (TopologicalSpace.Opens.map p.base).monotone hD

  have hW : ∀ i : K'.ι, IsAffineOpen (OModulePresheaf.cechPushforward.chart p K' U.1 i) := fun i =>
    Scheme.OrderedAffineCover.fiberAffineOpen p q (K'.isAffineOpen i) U.2
  have hW2 : ∀ i j : K'.ι, IsAffineOpen (OModulePresheaf.cechPushforward.chart p K' U.1 i ⊓
      OModulePresheaf.cechPushforward.chart p K' U.1 j) := fun i j =>
    Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated (p ≫ q) (hW i) (hW j)

  have hch : ∀ i : K'.ι, OModulePresheaf.cechPushforward.chart p K' U.1 i ≤ p ⁻¹ᵁ U.1 := fun i => inf_le_right
  let g : ∀ (W : V'.Opens), W ≤ p ⁻¹ᵁ U.1 → Γ(V', W) := fun W h => (p.appLE U.1 W h).hom f
  have g_res : ∀ (W W' : V'.Opens) (h' : W' ≤ p ⁻¹ᵁ U.1) (e : W ≤ W'),
      (V'.presheaf.map (homOfLE e).op).hom (g W' h') = g W (e.trans h') := by
    intro W W' h' e
    show (p.appLE U.1 W' h' ≫ V'.presheaf.map (homOfLE e).op).hom f = _
    rw [Scheme.Hom.appLE_map]
  have g_D : ∀ (W : V'.Opens) (h : W ≤ p ⁻¹ᵁ P.basicOpen f) (r : Γ(P, U.1)),
      (p.appLE (P.basicOpen f) W h).hom ((P.presheaf.map (homOfLE hD).op).hom r) = (p.appLE U.1 W (h.trans hpre)).hom r := by
    intro W h r
    show (P.presheaf.map (homOfLE hD).op ≫ p.appLE (P.basicOpen f) W h).hom r = _
    rw [Scheme.Hom.map_appLE]

  have bo : ∀ (W : V'.Opens) (h : W ≤ p ⁻¹ᵁ U.1), V'.basicOpen (g W h) = W ⊓ p ⁻¹ᵁ P.basicOpen f := fun W h =>
    Scheme.basicOpen_appLE p W U.1 h f

  have eD : ∀ i : K'.ι, OModulePresheaf.cechPushforward.chart p K' (P.basicOpen f) i =
      V'.basicOpen (g _ (hch i)) := by
    intro i
    rw [bo]
    apply le_antisymm
    · exact le_inf (le_inf inf_le_left (inf_le_right.trans hpre)) inf_le_right
    · exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have eD2 : ∀ i j : K'.ι, OModulePresheaf.cechPushforward.chart p K' (P.basicOpen f) i ⊓
      OModulePresheaf.cechPushforward.chart p K' (P.basicOpen f) j =
      V'.basicOpen (g _ ((inf_le_left.trans (hch i)) :
        OModulePresheaf.cechPushforward.chart p K' U.1 i ⊓ OModulePresheaf.cechPushforward.chart p K' U.1 j ≤ _)) := by
    intro i j
    rw [bo, eD, eD, bo, bo]
    apply le_antisymm
    · exact le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)) (inf_le_left.trans inf_le_right)
    · exact le_inf (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
  refine ⟨?_, ?_⟩
  ·
    intro x

    have hx' : ∀ i : K'.ι, ∃ (n : ℕ) (y : G.obj (OModulePresheaf.cechPushforward.chart p K' U.1 i)),
        G.res (V'.basicOpen_le (g _ (hch i))) y =
          (V'.presheaf.map (homOfLE (V'.basicOpen_le (g _ (hch i)))).op).hom (g _ (hch i) ^ n) •
            G.res (eD i).ge (x.1 i) := fun i =>
      (hqc ⟨_, hW i⟩ (g _ (hch i))).1 (G.res (eD i).ge (x.1 i))
    choose n y hy using hx'
    let N : ℕ := Finset.univ.sup n
    have hnN : ∀ i, n i ≤ N := fun i => Finset.le_sup (Finset.mem_univ i)

    let y' : ∀ i : K'.ι, G.obj (OModulePresheaf.cechPushforward.chart p K' U.1 i) := fun i => g _ (hch i) ^ (N - n i) • y i
    have hy' : ∀ i, G.res (V'.basicOpen_le (g _ (hch i))) (y' i) =
        (V'.presheaf.map (homOfLE (V'.basicOpen_le (g _ (hch i)))).op).hom (g _ (hch i)) ^ N •
          G.res (eD i).ge (x.1 i) := by
      intro i
      simp only [y']
      rw [res_smul' G _ (g _ (hch i) ^ (N - n i)) (y i), hy i, smul_smul, ← map_mul, ← pow_add, Nat.sub_add_cancel (hnN i), map_pow]

    let δ : ∀ i j : K'.ι, G.obj (OModulePresheaf.cechPushforward.chart p K' U.1 i ⊓
        OModulePresheaf.cechPushforward.chart p K' U.1 j) := fun i j =>
      G.res inf_le_left (y' i) - G.res inf_le_right (y' j)
    have hδ : ∀ i j, G.res (V'.basicOpen_le (g _ ((inf_le_left.trans (hch i)) :
        OModulePresheaf.cechPushforward.chart p K' U.1 i ⊓ OModulePresheaf.cechPushforward.chart p K' U.1 j ≤ _)))
        (δ i j) = 0 := by
      intro i j

      have hBi : V'.basicOpen (g _ ((inf_le_left.trans (hch i)) :
          OModulePresheaf.cechPushforward.chart p K' U.1 i ⊓ OModulePresheaf.cechPushforward.chart p K' U.1 j ≤ _)) ≤
          V'.basicOpen (g _ (hch i)) := by rw [bo, bo]; exact inf_le_inf_right _ inf_le_left
      have hBj : V'.basicOpen (g _ ((inf_le_left.trans (hch i)) :
          OModulePresheaf.cechPushforward.chart p K' U.1 i ⊓ OModulePresheaf.cechPushforward.chart p K' U.1 j ≤ _)) ≤
          V'.basicOpen (g _ (hch j)) := by rw [bo, bo]; exact inf_le_inf_right _ inf_le_right
      simp only [δ, map_sub]
      rw [G.res_res, G.res_res]
      rw [res_via G hBi (V'.basicOpen_le _) _ (y' i), res_via G hBj (V'.basicOpen_le _) _ (y' j), hy' i, hy' j,
        res_smul' G hBi, res_smul' G hBj, map_pow, map_pow, g_res, g_res, g_res, g_res, G.res_res, G.res_res]

      have hc := (OModulePresheaf.cechPushforward.mem_cocycles_iff p q K' G _ x.1).mp x.2 i j
      have key : G.res ((eD2 i j).ge.trans inf_le_left) (x.1 i) = G.res ((eD2 i j).ge.trans inf_le_right) (x.1 j) := by
        rw [res_via G (eD2 i j).ge inf_le_left, res_via G (eD2 i j).ge inf_le_right, hc]
      rw [key, sub_self]
    have hm : ∀ i j, ∃ m : ℕ, (g _ ((inf_le_left.trans (hch i)) :
        OModulePresheaf.cechPushforward.chart p K' U.1 i ⊓ OModulePresheaf.cechPushforward.chart p K' U.1 j ≤ _)) ^ m • δ i j = 0 :=
      fun i j => (hqc ⟨_, hW2 i j⟩ _).2 (δ i j) (hδ i j)
    choose m hm' using hm
    let M : ℕ := Finset.univ.sup (fun ij : K'.ι × K'.ι => m ij.1 ij.2)
    have hmM : ∀ i j, m i j ≤ M := fun i j => Finset.le_sup (f := fun ij : K'.ι × K'.ι => m ij.1 ij.2) (Finset.mem_univ (i, j))

    let z : ∀ i : K'.ι, G.obj (OModulePresheaf.cechPushforward.chart p K' U.1 i) := fun i => g _ (hch i) ^ M • y' i
    have hz : z ∈ OModulePresheaf.cechPushforward.cocycles p q K' G U.1 := by
      rw [OModulePresheaf.cechPushforward.mem_cocycles_iff]
      intro i j
      simp only [z]
      rw [res_smul' G inf_le_left (g _ (hch i) ^ M) (y' i), res_smul' G inf_le_right (g _ (hch j) ^ M) (y' j),
        map_pow, map_pow, g_res, g_res, ← sub_eq_zero, ← smul_sub]
      change (g _ ((inf_le_left.trans (hch i)) :
        OModulePresheaf.cechPushforward.chart p K' U.1 i ⊓ OModulePresheaf.cechPushforward.chart p K' U.1 j ≤ _)) ^ M • δ i j = 0
      rw [← Nat.sub_add_cancel (hmM i j), pow_add, mul_smul, hm' i j, smul_zero]
    refine ⟨M + N, ⟨z, hz⟩, ?_⟩
    apply OModulePresheaf.cechPushforward.ext
    intro i
    rw [OModulePresheaf.cechPushforward.coe_res, OModulePresheaf.cechPushforward.coe_sectionsSMul]
    change G.res _ (z i) = (p.appLE (P.basicOpen f) _ _).hom ((P.presheaf.map (homOfLE hD).op).hom (f ^ (M + N))) • x.1 i
    rw [g_D, map_pow]
    simp only [z]
    rw [res_via G (eD i).le (V'.basicOpen_le _) _ (g _ (hch i) ^ M • y' i), res_smul' G _ (g _ (hch i) ^ M) (y' i), hy' i,
      res_smul' G (eD i).le, res_smul' G (eD i).le, res_res_of_eq, smul_smul]
    simp only [map_pow, g_res, ← pow_add]
    rfl
  ·
    intro yy hyy
    have hy0 : ∀ i : K'.ι, G.res (V'.basicOpen_le (g _ (hch i))) (yy.1 i) = 0 := by
      intro i
      have h1 : G.res (OModulePresheaf.cechPushforward.chart_mono p K' hD i) (yy.1 i) = 0 := by
        have := congrArg (fun w => w.1 i) hyy
        exact this
      exact res_eq_zero_of_eq G (eD i) _ _ _ h1
    have hn : ∀ i : K'.ι, ∃ n : ℕ, (g _ (hch i)) ^ n • yy.1 i = 0 := fun i =>
      (hqc ⟨_, hW i⟩ (g _ (hch i))).2 (yy.1 i) (hy0 i)
    choose n hn' using hn
    refine ⟨Finset.univ.sup n, ?_⟩
    apply OModulePresheaf.cechPushforward.ext
    intro i
    rw [OModulePresheaf.cechPushforward.coe_sectionsSMul]
    change (p.appLE U.1 _ _).hom (f ^ Finset.univ.sup n) • yy.1 i = 0
    rw [map_pow]
    change g _ (hch i) ^ Finset.univ.sup n • yy.1 i = 0
    rw [← Nat.sub_add_cancel (Finset.le_sup (f := n) (Finset.mem_univ i)), pow_add, mul_smul, hn' i, smul_zero]

end S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_cechPushforward_of_isSeparated
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_cechPushforward_of_isSeparated (solution)
