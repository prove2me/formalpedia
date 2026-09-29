-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_cochain_internalHom_forall_eq_comp_sub_of_chartData
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/3699ac19-d53f-5b0b-b489-f0f276cb97d2

import Mathlib
import Theorems.Thm_LinearMap_existsUnique_sub_eq_comp_comp_of_extension
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cochain_internalHom_forall_eq_comp_sub_of_chartData

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (hεs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U))
    (hεc : ∀ (k : ℕ) (U : P.affineOpens),
      (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U)
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (hψEs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψE k).app U))
    (hψEk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψE k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GE.obj U.1)))
    (hψEc : ∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψE (k + 1)).app U = (ψE k).app U)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1)))
    (K : P.OrderedAffineCover)
    (M : ∀ i : K.ι, {U : P.affineOpens // U.1 ≤ K.U i} → Type u)
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), AddCommGroup (M i U)]
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module A (M i U)]
    [iΓ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module Γ(P, U.1.1) (M i U)]
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
        letI := Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1; IsScalarTower A Γ(P, U.1.1) (M i U)]
    (res : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}}, U'.1.1 ≤ U.1.1 → (M i U →ₗ[A] M i U'))
    (res_smul : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}} (h : U'.1.1 ≤ U.1.1) (a : Γ(P, U.1.1)) (x : M i U),
        res i h (a • x) = (P.presheaf.map (homOfLE h).op).hom a • res i h x)
    (res_refl : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (x : M i U), res i (le_refl U.1.1) x = x)
    (res_comp : ∀ (i : K.ι) {U U' U'' : {U : P.affineOpens // U.1 ≤ K.U i}} (h : U''.1.1 ≤ U'.1.1) (h' : U'.1.1 ≤ U.1.1)
        (x : M i U), res i (h.trans h') x = res i h (res i h' x))
    (hqc : ∀ (i : K.ι) (U Ug : {U : P.affineOpens // U.1 ≤ K.U i}) (g : Γ(P, U.1.1)) (hUg : Ug.1.1 = P.basicOpen g),
        (∀ y : M i Ug, ∃ (n : ℕ) (x : M i U),
            res i (hUg.trans_le (P.basicOpen_le g)) x =
              (P.presheaf.map (homOfLE (hUg.trans_le (P.basicOpen_le g))).op).hom (g ^ n) • y) ∧
        (∀ x : M i U, res i (hUg.trans_le (P.basicOpen_le g)) x = 0 → ∃ n : ℕ, (g ^ n) • x = 0))
    (hfg : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module.Finite (Γ(P, U.1.1) : Type u) (M i U))
    (ϑ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), GK.obj U.1.1 →ₗ[A] M i U)
    (θE : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] GE.obj U.1.1)
    (θF : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] (F k).obj U.1.1)
    (hϑs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : GK.obj U.1.1), ϑ i U (a • x) = a • ϑ i U x)
    (hθEs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U), θE i U (a • x) = a • θE i U x)
    (hθFs : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U),
        θF i k U (a • x) = a • θF i k U x)
    (hϑn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : GK.obj U.1.1),
        ϑ i U' (GK.res h x) = res i h (ϑ i U x))
    (hθEn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θE i U' (res i h x) = GE.res h (θE i U x))
    (hθFn : ∀ (i : K.ι) (k : ℕ) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θF i k U' (res i h x) = (F k).res h (θF i k U x))
    (hexact : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), LinearMap.range (ϑ i U) = LinearMap.ker (θE i U))
    (hsurj : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Surjective (θE i U))
    (hϑi : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Injective (ϑ i U))
    (hc1 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (φ k).app U.1 ∘ₗ θF i (k + 1) U = θF i k U)
    (hc2 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), θF i k U ∘ₗ ϑ i U = (lam k).app U.1)
    (hc3 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (ε k).app U.1 ∘ₗ θF i k U = (ψE k).app U.1 ∘ₗ θE i U)

    (u : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), M i W →ₗ[A] M j ⟨W.1, hj⟩)
    (hub : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), Function.Bijective (u i j W hj))
    (hus : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (a : Γ(P, W.1.1)) (x : M i W),
        letI : Module Γ(P, W.1.1) (M j ⟨W.1, hj⟩) := iΓ j ⟨W.1, hj⟩
        u i j W hj (a • x) = a • u i j W hj x)
    (hun : ∀ (i j : K.ι) (W W' : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (h : W'.1.1 ≤ W.1.1) (x : M i W),
        u i j W' (h.trans hj) (res i h x) = res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (u i j W hj x))
    (huϑ : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : GK.obj W.1.1),
        u i j W hj (ϑ i W x) = ϑ j ⟨W.1, hj⟩ x)
    (huθE : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : M i W),
        θE j ⟨W.1, hj⟩ (u i j W hj x) = θE i W x)
    :
    ∃ g : (OModulePresheaf.internalHom GE GK).cochain K 2,
      ∀ (s : K.Idx 2) (W : {U : P.affineOpens // U.1 ≤ K.inter s})
        (x : M (s.1 0) ⟨W.1, W.2.trans (K.inter_le s 0)⟩),
        ϑ (s.1 2) ⟨W.1, W.2.trans (K.inter_le s 2)⟩ ((g s).1 W (θE (s.1 0) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ x)) =
          u (s.1 1) (s.1 2) ⟨W.1, W.2.trans (K.inter_le s 1)⟩ (W.2.trans (K.inter_le s 2))
              (u (s.1 0) (s.1 1) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ (W.2.trans (K.inter_le s 1)) x) -
            u (s.1 0) (s.1 2) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ (W.2.trans (K.inter_le s 2)) x := by
  classical
  have huθE' : ∀ (i j : K.ι) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j) (x : M i ⟨W, hi⟩),
      θE j ⟨W, hj⟩ (u i j ⟨W, hi⟩ hj x) = θE i ⟨W, hi⟩ x := fun i j W hi hj x => huθE i j ⟨W, hi⟩ hj x
  have hEU : ∀ (s : K.Idx 2) (W : {U : P.affineOpens // U.1 ≤ K.inter s}),
      ∃! γ : GE.obj W.1.1 →ₗ[A] GK.obj W.1.1,
        (u (s.1 1) (s.1 2) ⟨W.1, W.2.trans (K.inter_le s 1)⟩ (W.2.trans (K.inter_le s 2)) ∘ₗ u (s.1 0) (s.1 1) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ (W.2.trans (K.inter_le s 1))) - (u (s.1 0) (s.1 2) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ (W.2.trans (K.inter_le s 2))) = ϑ (s.1 2) ⟨W.1, W.2.trans (K.inter_le s 2)⟩ ∘ₗ γ ∘ₗ θE (s.1 0) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ := by
    intro s W
    refine LinearMap.existsUnique_sub_eq_comp_comp_of_extension (ϑ (s.1 0) ⟨W.1, W.2.trans (K.inter_le s 0)⟩) (θE (s.1 0) ⟨W.1, W.2.trans (K.inter_le s 0)⟩) (ϑ (s.1 2) ⟨W.1, W.2.trans (K.inter_le s 2)⟩) (θE (s.1 2) ⟨W.1, W.2.trans (K.inter_le s 2)⟩)
      (hsurj _ _) (hexact _ _) (hϑi _ _) (hexact _ _) _ _ ?_ ?_
    · ext y
      simp only [LinearMap.coe_comp, Function.comp_apply]
      rw [huϑ, huϑ, huϑ]
    · ext y
      simp only [LinearMap.coe_comp, Function.comp_apply]
      rw [huθE', huθE', huθE']
  choose γ hγu using hEU
  have hγ : ∀ (s : K.Idx 2) (W : {U : P.affineOpens // U.1 ≤ K.inter s}) (x : M (s.1 0) ⟨W.1, W.2.trans (K.inter_le s 0)⟩),
      ϑ (s.1 2) ⟨W.1, W.2.trans (K.inter_le s 2)⟩ (γ s W (θE (s.1 0) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ x)) =
        u (s.1 1) (s.1 2) ⟨W.1, W.2.trans (K.inter_le s 1)⟩ (W.2.trans (K.inter_le s 2)) (u (s.1 0) (s.1 1) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ (W.2.trans (K.inter_le s 1)) x) -
          u (s.1 0) (s.1 2) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ (W.2.trans (K.inter_le s 2)) x := by
    intro s W x
    have := congrArg (fun f : M (s.1 0) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ →ₗ[A] M (s.1 2) ⟨W.1, W.2.trans (K.inter_le s 2)⟩ => f x) (hγu s W).1
    simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply] at this
    exact this.symm

  have hγs : ∀ (s : K.Idx 2) (W : {U : P.affineOpens // U.1 ≤ K.inter s}) (a : Γ(P, W.1.1)) (e : GE.obj W.1.1),
      γ s W (a • e) = a • γ s W e := by
    intro s W a e
    obtain ⟨x, rfl⟩ := hsurj (s.1 0) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ e
    apply hϑi (s.1 2) ⟨W.1, W.2.trans (K.inter_le s 2)⟩
    have e1 := hθEs (s.1 0) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ a x
    have e2 := hϑs (s.1 2) ⟨W.1, W.2.trans (K.inter_le s 2)⟩ a (γ s W (θE (s.1 0) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ x))
    have e3 := hus (s.1 0) (s.1 1) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ (W.2.trans (K.inter_le s 1)) a x
    have e4 := hus (s.1 1) (s.1 2) ⟨W.1, W.2.trans (K.inter_le s 1)⟩ (W.2.trans (K.inter_le s 2)) a
      (u (s.1 0) (s.1 1) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ (W.2.trans (K.inter_le s 1)) x)
    have e5 := hus (s.1 0) (s.1 2) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ (W.2.trans (K.inter_le s 2)) a x
    rw [← e1, hγ, e2, hγ, e3, e4, e5, smul_sub]

  have hγn : ∀ (s : K.Idx 2) (W W' : {U : P.affineOpens // U.1 ≤ K.inter s}) (h : W.1.1 ≤ W'.1.1) (e : GE.obj W'.1.1),
      γ s W (GE.res h e) = GK.res h (γ s W' e) := by
    intro s W W' h e
    obtain ⟨x, rfl⟩ := hsurj (s.1 0) ⟨W'.1, W'.2.trans (K.inter_le s 0)⟩ e
    apply hϑi (s.1 2) ⟨W.1, W.2.trans (K.inter_le s 2)⟩
    have e1 := hθEn (s.1 0) ⟨W'.1, W'.2.trans (K.inter_le s 0)⟩ ⟨W.1, W.2.trans (K.inter_le s 0)⟩ h x
    have e2 := hϑn (s.1 2) ⟨W'.1, W'.2.trans (K.inter_le s 2)⟩ ⟨W.1, W.2.trans (K.inter_le s 2)⟩ h (γ s W' (θE (s.1 0) ⟨W'.1, W'.2.trans (K.inter_le s 0)⟩ x))
    have e3 := hun (s.1 0) (s.1 2) ⟨W'.1, W'.2.trans (K.inter_le s 0)⟩ ⟨W.1, W.2.trans (K.inter_le s 0)⟩ (W'.2.trans (K.inter_le s 2)) h x
    have e4 := hun (s.1 0) (s.1 1) ⟨W'.1, W'.2.trans (K.inter_le s 0)⟩ ⟨W.1, W.2.trans (K.inter_le s 0)⟩ (W'.2.trans (K.inter_le s 1)) h x
    have e5 := hun (s.1 1) (s.1 2) ⟨W'.1, W'.2.trans (K.inter_le s 1)⟩ ⟨W.1, W.2.trans (K.inter_le s 1)⟩ (W'.2.trans (K.inter_le s 2)) h
      (u (s.1 0) (s.1 1) ⟨W'.1, W'.2.trans (K.inter_le s 0)⟩ (W'.2.trans (K.inter_le s 1)) x)
    rw [← e1, hγ, e2, hγ, map_sub, e4, e5, e3]
  refine ⟨fun s => ⟨fun W => γ s W, ⟨fun W a e => hγs s W a e, fun W W' h e => hγn s W W' h e⟩⟩, ?_⟩
  intro s W x
  exact hγ s W x

end S_AlgebraicGeometry_OModulePresheaf_exists_cochain_internalHom_forall_eq_comp_sub_of_chartData
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cochain_internalHom_forall_eq_comp_sub_of_chartData (solution)
