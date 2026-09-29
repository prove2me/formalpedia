-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_basisData_of_chartData_of_cocycle_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/2c0fceee-15c7-5672-93e4-b9d920242369

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_cocycle_of_comp_eq

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

noncomputable section

namespace GlueY3Sol

open Classical

variable {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}
variable (K : P.OrderedAffineCover)

def B : Set P.affineOpens := {U | ∃ i : K.ι, U.1 ≤ K.U i}

theorem hdown : ∀ (W W' : P.affineOpens), W'.1 ≤ W.1 → W ∈ B K → W' ∈ B K :=
  fun _ _ h ⟨i, hi⟩ => ⟨i, h.trans hi⟩

theorem hcov : ∀ x : P, ∃ W ∈ B K, x ∈ W.1 := by
  intro x
  have hx : x ∈ (⨆ i, K.U i : P.Opens) := by rw [K.iSup_eq_top]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact ⟨⟨K.U i, K.isAffineOpen i⟩, ⟨i, le_rfl⟩, hi⟩

def idx (U : ↥(B K)) : K.ι :=
  (Finset.univ.filter fun i => U.1.1 ≤ K.U i).min'
    (by obtain ⟨i, hi⟩ := U.2; exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩)

theorem le_idx (U : ↥(B K)) : U.1.1 ≤ K.U (idx K U) := by
  have := Finset.min'_mem (Finset.univ.filter fun i => U.1.1 ≤ K.U i)
    (by obtain ⟨i, hi⟩ := U.2; exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩)
  exact (Finset.mem_filter.mp this).2

abbrev toChart (U : ↥(B K)) : {U' : P.affineOpens // U'.1 ≤ K.U (idx K U)} := ⟨U.1, le_idx K U⟩

abbrev toChart' (U U' : ↥(B K)) (h : U'.1.1 ≤ U.1.1) : {U'' : P.affineOpens // U''.1 ≤ K.U (idx K U)} :=
  ⟨U'.1, h.trans (le_idx K U)⟩

variable (M : ∀ i : K.ι, {U : P.affineOpens // U.1 ≤ K.U i} → Type u)
  [i1 : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), AddCommGroup (M i U)]
  [i2 : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module A (M i U)]
  [iΓ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module Γ(P, U.1.1) (M i U)]

def N (U : ↥(B K)) : Type u := M (idx K U) (toChart K U)

scoped instance instN1 (U : ↥(B K)) : AddCommGroup (N K M U) := i1 (idx K U) (toChart K U)
scoped instance instN2 (U : ↥(B K)) : Module A (N K M U) := i2 (idx K U) (toChart K U)
scoped instance instNΓ (U : ↥(B K)) : Module Γ(P, U.1.1) (N K M U) := iΓ (idx K U) (toChart K U)

variable (res : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}}, U'.1.1 ≤ U.1.1 → (M i U →ₗ[A] M i U'))
  (u : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), M i W →ₗ[A] M j ⟨W.1, hj⟩)

def Nres {U U' : ↥(B K)} (h : U'.1.1 ≤ U.1.1) : N K M U →ₗ[A] N K M U' :=
  (u (idx K U) (idx K U') (toChart' K U U' h) (le_idx K U')) ∘ₗ
    (res (idx K U) (U := toChart K U) (U' := toChart' K U U' h) h)

theorem Nres_apply {U U' : ↥(B K)} (h : U'.1.1 ≤ U.1.1) (x : N K M U) :
    Nres K M res u h x = u (idx K U) (idx K U') (toChart' K U U' h) (le_idx K U')
      (res (idx K U) (U := toChart K U) (U' := toChart' K U U' h) h x) := rfl

end GlueY3Sol
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_cocycle_of_comp_eq.GlueY3Sol"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_cocycle_of_comp_eq.GlueY3Sol"

open GlueY3Sol in
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
    (hcocy : ∀ (i j l : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (hl : W.1.1 ≤ K.U l) (x : M i W),
        u j l ⟨W.1, hj⟩ hl (u i j W hj x) = u i l W hl x)
    (huθF : ∀ (i j : K.ι) (k : ℕ) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : M i W),
        θF j k ⟨W.1, hj⟩ (u i j W hj x) = θF i k W x)
    :
    ∃ (B : Set P.affineOpens)
      (_hdown : ∀ (W W' : P.affineOpens), W'.1 ≤ W.1 → W ∈ B → W' ∈ B)
      (_hcov : ∀ x : P, ∃ W ∈ B, x ∈ W.1)
      (M : ↥B → Type u) (_ : ∀ W, AddCommGroup (M W)) (_ : ∀ W, Module A (M W)) (_ : ∀ W, Module Γ(P, W.1.1) (M W))
      (_ : ∀ W : ↥B, letI := Scheme.TwoAffineOpenCover.algebraOfHom q W.1.1; IsScalarTower A Γ(P, W.1.1) (M W))
      (res : ∀ {W W' : ↥B}, W'.1.1 ≤ W.1.1 → (M W →ₗ[A] M W'))
      (_res_smul : ∀ {W W' : ↥B} (h : W'.1.1 ≤ W.1.1) (a : Γ(P, W.1.1)) (x : M W),
        res h (a • x) = (P.presheaf.map (homOfLE h).op).hom a • res h x)
      (_res_refl : ∀ (W : ↥B) (x : M W), res (le_refl W.1.1) x = x)
      (_res_comp : ∀ {W W' W'' : ↥B} (h : W''.1.1 ≤ W'.1.1) (h' : W'.1.1 ≤ W.1.1) (x : M W),
        res (h.trans h') x = res h (res h' x))
      (_hqc : ∀ (W Wg : ↥B) (g : Γ(P, W.1.1)) (hWg : Wg.1.1 = P.basicOpen g),
        (∀ y : M Wg, ∃ (n : ℕ) (x : M W),
            res (hWg.trans_le (P.basicOpen_le g)) x =
              (P.presheaf.map (homOfLE (hWg.trans_le (P.basicOpen_le g))).op).hom (g ^ n) • y) ∧
        (∀ x : M W, res (hWg.trans_le (P.basicOpen_le g)) x = 0 → ∃ n : ℕ, (g ^ n) • x = 0))
      (_hfg : ∀ W : ↥B, Module.Finite (Γ(P, W.1.1) : Type u) (M W))

      (ϑ : ∀ W : ↥B, GK.obj W.1.1 →ₗ[A] M W)
      (θE : ∀ W : ↥B, M W →ₗ[A] GE.obj W.1.1)
      (θF : ∀ (k : ℕ) (W : ↥B), M W →ₗ[A] (F k).obj W.1.1),

      (∀ (W : ↥B) (a : Γ(P, W.1.1)) (x : GK.obj W.1.1), ϑ W (a • x) = a • ϑ W x) ∧
      (∀ (W : ↥B) (a : Γ(P, W.1.1)) (x : M W), θE W (a • x) = a • θE W x) ∧
      (∀ (k : ℕ) (W : ↥B) (a : Γ(P, W.1.1)) (x : M W), θF k W (a • x) = a • θF k W x) ∧

      (∀ (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : GK.obj W.1.1), ϑ W' (GK.res h x) = res h (ϑ W x)) ∧
      (∀ (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : M W), θE W' (res h x) = GE.res h (θE W x)) ∧
      (∀ (k : ℕ) (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : M W), θF k W' (res h x) = (F k).res h (θF k W x)) ∧

      (∀ W : ↥B, LinearMap.range (ϑ W) = LinearMap.ker (θE W)) ∧
      (∀ W : ↥B, Function.Surjective (θE W)) ∧

      (∀ (k : ℕ) (W : ↥B), (φ k).app W.1 ∘ₗ θF (k + 1) W = θF k W) ∧
      (∀ (k : ℕ) (W : ↥B), θF k W ∘ₗ ϑ W = (lam k).app W.1) ∧
      (∀ (k : ℕ) (W : ↥B), (ε k).app W.1 ∘ₗ θF k W = (ψE k).app W.1 ∘ₗ θE W) := by
  classical

  have u_self : ∀ (i : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (x : M i W), u i i W W.2 x = x := by
    intro i W x
    have h := hcocy i i i W W.2 W.2 x
    exact (hub i i W W.2).1 h

  refine ⟨B K, hdown K, hcov K, N K M, inferInstance, inferInstance, inferInstance, fun W => ?_, Nres K M res u,
    ?_, ?_, ?_, ?_, fun W => hfg (idx K W) (toChart K W),
    fun W => ϑ (idx K W) (toChart K W), fun W => θE (idx K W) (toChart K W), fun k W => θF (idx K W) k (toChart K W),
    fun W a x => hϑs (idx K W) (toChart K W) a x, fun W a x => hθEs (idx K W) (toChart K W) a x,
    fun k W a x => hθFs (idx K W) k (toChart K W) a x, ?_, ?_, ?_,
    fun W => hexact (idx K W) (toChart K W), fun W => hsurj (idx K W) (toChart K W),
    fun k W => hc1 (idx K W) k (toChart K W), fun k W => hc2 (idx K W) k (toChart K W), fun k W => hc3 (idx K W) k (toChart K W)⟩
  ·
    exact (inferInstance : letI := Scheme.TwoAffineOpenCover.algebraOfHom q (toChart K W).1.1;
      IsScalarTower A Γ(P, (toChart K W).1.1) (M (idx K W) (toChart K W)))
  ·
    intro W W' h a x
    have e1 := res_smul (idx K W) (U := toChart K W) (U' := toChart' K W W' h) h a x
    have e2 := hus (idx K W) (idx K W') (toChart' K W W' h) (le_idx K W')
      ((P.presheaf.map (homOfLE h).op).hom a) (res (idx K W) (U := toChart K W) (U' := toChart' K W W' h) h x)
    exact (congrArg (u (idx K W) (idx K W') (toChart' K W W' h) (le_idx K W')) e1).trans e2
  ·
    intro W x
    change u (idx K W) (idx K W) (toChart K W) (le_idx K W) (res (idx K W) (U := toChart K W) (U' := toChart K W) (le_refl _) x) = x
    rw [res_refl, u_self]
  ·
    intro W W' W'' h h' x
    show u (idx K W) (idx K W'') (toChart' K W W'' (h.trans h')) (le_idx K W'') (res (idx K W) (h.trans h') x) =
      u (idx K W') (idx K W'') (toChart' K W' W'' h) (le_idx K W'')
        (res (idx K W') h (u (idx K W) (idx K W') (toChart' K W W' h') (le_idx K W') (res (idx K W) h' x)))
    rw [res_comp (idx K W) (U := toChart K W) (U' := toChart' K W W' h') (U'' := toChart' K W W'' (h.trans h')) h h',
      ← hun (idx K W) (idx K W') (toChart' K W W' h') (toChart' K W W'' (h.trans h')) (le_idx K W') h,
      hcocy (idx K W) (idx K W') (idx K W'') (toChart' K W W'' (h.trans h')) ((h.trans (le_idx K W'))) (le_idx K W'')]
  ·
    intro W Wg g hWg
    have hq := hqc (idx K W) (toChart K W) (toChart' K W Wg (hWg.trans_le (P.basicOpen_le g))) g hWg
    constructor
    · intro y

      obtain ⟨y₁, hy₁⟩ := (hub (idx K W) (idx K Wg) (toChart' K W Wg (hWg.trans_le (P.basicOpen_le g))) (le_idx K Wg)).2 y
      obtain ⟨n, x, hx⟩ := hq.1 y₁
      refine ⟨n, x, ?_⟩
      have e2 := hus (idx K W) (idx K Wg) (toChart' K W Wg (hWg.trans_le (P.basicOpen_le g))) (le_idx K Wg)
        ((P.presheaf.map (homOfLE (hWg.trans_le (P.basicOpen_le g))).op).hom (g ^ n)) y₁
      rw [hy₁] at e2
      exact (congrArg (u (idx K W) (idx K Wg) (toChart' K W Wg (hWg.trans_le (P.basicOpen_le g))) (le_idx K Wg)) hx).trans e2
    · intro x hx
      have h0 : res (idx K W) (U := toChart K W) (U' := toChart' K W Wg (hWg.trans_le (P.basicOpen_le g)))
          (hWg.trans_le (P.basicOpen_le g)) x = 0 := by
        apply (hub (idx K W) (idx K Wg) (toChart' K W Wg (hWg.trans_le (P.basicOpen_le g))) (le_idx K Wg)).1
        rw [map_zero]
        exact hx
      exact hq.2 x h0
  ·
    intro W W' h x
    show ϑ (idx K W') (toChart K W') (GK.res h x) = Nres K M res u h (ϑ (idx K W) (toChart K W) x)
    rw [Nres_apply, ← hϑn (idx K W) (toChart K W) (toChart' K W W' h) h x,
      huϑ (idx K W) (idx K W') (toChart' K W W' h) (le_idx K W')]
  ·
    intro W W' h x
    show θE (idx K W') (toChart K W') (Nres K M res u h x) = GE.res h (θE (idx K W) (toChart K W) x)
    rw [Nres_apply, huθE (idx K W) (idx K W') (toChart' K W W' h) (le_idx K W'),
      hθEn (idx K W) (toChart K W) (toChart' K W W' h) h x]
  ·
    intro k W W' h x
    show θF (idx K W') k (toChart K W') (Nres K M res u h x) = (F k).res h (θF (idx K W) k (toChart K W) x)
    rw [Nres_apply, huθF (idx K W) (idx K W') k (toChart' K W W' h) (le_idx K W'),
      hθFn (idx K W) k (toChart K W) (toChart' K W W' h) h x]

end S_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_cocycle_of_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_cocycle_of_comp_eq (solution)
