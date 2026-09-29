-- Prove2me | solution 1 for AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.exists_pow_mul_eq_zero_of_map_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/c7dd4880-a074-5c8d-b1ee-6d22fd0440b5

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Proj_basicOpen_mul_eq_basicOpen_awayToSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_pow_mul_eq_zero_of_map_eq_zero

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization"

attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section

namespace DehomSol

open AlgebraicGeometry.GradedOAlgebra AlgebraicGeometry.Scheme.Modules

theorem smul_one_nat (m : ℕ) : m • (1 : ℕ) = m := by simp

theorem map_app {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) {U W : X.Opens} (i : W ⟶ U) (x : Γ(M, U)) :
    N.presheaf.map i.op (φ.app U x) = φ.app W (M.presheaf.map i.op x) := by
  have h := congr($(φ.mapPresheaf.naturality i.op) x)
  simp only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app] at h
  exact h.symm

variable {S : Type u} [CommRing S] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of S)} {L : X.Modules}
    {R : Type u} [CommRing R] [Algebra S R] {𝓡 : ℕ → Submodule S R} [GradedAlgebra 𝓡]
    {ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)} (hR : IsSectionRing f L R 𝓡 ι)
    (τ : 𝓡 1) (V : X.Opens) (hτ : IsFrameOn (ι 1 τ) V)

theorem pow_mem (d : ℕ) : (τ : R) ^ d ∈ 𝓡 d := by
  simpa only [smul_eq_mul, mul_one] using SetLike.pow_mem_graded d τ.2

def τpow (d : ℕ) : 𝓡 d := ⟨(τ : R) ^ d, pow_mem τ d⟩

@[scoped simp] theorem coe_τpow (d : ℕ) : (τpow τ d : R) = (τ : R) ^ d := rfl

theorem τpow_zero : τpow τ 0 = ⟨1, SetLike.GradedOne.one_mem⟩ := Subtype.ext (pow_zero _)

theorem τpow_succ (d : ℕ) :
    τpow τ (d + 1) = ⟨(τpow τ d : R) * (τ : R), SetLike.GradedMul.mul_mem (τpow τ d).2 τ.2⟩ :=
  Subtype.ext (pow_succ _ _)

theorem τpow_add (i j : ℕ) :
    τpow τ (i + j) = ⟨(τpow τ i : R) * (τpow τ j : R), SetLike.GradedMul.mul_mem (τpow τ i).2 (τpow τ j).2⟩ :=
  Subtype.ext (pow_add _ _ _)

include hR hτ in

theorem isFrameOn_pow : ∀ d : ℕ, IsFrameOn (ι d (τpow τ d)) V
  | 0 => by
    rw [τpow_zero, hR.map_one]
    exact isFrameOn_unitSection V
  | d + 1 => by
    rw [τpow_succ, hR.map_mul d 1 (τpow τ d) τ]
    exact ((isFrameOn_pow d).tensorSections_monoidalV2 hτ).map_iso (tensorPowAdd L d 1)

def frameEquiv (d : ℕ) : Γ(X, V) ≃ Γ(L.tensorPow d, V) :=
  Equiv.ofBijective
    (fun g : Γ(X, V) => g • (L.tensorPow d).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (ι d (τpow τ d)))
    (isFrameOn_pow hR τ V hτ d (le_top : V ≤ ⊤) le_rfl)

theorem frameEquiv_apply (d : ℕ) (g : Γ(X, V)) :
    frameEquiv hR τ V hτ d g = g • (L.tensorPow d).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (ι d (τpow τ d)) :=
  rfl

def ψfun (d : ℕ) (s : 𝓡 d) : Γ(X, V) :=
  (frameEquiv hR τ V hτ d).symm ((L.tensorPow d).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (ι d s))

theorem ψfun_smul (d : ℕ) (s : 𝓡 d) :
    ψfun hR τ V hτ d s • (L.tensorPow d).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (ι d (τpow τ d)) =
      (L.tensorPow d).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (ι d s) := by
  rw [← frameEquiv_apply hR τ V hτ d]
  exact Equiv.apply_symm_apply _ _

theorem eq_ψfun (d : ℕ) (s : 𝓡 d) (g : Γ(X, V))
    (hg : g • (L.tensorPow d).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (ι d (τpow τ d)) =
      (L.tensorPow d).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (ι d s)) :
    g = ψfun hR τ V hτ d s := by
  apply (frameEquiv hR τ V hτ d).injective
  rw [frameEquiv_apply, frameEquiv_apply, hg, ψfun_smul]

def ψ (d : ℕ) : 𝓡 d →+ Γ(X, V) :=
  AddMonoidHom.mk' (ψfun hR τ V hτ d) fun a b => by
    symm
    apply eq_ψfun
    rw [add_smul, ψfun_smul, ψfun_smul, hR.map_add, map_add]

@[scoped simp] theorem ψ_apply (d : ℕ) (s : 𝓡 d) : ψ hR τ V hτ d s = ψfun hR τ V hτ d s := rfl

theorem ψ_one : ψ hR τ V hτ 0 (GradedMonoid.GOne.one (A := fun i => ↥(𝓡 i))) = 1 := by
  rw [ψ_apply]; symm; apply eq_ψfun
  rw [one_smul, τpow_zero]
  rfl

theorem ψ_mul {i j : ℕ} (a : 𝓡 i) (b : 𝓡 j) :
    ψ hR τ V hτ (i + j) (GradedMonoid.GMul.mul (A := fun i => ↥(𝓡 i)) a b) =
      ψ hR τ V hτ i a * ψ hR τ V hτ j b := by
  rw [ψ_apply, ψ_apply, ψ_apply]; symm; apply eq_ψfun
  change _ = (L.tensorPow (i + j)).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
    (ι (i + j) ⟨(a : R) * (b : R), SetLike.GradedMul.mul_mem a.2 b.2⟩)
  rw [τpow_add, hR.map_mul i j (τpow τ i) (τpow τ j), hR.map_mul i j a b, map_app, map_app,
    map_homOfLE_tensorSections, map_homOfLE_tensorSections, ← Scheme.Modules.Hom.app_smul,
    mul_smul, ← tensorSections_smul_right, ← tensorSections_smul_left, ψfun_smul, ψfun_smul]

def φ : R →+* Γ(X, V) :=
  (DirectSum.toSemiring (fun d => ψ hR τ V hτ d) (ψ_one hR τ V hτ) (fun a b => ψ_mul hR τ V hτ a b)).comp
    (DirectSum.decomposeRingEquiv 𝓡).toRingHom

theorem φ_coe (d : ℕ) (s : 𝓡 d) : φ hR τ V hτ (s : R) = ψfun hR τ V hτ d s := by
  simp only [φ, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [show DirectSum.decomposeRingEquiv 𝓡 (s : R) = DirectSum.decompose 𝓡 (s : R) from rfl,
    DirectSum.decompose_coe, DirectSum.toSemiring_of, ψ_apply]

theorem φ_algebraMap (a : S) :
    φ hR τ V hτ (algebraMap S R a) = X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (baseScalar f a) := by
  have hmem : algebraMap S R a ∈ 𝓡 0 := SetLike.algebraMap_mem_graded 𝓡 a
  rw [show algebraMap S R a = ((⟨algebraMap S R a, hmem⟩ : 𝓡 0) : R) from rfl, φ_coe]
  symm; apply eq_ψfun
  have e : (⟨algebraMap S R a, hmem⟩ : 𝓡 0) = a • (⟨1, SetLike.GradedOne.one_mem⟩ : 𝓡 0) :=
    Subtype.ext (Algebra.algebraMap_eq_smul_one a)
  rw [e, hR.map_smul, Scheme.Modules.map_smul, τpow_zero]

end DehomSol
p2m_reactivate "P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_pow_mul_eq_zero_of_map_eq_zero.DehomSol"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_pow_mul_eq_zero_of_map_eq_zero.DehomSol"

noncomputable section

namespace InjSol

open AlgebraicGeometry.GradedOAlgebra AlgebraicGeometry.Scheme.Modules DehomSol TopologicalSpace

section General

variable {X : Scheme.{u}}

theorem res_res {M : X.Modules} {U V W : X.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (x : Γ(M, U)) :
    M.presheaf.map (homOfLE h₁).op (M.presheaf.map (homOfLE h₂).op x) =
      M.presheaf.map (homOfLE (h₁.trans h₂)).op x := by
  rw [← CategoryTheory.comp_apply, ← M.presheaf.map_comp]; rfl

theorem isUnit_of_isFrameOn_smul {M : X.Modules} {U V W : X.Opens} (s : Γ(M, U))
    (hs : IsFrameOn s V) (hWU : W ≤ U) (hWV : W ≤ V) (g : Γ(X, W))
    (hg : IsFrameOn (g • M.presheaf.map (homOfLE hWU).op s) W) : IsUnit g := by
  have hb := hg (le_refl W) (le_refl W)
  have hid : ∀ t : Γ(M, W), M.presheaf.map (homOfLE (le_refl W)).op t = t := fun t => by
    rw [show (homOfLE (le_refl W)).op = 𝟙 (Opposite.op W) from rfl, CategoryTheory.Functor.map_id]
    rfl
  obtain ⟨g', hg'⟩ := hb.2 (M.presheaf.map (homOfLE hWU).op s)
  dsimp only at hg'
  rw [hid, smul_smul] at hg'
  have h1 : (g' * g) • M.presheaf.map (homOfLE hWU).op s =
      (1 : Γ(X, W)) • M.presheaf.map (homOfLE hWU).op s := by
    rw [hg', one_smul]
  have h2 : g' * g = 1 := (hs hWU hWV).1 h1
  exact isUnit_iff_exists_inv'.2 ⟨g', h2⟩

theorem isFrameOn_of_unit_smul {M : X.Modules} {V W' : X.Opens} (e : Γ(M, ⊤)) (he : IsFrameOn e V)
    (hW'V : W' ≤ V) (u : Γ(X, W')) (hu : IsUnit u) (s : Γ(M, ⊤))
    (hs : M.presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op s =
      u • M.presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op e) :
    IsFrameOn s W' := by
  intro W hWtop hWW'
  have hu' : IsUnit (X.presheaf.map (homOfLE hWW').op u) := hu.map _
  have key : M.presheaf.map (homOfLE hWtop).op s =
      X.presheaf.map (homOfLE hWW').op u • M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op e := by
    rw [← res_res hWW' le_top s, hs, Scheme.Modules.map_smul, res_res]
  have hcomp : (fun g : Γ(X, W) => g • M.presheaf.map (homOfLE hWtop).op s) =
      (fun g : Γ(X, W) => g • M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op e) ∘
        fun g => g * (hu'.unit : Γ(X, W)) := by
    funext g
    simp only [Function.comp_apply, key, smul_smul, IsUnit.unit_spec]
  rw [hcomp]
  exact (he le_top (hWW'.trans hW'V)).comp (Units.mulRight hu'.unit).bijective

end General
p2m_reactivate "P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_pow_mul_eq_zero_of_map_eq_zero.DehomSol"

variable {S : Type u} [CommRing S] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of S)} {L : X.Modules}
    {R : Type u} [CommRing R] [Algebra S R] {𝓡 : ℕ → Submodule S R} [GradedAlgebra 𝓡]
    {ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)} (hR : IsSectionRing f L R 𝓡 ι)
    (τ : 𝓡 1) (V : X.Opens) (hτ : IsFrameOn (ι 1 τ) V) {θ : X ⟶ Proj 𝓡} (hθ : IsCanonicalToProj f L R 𝓡 ι θ)

theorem exists_mem_basicOpen (p : Proj 𝓡) :
    ∃ (m : ℕ) (hm : 0 < m) (τ : 𝓡 m), p ∈ Proj.basicOpen 𝓡 (τ : R) := by
  have hp := (Proj.affineOpenCover 𝓡).covers p
  change p ∈ (Proj.awayι 𝓡 _ _ _).opensRange at hp
  rw [Proj.opensRange_awayι] at hp
  exact ⟨_, ((Proj.affineOpenCover 𝓡).idx p).1.2, _, hp⟩

include hθ in

theorem basicOpen_φ_le {n : ℕ} (hn : 0 < n) (σ : 𝓡 n) :
    X.basicOpen (φ hR τ V hτ (σ : R)) ≤ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) := by
  intro x hxB
  obtain ⟨d, hd, τ', hτ'⟩ := exists_mem_basicOpen (𝓡 := 𝓡) (θ.base x)
  have hx₁ : x ∈ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ' : R) := hτ'
  have hσd : (σ : R) ^ d ∈ 𝓡 (n • d) := by
    rw [smul_eq_mul, Nat.mul_comm]; exact SetLike.pow_mem_graded d σ.2

  set g : Γ(X, θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ' : R)) :=
    θ.appLE (Proj.basicOpen 𝓡 (τ' : R)) (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ' : R)) le_rfl
      (Proj.awayToSection 𝓡 (τ' : R) (Away.mk 𝓡 τ'.2 n ((σ : R) ^ d) hσd)) with hg
  have key : g • (L.tensorPow (n • d)).presheaf.map
        (homOfLE (le_top : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ' : R) ≤ ⊤)).op
        (ι (n • d) ⟨(τ' : R) ^ n, SetLike.pow_mem_graded n τ'.2⟩) =
      (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ' : R) ≤ ⊤)).op
        (ι (n • d) ⟨(σ : R) ^ d, hσd⟩) := by
    rw [hg]; exact hθ.appLE_awayToSection_smul d hd τ' n ⟨(σ : R) ^ d, hσd⟩
  have hnd : 0 < n • d := by rw [smul_eq_mul]; exact Nat.mul_pos hn hd
  have hfr₁ : IsFrameOn (ι (n • d) ⟨(τ' : R) ^ n, SetLike.pow_mem_graded n τ'.2⟩)
      (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ' : R)) := by
    have := hθ.isFrameOn (n • d) hnd ⟨(τ' : R) ^ n, SetLike.pow_mem_graded n τ'.2⟩
    rwa [Proj.basicOpen_pow 𝓡 _ n hn] at this

  have hBV : X.basicOpen (φ hR τ V hτ (σ : R)) ≤ V := X.basicOpen_le _
  have hfr₂ : IsFrameOn (ι (n • d) ⟨(σ : R) ^ d, hσd⟩) (X.basicOpen (φ hR τ V hτ (σ : R))) := by
    refine isFrameOn_of_unit_smul (ι (n • d) (τpow τ (n • d))) (isFrameOn_pow hR τ V hτ (n • d)) hBV
      ((X.presheaf.map (homOfLE hBV).op (φ hR τ V hτ (σ : R))) ^ d)
      ((RingedSpace.isUnit_res_basicOpen _ (φ hR τ V hτ (σ : R))).pow d) (ι (n • d) ⟨(σ : R) ^ d, hσd⟩) ?_
    have e1 : (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (ι (n • d) ⟨(σ : R) ^ d, hσd⟩) =
        (φ hR τ V hτ (σ : R)) ^ d •
          (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (ι (n • d) (τpow τ (n • d))) := by
      rw [← ψfun_smul hR τ V hτ (n • d) ⟨_, hσd⟩, ← φ_coe, ← map_pow]
    rw [← res_res hBV le_top (ι (n • d) ⟨(σ : R) ^ d, hσd⟩), e1, Scheme.Modules.map_smul, res_res, map_pow]

  set W : X.Opens := X.basicOpen (φ hR τ V hτ (σ : R)) ⊓ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ' : R) with hW
  have hxW : x ∈ W := Opens.mem_inf.mpr ⟨hxB, hx₁⟩
  set gW : Γ(X, W) := X.presheaf.map (homOfLE (inf_le_right : W ≤ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ' : R))).op g
    with hgW
  have keyW : gW • (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
        (ι (n • d) ⟨(τ' : R) ^ n, SetLike.pow_mem_graded n τ'.2⟩) =
      (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (ι (n • d) ⟨(σ : R) ^ d, hσd⟩) := by
    have := congrArg ((L.tensorPow (n • d)).presheaf.map
      (homOfLE (inf_le_right : W ≤ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ' : R))).op) key
    rwa [Scheme.Modules.map_smul, res_res, res_res] at this
  have hgfr : IsFrameOn (gW • (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
      (ι (n • d) ⟨(τ' : R) ^ n, SetLike.pow_mem_graded n τ'.2⟩)) W := by
    rw [keyW]
    exact (hfr₂.map (homOfLE (le_top : W ≤ ⊤))).mono inf_le_left
  have hunit : IsUnit gW :=
    isUnit_of_isFrameOn_smul _ hfr₁ le_top inf_le_right gW hgfr

  have hxg : x ∈ X.basicOpen g := by
    have h := X.basicOpen_of_isUnit hunit
    rw [hgW, Scheme.basicOpen_res] at h
    have : x ∈ W ⊓ X.basicOpen g := by rw [h]; exact hxW
    exact (Opens.mem_inf.mp this).2
  have h52 := AlgebraicGeometry.Proj.basicOpen_mul_eq_basicOpen_awayToSection 𝓡 τ'.2 hd σ.2 hn
  change Proj.basicOpen 𝓡 ((τ' : R) * σ) =
    (Proj 𝓡).basicOpen (Proj.awayToSection 𝓡 (τ' : R) (Away.mk 𝓡 τ'.2 n ((σ : R) ^ d) hσd)) at h52
  rw [hg, Scheme.basicOpen_appLE, ← h52, Proj.basicOpen_mul] at hxg
  exact (Opens.mem_inf.mp (Opens.mem_inf.mp hxg).2).2

include hθ in

theorem exists_pow_mul_φ_eq_zero (hVc : IsCompact (V : Set X)) {n : ℕ} (hn : 0 < n) (σ : 𝓡 n)
    {m : ℕ} (t : 𝓡 m)
    (ht : (L.tensorPow m).presheaf.map (homOfLE (le_top : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) ≤ ⊤)).op (ι m t) = 0) :
    ∃ k : ℕ, (φ hR τ V hτ (σ : R)) ^ k * φ hR τ V hτ (t : R) = 0 := by
  apply exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hVc
  have hBV : X.basicOpen (φ hR τ V hτ (σ : R)) ≤ V := X.basicOpen_le _
  have hBσ : X.basicOpen (φ hR τ V hτ (σ : R)) ≤ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) :=
    basicOpen_φ_le hR τ V hτ hθ hn σ
  have h0 : (L.tensorPow m).presheaf.map (homOfLE (le_top : X.basicOpen (φ hR τ V hτ (σ : R)) ≤ ⊤)).op
      (ι m t) = 0 := by
    rw [← res_res hBσ le_top (ι m t), ht, map_zero]
  have h1 : X.presheaf.map (homOfLE hBV).op (φ hR τ V hτ (t : R)) •
      (L.tensorPow m).presheaf.map (homOfLE (le_top : X.basicOpen (φ hR τ V hτ (σ : R)) ≤ ⊤)).op
        (ι m (τpow τ m)) = 0 := by
    rw [← res_res hBV le_top (ι m (τpow τ m)), ← Scheme.Modules.map_smul, φ_coe hR τ V hτ m t, ψfun_smul,
      res_res, h0]
  exact ((isFrameOn_pow hR τ V hτ m).smul_eq_zero_iff le_top hBV _).1 h1

include hR hθ in

theorem main_of_charts {N : ℕ} (W : Fin (N + 1) → X.Opens) (hcov : (⨆ i, W i) = ⊤)
    (hWc : ∀ i, IsCompact (W i : Set X)) (τs : Fin (N + 1) → 𝓡 1) (hfr : ∀ i, IsFrameOn (ι 1 (τs i)) (W i))
    {n : ℕ} (hn : 0 < n) (σ : 𝓡 n) {m : ℕ} (t : 𝓡 m)
    (ht : (L.tensorPow m).presheaf.map (homOfLE (le_top : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) ≤ ⊤)).op (ι m t) = 0) :
    ∃ k : ℕ, (σ : R) ^ k * (t : R) = 0 := by
  have hk : ∀ i, ∃ k : ℕ,
      (φ hR (τs i) (W i) (hfr i) (σ : R)) ^ k * φ hR (τs i) (W i) (hfr i) (t : R) = 0 :=
    fun i => exists_pow_mul_φ_eq_zero hR (τs i) (W i) (hfr i) hθ (hWc i) hn σ t ht
  choose k hk using hk
  refine ⟨∑ i, k i, ?_⟩
  have hu : (σ : R) ^ (∑ i, k i) * (t : R) ∈ 𝓡 ((∑ i, k i) • n + m) :=
    SetLike.GradedMul.mul_mem (SetLike.pow_mem_graded _ σ.2) t.2
  have hφ : ∀ i, φ hR (τs i) (W i) (hfr i) ((σ : R) ^ (∑ i, k i) * (t : R)) = 0 := fun i => by
    have hle : k i ≤ ∑ i, k i := Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i)
    rw [map_mul, map_pow, ← Nat.sub_add_cancel hle, pow_add, mul_assoc, hk i, mul_zero]
  have hres : ∀ i, (L.tensorPow ((∑ i, k i) • n + m)).presheaf.map (homOfLE (le_top : W i ≤ ⊤)).op
      (ι ((∑ i, k i) • n + m) ⟨_, hu⟩) = 0 := fun i => by
    rw [← ψfun_smul hR (τs i) (W i) (hfr i) ((∑ i, k i) • n + m) ⟨_, hu⟩, ← φ_coe]
    have : φ hR (τs i) (W i) (hfr i) (((⟨_, hu⟩ : 𝓡 ((∑ i, k i) • n + m)) : R)) = 0 := hφ i
    rw [this, zero_smul]
  have hzero : ι ((∑ i, k i) • n + m) ⟨_, hu⟩ = 0 := by
    refine TopCat.Sheaf.eq_of_locally_eq'
      (⟨(L.tensorPow ((∑ i, k i) • n + m)).presheaf, (L.tensorPow ((∑ i, k i) • n + m)).isSheaf⟩ : TopCat.Sheaf _ _)
      W ⊤ (fun i => homOfLE le_top) hcov.ge _ _ fun i => ?_
    rw [map_zero]
    exact hres i
  have hι0 : ι ((∑ i, k i) • n + m) 0 = 0 := by
    have h := hR.map_add ((∑ i, k i) • n + m) 0 0
    rw [add_zero] at h
    exact left_eq_add.mp h
  have hinj := (hR.bijective ((∑ i, k i) • n + m)).1 (hzero.trans hι0.symm)
  exact congrArg Subtype.val hinj

end InjSol
p2m_reactivate "P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_pow_mul_eq_zero_of_map_eq_zero.DehomSol"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_pow_mul_eq_zero_of_map_eq_zero.DehomSol"

open InjSol in
theorem solution
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (hL : Scheme.Modules.IsInvertible L) (hva : Scheme.Modules.ClosedImmersionBySections L f)
    (θ : X ⟶ Proj 𝓡) (hθ : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ)
    (n : ℕ) (hn : 0 < n) (σ : 𝓡 n) (m : ℕ) (t : 𝓡 m)
    (ht : (L.tensorPow m).presheaf.map (homOfLE (le_top : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) ≤ ⊤)).op (ι m t) = 0) :
    ∃ k : ℕ, (σ : R) ^ k * (t : R) = 0 := by
  obtain ⟨N, 𝔓, hci⟩ := hva
  have hcov : (⨆ i : Fin (N + 1), 𝔓.toProj ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S) (MvPolynomial.X i)) = ⊤ :=
    𝔓.toProj.iSup_preimage_eq_top
      (Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S)
        (fun j => MvPolynomial.X j) (ProjSpace.irrelevant_le_span_X S N))
  have hWc : ∀ i : Fin (N + 1), IsCompact ((𝔓.toProj ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S) (MvPolynomial.X i) : X.Opens) : Set X) :=
    fun i => ((Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S)
      (MvPolynomial.X i) (ProjSpace.X_mem_one S N i) one_pos).preimage 𝔓.toProj).isCompact
  have hsurj : ∀ i : Fin (N + 1), ∃ τ : 𝓡 1, ι 1 τ = (tensorPowOneIso L).symm.hom.app ⊤ (𝔓.σ i) :=
    fun i => (hR.bijective 1).2 _
  choose τs hτs using hsurj
  have hfr : ∀ i, IsFrameOn (ι 1 (τs i)) (𝔓.toProj ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S) (MvPolynomial.X i)) := fun i => by
    rw [hτs i]
    have hfr0 : IsFrameOn (𝔓.σ i) (𝔓.toProj ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S) (MvPolynomial.X i)) :=
      fun W hWU hWV => 𝔓.frame i W hWV
    exact hfr0.map_iso (tensorPowOneIso L).symm
  exact main_of_charts hR hθ _ hcov hWc τs hfr hn σ t ht

end S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_pow_mul_eq_zero_of_map_eq_zero
end P2MW
export P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_pow_mul_eq_zero_of_map_eq_zero (solution)
