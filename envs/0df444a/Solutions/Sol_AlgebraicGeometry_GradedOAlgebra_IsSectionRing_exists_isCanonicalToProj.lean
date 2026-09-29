-- Prove2me | solution 1 for AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_isCanonicalToProj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/f64b10ba-bbc1-594b-9b06-e4ab0a8af449

import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_exists_iSup_eq_top_isFrameOn_of_isSectionRing
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_ringHom_smul_map_pow_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_isUnit_of_isFrameOn_smul
import Theorems.Thm_AlgebraicGeometry_Proj_fromOfGlobalSections_appLE_awayToSection_mk_mul_pow
import Theorems.Thm_AlgebraicGeometry_Proj_hom_ext_of_forall_exists_basicOpen
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_of_iSup_monoidalV2
import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_isCanonicalToProj

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization"

namespace K10F2

open AlgebraicGeometry.GradedOAlgebra Opposite

variable {X : Scheme.{u}}

theorem op_hom_eq {U V : X.Opens} (i j : op U ⟶ op V) : i = j :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem Xmap_congr {U V : X.Opens} (i j : op U ⟶ op V) (x : Γ(X, U)) :
    X.presheaf.map i x = X.presheaf.map j x := by rw [op_hom_eq i j]

theorem Xmap_comp {U V W : X.Opens} (i : op U ⟶ op V) (j : op V ⟶ op W) (k : op U ⟶ op W) (x : Γ(X, U)) :
    X.presheaf.map j (X.presheaf.map i x) = X.presheaf.map k x := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp, op_hom_eq (i ≫ j) k]

theorem Mmap_congr (M : X.Modules) {U V : X.Opens} (i j : op U ⟶ op V) (x : Γ(M, U)) :
    M.presheaf.map i x = M.presheaf.map j x := by rw [op_hom_eq i j]

theorem Mmap_comp (M : X.Modules) {U V W : X.Opens} (i : op U ⟶ op V) (j : op V ⟶ op W) (k : op U ⟶ op W)
    (x : Γ(M, U)) : M.presheaf.map j (M.presheaf.map i x) = M.presheaf.map k x := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp, op_hom_eq (i ≫ j) k]

theorem res_chain (U : X.Opens) {D W : (U : Scheme.{u}).Opens} (j : op (⊤ : (U : Scheme.{u}).Opens) ⟶ op D)
    (h : op D ⟶ op W) {W₀ : X.Opens} (i₁ : op (U.ι ''ᵁ W) ⟶ op W₀) (i₂ : op U ⟶ op W₀) (x : Γ(X, U)) :
    X.presheaf.map i₁ ((U : Scheme.{u}).presheaf.map h ((U : Scheme.{u}).presheaf.map j (U.topIso.inv x))) =
      X.presheaf.map i₂ x := by
  change (X.presheaf.map (eqToHom U.ι_image_top).op ≫ X.presheaf.map ((Scheme.Hom.opensFunctor U.ι).map j.unop).op ≫
    X.presheaf.map ((Scheme.Hom.opensFunctor U.ι).map h.unop).op ≫ X.presheaf.map i₁) x = X.presheaf.map i₂ x
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  exact Xmap_congr _ _ x

theorem homOfLE_appTop_topIso_inv {U V : X.Opens} (e : U ≤ V) (i₂ : op V ⟶ op (U.ι ''ᵁ ⊤)) (x : Γ(X, V)) :
    (X.homOfLE e).appTop (V.topIso.inv x) = X.presheaf.map i₂ x := by
  rw [Scheme.homOfLE_appTop]
  change (X.presheaf.map (eqToHom V.ι_image_top).op ≫
    X.presheaf.map (homOfLE (X.ι_image_homOfLE_le_ι_image e ⊤)).op) x = X.presheaf.map i₂ x
  rw [← Functor.map_comp]
  exact Xmap_congr _ _ x

section Local

variable {S : Type u} [CommRing S] (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]

noncomputable def gOf (U : X.Opens) (φ : R →+* Γ(X, U)) : R →+* Γ(U, ⊤) :=
  (U.topIso.inv).hom.comp φ

theorem gOf_apply (U : X.Opens) (φ : R →+* Γ(X, U)) (r : R) : gOf R U φ r = U.topIso.inv (φ r) := rfl

theorem res_chain_gOf (U : X.Opens) (φ : R →+* Γ(X, U)) {D W : (U : Scheme.{u}).Opens}
    (j : op (⊤ : (U : Scheme.{u}).Opens) ⟶ op D) (h : op D ⟶ op W) {W₀ : X.Opens}
    (i₁ : op (U.ι ''ᵁ W) ⟶ op W₀) (i₂ : op U ⟶ op W₀) (x : R) :
    X.presheaf.map i₁ ((U : Scheme.{u}).presheaf.map h ((U : Scheme.{u}).presheaf.map j (gOf R U φ x))) =
      X.presheaf.map i₂ (φ x) := by
  rw [gOf_apply]
  exact res_chain U j h i₁ i₂ (φ x)

theorem map_irrelevant_eq_top (U : X.Opens) (φ : R →+* Γ(X, U)) (τ : 𝓡 1) (hτ : φ τ = 1) :
    (HomogeneousIdeal.irrelevant 𝓡).toIdeal.map (gOf R U φ) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have hmem : (τ : R) ∈ (HomogeneousIdeal.irrelevant 𝓡).toIdeal := by
    change (τ : R) ∈ HomogeneousIdeal.irrelevant 𝓡
    rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
      DirectSum.decompose_of_mem_ne 𝓡 τ.2 one_ne_zero]
  have := Ideal.mem_map_of_mem (gOf R U φ) hmem
  rwa [gOf_apply, hτ, map_one] at this

noncomputable def θOf (U : X.Opens) (φ : R →+* Γ(X, U)) (τ : 𝓡 1) (hτ : φ τ = 1) : (U : Scheme.{u}) ⟶ Proj 𝓡 :=
  Proj.fromOfGlobalSections 𝓡 (gOf R U φ) (map_irrelevant_eq_top R 𝓡 U φ τ hτ)

variable {R 𝓡}

theorem θOf_preimage (U : X.Opens) (φ : R →+* Γ(X, U)) (τ : 𝓡 1) (hτ : φ τ = 1)
    (a : (U : Scheme.{u}) ⟶ Proj 𝓡) (ha : a = θOf R 𝓡 U φ τ hτ) {n : ℕ} (hn : 0 < n) (σ : 𝓡 n) :
    a ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) = (U : Scheme.{u}).basicOpen (gOf R U φ σ) := by
  subst ha
  exact Proj.fromOfGlobalSections_preimage_basicOpen 𝓡 _ _ hn σ.2

theorem image_θOf_preimage (U : X.Opens) (φ : R →+* Γ(X, U)) (τ : 𝓡 1) (hτ : φ τ = 1)
    (a : (U : Scheme.{u}) ⟶ Proj 𝓡) (ha : a = θOf R 𝓡 U φ τ hτ) {n : ℕ} (hn : 0 < n) (σ : 𝓡 n) :
    U.ι ''ᵁ (a ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R)) = X.basicOpen (φ σ) := by
  rw [θOf_preimage U φ τ hτ a ha hn σ, gOf_apply]
  exact U.ι_image_basicOpen_topIso_inv (φ σ)

theorem θOf_value (U : X.Opens) (φ : R →+* Γ(X, U)) (τ : 𝓡 1) (hτ : φ τ = 1)
    (a : (U : Scheme.{u}) ⟶ Proj 𝓡) (ha : a = θOf R 𝓡 U φ τ hτ) {n : ℕ} (hn : 0 < n) (σ : 𝓡 n)
    (k : ℕ) (s : R) (hs : s ∈ 𝓡 (k • n)) (W : (U : Scheme.{u}).Opens) (hW : W ≤ a ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R))
    {W₀ : X.Opens} (i₁ : op (U.ι ''ᵁ W) ⟶ op W₀) (i₂ : op U ⟶ op W₀) :
    X.presheaf.map i₁ (a.appLE (Proj.basicOpen 𝓡 (σ : R)) W hW
        (Proj.awayToSection 𝓡 (σ : R) (Away.mk 𝓡 σ.2 k s hs))) *
      X.presheaf.map i₂ (φ σ) ^ k = X.presheaf.map i₂ (φ s) := by
  subst ha
  have hW' : W ≤ (U : Scheme.{u}).basicOpen (gOf R U φ σ) := by
    rwa [θOf_preimage U φ τ hτ _ rfl hn σ] at hW
  have E := AlgebraicGeometry.Proj.fromOfGlobalSections_appLE_awayToSection_mk_mul_pow 𝓡 (gOf R U φ)
    (map_irrelevant_eq_top R 𝓡 U φ τ hτ) hn σ.2 k s hs
  have hA : (θOf R 𝓡 U φ τ hτ).appLE (Proj.basicOpen 𝓡 (σ : R)) W hW
        (Proj.awayToSection 𝓡 (σ : R) (Away.mk 𝓡 σ.2 k s hs)) =
      (U : Scheme.{u}).presheaf.map (homOfLE hW').op
        ((θOf R 𝓡 U φ τ hτ).appLE (Proj.basicOpen 𝓡 (σ : R)) ((U : Scheme.{u}).basicOpen (gOf R U φ σ))
          (Proj.fromOfGlobalSections_preimage_basicOpen 𝓡 _ _ hn σ.2).ge
          (Proj.awayToSection 𝓡 (σ : R) (Away.mk 𝓡 σ.2 k s hs))) :=
    (ConcreteCategory.congr_hom ((θOf R 𝓡 U φ τ hτ).appLE_map
      (Proj.fromOfGlobalSections_preimage_basicOpen 𝓡 _ _ hn σ.2).ge (homOfLE hW').op)
      (Proj.awayToSection 𝓡 (σ : R) (Away.mk 𝓡 σ.2 k s hs))).symm
  rw [hA]
  have E' := congrArg ((U : Scheme.{u}).presheaf.map (homOfLE hW').op) E
  simp only [map_mul, map_pow] at E'
  have key : ∀ (ρ : Γ((U : Scheme.{u}), W) →+* Γ(X, W₀)) (a b c : Γ((U : Scheme.{u}), W)),
      a * b ^ k = c → ρ a * ρ b ^ k = ρ c := by
    intro ρ a b c h
    simpa only [map_mul, map_pow] using congrArg ρ h
  have E'' := key (ConcreteCategory.hom (X.presheaf.map i₁)) _ _ _ E'
  rw [← res_chain_gOf R U φ (homOfLE ((U : Scheme.{u}).basicOpen_le (gOf R U φ σ))).op (homOfLE hW').op i₁ i₂ σ,
    ← res_chain_gOf R U φ (homOfLE ((U : Scheme.{u}).basicOpen_le (gOf R U φ σ))).op (homOfLE hW').op i₁ i₂ s]
  unfold θOf
  exact E''

end Local

section Frames

variable {M : X.Modules}

theorem isFrameOn_smul_of_isUnit {U V W : X.Opens} (s : Γ(M, U)) (hs : IsFrameOn s V)
    (hWU : W ≤ U) (hWV : W ≤ V) (g : Γ(X, W)) (hg : IsUnit g) :
    IsFrameOn (g • M.presheaf.map (homOfLE hWU).op s) W := by
  intro W' hW'W _
  have e : (fun t : Γ(X, W') => t • M.presheaf.map (homOfLE hW'W).op (g • M.presheaf.map (homOfLE hWU).op s)) =
      (fun t : Γ(X, W') => t • M.presheaf.map (homOfLE (hW'W.trans hWU)).op s) ∘
        (fun t : Γ(X, W') => t * X.presheaf.map (homOfLE hW'W).op g) := by
    funext t
    simp only [Function.comp_apply, Scheme.Modules.map_smul, smul_smul]
    rw [Mmap_comp M _ _ (homOfLE (hW'W.trans hWU)).op]
  rw [e]
  refine (hs (hW'W.trans hWU) (hW'W.trans hWV)).comp ?_
  have hu : IsUnit (X.presheaf.map (homOfLE hW'W).op g) := hg.map _
  exact ⟨fun a b h => hu.mul_left_injective h, fun y => ⟨y * hu.unit⁻¹, by simp [mul_assoc]⟩⟩

theorem isFrameOn_of_restrict {U B : X.Opens} (t : Γ(M, U)) (hBU : B ≤ U)
    (h : IsFrameOn (M.presheaf.map (homOfLE hBU).op t) B) : IsFrameOn t B := by
  intro W' hW'U hW'B
  have e : (fun g : Γ(X, W') => g • M.presheaf.map (homOfLE hW'U).op t) =
      (fun g : Γ(X, W') => g • M.presheaf.map (homOfLE hW'B).op (M.presheaf.map (homOfLE hBU).op t)) := by
    funext g
    rw [Mmap_comp M _ _ (homOfLE hW'U).op]
  rw [e]
  exact h hW'B hW'B

theorem sections_ext {W : X.Opens} {J : Type*} (V : J → X.Opens) (hV : (⨆ i, V i) = ⊤)
    (x y : Γ(M, W))
    (h : ∀ i, M.presheaf.map (homOfLE (inf_le_right : V i ⊓ W ≤ W)).op x =
      M.presheaf.map (homOfLE (inf_le_right : V i ⊓ W ≤ W)).op y) : x = y := by
  let FM : TopCat.Sheaf Ab X.carrier := ⟨M.presheaf, M.isSheaf⟩
  have hcov : W ≤ ⨆ i, (V i ⊓ W) := by
    rw [← iSup_inf_eq, hV, top_inf_eq]
  exact FM.eq_of_locally_eq' (fun i => V i ⊓ W) W (fun i => homOfLE inf_le_right) hcov x y h

end Frames

section Transport

variable {S : Type u} [CommRing S] (L : X.Modules) {R : Type u} [CommRing R] [Algebra S R]
  (𝓡 : ℕ → Submodule S R) (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤))

theorem isFrameOn_transport {a b : ℕ} (h : a = b) (x : 𝓡 a) (W : X.Opens) :
    IsFrameOn (ι a x) W ↔ IsFrameOn (ι b ⟨(x : R), h ▸ x.2⟩) W := by
  subst h; exact Iff.rfl

theorem smul_eq_transport {a b : ℕ} (h : a = b) (x y : 𝓡 a) {W : X.Opens} (hW : W ≤ ⊤) (g : Γ(X, W)) :
    (g • (L.tensorPow a).presheaf.map (homOfLE hW).op (ι a x) =
        (L.tensorPow a).presheaf.map (homOfLE hW).op (ι a y)) ↔
      (g • (L.tensorPow b).presheaf.map (homOfLE hW).op (ι b ⟨(x : R), h ▸ x.2⟩) =
        (L.tensorPow b).presheaf.map (homOfLE hW).op (ι b ⟨(y : R), h ▸ y.2⟩)) := by
  subst h; exact Iff.rfl

end Transport

end K10F2

open K10F2 Opposite in
theorem solution
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (hL : Scheme.Modules.IsInvertible L) (hva : Scheme.Modules.ClosedImmersionBySections L f) :
    ∃ θ : X ⟶ Proj 𝓡, AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ := by
  classical

  obtain ⟨N, τ, V, hV, hτV⟩ :=
    AlgebraicGeometry.Scheme.Modules.ClosedImmersionBySections.exists_iSup_eq_top_isFrameOn_of_isSectionRing
      f L R 𝓡 ι hR hva
  have dh := fun i =>
    AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_ringHom_smul_map_pow_eq f L R 𝓡 ι hR (τ i) (V i) (hτV i)
  choose φ hφa hφb hφc using dh

  have hφτ : ∀ i, φ i (τ i) = 1 := by
    intro i
    have h1 := hφc i 1 ⟨(τ i : R) ^ 1, SetLike.pow_mem_graded 1 (τ i).2⟩
    have hinj := ((hφb i 1) (le_top : V i ≤ ⊤) le_rfl).1
    have h2 : φ i ((τ i : R) ^ 1) = 1 := hinj (h1.trans (one_smul _ _).symm)
    simpa using h2

  have hunit : ∀ i j, IsUnit (X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (φ j (τ i))) := by
    intro i j
    have hc := hφc j 1 ⟨(τ i : R) ^ 1, SetLike.pow_mem_graded 1 (τ i).2⟩
    have hc' := congrArg ((L.tensorPow (1 • 1)).presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op) hc
    simp only [Scheme.Modules.map_smul] at hc'
    rw [Mmap_comp _ _ _ (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op,
      Mmap_comp _ _ _ (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op] at hc'
    have hfr : IsFrameOn ((L.tensorPow (1 • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op
        (ι (1 • 1) ⟨(τ i : R) ^ 1, SetLike.pow_mem_graded 1 (τ i).2⟩)) (V i ⊓ V j) :=
      ((hφb i 1).mono inf_le_left).map (homOfLE (le_top : V i ⊓ V j ≤ ⊤))
    rw [← hc'] at hfr
    have key := AlgebraicGeometry.Scheme.Modules.IsFrameOn.isUnit_of_isFrameOn_smul
      (ι (1 • 1) ⟨(τ j : R) ^ 1, SetLike.pow_mem_graded 1 (τ j).2⟩) (hφb j 1)
      (le_top : V i ⊓ V j ≤ ⊤) inf_le_right _ hfr
    simpa using key

  have hkey : ∀ i j (k : ℕ) (s : R) (hs : s ∈ 𝓡 (k • 1)),
      X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (φ i s) *
        X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (φ j (τ i)) ^ k =
      X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (φ j s) := by
    intro i j k s hs
    apply ((hφb j k) (le_top : V i ⊓ V j ≤ ⊤) inf_le_right).1
    simp only

    have cj : ∀ t : 𝓡 (k • 1), X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (φ j t) •
        (L.tensorPow (k • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op
          (ι (k • 1) ⟨(τ j : R) ^ k, SetLike.pow_mem_graded k (τ j).2⟩) =
        (L.tensorPow (k • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op (ι (k • 1) t) := by
      intro t
      have := congrArg ((L.tensorPow (k • 1)).presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op) (hφc j k t)
      simp only [Scheme.Modules.map_smul] at this
      rw [Mmap_comp _ _ _ (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op,
        Mmap_comp _ _ _ (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op] at this
      exact this
    have ci : ∀ t : 𝓡 (k • 1), X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (φ i t) •
        (L.tensorPow (k • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op
          (ι (k • 1) ⟨(τ i : R) ^ k, SetLike.pow_mem_graded k (τ i).2⟩) =
        (L.tensorPow (k • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op (ι (k • 1) t) := by
      intro t
      have := congrArg ((L.tensorPow (k • 1)).presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op) (hφc i k t)
      simp only [Scheme.Modules.map_smul] at this
      rw [Mmap_comp _ _ _ (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op,
        Mmap_comp _ _ _ (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op] at this
      exact this
    have cjs : X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (φ j s) •
        (L.tensorPow (k • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op
          (ι (k • 1) ⟨(τ j : R) ^ k, SetLike.pow_mem_graded k (τ j).2⟩) =
        (L.tensorPow (k • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op (ι (k • 1) ⟨s, hs⟩) := cj ⟨s, hs⟩
    have cjτ : X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (φ j ((τ i : R) ^ k)) •
        (L.tensorPow (k • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op
          (ι (k • 1) ⟨(τ j : R) ^ k, SetLike.pow_mem_graded k (τ j).2⟩) =
        (L.tensorPow (k • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op
          (ι (k • 1) ⟨(τ i : R) ^ k, SetLike.pow_mem_graded k (τ i).2⟩) :=
      cj ⟨(τ i : R) ^ k, SetLike.pow_mem_graded k (τ i).2⟩
    have cis : X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (φ i s) •
        (L.tensorPow (k • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op
          (ι (k • 1) ⟨(τ i : R) ^ k, SetLike.pow_mem_graded k (τ i).2⟩) =
        (L.tensorPow (k • 1)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op (ι (k • 1) ⟨s, hs⟩) := ci ⟨s, hs⟩
    rw [cjs, mul_smul, ← map_pow, ← map_pow, cjτ, cis]

  let θV : ∀ i, ((V i : X.Opens) : Scheme.{u}) ⟶ Proj 𝓡 := fun i => θOf R 𝓡 (V i) (φ i) (τ i) (hφτ i)
  have hcompat : ∀ i j, X.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ θV i =
      X.homOfLE (inf_le_right : V i ⊓ V j ≤ V j) ≫ θV j := by
    intro i j
    apply AlgebraicGeometry.Proj.hom_ext_of_forall_exists_basicOpen 𝓡
    intro w
    have hpa : (X.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ θV i) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R) = ⊤ := by
      rw [Scheme.Hom.comp_preimage, θOf_preimage (V i) (φ i) (τ i) (hφτ i) _ rfl one_pos (τ i), gOf_apply, hφτ i,
        map_one, Scheme.basicOpen_one, Scheme.Hom.preimage_top]
    have hpb : (X.homOfLE (inf_le_right : V i ⊓ V j ≤ V j) ≫ θV j) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R) = ⊤ := by
      rw [Scheme.Hom.comp_preimage, θOf_preimage (V j) (φ j) (τ j) (hφτ j) _ rfl one_pos (τ i),
        Scheme.preimage_basicOpen_top]
      apply Scheme.basicOpen_of_isUnit
      rw [gOf_apply, homOfLE_appTop_topIso_inv _ ((homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op ≫
        (homOfLE ((V i ⊓ V j).ι_image_le ⊤)).op), Functor.map_comp, CategoryTheory.comp_apply]
      exact (hunit i j).map _
    refine ⟨1, (τ i : R), one_pos, (τ i).2, hpa.trans hpb.symm, by rw [hpa]; trivial, ?_⟩
    intro x
    obtain ⟨k, s, hs, rfl⟩ := Away.mk_surjective 𝓡 (τ i).2 x

    erw [← Scheme.Hom.appLE_comp_appLE (X.homOfLE (inf_le_left : V i ⊓ V j ≤ V i)) (θV i)
        (Proj.basicOpen 𝓡 (τ i : R)) ((θV i) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R))
        ((X.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ θV i) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)) le_rfl le_rfl]
    erw [← Scheme.Hom.appLE_comp_appLE (X.homOfLE (inf_le_right : V i ⊓ V j ≤ V j)) (θV j)
        (Proj.basicOpen 𝓡 (τ i : R)) ((θV j) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R))
        ((X.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ θV i) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)) le_rfl
        (hpa.trans hpb.symm).le]
    rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, Scheme.homOfLE_appLE, Scheme.homOfLE_appLE]
    have hΩle : (V i ⊓ V j).ι ''ᵁ ((X.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ θV i) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)) ≤
        V i ⊓ V j := (V i ⊓ V j).ι_image_le _
    have key2 : ∀ (m₁ : op ((V i).ι ''ᵁ ((θV i) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R))) ⟶
          op ((V i ⊓ V j).ι ''ᵁ ((X.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ θV i) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R))))
        (m₂ : op ((V j).ι ''ᵁ ((θV j) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R))) ⟶
          op ((V i ⊓ V j).ι ''ᵁ ((X.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ θV i) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)))),
        X.presheaf.map m₁ ((θV i).appLE (Proj.basicOpen 𝓡 (τ i : R)) ((θV i) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)) le_rfl
          (Proj.awayToSection 𝓡 (τ i : R) (Away.mk 𝓡 (τ i).2 k s hs))) =
        X.presheaf.map m₂ ((θV j).appLE (Proj.basicOpen 𝓡 (τ i : R)) ((θV j) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)) le_rfl
          (Proj.awayToSection 𝓡 (τ i : R) (Away.mk 𝓡 (τ i).2 k s hs))) := by
      intro m₁ m₂
      have vi := θOf_value (V i) (φ i) (τ i) (hφτ i) (θV i) rfl one_pos (τ i) k s hs
        ((θV i) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)) le_rfl m₁ (homOfLE (hΩle.trans inf_le_left)).op
      rw [hφτ i, map_one, one_pow, mul_one] at vi
      have vj := θOf_value (V j) (φ j) (τ j) (hφτ j) (θV j) rfl one_pos (τ i) k s hs
        ((θV j) ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)) le_rfl m₂ (homOfLE (hΩle.trans inf_le_right)).op
      have hk := congrArg (X.presheaf.map (homOfLE hΩle).op) (hkey i j k s hs)
      rw [map_mul, map_pow, Xmap_comp _ _ (homOfLE (hΩle.trans inf_le_left)).op,
        Xmap_comp _ _ (homOfLE (hΩle.trans inf_le_right)).op, Xmap_comp _ _ (homOfLE (hΩle.trans inf_le_right)).op,
        ← vi, ← vj] at hk
      have hu : IsUnit (X.presheaf.map (homOfLE (hΩle.trans inf_le_right)).op (φ j (τ i)) ^ k) := by
        have := ((hunit i j).map (ConcreteCategory.hom (X.presheaf.map (homOfLE hΩle).op))).pow k
        rwa [Xmap_comp _ _ (homOfLE (hΩle.trans inf_le_right)).op] at this
      exact hu.mul_left_inj.mp hk
    exact key2 _ _

  let 𝒰 : X.OpenCover := X.openCoverOfIsOpenCover V hV
  have hglue : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ θV i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ θV j := by
    intro i j
    have P := isPullback_opens_inf (V i) (V j)
    change pullback.fst (V i).ι (V j).ι ≫ θV i = pullback.snd (V i).ι (V j).ι ≫ θV j
    rw [← cancel_epi P.isoPullback.hom, P.isoPullback_hom_fst_assoc, P.isoPullback_hom_snd_assoc]
    exact hcompat i j
  let θ : X ⟶ Proj 𝓡 := 𝒰.glueMorphisms θV hglue
  have hθV : ∀ i, (V i).ι ≫ θ = θV i := fun i => 𝒰.ι_glueMorphisms θV hglue i

  have hVW : ∀ {n : ℕ} (hn : 0 < n) (σ : 𝓡 n) (i),
      V i ⊓ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) = X.basicOpen (φ i σ) := by
    intro n hn σ i
    rw [← image_θOf_preimage (V i) (φ i) (τ i) (hφτ i) ((V i).ι ≫ θ) (hθV i) hn σ, Scheme.Hom.comp_preimage,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  have hcovσ : ∀ {n : ℕ} (hn : 0 < n) (σ : 𝓡 n),
      θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) = ⨆ i, X.basicOpen (φ i σ) := by
    intro n hn σ
    calc θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) = (⨆ i, V i) ⊓ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) := by rw [hV, top_inf_eq]
      _ = ⨆ i, (V i ⊓ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R)) := iSup_inf_eq _ _
      _ = ⨆ i, X.basicOpen (φ i σ) := by simp_rw [hVW hn σ]
  refine ⟨θ, ⟨?_, ?_, ?_⟩⟩
  ·
    apply 𝒰.hom_ext
    intro i
    change (V i).ι ≫ θ ≫ Proj.toSpecZero 𝓡 ≫ _ = (V i).ι ≫ f
    rw [← Category.assoc, hθV i]
    change Proj.fromOfGlobalSections 𝓡 (gOf R (V i) (φ i)) _ ≫ Proj.toSpecZero 𝓡 ≫ _ = (V i).ι ≫ f
    rw [Proj.fromOfGlobalSections_toSpecZero_assoc, ← Spec.map_comp]
    have hr : (V i).ι ≫ f = ((V i : X.Opens) : Scheme.{u}).toSpecΓ ≫
        Spec.map ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ ((V i).ι ≫ f).appTop) := by
      rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, Category.assoc,
        toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    rw [hr]
    congr 2
    apply CommRingCat.hom_ext
    ext a
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
      Scheme.Hom.comp_appTop]
    have ha0 : algebraMap S R a ∈ 𝓡 0 := by
      rw [Algebra.algebraMap_eq_smul_one]; exact Submodule.smul_mem _ a SetLike.GradedOne.one_mem
    have e1 : (GradedRing.projZeroRingHom' 𝓡) (algebraMap S R a) = ⟨algebraMap S R a, ha0⟩ :=
      GradedRing.projZeroRingHom'_apply_coe 𝓡 ⟨algebraMap S R a, ha0⟩
    rw [e1]
    change gOf R (V i) (φ i) (algebraMap S R a) = (V i).ι.appTop (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of S)).inv a))
    rw [gOf_apply, hφa i a, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv]
    exact Xmap_comp _ _ _ _
  ·
    intro n hn σ
    rw [hcovσ hn σ]
    apply AlgebraicGeometry.Scheme.Modules.IsFrameOn.of_iSup_monoidalV2
    intro i
    have hn1 : n = n • 1 := by simp
    rw [isFrameOn_transport L 𝓡 ι hn1 σ]
    have hBV : X.basicOpen (φ i σ) ≤ V i := X.basicOpen_le _
    apply isFrameOn_of_restrict _ (hBV.trans le_top)
    have hc := hφc i n ⟨(σ : R), hn1 ▸ σ.2⟩
    have hc' := congrArg ((L.tensorPow (n • 1)).presheaf.map (homOfLE hBV).op) hc
    simp only [Scheme.Modules.map_smul] at hc'
    rw [Mmap_comp _ _ _ (homOfLE (hBV.trans le_top)).op, Mmap_comp _ _ _ (homOfLE (hBV.trans le_top)).op] at hc'
    rw [← hc']
    exact isFrameOn_smul_of_isUnit _ (hφb i n) le_top hBV _ (RingedSpace.isUnit_res_basicOpen _ (φ i σ))
  ·
    intro n hn σ k s
    have hkn : k • n = (k • n) • 1 := by simp
    apply sections_ext V hV
    intro i
    simp only [Scheme.Modules.map_smul]
    rw [Mmap_comp _ _ _ (homOfLE le_top).op, Mmap_comp _ _ _ (homOfLE le_top).op]

    have hWle : V i ⊓ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) ≤ V i := inf_le_left
    have cσ := hφc i (k • n) ⟨((⟨(σ : R) ^ k, SetLike.pow_mem_graded k σ.2⟩ : 𝓡 (k • n)) : R),
      hkn ▸ (⟨(σ : R) ^ k, SetLike.pow_mem_graded k σ.2⟩ : 𝓡 (k • n)).2⟩
    have cs := hφc i (k • n) ⟨(s : R), hkn ▸ s.2⟩
    rw [smul_eq_transport L 𝓡 ι hkn ⟨(σ : R) ^ k, SetLike.pow_mem_graded k σ.2⟩ s]
    have cσ' := congrArg ((L.tensorPow ((k • n) • 1)).presheaf.map (homOfLE hWle).op) cσ
    have cs' := congrArg ((L.tensorPow ((k • n) • 1)).presheaf.map (homOfLE hWle).op) cs
    simp only [Scheme.Modules.map_smul] at cσ' cs'
    rw [Mmap_comp _ _ _ (homOfLE le_top).op, Mmap_comp _ _ _ (homOfLE le_top).op] at cσ' cs'
    rw [← cσ', ← cs', smul_smul]
    congr 1

    have v := θOf_value (V i) (φ i) (τ i) (hφτ i) ((V i).ι ≫ θ) (hθV i) hn σ k (s : R) s.2
      (((V i).ι ≫ θ) ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R)) le_rfl
      (W₀ := V i ⊓ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R))
      (homOfLE (by rw [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
        Scheme.Opens.opensRange_ι])).op (homOfLE hWle).op
    rw [map_pow, map_pow, ← v]
    congr 1
    rw [← Scheme.Hom.appLE_comp_appLE ((V i).ι) θ (Proj.basicOpen 𝓡 (σ : R)) (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R))
        (((V i).ι ≫ θ) ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R)) le_rfl le_rfl, CategoryTheory.comp_apply, Scheme.Opens.ι_appLE]
    exact (Xmap_comp _ _ _ _).symm

end S_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_isCanonicalToProj
end P2MW
export P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_isCanonicalToProj (solution)
