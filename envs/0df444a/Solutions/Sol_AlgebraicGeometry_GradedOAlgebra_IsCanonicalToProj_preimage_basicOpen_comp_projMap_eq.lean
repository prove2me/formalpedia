-- Prove2me | solution 1 for AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.preimage_basicOpen_comp_projMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/b914a606-5b55-5af5-9efe-b53e51de31dd

import Mathlib
import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_comp_projMap
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_comp_of_commSq
import Theorems.Thm_AlgebraicGeometry_Proj_basicOpen_mul_eq_basicOpen_awayToSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_preimage_basicOpen_comp_projMap_eq

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_preimage_basicOpen_comp_projMap_eq.AlgebraicGeometry HomogeneousLocalization"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.basicOpen_res Proj.opensRange_awayι Scheme.Modules.pullback Proj.basicOpen_pow Spec Spec.map Scheme Proj.awayι Proj.affineOpenCover Proj Scheme.basicOpen_appLE Scheme.Modules.pullbackPushforwardAdjunction Proj.basicOpen Proj.basicOpen_mul Scheme.Modules Proj.awayToSection Proj.map Scheme.Modules.map_smul GradedOAlgebra.IsCanonicalToProj Scheme.Modules.tensorPowMapIso Scheme.Modules.pullbackTensorPowIso GradedOAlgebra.IsSectionRing Scheme.Modules.IsFrameOn Scheme.Modules.IsInvertible GradedOAlgebra.IsCanonicalToProj.comp_projMap GradedOAlgebra.IsCanonicalToProj.comp_of_commSq Proj.basicOpen_mul_eq_basicOpen_awayToSection"
namespace GradedOAlgebra
p2m_export "AlgebraicGeometry.GradedOAlgebra" "IsCanonicalToProj IsSectionRing IsCanonicalToProj.comp_projMap IsCanonicalToProj.comp_of_commSq"
namespace PreimageBasicOpen
p2m_open "AlgebraicGeometry.GradedOAlgebra AlgebraicGeometry"

open AlgebraicGeometry.Scheme.Modules

theorem isUnit_of_isFrameOn_smul {X : Scheme.{u}} {M : X.Modules} {U V W : X.Opens} (s : Γ(M, U))
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

section SameCharts

variable {S : Type u} [CommRing S] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of S)} {L : X.Modules}
  {R : Type u} [CommRing R] [Algebra S R] {𝓡 : ℕ → Submodule S R} [GradedAlgebra 𝓡]
  {ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)} {θ₁ θ₂ : X ⟶ Proj 𝓡}

theorem exists_mem_basicOpen (p : Proj 𝓡) :
    ∃ (m : ℕ) (hm : 0 < m) (τ : 𝓡 m), p ∈ Proj.basicOpen 𝓡 (τ : R) := by
  have hp := (Proj.affineOpenCover 𝓡).covers p
  change p ∈ (Proj.awayι 𝓡 _ _ _).opensRange at hp
  rw [Proj.opensRange_awayι] at hp
  exact ⟨_, ((Proj.affineOpenCover 𝓡).idx p).1.2, _, hp⟩

theorem preimage_basicOpen_le (h₁ : IsCanonicalToProj f L R 𝓡 ι θ₁) (h₂ : IsCanonicalToProj f L R 𝓡 ι θ₂)
    {n : ℕ} (hn : 0 < n) (σ : 𝓡 n) :
    θ₂ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) ≤ θ₁ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) := by
  intro x hx₂
  obtain ⟨m, hm, τ, hτ⟩ := exists_mem_basicOpen (𝓡 := 𝓡) (θ₁.base x)

  set M : X.Modules := L.tensorPow (n • m) with hM
  set U₁ : (Proj 𝓡).Opens := Proj.basicOpen 𝓡 (τ : R) with hU₁
  set V₁ : X.Opens := θ₁ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R) with hV₁
  set V₂ : X.Opens := θ₂ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) with hV₂
  have hx₁ : x ∈ V₁ := hτ
  have hσm : (σ : R) ^ m ∈ 𝓡 (n • m) := by
    rw [smul_eq_mul, Nat.mul_comm]; exact SetLike.pow_mem_graded m σ.2
  set s₁ : 𝓡 (n • m) := ⟨(σ : R) ^ m, hσm⟩ with hs₁
  set t₁ : 𝓡 (n • m) := ⟨(τ : R) ^ n, SetLike.pow_mem_graded n τ.2⟩ with ht₁

  set g : Γ(X, V₁) := θ₁.appLE U₁ V₁ le_rfl
      (Proj.awayToSection 𝓡 (τ : R) (Away.mk 𝓡 τ.2 n ((σ : R) ^ m) hσm)) with hg
  have key : g • M.presheaf.map (homOfLE (le_top : V₁ ≤ ⊤)).op (ι (n • m) t₁) =
      M.presheaf.map (homOfLE (le_top : V₁ ≤ ⊤)).op (ι (n • m) s₁) :=
    h₁.appLE_awayToSection_smul m hm τ n s₁

  have hnm : 0 < n • m := by rw [smul_eq_mul]; exact Nat.mul_pos hn hm
  have hfr₁ : IsFrameOn (ι (n • m) t₁) V₁ := by
    have := h₁.isFrameOn (n • m) hnm t₁
    rwa [Proj.basicOpen_pow 𝓡 _ n hn] at this
  have hfr₂ : IsFrameOn (ι (n • m) s₁) V₂ := by
    have := h₂.isFrameOn (n • m) hnm s₁
    rwa [Proj.basicOpen_pow 𝓡 _ m hm] at this

  set W : X.Opens := V₁ ⊓ V₂ with hW
  have hxW : x ∈ W := Opens.mem_inf.mpr ⟨hx₁, hx₂⟩
  set gW : Γ(X, W) := X.presheaf.map (homOfLE (inf_le_left : W ≤ V₁)).op g with hgW
  have res : ∀ u : Γ(M, ⊤), M.presheaf.map (homOfLE (inf_le_left : W ≤ V₁)).op
      (M.presheaf.map (homOfLE (le_top : V₁ ≤ ⊤)).op u) = M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op u := by
    intro u
    rw [← CategoryTheory.comp_apply, ← M.presheaf.map_comp]
    rfl
  have keyW : gW • M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (ι (n • m) t₁) =
      M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (ι (n • m) s₁) := by
    have := congrArg (M.presheaf.map (homOfLE (inf_le_left : W ≤ V₁)).op) key
    rwa [Scheme.Modules.map_smul, res, res] at this
  have hgfr : IsFrameOn (gW • M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (ι (n • m) t₁)) W := by
    rw [keyW]
    exact (hfr₂.map (homOfLE (le_top : W ≤ ⊤))).mono inf_le_right
  have hunit : IsUnit gW := isUnit_of_isFrameOn_smul (ι (n • m) t₁) hfr₁ le_top inf_le_left gW hgfr

  have hxg : x ∈ X.basicOpen g := by
    have h := X.basicOpen_of_isUnit hunit
    rw [hgW, Scheme.basicOpen_res] at h
    have : x ∈ W ⊓ X.basicOpen g := by rw [h]; exact hxW
    exact (Opens.mem_inf.mp this).2
  have h52 := AlgebraicGeometry.Proj.basicOpen_mul_eq_basicOpen_awayToSection 𝓡 τ.2 hm σ.2 hn
  change Proj.basicOpen 𝓡 ((τ : R) * σ) =
    (Proj 𝓡).basicOpen (Proj.awayToSection 𝓡 (τ : R) (Away.mk 𝓡 τ.2 n ((σ : R) ^ m) hσm)) at h52
  rw [hg, Scheme.basicOpen_appLE, ← h52, Proj.basicOpen_mul] at hxg
  exact (Opens.mem_inf.mp (Opens.mem_inf.mp hxg).2).2

theorem preimage_basicOpen_eq (h₁ : IsCanonicalToProj f L R 𝓡 ι θ₁) (h₂ : IsCanonicalToProj f L R 𝓡 ι θ₂)
    {n : ℕ} (hn : 0 < n) (σ : 𝓡 n) :
    θ₁ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) = θ₂ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) :=
  le_antisymm (preimage_basicOpen_le h₂ h₁ hn σ) (preimage_basicOpen_le h₁ h₂ hn σ)

end SameCharts

theorem isFrameOn_of_deg_eq_zero {S' : Type u} [CommRing S'] {X' : Scheme.{u}}
    {f' : X' ⟶ Spec (CommRingCat.of S')} {L' : X'.Modules}
    {R' : Type u} [CommRing R'] [Algebra S' R'] {𝓡' : ℕ → Submodule S' R'} [GradedAlgebra 𝓡']
    {ι' : ∀ n : ℕ, 𝓡' n → Γ(L'.tensorPow n, ⊤)} (hR' : IsSectionRing f' L' R' 𝓡' ι')
    {m : ℕ} (hm : m = 0) (x : 𝓡' m) (hx : (x : R') = 1) (V : X'.Opens) :
    IsFrameOn (ι' m x) V := by
  subst hm
  obtain rfl : x = ⟨1, SetLike.GradedOne.one_mem⟩ := Subtype.ext hx
  rw [hR'.map_one]
  exact isFrameOn_unitSection V

end AlgebraicGeometry.GradedOAlgebra.PreimageBasicOpen

end

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_preimage_basicOpen_comp_projMap_eq.AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization"

theorem solution
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (f' : X' ⟶ Spec (CommRingCat.of S')) (c : X' ⟶ X)
    (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (L' : X'.Modules) (e : (Scheme.Modules.pullback c).obj L ≅ L')
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (R' : Type u) [CommRing R'] [Algebra S' R'] [Algebra S R'] [IsScalarTower S S' R']
    (𝓡' : ℕ → Submodule S' R') [GradedAlgebra 𝓡']
    (ι' : ∀ n : ℕ, 𝓡' n → Γ(L'.tensorPow n, ⊤)) (hR' : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f' L' R' 𝓡' ι')
    (ϑ : R →ₐ[S] R') (hϑdeg : ∀ n, ∀ x ∈ 𝓡 n, ϑ x ∈ 𝓡' n)
    (hϑ : ∀ (n : ℕ) (x : 𝓡 n), ι' n ⟨ϑ x, hϑdeg n x x.2⟩ =
        ((Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow n)).app ⊤) (ι n x)))
    (hirr : HomogeneousIdeal.irrelevant 𝓡' ≤
      (HomogeneousIdeal.irrelevant 𝓡).map ({ ϑ.toRingHom with map_mem := fun h => hϑdeg _ _ h } : 𝓡 →+*ᵍ 𝓡'))
    (θ : X ⟶ Proj 𝓡) (hθ : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ)
    (θ' : X' ⟶ Proj 𝓡') (hθ' : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f' L' R' 𝓡' ι' θ') :
    ∀ (n : ℕ), 0 < n → ∀ σ : 𝓡 n,
      (θ' ≫ Proj.map ({ ϑ.toRingHom with map_mem := fun h => hϑdeg _ _ h } : 𝓡 →+*ᵍ 𝓡') hirr) ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) =
          (c ≫ θ) ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) ∧
      ∀ (k : ℕ),
        Scheme.Modules.IsFrameOn
          (((Scheme.Modules.pullbackTensorPowIso c L (k • n) ≪≫ Scheme.Modules.tensorPowMapIso e (k • n)).hom.app ⊤)
            ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow (k • n))).app ⊤)
              (ι (k • n) ⟨(σ : R) ^ k, SetLike.pow_mem_graded k σ.2⟩)))
          ((θ' ≫ Proj.map ({ ϑ.toRingHom with map_mem := fun h => hϑdeg _ _ h } : 𝓡 →+*ᵍ 𝓡') hirr) ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R)) := by
  open AlgebraicGeometry.GradedOAlgebra.PreimageBasicOpen in
  intro n hn σ

  have h₁ := AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.comp_projMap S' f' L' R 𝓡 R' 𝓡' ι' ϑ hϑdeg
    hirr θ' hθ'
  have h₂ := AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.comp_of_commSq S' f f' c hc.w L L' e R 𝓡 ι θ hθ
  have hι : (fun (n : ℕ) (x : 𝓡 n) => ι' n ⟨ϑ x, hϑdeg n x x.2⟩) =
      (fun (n : ℕ) (x : 𝓡 n) =>
        ((Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow n)).app ⊤) (ι n x))) :=
    funext fun n => funext fun x => hϑ n x
  rw [hι] at h₁
  refine ⟨AlgebraicGeometry.GradedOAlgebra.PreimageBasicOpen.preimage_basicOpen_eq h₁ h₂ hn σ, fun k => ?_⟩
  cases k with
  | zero =>
    rw [← hϑ]
    exact AlgebraicGeometry.GradedOAlgebra.PreimageBasicOpen.isFrameOn_of_deg_eq_zero hR' (by simp) _
      (by simp) _
  | succ k =>
    have := h₁.isFrameOn ((k + 1) • n) (by rw [smul_eq_mul]; exact Nat.mul_pos k.succ_pos hn)
      ⟨(σ : R) ^ (k + 1), SetLike.pow_mem_graded (k + 1) σ.2⟩
    rwa [Proj.basicOpen_pow 𝓡 _ (k + 1) k.succ_pos] at this

end S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_preimage_basicOpen_comp_projMap_eq
end P2MW
export P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_preimage_basicOpen_comp_projMap_eq (solution)
