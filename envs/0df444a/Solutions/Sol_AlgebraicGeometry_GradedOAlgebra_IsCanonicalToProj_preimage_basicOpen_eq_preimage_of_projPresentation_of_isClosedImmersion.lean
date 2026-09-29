-- Prove2me | solution 1 for AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.preimage_basicOpen_eq_preimage_of_projPresentation_of_isClosedImmersion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/45e6ab41-ee25-5984-9f16-71629d4eb1f3

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Proj_basicOpen_mul_eq_basicOpen_awayToSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_preimage_basicOpen_eq_preimage_of_projPresentation_of_isClosedImmersion

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization"

attribute [local instance] MvPolynomial.gradedAlgebra

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace ChartSol

open Opposite TopologicalSpace AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.GradedOAlgebra

variable {S : Type u} [CommRing S] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of S)} {L : X.Modules}
  {R : Type u} [CommRing R] [Algebra S R] {𝓡 : ℕ → Submodule S R} [GradedAlgebra 𝓡]
  {ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)}

lemma app_map {N N' : X.Modules} (φ : N ⟶ N') {W W' : X.Opens} (i : W' ⟶ W) (x : Γ(N, W)) :
    φ.app W' (N.presheaf.map i.op x) = N'.presheaf.map i.op (φ.app W x) := by
  have h := φ.mapPresheaf.naturality i.op
  exact ConcreteCategory.congr_hom h x

lemma map_map (N : X.Modules) {W W' W'' : X.Opens} (i : W' ⟶ W) (j : W'' ⟶ W') (k : W'' ⟶ W)
    (x : Γ(N, W)) :
    N.presheaf.map j.op (N.presheaf.map i.op x) = N.presheaf.map k.op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  obtain rfl : k = j ≫ i := Subsingleton.elim _ _
  rfl

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

theorem le_basicOpen_of_smul_eq {M : X.Modules} {U W V V' : X.Opens} (s t : Γ(M, U))
    (hs : IsFrameOn s V) (ht : IsFrameOn t V') (hWU : W ≤ U) (hWV : W ≤ V) (hWV' : W ≤ V')
    (g : Γ(X, W)) (hg : g • M.presheaf.map (homOfLE hWU).op s = M.presheaf.map (homOfLE hWU).op t) :
    W ≤ X.basicOpen g := by
  have hfr : IsFrameOn (g • M.presheaf.map (homOfLE hWU).op s) W := by
    rw [hg]; exact (ht.map (homOfLE hWU)).mono hWV'
  have hunit : IsUnit g := isUnit_of_isFrameOn_smul s hs hWU hWV g hfr
  rw [X.basicOpen_of_isUnit hunit]

theorem exists_mem_basicOpen (p : Proj 𝓡) :
    ∃ (m : ℕ) (hm : 0 < m) (τ : 𝓡 m), p ∈ Proj.basicOpen 𝓡 (τ : R) := by
  have hp := (Proj.affineOpenCover 𝓡).covers p
  change p ∈ (Proj.awayι 𝓡 _ _ _).opensRange at hp
  rw [Proj.opensRange_awayι] at hp
  exact ⟨_, ((Proj.affineOpenCover 𝓡).idx p).1.2, _, hp⟩

theorem exists_mem_basicOpen_X (N : ℕ)
    (p : Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S)) :
    ∃ j : Fin (N + 1),
      p ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S) (MvPolynomial.X j) := by
  have hp := (ProjSpace.affineOpenCover S N).covers p
  refine ⟨(ProjSpace.affineOpenCover S N).idx p, ?_⟩
  change p ∈ (Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S) _ _ _).opensRange at hp
  rwa [Proj.opensRange_awayι] at hp

section Pow

variable (hR : IsSectionRing f L R 𝓡 ι) (τ : 𝓡 1) {V : X.Opens} (hfr : IsFrameOn (ι 1 τ) V)
include hR hfr

theorem isFrameOn_pow (m : ℕ) :
    ∀ (d : ℕ) (c : 𝓡 d), d = m → (c : R) = (τ : R) ^ m → IsFrameOn (ι d c) V := by
  induction m with
  | zero =>
    intro d c hd hc
    subst hd
    obtain rfl : c = ⟨1, SetLike.GradedOne.one_mem⟩ := Subtype.ext (by simpa using hc)
    rw [hR.map_one]
    exact isFrameOn_unitSection V
  | succ m ih =>
    intro d c hd hc
    subst hd
    have hτm : (τ : R) ^ m ∈ 𝓡 m := by simpa using SetLike.pow_mem_graded m τ.2
    obtain rfl : c = ⟨((⟨(τ : R) ^ m, hτm⟩ : 𝓡 m) : R) * (τ : R),
        SetLike.GradedMul.mul_mem hτm τ.2⟩ := Subtype.ext (by rw [hc, pow_succ])
    rw [hR.map_mul]
    exact (IsFrameOn.tensorSections_monoidalV2 (ih m ⟨(τ : R) ^ m, hτm⟩ rfl rfl) hfr).map_iso
      (tensorPowAdd L m 1)

end Pow

theorem mem_preimage_basicOpen_of_isFrameOn_pow (hR : IsSectionRing f L R 𝓡 ι) {θ : X ⟶ Proj 𝓡}
    (hθ : IsCanonicalToProj f L R 𝓡 ι θ) (τ : 𝓡 1) {V : X.Opens} (hfr : IsFrameOn (ι 1 τ) V)
    (x : X) (hx : x ∈ V) : x ∈ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R) := by
  obtain ⟨m, hm, τ', hτ'⟩ := exists_mem_basicOpen (𝓡 := 𝓡) (θ.base x)
  set M : X.Modules := L.tensorPow (1 • m) with hM
  set U₁ : (Proj 𝓡).Opens := Proj.basicOpen 𝓡 (τ' : R) with hU₁
  set V₁ : X.Opens := θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ' : R) with hV₁
  have hx₁ : x ∈ V₁ := hτ'
  have hσm : (τ : R) ^ m ∈ 𝓡 (1 • m) := by
    rw [smul_eq_mul, Nat.mul_comm]; exact SetLike.pow_mem_graded m τ.2
  set s₁ : 𝓡 (1 • m) := ⟨(τ : R) ^ m, hσm⟩ with hs₁
  set t₁ : 𝓡 (1 • m) := ⟨(τ' : R) ^ 1, SetLike.pow_mem_graded 1 τ'.2⟩ with ht₁
  set g : Γ(X, V₁) := θ.appLE U₁ V₁ le_rfl
      (Proj.awayToSection 𝓡 (τ' : R) (Away.mk 𝓡 τ'.2 1 ((τ : R) ^ m) hσm)) with hg
  have key : g • M.presheaf.map (homOfLE (le_top : V₁ ≤ ⊤)).op (ι (1 • m) t₁) =
      M.presheaf.map (homOfLE (le_top : V₁ ≤ ⊤)).op (ι (1 • m) s₁) :=
    hθ.appLE_awayToSection_smul m hm τ' 1 s₁
  have hnm : 0 < 1 • m := by rw [smul_eq_mul]; omega
  have hfr₁ : IsFrameOn (ι (1 • m) t₁) V₁ := by
    have := hθ.isFrameOn (1 • m) hnm t₁
    rwa [Proj.basicOpen_pow 𝓡 _ 1 one_pos] at this
  have hfr₂ : IsFrameOn (ι (1 • m) s₁) V :=
    isFrameOn_pow hR τ hfr m (1 • m) s₁ (by simp) rfl
  set W : X.Opens := V₁ ⊓ V with hW
  have hxW : x ∈ W := Opens.mem_inf.mpr ⟨hx₁, hx⟩
  set gW : Γ(X, W) := X.presheaf.map (homOfLE (inf_le_left : W ≤ V₁)).op g with hgW
  have keyW : gW • M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (ι (1 • m) t₁) =
      M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (ι (1 • m) s₁) := by
    have := congrArg (M.presheaf.map (homOfLE (inf_le_left : W ≤ V₁)).op) key
    rwa [Scheme.Modules.map_smul, map_map M _ _ (homOfLE (le_top : W ≤ ⊤)),
      map_map M _ _ (homOfLE (le_top : W ≤ ⊤))] at this
  have hWg : W ≤ X.basicOpen gW :=
    le_basicOpen_of_smul_eq _ _ hfr₁ hfr₂ le_top inf_le_left inf_le_right gW keyW
  have hxg : x ∈ X.basicOpen g := by
    have := hWg hxW
    rw [hgW, Scheme.basicOpen_res] at this
    exact (Opens.mem_inf.mp this).2
  have h52 := AlgebraicGeometry.Proj.basicOpen_mul_eq_basicOpen_awayToSection 𝓡 τ'.2 hm τ.2 one_pos
  change Proj.basicOpen 𝓡 ((τ' : R) * τ) =
    (Proj 𝓡).basicOpen (Proj.awayToSection 𝓡 (τ' : R) (Away.mk 𝓡 τ'.2 1 ((τ : R) ^ m) hσm)) at h52
  rw [hg, Scheme.basicOpen_appLE, ← h52, Proj.basicOpen_mul] at hxg
  exact (Opens.mem_inf.mp (Opens.mem_inf.mp hxg).2).2

theorem mem_preimage_X_of_isFrameOn {N : ℕ} (𝔓 : ProjPresentation L f N) (i : Fin (N + 1))
    {V : X.Opens} (hfr : IsFrameOn (𝔓.σ i) V) (x : X) (hx : x ∈ V) :
    x ∈ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S) (MvPolynomial.X i) := by
  obtain ⟨j, hj⟩ := exists_mem_basicOpen_X (S := S) N (𝔓.toProj.base x)
  set 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S with h𝒜
  set Uj : (Proj 𝒜).Opens := Proj.basicOpen 𝒜 (MvPolynomial.X j) with hUj
  set Vj : X.Opens := 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X j) with hVj
  have hxj : x ∈ Vj := hj
  have hfrj : IsFrameOn (𝔓.σ j) Vj := fun W' hWU hWV => 𝔓.frame j W' hWV
  set r : Γ(X, Vj) := 𝔓.toProj.app Uj (Proj.awayToSection 𝒜 (MvPolynomial.X j) (ProjSpace.ratio S N j i))
    with hr
  have key : r • L.presheaf.map (homOfLE (le_top : Vj ≤ ⊤)).op (𝔓.σ j) =
      L.presheaf.map (homOfLE (le_top : Vj ≤ ⊤)).op (𝔓.σ i) := 𝔓.app_ratio_smul j i
  set W : X.Opens := Vj ⊓ V with hW
  have hxW : x ∈ W := Opens.mem_inf.mpr ⟨hxj, hx⟩
  set rW : Γ(X, W) := X.presheaf.map (homOfLE (inf_le_left : W ≤ Vj)).op r with hrW
  have keyW : rW • L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (𝔓.σ j) =
      L.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (𝔓.σ i) := by
    have := congrArg (L.presheaf.map (homOfLE (inf_le_left : W ≤ Vj)).op) key
    rwa [Scheme.Modules.map_smul, map_map L _ _ (homOfLE (le_top : W ≤ ⊤)),
      map_map L _ _ (homOfLE (le_top : W ≤ ⊤))] at this
  have hWr : W ≤ X.basicOpen rW :=
    le_basicOpen_of_smul_eq _ _ hfrj hfr le_top inf_le_left inf_le_right rW keyW
  have hxr : x ∈ X.basicOpen r := by
    have := hWr hxW
    rw [hrW, Scheme.basicOpen_res] at this
    exact (Opens.mem_inf.mp this).2
  have h52 := AlgebraicGeometry.Proj.basicOpen_mul_eq_basicOpen_awayToSection 𝒜
    (ProjSpace.X_mem_one S N j) one_pos (ProjSpace.X_mem_one S N i) one_pos
  have hratio : Away.isLocalizationElem (𝒜 := 𝒜) (ProjSpace.X_mem_one S N j) (ProjSpace.X_mem_one S N i) =
      ProjSpace.ratio S N j i := by
    unfold ProjSpace.ratio Away.isLocalizationElem
    congr 1
    exact pow_one _
  rw [hratio] at h52
  rw [hr, ← Scheme.preimage_basicOpen, ← h52, Proj.basicOpen_mul] at hxr
  exact (Opens.mem_inf.mp hxr).2

end ChartSol

end

theorem solution
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (hL : Scheme.Modules.IsInvertible L) (hva : Scheme.Modules.ClosedImmersionBySections L f)
    (θ : X ⟶ Proj 𝓡) (hθ : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ)
    (N : ℕ) (𝔓 : Scheme.Modules.ProjPresentation L f N) (h𝔓 : AlgebraicGeometry.IsClosedImmersion 𝔓.toProj)
    (i : Fin (N + 1)) (τ : 𝓡 1)
    (hτ : (λ_ L).hom.app ⊤ (ι 1 τ) = 𝔓.σ i) :
    θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R) =
        𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S) (MvPolynomial.X i) ∧
      IsAffineOpen (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)) := by
  classical
  open ChartSol in
  set 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S with h𝒜

  have hfrσ : IsFrameOn (𝔓.σ i) (𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X i)) :=
    fun W hWU hWV => 𝔓.frame i W hWV
  have hιτ : ι 1 τ = (λ_ L).inv.app ⊤ (𝔓.σ i) := by
    rw [← hτ]
    change ι 1 τ = ((λ_ L).hom.app ⊤ ≫ (λ_ L).inv.app ⊤) (ι 1 τ)
    rw [← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id, Scheme.Modules.Hom.id_app]; rfl
  have hfrτV : IsFrameOn (ι 1 τ) (𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X i)) := by
    rw [hιτ]; exact hfrσ.map_iso (λ_ L).symm
  have hfrτ : IsFrameOn (ι 1 τ) (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)) := hθ.isFrameOn 1 one_pos τ
  have hfrσ' : IsFrameOn (𝔓.σ i) (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)) := by
    rw [← hτ]; exact hfrτ.map_iso (λ_ L)
  have heq : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R) = 𝔓.toProj ⁻¹ᵁ Proj.basicOpen 𝒜 (MvPolynomial.X i) :=
    le_antisymm
      (fun x hx => ChartSol.mem_preimage_X_of_isFrameOn 𝔓 i hfrσ' x hx)
      (fun x hx => ChartSol.mem_preimage_basicOpen_of_isFrameOn_pow hR hθ τ hfrτV x hx)
  refine ⟨heq, ?_⟩
  rw [heq]
  haveI : IsClosedImmersion 𝔓.toProj := h𝔓
  exact (Proj.isAffineOpen_basicOpen 𝒜 (MvPolynomial.X i) (ProjSpace.X_mem_one S N i) one_pos).preimage 𝔓.toProj

end S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_preimage_basicOpen_eq_preimage_of_projPresentation_of_isClosedImmersion
end P2MW
export P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_preimage_basicOpen_eq_preimage_of_projPresentation_of_isClosedImmersion (solution)
