-- Prove2me | solution 1 for AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj.exists_smul_map_pow_eq_map_of_section
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/0f1aa087-64c5-59f0-be7b-7bff7fa668e4

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraToProj
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_exists_ringHom_smul_map_pow_eq
import Theorems.Thm_AlgebraicGeometry_Proj_basicOpen_mul_eq_basicOpen_awayToSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_eq_of_forall_map_homOfLE_eq_and_exists_of_compatible
import Theorems.Thm_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_preimage_basicOpen_eq_preimage_of_projPresentation_of_isClosedImmersion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_smul_map_pow_eq_map_of_section

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules HomogeneousLocalization"

attribute [local instance] MvPolynomial.gradedAlgebra

namespace F2SurjSol

open AlgebraicGeometry.GradedOAlgebra

section Generic
variable {X : Scheme.{u}}

theorem res_res (M : X.Modules) {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(M, U)) :
    M.presheaf.map (homOfLE h₂).op (M.presheaf.map (homOfLE h₁).op x) =
      M.presheaf.map (homOfLE (h₂.trans h₁)).op x := by
  rw [← CategoryTheory.comp_apply, ← M.presheaf.map_comp]
  rfl

theorem resf_resf {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)) :
    X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op x) =
      X.presheaf.map (homOfLE (h₂.trans h₁)).op x := by
  rw [← CategoryTheory.comp_apply, ← X.presheaf.map_comp]
  rfl

theorem app_res {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (h : V ≤ U) (x : Γ(M, U)) :
    N.presheaf.map (homOfLE h).op (φ.app U x) = φ.app V (M.presheaf.map (homOfLE h).op x) := by
  have := φ.mapPresheaf.naturality (homOfLE h).op
  exact (congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(M, U) → Γ(N, V))) this) x).symm

end Generic

variable {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤))

noncomputable abbrev resι (U : X.Opens) (d : ℕ) (s : 𝓡 d) : Γ(L.tensorPow d, U) :=
  (L.tensorPow d).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (ι d s)

theorem mem_of_index_eq {d d' : ℕ} (h : d = d') {r : R} (hr : r ∈ 𝓡 d) : r ∈ 𝓡 d' := h ▸ hr

theorem pow_mem_one (τ : 𝓡 1) (d : ℕ) : (τ : R) ^ d ∈ 𝓡 d :=
  mem_of_index_eq R 𝓡 (by simp) (SetLike.pow_mem_graded d τ.2)

structure ChartData (U : X.Opens) (τ : 𝓡 1) where
  φ : R →+* Γ(X, U)
  frame : ∀ d : ℕ, IsFrameOn (ι d ⟨(τ : R) ^ d, pow_mem_one R 𝓡 τ d⟩) U
  eq : ∀ (d : ℕ) (s : 𝓡 d), φ (s : R) • resι L R 𝓡 ι U d ⟨(τ : R) ^ d, pow_mem_one R 𝓡 τ d⟩ = resι L R 𝓡 ι U d s

include f in
theorem nonempty_chartData (hR : IsSectionRing f L R 𝓡 ι) (U : X.Opens) (τ : 𝓡 1)
    (hτ : IsFrameOn (ι 1 τ) U) : Nonempty (ChartData L R 𝓡 ι U τ) := by
  obtain ⟨φ, -, hfr, heq⟩ := hR.exists_ringHom_smul_map_pow_eq f L R 𝓡 ι τ U hτ
  have hfr' : ∀ (d m : ℕ) (h : m • 1 = d),
      IsFrameOn (ι d ⟨(τ : R) ^ m, mem_of_index_eq R 𝓡 h (SetLike.pow_mem_graded m τ.2)⟩) U := by
    intro d m h; subst h; exact hfr m
  have heq' : ∀ (d m : ℕ) (h : m • 1 = d) (s : 𝓡 d),
      φ (s : R) • resι L R 𝓡 ι U d ⟨(τ : R) ^ m, mem_of_index_eq R 𝓡 h (SetLike.pow_mem_graded m τ.2)⟩ =
        resι L R 𝓡 ι U d s := by
    intro d m h s; subst h; exact heq m s
  exact ⟨⟨φ, fun d => hfr' d d (by simp), fun d s => heq' d d (by simp) s⟩⟩

section Chart
variable {L R 𝓡 ι}
variable {U : X.Opens} {τ : 𝓡 1} (C : ChartData L R 𝓡 ι U τ)

noncomputable abbrev ChartData.G (_C : ChartData L R 𝓡 ι U τ) (d : ℕ) : Γ(L.tensorPow d, U) :=
  resι L R 𝓡 ι U d ⟨(τ : R) ^ d, pow_mem_one R 𝓡 τ d⟩

theorem ChartData.isFrameOn_G (d : ℕ) {W : X.Opens} (hW : W ≤ U) :
    Function.Bijective fun c : Γ(X, W) => c • (L.tensorPow d).presheaf.map (homOfLE hW).op (C.G d) := by
  have h := C.frame d (le_top : W ≤ ⊤) hW
  have e : (L.tensorPow d).presheaf.map (homOfLE hW).op (C.G d) =
      (L.tensorPow d).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (ι d ⟨(τ : R) ^ d, pow_mem_one R 𝓡 τ d⟩) :=
    res_res _ _ _ _
  rw [e]; exact h

theorem ChartData.resι_pow {n : ℕ} (σ : 𝓡 n) (K : ℕ) :
    resι L R 𝓡 ι U (K • n) ⟨(σ : R) ^ K, SetLike.pow_mem_graded K σ.2⟩ = (C.φ (σ : R)) ^ K • C.G (K • n) := by
  rw [← map_pow, ← C.eq (K • n) ⟨(σ : R) ^ K, SetLike.pow_mem_graded K σ.2⟩]

end Chart

section ChartOpen
variable {f L R 𝓡 ι}
variable {θ : X ⟶ Proj 𝓡} (hθ : IsCanonicalToProj f L R 𝓡 ι θ)
variable {τ : 𝓡 1} (C : ChartData L R 𝓡 ι (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)) τ)

include hθ in

theorem preimage_inf_eq_basicOpen {n : ℕ} (hn : 0 < n) (σ : 𝓡 n) :
    θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R) ⊓ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) = X.basicOpen (C.φ (σ : R)) := by
  have hσ1 : (σ : R) ^ 1 ∈ 𝓡 (n • 1) := by simpa using σ.2
  have key : (θ.appLE (Proj.basicOpen 𝓡 (τ : R)) (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)) le_rfl
      (Proj.awayToSection 𝓡 (τ : R) (Away.mk 𝓡 τ.2 n ((σ : R) ^ 1) hσ1))) •
        resι L R 𝓡 ι (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)) (n • 1) ⟨(τ : R) ^ n, SetLike.pow_mem_graded n τ.2⟩ =
      resι L R 𝓡 ι (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)) (n • 1) ⟨(σ : R) ^ 1, hσ1⟩ :=
    hθ.appLE_awayToSection_smul 1 one_pos τ n ⟨(σ : R) ^ 1, hσ1⟩
  have hG : (⟨(τ : R) ^ n, SetLike.pow_mem_graded n τ.2⟩ : 𝓡 (n • 1)) =
      ⟨(τ : R) ^ (n • 1), pow_mem_one R 𝓡 τ (n • 1)⟩ := Subtype.ext (by simp)
  rw [hG] at key
  have key2 := C.eq (n • 1) ⟨(σ : R) ^ 1, hσ1⟩
  have hu : θ.appLE (Proj.basicOpen 𝓡 (τ : R)) (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R)) le_rfl
      (Proj.awayToSection 𝓡 (τ : R) (Away.mk 𝓡 τ.2 n ((σ : R) ^ 1) hσ1)) = C.φ (σ : R) := by
    have e := (C.frame (n • 1) le_top le_rfl).1 (key.trans key2.symm)
    rw [e]
    change C.φ ((σ : R) ^ 1) = C.φ (σ : R)
    rw [pow_one]
  rw [← hu, Scheme.basicOpen_appLE]
  have h52 := AlgebraicGeometry.Proj.basicOpen_mul_eq_basicOpen_awayToSection 𝓡 τ.2 one_pos σ.2 hn
  change Proj.basicOpen 𝓡 ((τ : R) * σ) =
    (Proj 𝓡).basicOpen (Proj.awayToSection 𝓡 (τ : R) (Away.mk 𝓡 τ.2 n ((σ : R) ^ 1) hσ1)) at h52
  rw [← h52, Proj.basicOpen_mul, Scheme.Hom.preimage_inf, ← inf_assoc, inf_idem]

include hθ in

theorem preimage_inf_preimage_eq_basicOpen (τ' : 𝓡 1) :
    θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ : R) ⊓ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ' : R) = X.basicOpen (C.φ (τ' : R)) :=
  preimage_inf_eq_basicOpen hθ C one_pos τ'

end ChartOpen

section Cover
variable {f L R 𝓡 ι}

theorem exists_cover (hR : IsSectionRing f L R 𝓡 ι) (hL : Scheme.Modules.IsInvertible L)
    (hva : Scheme.Modules.ClosedImmersionBySections L f)
    {θ : X ⟶ Proj 𝓡} (hθ : IsCanonicalToProj f L R 𝓡 ι θ) :
    ∃ (N : ℕ) (τ : Fin (N + 1) → 𝓡 1),
      (⨆ i, θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)) = ⊤ ∧
      ∀ i, IsAffineOpen (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)) := by
  obtain ⟨N, 𝔓, hci⟩ := id hva
  have hsurj : ∀ i : Fin (N + 1), ∃ t : 𝓡 1, ι 1 t = (tensorPowOneIso L).symm.hom.app ⊤ (𝔓.σ i) :=
    fun i => (hR.bijective 1).2 _
  choose τ hτ using hsurj
  have hτ' : ∀ i, (λ_ L).hom.app ⊤ (ι 1 (τ i)) = 𝔓.σ i := by
    intro i
    rw [hτ i]
    change ((tensorPowOneIso L).inv ≫ (tensorPowOneIso L).hom).app ⊤ (𝔓.σ i) = 𝔓.σ i
    rw [Iso.inv_hom_id, Scheme.Modules.Hom.id_app]
    rfl
  have hchart := fun i =>
    IsCanonicalToProj.preimage_basicOpen_eq_preimage_of_projPresentation_of_isClosedImmersion f L R 𝓡 ι hR hL hva θ
      hθ N 𝔓 hci i (τ i) (hτ' i)
  refine ⟨N, τ, ?_, fun i => (hchart i).2⟩
  calc (⨆ i, θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R))
      = ⨆ i, 𝔓.toProj ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S) (MvPolynomial.X i) :=
        iSup_congr fun i => (hchart i).1
    _ = ⊤ := 𝔓.toProj.iSup_preimage_eq_top
      (Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) S)
        (fun j => MvPolynomial.X j) (ProjSpace.irrelevant_le_span_X S N))

end Cover

section Main
variable {f L R 𝓡 ι}
variable (hR : IsSectionRing f L R 𝓡 ι)
  {N : ℕ} {τ : Fin (N + 1) → 𝓡 1} {V : Fin (N + 1) → X.Opens}
  (hcov : (⨆ i, V i) = ⊤) (haff : ∀ i, IsAffineOpen (V i))
  (C : ∀ i, ChartData L R 𝓡 ι (V i) (τ i))
  (hVV : ∀ i j, IsCompact ((V i ⊓ V j : X.Opens) : Set X))
  (n : ℕ) (σ : 𝓡 n) (Xσ : X.Opens)
  (hD : ∀ i, V i ⊓ Xσ = X.basicOpen ((C i).φ (σ : R)))

abbrev σpow (K : ℕ) : 𝓡 (K • n) := ⟨(σ : R) ^ K, SetLike.pow_mem_graded K σ.2⟩

theorem resι_σpow (i : Fin (N + 1)) (K : ℕ) :
    resι L R 𝓡 ι (V i) (K • n) (σpow n σ K) = ((C i).φ (σ : R)) ^ K • (C i).G (K • n) :=
  (C i).resι_pow σ K

include hD in
theorem basicOpen_le_Xσ (i : Fin (N + 1)) : X.basicOpen ((C i).φ (σ : R)) ≤ Xσ :=
  (hD i) ▸ inf_le_right

theorem basicOpen_le_V (i : Fin (N + 1)) : X.basicOpen ((C i).φ (σ : R)) ≤ V i := X.basicOpen_le _

include haff in

theorem exists_mul_pow_eq (i : Fin (N + 1)) (g : Γ(X, X.basicOpen ((C i).φ (σ : R)))) :
    ∃ (k : ℕ) (b : Γ(X, V i)),
      g * X.presheaf.map (homOfLE (X.basicOpen_le _)).op (((C i).φ (σ : R)) ^ k) =
        X.presheaf.map (homOfLE (X.basicOpen_le _)).op b := by
  have := (haff i).isLocalization_basicOpen ((C i).φ (σ : R))
  obtain ⟨⟨b, ⟨_, k, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers ((C i).φ (σ : R))) g
  exact ⟨k, b, h⟩

include haff in

theorem exists_uniform (g : Γ(X, Xσ)) :
    ∃ (K : ℕ) (b : ∀ i, Γ(X, V i)), ∀ i,
      X.presheaf.map (homOfLE (basicOpen_le_Xσ C n σ Xσ hD i)).op g *
          X.presheaf.map (homOfLE (X.basicOpen_le _)).op (((C i).φ (σ : R)) ^ K) =
        X.presheaf.map (homOfLE (X.basicOpen_le _)).op (b i) := by
  have H := fun i => exists_mul_pow_eq haff C n σ i
    (X.presheaf.map (homOfLE (basicOpen_le_Xσ C n σ Xσ hD i)).op g)
  choose k b hb using H
  refine ⟨Finset.univ.sup k, fun i => b i * ((C i).φ (σ : R)) ^ (Finset.univ.sup k - k i), fun i => ?_⟩
  have hk : k i ≤ Finset.univ.sup k := Finset.le_sup (Finset.mem_univ i)
  rw [map_mul, ← hb i, mul_assoc, ← map_mul, ← pow_add, Nat.add_sub_of_le hk]

noncomputable abbrev sloc (K : ℕ) (b : ∀ i, Γ(X, V i)) (i : Fin (N + 1)) : Γ(L.tensorPow (K • n), V i) :=
  b i • (C i).G (K • n)

def LocalData (g : Γ(X, Xσ)) (K : ℕ) (b : ∀ i, Γ(X, V i)) : Prop :=
  ∀ i, X.presheaf.map (homOfLE (basicOpen_le_Xσ C n σ Xσ hD i)).op g *
      X.presheaf.map (homOfLE (X.basicOpen_le _)).op (((C i).φ (σ : R)) ^ K) =
    X.presheaf.map (homOfLE (X.basicOpen_le _)).op (b i)

theorem sloc_res {g : Γ(X, Xσ)} {K : ℕ} {b : ∀ i, Γ(X, V i)} (hb : LocalData C n σ Xσ hD g K b)
    (i : Fin (N + 1)) :
    (L.tensorPow (K • n)).presheaf.map (homOfLE (basicOpen_le_V C n σ i)).op (sloc C n K b i) =
      X.presheaf.map (homOfLE (basicOpen_le_Xσ C n σ Xσ hD i)).op g •
        resι L R 𝓡 ι (X.basicOpen ((C i).φ (σ : R))) (K • n) (σpow n σ K) := by
  have e1 : resι L R 𝓡 ι (X.basicOpen ((C i).φ (σ : R))) (K • n) (σpow n σ K) =
      (L.tensorPow (K • n)).presheaf.map (homOfLE (basicOpen_le_V C n σ i)).op
        (resι L R 𝓡 ι (V i) (K • n) (σpow n σ K)) := (res_res _ _ _ _).symm
  rw [e1, resι_σpow C n σ i K, Scheme.Modules.map_smul, Scheme.Modules.map_smul, smul_smul, hb i]

theorem tensorSections_sub_left {M M' : X.Modules} {U : X.Opens} (s s' : Γ(M, U)) (t : Γ(M', U)) :
    tensorSections (s - s') t = tensorSections s t - tensorSections s' t := by
  rw [sub_eq_add_neg, tensorSections_add_left, ← neg_one_smul (Γ(X, U)) s', tensorSections_smul_left,
    neg_one_smul, ← sub_eq_add_neg]

def Killed (K : ℕ) (b : ∀ i, Γ(X, V i)) (E : ℕ) : Prop :=
  ∀ i j,
    X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (((C i).φ (σ : R)) ^ E) •
      ((L.tensorPow (K • n)).presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (sloc C n K b i) -
        (L.tensorPow (K • n)).presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (sloc C n K b j)) = 0

include hVV in

theorem exists_killed_pair {g : Γ(X, Xσ)} {K : ℕ} {b : ∀ i, Γ(X, V i)} (hb : LocalData C n σ Xσ hD g K b)
    (i j : Fin (N + 1)) :
    ∃ e : ℕ, ∀ E : ℕ, e ≤ E →
      X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (((C i).φ (σ : R)) ^ E) •
        ((L.tensorPow (K • n)).presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (sloc C n K b i) -
          (L.tensorPow (K • n)).presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (sloc C n K b j))
        = 0 := by

  set a : Γ(X, V i) := (C i).φ (σ : R) with ha
  set aij : Γ(X, V i ⊓ V j) := X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op a with haij
  set d : Γ(L.tensorPow (K • n), V i ⊓ V j) :=
    (L.tensorPow (K • n)).presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (sloc C n K b i) -
      (L.tensorPow (K • n)).presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (sloc C n K b j)
    with hd

  obtain ⟨c, hc⟩ := ((C i).isFrameOn_G (K • n) (inf_le_left : V i ⊓ V j ≤ V i)).2 d

  have hW : X.basicOpen aij = (V i ⊓ V j) ⊓ X.basicOpen a := X.basicOpen_res a (homOfLE inf_le_left).op
  have hWij : X.basicOpen aij ≤ V i ⊓ V j := X.basicOpen_le aij
  have hWDi : X.basicOpen aij ≤ X.basicOpen a := hW ▸ inf_le_right
  have hWDj : X.basicOpen aij ≤ X.basicOpen ((C j).φ (σ : R)) := by
    rw [← hD j]
    exact le_inf (hWij.trans inf_le_right) (hWDi.trans (basicOpen_le_Xσ C n σ Xσ hD i))

  have hd0 : (L.tensorPow (K • n)).presheaf.map (homOfLE hWij).op d = 0 := by
    rw [hd, map_sub]
    have ei : (L.tensorPow (K • n)).presheaf.map (homOfLE hWij).op
        ((L.tensorPow (K • n)).presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (sloc C n K b i)) =
        (L.tensorPow (K • n)).presheaf.map (homOfLE hWDi).op
          ((L.tensorPow (K • n)).presheaf.map (homOfLE (basicOpen_le_V C n σ i)).op (sloc C n K b i)) := by
      rw [res_res, res_res]
    have ej : (L.tensorPow (K • n)).presheaf.map (homOfLE hWij).op
        ((L.tensorPow (K • n)).presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (sloc C n K b j)) =
        (L.tensorPow (K • n)).presheaf.map (homOfLE hWDj).op
          ((L.tensorPow (K • n)).presheaf.map (homOfLE (basicOpen_le_V C n σ j)).op (sloc C n K b j)) := by
      rw [res_res, res_res]
    rw [ei, ej, sloc_res C n σ Xσ hD hb i, sloc_res C n σ Xσ hD hb j, Scheme.Modules.map_smul,
      Scheme.Modules.map_smul, resf_resf, resf_resf, res_res, res_res, sub_self]

  have hc0 : X.presheaf.map (homOfLE hWij).op c = 0 := by
    have h := congrArg ((L.tensorPow (K • n)).presheaf.map (homOfLE hWij).op) hc
    dsimp only at h
    rw [hd0, Scheme.Modules.map_smul, res_res, res_res] at h
    exact (((C i).frame (K • n)).smul_eq_zero_iff le_top (hWij.trans inf_le_left) _).1 h

  obtain ⟨e, he⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X (hVV i j) c aij hc0
  refine ⟨e, fun E hE => ?_⟩
  rw [← hc, map_pow, smul_smul, ← haij, ← Nat.sub_add_cancel hE, pow_add, mul_assoc, he, mul_zero, zero_smul]

include hVV in

theorem exists_killed {g : Γ(X, Xσ)} {K : ℕ} {b : ∀ i, Γ(X, V i)} (hb : LocalData C n σ Xσ hD g K b) :
    ∃ E : ℕ, Killed C n σ K b E := by
  have H := fun p : Fin (N + 1) × Fin (N + 1) => exists_killed_pair C hVV n σ Xσ hD hb p.1 p.2
  choose e he using H
  exact ⟨Finset.univ.sup e, fun i j => he (i, j) _ (Finset.le_sup (Finset.mem_univ (i, j)))⟩

noncomputable abbrev stw (K : ℕ) (b : ∀ i, Γ(X, V i)) (E : ℕ) (i : Fin (N + 1)) :
    Γ(L.tensorPow (K • n + E • n), V i) :=
  (tensorPowAdd L (K • n) (E • n)).hom.app (V i)
    (tensorSections (sloc C n K b i) (resι L R 𝓡 ι (V i) (E • n) (σpow n σ E)))

theorem stw_compat {K : ℕ} {b : ∀ i, Γ(X, V i)} {E : ℕ} (hE : Killed C n σ K b E) (i j : Fin (N + 1)) :
    (L.tensorPow (K • n + E • n)).presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op
        (stw C n σ K b E i) =
      (L.tensorPow (K • n + E • n)).presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op
        (stw C n σ K b E j) := by
  rw [app_res, app_res, map_homOfLE_tensorSections, map_homOfLE_tensorSections, res_res, res_res]
  congr 1

  have er : (L.tensorPow (E • n)).presheaf.map (homOfLE (le_top : V i ⊓ V j ≤ ⊤)).op (ι (E • n) (σpow n σ E)) =
      X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (((C i).φ (σ : R)) ^ E) •
        (L.tensorPow (E • n)).presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op ((C i).G (E • n)) := by
    rw [← Scheme.Modules.map_smul, ← resι_σpow C n σ i E, res_res]
  rw [er, tensorSections_smul_right, tensorSections_smul_right, ← sub_eq_zero, ← smul_sub,
    ← tensorSections_sub_left, ← tensorSections_smul_left, hE i j, tensorSections_zero_left]

include hcov in
theorem exists_glued {K : ℕ} {b : ∀ i, Γ(X, V i)} {E : ℕ} (hE : Killed C n σ K b E) :
    ∃ T : Γ(L.tensorPow (K • n + E • n), ⊤), ∀ i,
      (L.tensorPow (K • n + E • n)).presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op T = stw C n σ K b E i := by
  have hV : (⊤ : X.Opens) ≤ ⨆ i : ULift.{u} (Fin (N + 1)), V i.down := by
    rw [← hcov]
    exact iSup_le fun i => le_iSup (fun j : ULift.{u} (Fin (N + 1)) => V j.down) ⟨i⟩
  obtain ⟨T, hT⟩ := (Scheme.Modules.eq_of_forall_map_homOfLE_eq_and_exists_of_compatible
    (L.tensorPow (K • n + E • n)) (fun i : ULift.{u} (Fin (N + 1)) => V i.down) ⊤ (fun _ => le_top) hV).2
    (fun i => stw C n σ K b E i.down) (fun i j => stw_compat C n σ hE i.down j.down)
  exact ⟨T, fun i => hT ⟨i⟩⟩

include hR in

theorem glued_res {g : Γ(X, Xσ)} {K : ℕ} {b : ∀ i, Γ(X, V i)} (hb : LocalData C n σ Xσ hD g K b) {E : ℕ}
    (T : Γ(L.tensorPow (K • n + E • n), ⊤))
    (hT : ∀ i, (L.tensorPow (K • n + E • n)).presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op T =
      stw C n σ K b E i)
    (i : Fin (N + 1)) :
    (L.tensorPow (K • n + E • n)).presheaf.map (homOfLE (basicOpen_le_Xσ C n σ Xσ hD i)).op
        (g • resι L R 𝓡 ι Xσ (K • n + E • n)
          ⟨(σ : R) ^ (K + E), mem_of_index_eq R 𝓡 (add_smul K E n) (SetLike.pow_mem_graded (K + E) σ.2)⟩) =
      (L.tensorPow (K • n + E • n)).presheaf.map
        (homOfLE ((basicOpen_le_Xσ C n σ Xσ hD i).trans le_top)).op T := by

  have eT : (L.tensorPow (K • n + E • n)).presheaf.map
        (homOfLE ((basicOpen_le_Xσ C n σ Xσ hD i).trans le_top)).op T =
      (L.tensorPow (K • n + E • n)).presheaf.map (homOfLE (basicOpen_le_V C n σ i)).op
        ((L.tensorPow (K • n + E • n)).presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op T) := (res_res _ _ _ _).symm
  rw [eT, hT i, app_res, map_homOfLE_tensorSections, sloc_res C n σ Xσ hD hb i, res_res,
    tensorSections_smul_left, Scheme.Modules.Hom.app_smul, Scheme.Modules.map_smul, res_res]
  congr 1

  have epow : (⟨(σ : R) ^ (K + E), mem_of_index_eq R 𝓡 (add_smul K E n) (SetLike.pow_mem_graded (K + E) σ.2)⟩ :
      𝓡 (K • n + E • n)) =
      ⟨((σpow n σ K : 𝓡 (K • n)) : R) * ((σpow n σ E : 𝓡 (E • n)) : R),
        SetLike.GradedMul.mul_mem (σpow n σ K).2 (σpow n σ E).2⟩ := Subtype.ext (pow_add _ _ _)
  rw [epow]
  change (L.tensorPow (K • n + E • n)).presheaf.map (homOfLE _).op (ι (K • n + E • n) _) = _
  rw [hR.map_mul (K • n) (E • n) (σpow n σ K) (σpow n σ E), app_res, map_homOfLE_tensorSections]

include hR hcov haff hVV hD in

theorem main (g : Γ(X, Xσ)) :
    ∃ (K d : ℕ) (hd : K • n = d) (t : 𝓡 d),
      g • resι L R 𝓡 ι Xσ d ⟨(σ : R) ^ K, mem_of_index_eq R 𝓡 hd (SetLike.pow_mem_graded K σ.2)⟩ =
        resι L R 𝓡 ι Xσ d t := by
  obtain ⟨K, b, hb⟩ := exists_uniform haff C n σ Xσ hD g
  obtain ⟨E, hE⟩ := exists_killed C hVV n σ Xσ hD hb
  obtain ⟨T, hT⟩ := exists_glued hcov C n σ hE
  obtain ⟨t, ht⟩ := (hR.bijective (K • n + E • n)).2 T
  refine ⟨K + E, K • n + E • n, add_smul K E n, t, ?_⟩
  have cov : Xσ ≤ ⨆ i : ULift.{u} (Fin (N + 1)), X.basicOpen ((C i.down).φ (σ : R)) := by
    have h1 : Xσ = ⨆ i, V i ⊓ Xσ := by rw [← iSup_inf_eq, hcov, top_inf_eq]
    calc Xσ = ⨆ i, V i ⊓ Xσ := h1
      _ = ⨆ i, X.basicOpen ((C i).φ (σ : R)) := iSup_congr hD
      _ ≤ ⨆ i : ULift.{u} (Fin (N + 1)), X.basicOpen ((C i.down).φ (σ : R)) :=
        iSup_le fun i => le_iSup (fun j : ULift.{u} (Fin (N + 1)) => X.basicOpen ((C j.down).φ (σ : R))) ⟨i⟩
  refine (Scheme.Modules.eq_of_forall_map_homOfLE_eq_and_exists_of_compatible (L.tensorPow (K • n + E • n))
    (fun i : ULift.{u} (Fin (N + 1)) => X.basicOpen ((C i.down).φ (σ : R))) Xσ
    (fun i => basicOpen_le_Xσ C n σ Xσ hD i.down) cov).1 _ _ fun i => ?_
  rw [glued_res hR C n σ Xσ hD hb T hT i.down, ← ht]
  exact (res_res _ _ _ _).symm

end Main

end F2SurjSol

open F2SurjSol in
theorem solution
    {S : Type u} [CommRing S] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (hL : Scheme.Modules.IsInvertible L) (hva : Scheme.Modules.ClosedImmersionBySections L f)
    (θ : X ⟶ Proj 𝓡) (hθ : AlgebraicGeometry.GradedOAlgebra.IsCanonicalToProj f L R 𝓡 ι θ)
    (n : ℕ) (hn : 0 < n) (σ : 𝓡 n) (g : Γ(X, θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R))) :
    ∃ (k : ℕ) (t : 𝓡 (k • n)),
      g • (L.tensorPow (k • n)).presheaf.map (homOfLE (le_top : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) ≤ ⊤)).op
          (ι (k • n) ⟨(σ : R) ^ k, SetLike.pow_mem_graded k σ.2⟩) =
        (L.tensorPow (k • n)).presheaf.map (homOfLE (le_top : θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) ≤ ⊤)).op (ι (k • n) t) := by
  obtain ⟨N, τ, hcov, haff⟩ := exists_cover hR hL hva hθ
  have C : ∀ i, ChartData L R 𝓡 ι (θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R)) (τ i) :=
    fun i => (nonempty_chartData f L R 𝓡 ι hR _ (τ i) (hθ.isFrameOn 1 one_pos (τ i))).some
  have hD : ∀ i, θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R) ⊓ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (σ : R) =
      X.basicOpen ((C i).φ (σ : R)) := fun i => preimage_inf_eq_basicOpen hθ (C i) hn σ
  have hVV : ∀ i j, IsCompact ((θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ i : R) ⊓ θ ⁻¹ᵁ Proj.basicOpen 𝓡 (τ j : R) :
      X.Opens) : Set X) := by
    intro i j
    rw [preimage_inf_preimage_eq_basicOpen hθ (C i) (τ j)]
    exact ((haff i).basicOpen _).isCompact
  obtain ⟨K, d, hd, t, h⟩ := main hR hcov haff C hVV n σ _ hD g
  subst hd
  exact ⟨K, t, h⟩

end S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_smul_map_pow_eq_map_of_section
end P2MW
export P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsCanonicalToProj_exists_smul_map_pow_eq_map_of_section (solution)
