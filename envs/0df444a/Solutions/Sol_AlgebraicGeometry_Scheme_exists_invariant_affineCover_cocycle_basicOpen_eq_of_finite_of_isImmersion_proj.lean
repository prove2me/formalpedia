-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/5a3dc70c-e6c4-5f56-8d2f-a594d424b2f0

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj
import Theorems.Thm_AlgebraicGeometry_Proj_exists_cocycle_basicOpen_eq_inf_of_mem_of_pos
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_invariant_cocycle_basicOpen_eq_iInf_preimage_of_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace A2Asm

theorem isAffineOpen_inf_of_isSeparated {R : Type} [CommRing R] {X : Scheme.{0}} (π : X ⟶ Spec (.of R)) [IsSeparated π]
    {U W : X.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W) : IsAffineOpen (U ⊓ W) := by
  haveI : IsAffineHom (pullback.diagonal π) := inferInstance
  exact isAffineHom_diagonal_iff.mp this ⊤ (isAffineOpen_top _) U (by simp) W (by simp) hU hW

theorem mem_finset_inf {X : Scheme.{0}} {ι : Type} (V : ι → X.Opens) (s : Finset ι) (y : X) :
    y ∈ s.inf V ↔ ∀ i ∈ s, y ∈ V i := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.inf_cons, Opens.mem_inf, ih, Finset.forall_mem_cons]

theorem isAffineOpen_finset_inf {R : Type} [CommRing R] {X : Scheme.{0}} (π : X ⟶ Spec (.of R)) [IsSeparated π]
    {ι : Type} (V : ι → X.Opens) (hV : ∀ i, IsAffineOpen (V i)) (s : Finset ι) (hs : s.Nonempty) :
    IsAffineOpen (s.inf V) := by
  classical
  induction s using Finset.cons_induction with
  | empty => exact absurd hs Finset.not_nonempty_empty
  | cons a s ha ih =>
    rw [Finset.inf_cons]
    by_cases hs' : s.Nonempty
    · exact isAffineOpen_inf_of_isSeparated π (hV a) (ih hs')
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs', Finset.inf_empty, inf_top_eq]; exact hV a

theorem preimage_finset_univ_inf_eq {X : Scheme.{0}} {Γ : Type} [Group Γ] [Fintype Γ] (ρ : Γ →* Aut X)
    (U₀ : X.Opens) (h : Γ) :
    (ρ h).hom ⁻¹ᵁ (Finset.univ.inf fun g : Γ => (ρ g).hom ⁻¹ᵁ U₀) = Finset.univ.inf fun g : Γ => (ρ g).hom ⁻¹ᵁ U₀ := by
  classical
  set V : Γ → X.Opens := fun g => (ρ g).hom ⁻¹ᵁ U₀ with hVdef
  ext y
  constructor
  · intro hy
    have hy' : (ρ h).hom.base y ∈ Finset.univ.inf V := hy
    rw [SetLike.mem_coe, mem_finset_inf]
    intro g _
    have := (mem_finset_inf V _ _).mp hy' (g * h⁻¹) (Finset.mem_univ _)
    show (ρ g).hom.base y ∈ U₀
    have e : (ρ h).hom ≫ (ρ (g * h⁻¹)).hom = (ρ g).hom := by
      rw [← Iso.trans_hom, ← Aut.Aut_mul_def, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]
    rw [← e, Scheme.Hom.comp_base, TopCat.comp_app]
    exact this
  · intro hy
    have hy' : y ∈ Finset.univ.inf V := hy
    show (ρ h).hom.base y ∈ Finset.univ.inf V
    rw [mem_finset_inf]
    intro g _
    have := (mem_finset_inf V _ _).mp hy' (g * h) (Finset.mem_univ _)
    show (ρ g).hom.base ((ρ h).hom.base y) ∈ U₀
    have e : (ρ h).hom ≫ (ρ g).hom = (ρ (g * h)).hom := by
      rw [← Iso.trans_hom, ← Aut.Aut_mul_def, ← map_mul]
    rw [← TopCat.comp_app, ← Scheme.Hom.comp_base, e]
    exact this

theorem isSeparated_of_isImmersion_proj (B : Type) [CommRing B] {X : Scheme.{0}} (πX : X ⟶ Spec (CommRingCat.of B))
    (m : ℕ) (ι : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) B)) [IsImmersion ι]
    (h : ι ≫ ProjSpace.π B m = πX) : IsSeparated πX := by
  rw [← h]; infer_instance

theorem exists_fin_cover {X : Scheme.{0}} [CompactSpace X] (O : X → X.Opens) (hO : ∀ x, x ∈ O x) :
    ∃ (r : ℕ) (c : Fin r → X), (⨆ i, O (c i)) = ⊤ := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (O x : Set X)) (fun x => (O x).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hO x⟩)
  refine ⟨t.card, fun i => (t.equivFin.symm i).1, ?_⟩
  apply top_le_iff.mp
  intro y _
  obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ y))
  obtain ⟨hxt, hyx⟩ := Set.mem_iUnion.mp hx
  exact Opens.mem_iSup.mpr ⟨t.equivFin ⟨x, hxt⟩, by simpa using hyx⟩

theorem proj_basicOpen_pow {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (F : A) (e : ℕ) (he : 0 < e) : Proj.basicOpen 𝒜 (F ^ e) = Proj.basicOpen 𝒜 F := by
  exact Proj.basicOpen_pow 𝒜 F e he

end A2Asm
open A2Asm in
theorem solution
    (B : Type) [CommRing B] (X : Scheme.{0}) [CompactSpace X] (πX : X ⟶ Spec (CommRingCat.of B))
    (hQP : ∃ (qpm : ℕ) (qpι : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpm + 1)) B)),
      IsImmersion qpι ∧ qpι ≫ ProjSpace.π B qpm = πX)
    (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut X) (hρ : ∀ γ : Γ, (ρ γ).hom ≫ πX = πX) :
    ∃ (r : ℕ) (U : Fin r → X.Opens) (hinv : ∀ (γ : Γ) (i : Fin r), (ρ γ).hom ⁻¹ᵁ U i = U i)
      (w : ∀ i j : Fin r, Γ(X, U i)),
      (∀ i, IsAffineOpen (U i)) ∧ (⨆ i, U i) = ⊤ ∧
      (∀ i, w i i = 1) ∧
      (∀ i j k : Fin r,
        X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (w i k) =
          X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (w i j) *
            X.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (w j k)) ∧
      (∀ i j : Fin r, X.basicOpen (w i j) = U i ⊓ U j) ∧
      (∀ (γ : Γ) (i j : Fin r), (ρ γ).hom.appLE (U i) (U i) (le_of_eq (hinv γ i).symm) (w i j) = w i j) := by
  classical
  haveI : Fintype Γ := Fintype.ofFinite Γ
  obtain ⟨m, ι, hι, hιπ⟩ := hQP
  haveI := hι
  haveI : IsSeparated πX := isSeparated_of_isImmersion_proj B πX m ι hιπ

  have hA1 : ∀ x : X, ∃ (d : ℕ) (F : MvPolynomial (Fin (m + 1)) B),
      F ∈ MvPolynomial.homogeneousSubmodule (Fin (m + 1)) B d ∧ 0 < d ∧
      (∀ γ : Γ, (ρ γ).hom.base x ∈ ι ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) B) F) ∧
      IsAffineOpen (ι ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) B) F) := by
    intro x
    obtain ⟨d, F, hFd, hd, hS, haff, -⟩ :=
      AlgebraicGeometry.exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) B) ι (Finset.univ.image fun γ : Γ => (ρ γ).hom.base x)
    exact ⟨d, F, hFd, hd, fun γ => hS _ (Finset.mem_image_of_mem _ (Finset.mem_univ γ)), haff⟩
  choose d F hFd hd hmem haff using hA1

  set O : X → X.Opens := fun x => ⨅ γ : Γ, (ρ γ).hom ⁻¹ᵁ (ι ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) B) (F x)) with hOdef
  have hO : ∀ x, x ∈ O x := by
    intro x
    show x ∈ (⨅ γ : Γ, (ρ γ).hom ⁻¹ᵁ (ι ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) B) (F x)) : X.Opens)
    rw [← Finset.inf_univ_eq_iInf, mem_finset_inf]
    intro γ _
    exact hmem x γ
  obtain ⟨r, c, hcov⟩ := exists_fin_cover O hO

  set D : ℕ := ∏ i : Fin r, d (c i) with hDdef
  have hDpos : 0 < D := Finset.prod_pos fun i _ => hd (c i)
  have hdvd : ∀ i : Fin r, d (c i) ∣ D := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  set e : Fin r → ℕ := fun i => D / d (c i) with hedef
  have he : ∀ i, e i * d (c i) = D := fun i => Nat.div_mul_cancel (hdvd i)
  have hepos : ∀ i, 0 < e i := fun i => Nat.div_pos (Nat.le_of_dvd hDpos (hdvd i)) (hd (c i))
  set G : Fin r → MvPolynomial (Fin (m + 1)) B := fun i => F (c i) ^ e i with hGdef
  have hG : ∀ i, G i ∈ MvPolynomial.homogeneousSubmodule (Fin (m + 1)) B D := by
    intro i
    have := SetLike.pow_mem_graded (e i) (hFd (c i))
    rwa [smul_eq_mul, he i] at this
  have hGF : ∀ i, Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) B) (G i) =
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) B) (F (c i)) := fun i =>
    proj_basicOpen_pow _ _ _ (hepos i)

  obtain ⟨v, hVaff, hv1, hv2, hv3⟩ := AlgebraicGeometry.Proj.exists_cocycle_basicOpen_eq_inf_of_mem_of_pos (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) B) hDpos G hG
  obtain ⟨hu1, hu2, hu3⟩ := AlgebraicGeometry.Scheme.Hom.app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf ι (fun i => Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) B) (G i)) v hv1 hv2 hv3
  obtain ⟨U', hinv, w', hU', h1, h2, h3, h4⟩ := AlgebraicGeometry.Scheme.exists_invariant_cocycle_basicOpen_eq_iInf_preimage_of_finite X Γ ρ r
    (fun i => ι ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) B) (G i))
    (fun i j => ι.app _ (v i j)) hu1 hu2 hu3
  refine ⟨r, U', hinv, w', ?_, ?_, h1, h2, h3, h4⟩
  · intro i
    rw [hU' i, ← Finset.inf_univ_eq_iInf]
    apply isAffineOpen_finset_inf πX _ _ _ Finset.univ_nonempty
    intro γ
    rw [hGF i]
    exact (haff (c i)).preimage_of_isIso (ρ γ).hom
  · have : (fun i => U' i) = fun i => O (c i) := by
      funext i
      rw [hU' i]
      show (⨅ γ : Γ, (ρ γ).hom ⁻¹ᵁ (ι ⁻¹ᵁ Proj.basicOpen _ (G i))) = ⨅ γ : Γ, (ρ γ).hom ⁻¹ᵁ (ι ⁻¹ᵁ Proj.basicOpen _ (F (c i)))
      rw [hGF i]
    show (⨆ i, U' i) = ⊤
    rw [this]
    exact hcov

end S_AlgebraicGeometry_Scheme_exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj (solution)
