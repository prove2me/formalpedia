-- Prove2me | solution 1 for AlgebraicGeometry.HilbertFunctor.Point.I_eq_span_of_forall_finrank_piece_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/b0f16675-ccaa-5d60-8d8c-a62d28a27f9a

import Mathlib
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_HilbertFunctor_Point_I_eq_span_of_forall_finrank_piece_succ_le

set_option autoImplicit false

open MvPolynomial AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

namespace HilbGenH2c

section Modules

variable {A : Type} [CommRing A]

theorem exists_equiv_prod_ker {Q₁ Q₂ : Type} [AddCommGroup Q₁] [Module A Q₁] [AddCommGroup Q₂] [Module A Q₂]
    [Module.Projective A Q₂] (π : Q₁ →ₗ[A] Q₂) (hπ : Function.Surjective π) :
    ∃ e : Q₁ ≃ₗ[A] Q₂ × LinearMap.ker π, ∀ x, (e x).1 = π x := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have hs' : ∀ y, π (s y) = y := fun y => by simpa using LinearMap.congr_fun hs y
  refine ⟨{ toFun := fun x => (π x, ⟨x - s (π x), by simp [hs']⟩)
            invFun := fun yk => s yk.1 + yk.2
            map_add' := fun x y => by ext <;> simp [map_add]; abel
            map_smul' := fun a x => by ext <;> simp [map_smul, smul_sub]
            left_inv := fun x => by simp
            right_inv := fun yk => by
              obtain ⟨y, k, hk⟩ := yk
              have hk' : π k = 0 := hk
              ext <;> simp [hs', hk'] }, fun x => rfl⟩

theorem subsingleton_of_finrank_fiber_eq_zero (K : Type) [AddCommGroup K] [Module A K] [Module.Finite A K]
    (hK : ∀ p : PrimeSpectrum A, Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] K) = 0) :
    Subsingleton K := by

  have hnak : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → ∃ r : A, r - 1 ∈ 𝔪 ∧ ∀ k : K, r • k = 0 := by
    intro 𝔪 h𝔪
    let p : PrimeSpectrum A := ⟨𝔪, h𝔪.isPrime⟩
    let κ := p.asIdeal.ResidueField
    haveI : Module.Finite κ (κ ⊗[A] K) := Module.Finite.base_change A κ K
    have hsub : Subsingleton (κ ⊗[A] K) :=
      (subsingleton_iff_forall_eq 0).mpr (finrank_zero_iff_forall_zero.mp (hK p))

    have hbij := Ideal.bijective_algebraMap_quotient_residueField 𝔪
    let f : (A ⧸ 𝔪) →ₗ[A] κ := (IsScalarTower.toAlgHom A (A ⧸ 𝔪) κ).toLinearMap
    have hf : Function.Bijective f := hbij
    let e : (A ⧸ 𝔪) ≃ₗ[A] κ := LinearEquiv.ofBijective f hf
    have hsub' : Subsingleton ((A ⧸ 𝔪) ⊗[A] K) :=
      (TensorProduct.congr e (LinearEquiv.refl A K)).toEquiv.subsingleton
    have hsub'' : Subsingleton (K ⧸ (𝔪 • (⊤ : Submodule A K))) :=
      (TensorProduct.quotTensorEquivQuotSMul K 𝔪).symm.toEquiv.subsingleton
    have htop : (𝔪 • (⊤ : Submodule A K)) = ⊤ := Submodule.Quotient.subsingleton_iff.mp hsub''
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔪 (⊤ : Submodule A K)
      Module.Finite.fg_top (by rw [htop])
    exact ⟨r, hr, fun k => hr0 k Submodule.mem_top⟩

  by_contra hne
  have hann : Module.annihilator A K ≠ ⊤ := by
    intro htop
    apply hne
    refine ⟨fun x y => ?_⟩
    have h1 : (1 : A) ∈ Module.annihilator A K := by rw [htop]; exact Submodule.mem_top
    rw [Module.mem_annihilator] at h1
    have hx := h1 x
    have hy := h1 y
    rw [one_smul] at hx hy
    rw [hx, hy]
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hann
  obtain ⟨r, hr, hr0⟩ := hnak 𝔪 h𝔪
  have hrmem : r ∈ 𝔪 := hle (Module.mem_annihilator.mpr hr0)
  have : (1 : A) ∈ 𝔪 := by
    have := 𝔪.sub_mem hrmem hr
    rwa [sub_sub_cancel] at this
  exact h𝔪.ne_top (𝔪.eq_top_of_isUnit_mem this isUnit_one)

end Modules

variable {n : ℕ}

theorem finite_homogeneousSubmodule (R : Type) [CommRing R] (d : ℕ) :
    Module.Finite R ↥(homogeneousSubmodule (Fin (n + 1)) R d) := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  haveI : Finite {x : Fin (n + 1) →₀ ℕ | x.degree = d} :=
    ((Finsupp.finite_of_degree_le d).subset fun x (hx : x.degree = d) => le_of_eq hx).to_subtype
  exact Module.Finite.of_basis (MvPolynomial.basisRestrictSupport R {x : Fin (n + 1) →₀ ℕ | x.degree = d})

theorem free_homogeneousSubmodule (R : Type) [CommRing R] (d : ℕ) :
    Module.Free R ↥(homogeneousSubmodule (Fin (n + 1)) R d) := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  exact Module.Free.of_basis (MvPolynomial.basisRestrictSupport R {x : Fin (n + 1) →₀ ℕ | x.degree = d})

private theorem _root_.HilbGenH2c.finite_piece (R : Type) [CommRing R] (J : Ideal (MvPolynomial (Fin (n + 1)) R)) (d : ℕ) :
    Module.Finite R (piece J d) := by
  haveI := finite_homogeneousSubmodule (n := n) R d
  exact Module.Finite.quotient R _

p2m_export "HilbGenH2c" "finite_piece"

theorem natCard_degree_eq (d : ℕ) : Nat.card {s : Fin (n + 1) →₀ ℕ // s.degree = d} = (n + d).choose n := by
  classical
  let e : {s : Fin (n + 1) →₀ ℕ // s.degree = d} ≃ Sym (Fin (n + 1)) d :=
    { toFun := fun s => ⟨Finsupp.toMultiset s.1, by
        have h2 := s.2
        rw [Finsupp.degree_apply] at h2
        rw [Finsupp.card_toMultiset]
        simpa [Finsupp.sum] using h2⟩
      invFun := fun t => ⟨Multiset.toFinsupp (t : Multiset (Fin (n + 1))), by
        have h1 := Finsupp.card_toMultiset (Multiset.toFinsupp (t : Multiset (Fin (n + 1))))
        rw [Multiset.toFinsupp_toMultiset] at h1
        rw [Finsupp.degree_apply]
        have h2 : (t : Multiset (Fin (n + 1))).card = d := t.2
        simpa [Finsupp.sum, h2] using h1.symm⟩
      left_inv := fun s => by
        apply Subtype.ext
        simp
      right_inv := fun t => by
        apply Subtype.ext
        simp }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Sym.card_sym_eq_choose, Fintype.card_fin,
    show n + 1 + d - 1 = n + d by omega, Nat.choose_symm_add]

theorem finrank_homogeneousSubmodule (A : Type) [CommRing A] [Nontrivial A] (d : ℕ) :
    Module.finrank A ↥(homogeneousSubmodule (Fin (n + 1)) A d) = (n + d).choose n := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  exact (Module.finrank_eq_nat_card_basis
    (MvPolynomial.basisRestrictSupport A {x : Fin (n + 1) →₀ ℕ | x.degree = d})).trans (natCard_degree_eq d)

theorem span_homogeneous (A : Type) [CommRing A] (s : Set (MvPolynomial (Fin (n + 1)) A)) (e : ℕ)
    (hs : ∀ p ∈ s, p.IsHomogeneous e) :
    ∀ p ∈ Ideal.span s, ∀ d : ℕ, homogeneousComponent d p ∈ Ideal.span s := by
  intro p hp d
  have H := Ideal.homogeneous_span (homogeneousSubmodule (Fin (n + 1)) A) s (fun x hx => ⟨e, hs x hx⟩)
  have := H d hp
  rwa [show (DirectSum.decompose (homogeneousSubmodule (Fin (n + 1)) A) p d : MvPolynomial (Fin (n + 1)) A) =
      homogeneousComponent d p from MvPolynomial.decomposition.decompose'_apply p d] at this

section Step

variable {A : Type} [CommRing A] (h : ℕ → ℕ) (P : Point A n h) (e : ℕ)

noncomputable def J' : Ideal (MvPolynomial (Fin (n + 1)) A) := Ideal.span {p | p ∈ P.I ∧ p.IsHomogeneous e}

theorem J'_le : J' h P e ≤ P.I := Ideal.span_le.mpr fun _ hp => hp.1

theorem J'_generated : ∃ s : Set (MvPolynomial (Fin (n + 1)) A), (∀ p ∈ s, p.IsHomogeneous e) ∧ J' h P e = Ideal.span s :=
  ⟨_, fun _ hp => hp.2, rfl⟩

theorem J'_homogeneous : ∀ p ∈ J' h P e, ∀ d : ℕ, homogeneousComponent d p ∈ J' h P e :=
  span_homogeneous A _ e fun _ hp => hp.2

theorem comap_J'_eq :
    Submodule.comap (homogeneousSubmodule (Fin (n + 1)) A e).subtype ((J' h P e).restrictScalars A) =
      Submodule.comap (homogeneousSubmodule (Fin (n + 1)) A e).subtype (P.I.restrictScalars A) := by
  ext q
  simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.restrictScalars_mem]
  exact ⟨fun hq => J'_le h P e hq, fun hq => Ideal.subset_span ⟨hq, q.2⟩⟩

noncomputable def pieceJ'Equiv : piece (J' h P e) e ≃ₗ[A] piece P.I e :=
  Submodule.quotEquivOfEq _ _ (comap_J'_eq h P e)

noncomputable def π : piece (J' h P e) (e + 1) →ₗ[A] piece P.I (e + 1) :=
  Submodule.mapQ _ _ LinearMap.id fun q hq => by
    simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.restrictScalars_mem, LinearMap.id_coe,
      id_eq] at hq ⊢
    exact J'_le h P e hq

theorem π_mk (q : ↥(homogeneousSubmodule (Fin (n + 1)) A (e + 1))) :
    π h P e (Submodule.Quotient.mk q) = Submodule.Quotient.mk q := rfl

theorem π_surjective : Function.Surjective (π h P e) := by
  intro y
  obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨Submodule.Quotient.mk q, rfl⟩

variable (hm : ∀ (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) →
      Module.finrank K (piece J e) = h e → Module.finrank K (piece J (e + 1)) ≤ h (e + 1))

include hm in

theorem finrank_fiber_Q₁_le (p : PrimeSpectrum A) :
    Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] piece (J' h P e) (e + 1)) ≤ h (e + 1) := by
  let κ := p.asIdeal.ResidueField
  obtain ⟨-, hpiece⟩ := AlgebraicGeometry.HilbertFunctor.exists_linearEquiv_baseChange_piece_map n A κ (J' h P e)
    (J'_homogeneous h P e)
  obtain ⟨e₁, -⟩ := hpiece (e + 1)
  obtain ⟨e₀, -⟩ := hpiece e
  rw [e₁.finrank_eq]
  refine hm κ _ ⟨MvPolynomial.map (algebraMap A κ) '' {p | p ∈ P.I ∧ p.IsHomogeneous e}, ?_, Ideal.map_span _ _⟩ ?_
  · rintro _ ⟨q, hq, rfl⟩
    exact hq.2.map _
  · rw [← e₀.finrank_eq]
    haveI := P.finite_piece e
    haveI := P.projective_piece e
    haveI : Module.Finite A (piece (J' h P e) e) := Module.Finite.equiv (pieceJ'Equiv h P e).symm
    haveI : Module.Projective A (piece (J' h P e) e) := Module.Projective.of_equiv (pieceJ'Equiv h P e).symm
    rw [← P.rankAtStalk_piece e p, ← congrFun (Module.rankAtStalk_eq_of_equiv (pieceJ'Equiv h P e)) p,
      Module.rankAtStalk_eq]

include hm in

theorem ker_π_eq_bot : LinearMap.ker (π h P e) = ⊥ := by
  haveI := P.projective_piece (e + 1)
  haveI := P.finite_piece (e + 1)
  haveI : Module.Finite A (piece (J' h P e) (e + 1)) := finite_piece A _ _
  obtain ⟨E, hE⟩ := exists_equiv_prod_ker (π h P e) (π_surjective h P e)
  haveI : Module.Finite A (LinearMap.ker (π h P e)) :=
    Module.Finite.of_surjective ((LinearMap.snd A _ _).comp E.toLinearMap) fun k => ⟨E.symm (0, k), by simp⟩
  have hfib : ∀ p : PrimeSpectrum A,
      Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] LinearMap.ker (π h P e)) = 0 := by
    intro p
    haveI : Module.Finite p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] piece (J' h P e) (e + 1)) :=
      Module.Finite.base_change A _ _
    haveI : Module.Finite p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] piece P.I (e + 1)) :=
      Module.Finite.base_change A _ _
    haveI : Module.Finite p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] LinearMap.ker (π h P e)) :=
      Module.Finite.base_change A _ _
    haveI : Module.Free p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] piece P.I (e + 1)) :=
      Module.Free.of_divisionRing _ _
    haveI : Module.Free p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] LinearMap.ker (π h P e)) :=
      Module.Free.of_divisionRing _ _
    have hsum : Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] piece (J' h P e) (e + 1)) =
        Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] piece P.I (e + 1)) +
          Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] LinearMap.ker (π h P e)) := by
      rw [(E.baseChange A p.asIdeal.ResidueField _ _ ≪≫ₗ
        TensorProduct.prodRight A p.asIdeal.ResidueField p.asIdeal.ResidueField _ _).finrank_eq, Module.finrank_prod]
    have h1 := finrank_fiber_Q₁_le h P e hm p
    have h2 : Module.finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] piece P.I (e + 1)) = h (e + 1) := by
      rw [← P.rankAtStalk_piece (e + 1) p, Module.rankAtStalk_eq]
    omega
  have hsub := subsingleton_of_finrank_fiber_eq_zero (LinearMap.ker (π h P e)) hfib
  exact Submodule.eq_bot_iff _ |>.mpr fun x hx => congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : LinearMap.ker _) 0)

include hm in

theorem mem_J'_of_mem (q : MvPolynomial (Fin (n + 1)) A) (hqI : q ∈ P.I) (hq : q.IsHomogeneous (e + 1)) :
    q ∈ J' h P e := by
  have hker := ker_π_eq_bot h P e hm
  have hzero : π h P e (Submodule.Quotient.mk ⟨q, hq⟩) = 0 := by
    rw [π_mk, Submodule.Quotient.mk_eq_zero]
    simpa using hqI
  have hmem : (Submodule.Quotient.mk ⟨q, hq⟩ : piece (J' h P e) (e + 1)) ∈ LinearMap.ker (π h P e) := hzero
  rw [hker, Submodule.mem_bot, Submodule.Quotient.mk_eq_zero] at hmem
  simpa using hmem

end Step

section Low

variable {A : Type} [CommRing A] [Nontrivial A] (h : ℕ → ℕ) (P : Point A n h) (d : ℕ)
  (hd : h d = Nat.choose (n + d) n)

include hd in
theorem eq_zero_of_mem_of_lt (q : MvPolynomial (Fin (n + 1)) A) (hqI : q ∈ P.I) (hq : q.IsHomogeneous d) : q = 0 := by
  haveI := P.projective_piece d
  haveI := P.finite_piece d
  haveI := finite_homogeneousSubmodule (n := n) A d
  haveI := free_homogeneousSubmodule (n := n) A d
  let Kd : Submodule A ↥(homogeneousSubmodule (Fin (n + 1)) A d) :=
    Submodule.comap (homogeneousSubmodule (Fin (n + 1)) A d).subtype (P.I.restrictScalars A)
  obtain ⟨E, hE⟩ := exists_equiv_prod_ker (Kd.mkQ) (Submodule.mkQ_surjective _)

  haveI : Module.Finite A (LinearMap.ker Kd.mkQ) :=
    Module.Finite.of_surjective ((LinearMap.snd A _ _).comp E.toLinearMap) fun k => ⟨E.symm (0, k), by simp⟩
  haveI : Module.Projective A (LinearMap.ker Kd.mkQ) :=
    Module.Projective.of_split (E.symm.toLinearMap.comp (LinearMap.inr A _ _))
      ((LinearMap.snd A _ _).comp E.toLinearMap) (by ext x; simp)
  have hrank : Module.rankAtStalk (R := A) (LinearMap.ker Kd.mkQ) = 0 := by
    funext p
    have h1 := congrFun (Module.rankAtStalk_eq_of_equiv
      (N := (↥(homogeneousSubmodule (Fin (n + 1)) A d) ⧸ Kd) × ↥(LinearMap.ker Kd.mkQ)) E) p
    rw [Module.rankAtStalk_prod, Pi.add_apply, Module.rankAtStalk_eq_finrank_of_free,
      finrank_homogeneousSubmodule A d] at h1
    have h2 : Module.rankAtStalk (↥(homogeneousSubmodule (Fin (n + 1)) A d) ⧸ Kd) p = (n + d).choose n :=
      (P.rankAtStalk_piece d p).trans hd
    erw [h2] at h1
    simp only [Pi.natCast_apply, Nat.cast_id] at h1
    simp only [Pi.zero_apply]
    omega
  have hsub : Subsingleton (LinearMap.ker Kd.mkQ) := Module.rankAtStalk_eq_zero_iff_subsingleton.mp hrank
  have hmem : (⟨q, hq⟩ : ↥(homogeneousSubmodule (Fin (n + 1)) A d)) ∈ LinearMap.ker Kd.mkQ := by
    rw [Submodule.ker_mkQ]
    simpa [Kd] using hqI
  have := congrArg (fun x : LinearMap.ker Kd.mkQ => ((x : ↥(homogeneousSubmodule (Fin (n + 1)) A d)) :
    MvPolynomial (Fin (n + 1)) A)) (Subsingleton.elim (⟨_, hmem⟩ : LinearMap.ker Kd.mkQ) 0)
  simpa using this

end Low

end HilbGenH2c

open HilbGenH2c in
theorem solution
    (n m : ℕ) (h : ℕ → ℕ) (h₁ : ∀ d, d < m → h d = Nat.choose (n + d) n)
    (h₂ : ∀ e, m ≤ e → ∀ (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) →
      Module.finrank K (piece J e) = h e → Module.finrank K (piece J (e + 1)) ≤ h (e + 1))
    (A : Type) [CommRing A] (P : Point A n h) :
    P.I = Ideal.span {p | p ∈ P.I ∧ p.IsHomogeneous m} := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · haveI : Subsingleton (MvPolynomial (Fin (n + 1)) A) := inferInstance
    exact Subsingleton.elim _ _
  apply le_antisymm _ (Ideal.span_le.mpr fun _ hp => hp.1)

  have hgood : ∀ d, ∀ q ∈ P.I, q.IsHomogeneous d → q ∈ Ideal.span {p | p ∈ P.I ∧ p.IsHomogeneous m} := by
    intro d
    by_cases hdm : d < m
    · intro q hqI hq
      rw [eq_zero_of_mem_of_lt h P d (h₁ d hdm) q hqI hq]
      exact Ideal.zero_mem _
    · have hmd : m ≤ d := not_lt.mp hdm
      induction d, hmd using Nat.le_induction with
      | base => exact fun q hqI hq => Ideal.subset_span ⟨hqI, hq⟩
      | succ e hme ih =>
        intro q hqI hq
        have hqJ := mem_J'_of_mem h P e (h₂ e hme) q hqI hq
        exact (Ideal.span_le.mpr fun p hp => ih (by omega) p hp.1 hp.2) hqJ
  intro p hp
  rw [← sum_homogeneousComponent p]
  exact Ideal.sum_mem _ fun d _ => hgood d _ (P.homogeneous p hp d) (homogeneousComponent_isHomogeneous d p)

end S_AlgebraicGeometry_HilbertFunctor_Point_I_eq_span_of_forall_finrank_piece_succ_le
end P2MW
export P2MW.S_AlgebraicGeometry_HilbertFunctor_Point_I_eq_span_of_forall_finrank_piece_succ_le (solution)
