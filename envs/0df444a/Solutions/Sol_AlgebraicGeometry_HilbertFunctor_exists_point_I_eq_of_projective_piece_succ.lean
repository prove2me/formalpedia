-- Prove2me | solution 1 for AlgebraicGeometry.HilbertFunctor.exists_point_I_eq_of_projective_piece_succ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/dbe42223-9b2b-50f2-9d66-36740ceb4ac8

import Mathlib
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_free_piece_of_isLocalRing_of_forall_relation_mem_span
import Theorems.Thm_MvPolynomial_relation_mem_span_of_forall_finrank_piece_succ_le
import Theorems.Thm_MvPolynomial_finrank_piece_eq_of_maximal_growth
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_of_projective_piece_succ

set_option autoImplicit false

open MvPolynomial AlgebraicGeometry.HilbertFunctor
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GotzH2a

variable {n : ℕ}

section Pieces

variable {A : Type} [CommRing A]

theorem finite_homogeneousSubmodule (A : Type) [CommRing A] (d : ℕ) :
    Module.Finite A ↥(homogeneousSubmodule (Fin (n + 1)) A d) := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  haveI : Finite {x : Fin (n + 1) →₀ ℕ | x.degree = d} :=
    ((Finsupp.finite_of_degree_le d).subset fun x (hx : x.degree = d) => le_of_eq hx).to_subtype
  exact Module.Finite.of_basis (MvPolynomial.basisRestrictSupport A {x : Fin (n + 1) →₀ ℕ | x.degree = d})

theorem free_homogeneousSubmodule (A : Type) [CommRing A] (d : ℕ) :
    Module.Free A ↥(homogeneousSubmodule (Fin (n + 1)) A d) := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  exact Module.Free.of_basis (MvPolynomial.basisRestrictSupport A {x : Fin (n + 1) →₀ ℕ | x.degree = d})

theorem finite_piece (A : Type) [CommRing A] (J : Ideal (MvPolynomial (Fin (n + 1)) A)) (d : ℕ) :
    Module.Finite A (piece J d) := by
  haveI := finite_homogeneousSubmodule (n := n) A d
  exact Module.Finite.quotient A _

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

theorem decompose_eq (q : MvPolynomial (Fin (n + 1)) A) (d : ℕ) :
    (DirectSum.decompose (homogeneousSubmodule (Fin (n + 1)) A) q d : MvPolynomial (Fin (n + 1)) A) =
      homogeneousComponent d q :=
  MvPolynomial.decomposition.decompose'_apply q d

theorem homogeneousComponent_mul_add {G : MvPolynomial (Fin (n + 1)) A} {m : ℕ} (hG : G.IsHomogeneous m)
    (a : MvPolynomial (Fin (n + 1)) A) (d : ℕ) :
    homogeneousComponent (m + d) (a * G) = homogeneousComponent d a * G := by
  have := DirectSum.coe_decompose_mul_of_right_mem_of_le (𝒜 := homogeneousSubmodule (Fin (n + 1)) A)
    (a := a) (show G ∈ homogeneousSubmodule (Fin (n + 1)) A m from hG) (Nat.le_add_right m d)
  rw [decompose_eq, decompose_eq, Nat.add_sub_cancel_left] at this
  exact this

theorem homogeneousComponent_mul_of_lt {G : MvPolynomial (Fin (n + 1)) A} {m : ℕ} (hG : G.IsHomogeneous m)
    (a : MvPolynomial (Fin (n + 1)) A) {e : ℕ} (he : e < m) :
    homogeneousComponent e (a * G) = 0 := by
  classical
  have := DirectSum.coe_decompose_mul_of_right_mem (𝒜 := homogeneousSubmodule (Fin (n + 1)) A)
    (a := a) e (show G ∈ homogeneousSubmodule (Fin (n + 1)) A m from hG)
  rw [decompose_eq, if_neg (not_le.mpr he)] at this
  exact this

theorem span_homogeneous (A : Type) [CommRing A] (s : Set (MvPolynomial (Fin (n + 1)) A)) (m : ℕ)
    (hs : ∀ p ∈ s, p.IsHomogeneous m) :
    ∀ p ∈ Ideal.span s, ∀ d : ℕ, homogeneousComponent d p ∈ Ideal.span s := by
  intro p hp d
  have H := Ideal.homogeneous_span (homogeneousSubmodule (Fin (n + 1)) A) s (fun x hx => ⟨m, hs x hx⟩)
  have := H d hp
  rwa [decompose_eq] at this

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

end Pieces

section SpanF

variable {A : Type} [CommRing A] {g m : ℕ}
  (F : Fin g → MvPolynomial (Fin (n + 1)) A) (hF : ∀ i, (F i).IsHomogeneous m)

theorem mem_span_iff (u : MvPolynomial (Fin (n + 1)) A) :
    u ∈ Ideal.span (Set.range F) ↔ ∃ a : Fin g → MvPolynomial (Fin (n + 1)) A, ∑ i, a i * F i = u :=
  Ideal.mem_span_range_iff_exists_fun

theorem sum_mul_mem (a : Fin g → MvPolynomial (Fin (n + 1)) A) :
    ∑ i, a i * F i ∈ Ideal.span (Set.range F) :=
  (mem_span_iff F _).mpr ⟨a, rfl⟩

theorem map_span_range (B : Type) [CommRing B] (φ : A →+* B) :
    (Ideal.span (Set.range F)).map (MvPolynomial.map φ) =
      Ideal.span (Set.range fun i => MvPolynomial.map φ (F i)) := by
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

include hF

theorem span_range_homogeneous :
    ∀ p ∈ Ideal.span (Set.range F), ∀ d : ℕ, homogeneousComponent d p ∈ Ideal.span (Set.range F) :=
  span_homogeneous A _ m (by rintro _ ⟨i, rfl⟩; exact hF i)

theorem span_range_generated :
    ∃ s : Set (MvPolynomial (Fin (n + 1)) A), (∀ p ∈ s, p.IsHomogeneous m) ∧
      Ideal.span (Set.range F) = Ideal.span s :=
  ⟨Set.range F, by rintro _ ⟨i, rfl⟩; exact hF i, rfl⟩

theorem homogeneousComponent_sum_mul_add (a : Fin g → MvPolynomial (Fin (n + 1)) A) (d : ℕ) :
    homogeneousComponent (m + d) (∑ i, a i * F i) = ∑ i, homogeneousComponent d (a i) * F i := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => homogeneousComponent_mul_add (hF i) (a i) d

theorem isHomogeneous_sum_mul (a : Fin g → MvPolynomial (Fin (n + 1)) A) (d : ℕ)
    (ha : ∀ i, (a i).IsHomogeneous d) : (∑ i, a i * F i).IsHomogeneous (m + d) := by
  rw [Nat.add_comm m d]
  exact IsHomogeneous.sum _ _ _ fun i _ => (ha i).mul (hF i)

theorem exists_eq_sum_of_mem (u : MvPolynomial (Fin (n + 1)) A) (hu : u ∈ Ideal.span (Set.range F)) (d : ℕ)
    (hud : u.IsHomogeneous (m + d)) :
    ∃ a : Fin g → MvPolynomial (Fin (n + 1)) A, (∀ i, (a i).IsHomogeneous d) ∧ ∑ i, a i * F i = u := by
  obtain ⟨a, rfl⟩ := (mem_span_iff F _).mp hu
  refine ⟨fun i => homogeneousComponent d (a i), fun i => homogeneousComponent_isHomogeneous _ _, ?_⟩
  rw [← homogeneousComponent_sum_mul_add F hF,
    homogeneousComponent_of_mem (show ∑ i, a i * F i ∈ homogeneousSubmodule (Fin (n + 1)) A (m + d) from hud),
    if_pos rfl]

theorem eq_zero_of_mem_of_lt (u : MvPolynomial (Fin (n + 1)) A) (hu : u ∈ Ideal.span (Set.range F)) {e : ℕ}
    (he : e < m) (hue : u.IsHomogeneous e) : u = 0 := by
  obtain ⟨a, rfl⟩ := (mem_span_iff F _).mp hu
  have : homogeneousComponent e (∑ i, a i * F i) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero fun i _ => homogeneousComponent_mul_of_lt (hF i) (a i) he
  rwa [homogeneousComponent_of_mem (show ∑ i, a i * F i ∈ homogeneousSubmodule (Fin (n + 1)) A e from hue),
    if_pos rfl] at this

theorem comap_eq_bot_of_lt {e : ℕ} (he : e < m) :
    Submodule.comap (homogeneousSubmodule (Fin (n + 1)) A e).subtype
      ((Ideal.span (Set.range F)).restrictScalars A) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  apply Subtype.ext
  exact eq_zero_of_mem_of_lt F hF x hx he x.2

noncomputable def presMap (d : ℕ) :
    (Fin g → ↥(homogeneousSubmodule (Fin (n + 1)) A d)) →ₗ[A] ↥(homogeneousSubmodule (Fin (n + 1)) A (m + d)) :=
  LinearMap.codRestrict (homogeneousSubmodule (Fin (n + 1)) A (m + d))
    (∑ i : Fin g, LinearMap.mulRight A (F i) ∘ₗ (homogeneousSubmodule (Fin (n + 1)) A d).subtype ∘ₗ
      LinearMap.proj i)
    (fun a => by
      have : (∑ i : Fin g, LinearMap.mulRight A (F i) ∘ₗ (homogeneousSubmodule (Fin (n + 1)) A d).subtype ∘ₗ
          LinearMap.proj i) a = ∑ i, (a i : MvPolynomial (Fin (n + 1)) A) * F i := by
        simp [LinearMap.sum_apply]
      rw [this]
      exact isHomogeneous_sum_mul F hF (fun i => (a i : MvPolynomial (Fin (n + 1)) A)) d (fun i => (a i).2))

theorem presMap_apply_coe (d : ℕ) (a : Fin g → ↥(homogeneousSubmodule (Fin (n + 1)) A d)) :
    (presMap F hF d a : MvPolynomial (Fin (n + 1)) A) = ∑ i, (a i : MvPolynomial (Fin (n + 1)) A) * F i := by
  simp [presMap, LinearMap.sum_apply]

theorem range_presMap (d : ℕ) :
    LinearMap.range (presMap F hF d) =
      Submodule.comap (homogeneousSubmodule (Fin (n + 1)) A (m + d)).subtype
        ((Ideal.span (Set.range F)).restrictScalars A) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    change (presMap F hF d a : MvPolynomial (Fin (n + 1)) A) ∈ Ideal.span (Set.range F)
    rw [presMap_apply_coe]
    exact sum_mul_mem F _
  · intro hx
    change (x : MvPolynomial (Fin (n + 1)) A) ∈ Ideal.span (Set.range F) at hx
    obtain ⟨a, ha, hax⟩ := exists_eq_sum_of_mem F hF x hx d x.2
    refine ⟨fun i => ⟨a i, ha i⟩, Subtype.ext ?_⟩
    rw [presMap_apply_coe]
    exact hax

theorem finitePresentation_piece (e : ℕ) : Module.FinitePresentation A (piece (Ideal.span (Set.range F)) e) := by
  haveI := finite_homogeneousSubmodule (n := n) A e
  haveI := free_homogeneousSubmodule (n := n) A e
  haveI : Module.FinitePresentation A ↥(homogeneousSubmodule (Fin (n + 1)) A e) :=
    Module.finitePresentation_of_projective A _
  refine Module.finitePresentation_of_surjective
    (Submodule.comap (homogeneousSubmodule (Fin (n + 1)) A e).subtype
      ((Ideal.span (Set.range F)).restrictScalars A)).mkQ (Submodule.mkQ_surjective _) ?_
  rw [Submodule.ker_mkQ]
  by_cases he : e < m
  · rw [comap_eq_bot_of_lt F hF he]
    exact Submodule.fg_bot
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp he)
    haveI := finite_homogeneousSubmodule (n := n) A d
    rw [← range_presMap F hF d, LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _

end SpanF

theorem finrank_piece_of_lt {g m : ℕ} (K : Type) [Field K] (G : Fin g → MvPolynomial (Fin (n + 1)) K)
    (hG : ∀ i, (G i).IsHomogeneous m) {e : ℕ} (he : e < m) :
    Module.finrank K (piece (Ideal.span (Set.range G)) e) = (n + e).choose n := by
  have hbot := comap_eq_bot_of_lt G hG he
  change Module.finrank K (↥(homogeneousSubmodule (Fin (n + 1)) K e) ⧸
    Submodule.comap (homogeneousSubmodule (Fin (n + 1)) K e).subtype ((Ideal.span (Set.range G)).restrictScalars K)) = _
  rw [hbot, (Submodule.quotEquivOfEqBot _ rfl).finrank_eq, finrank_homogeneousSubmodule]

section AtPrime

variable {A : Type} [CommRing A] {g m : ℕ} (h : ℕ → ℕ)
  (h₂ : ∀ e, m ≤ e → ∀ (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) →
      Module.finrank K (piece J e) = h e → Module.finrank K (piece J (e + 1)) ≤ h (e + 1))
  (F : Fin g → MvPolynomial (Fin (n + 1)) A) (hF : ∀ i, (F i).IsHomogeneous m)
  (hm : Module.Projective A (piece (Ideal.span (Set.range F)) m) ∧
      ∀ p : PrimeSpectrum A, Module.rankAtStalk (piece (Ideal.span (Set.range F)) m) p = h m)
  (hm₁ : Module.Projective A (piece (Ideal.span (Set.range F)) (m + 1)) ∧
      ∀ p : PrimeSpectrum A, Module.rankAtStalk (piece (Ideal.span (Set.range F)) (m + 1)) p = h (m + 1))

include hF in

theorem finrank_piece_residueField (p : PrimeSpectrum A) (d : ℕ)
    (hproj : Module.Projective A (piece (Ideal.span (Set.range F)) d)) :
    Module.finrank p.asIdeal.ResidueField
        (piece (Ideal.span (Set.range fun i => MvPolynomial.map (algebraMap A p.asIdeal.ResidueField) (F i))) d) =
      Module.rankAtStalk (piece (Ideal.span (Set.range F)) d) p := by
  haveI := hproj
  haveI := finite_piece A (Ideal.span (Set.range F)) d
  obtain ⟨-, hbc⟩ := AlgebraicGeometry.HilbertFunctor.exists_linearEquiv_baseChange_piece_map n A
    p.asIdeal.ResidueField (Ideal.span (Set.range F)) (span_range_homogeneous F hF)
  obtain ⟨e, -⟩ := hbc d
  rw [← map_span_range F, ← e.finrank_eq, Module.rankAtStalk_eq]

include h₂ hF hm hm₁ in

theorem free_piece_atPrime (p : PrimeSpectrum A) (e : ℕ) :
    Module.Free (Localization.AtPrime p.asIdeal)
      (piece (Ideal.span (Set.range fun i =>
        MvPolynomial.map (algebraMap A (Localization.AtPrime p.asIdeal)) (F i))) e) := by
  set Ap := Localization.AtPrime p.asIdeal with hAp
  set Fp : Fin g → MvPolynomial (Fin (n + 1)) Ap := fun i => MvPolynomial.map (algebraMap A Ap) (F i) with hFp
  have hFp' : ∀ i, (Fp i).IsHomogeneous m := fun i => (hF i).map _
  obtain ⟨-, hbc⟩ := AlgebraicGeometry.HilbertFunctor.exists_linearEquiv_baseChange_piece_map n A Ap
    (Ideal.span (Set.range F)) (span_range_homogeneous F hF)

  have hprojp : ∀ d, Module.Projective A (piece (Ideal.span (Set.range F)) d) →
      Module.Projective Ap (piece (Ideal.span (Set.range Fp)) d) := by
    intro d hd
    haveI := hd
    obtain ⟨e, -⟩ := hbc d
    haveI : Module.Projective Ap (Ap ⊗[A] piece (Ideal.span (Set.range F)) d) := Module.Projective.tensorProduct
    have := Module.Projective.of_equiv e
    rwa [map_span_range F] at this
  have h0 := hprojp m hm.1
  have h1 := hprojp (m + 1) hm₁.1

  set K := IsLocalRing.ResidueField Ap with hK
  set Fk : Fin g → MvPolynomial (Fin (n + 1)) K := fun i => MvPolynomial.map (IsLocalRing.residue Ap) (Fp i)
    with hFk
  have hFk' : ∀ i, (Fk i).IsHomogeneous m := fun i => (hFp' i).map _
  have hFk_eq : Fk = fun i => MvPolynomial.map (algebraMap A K) (F i) := by
    funext i
    simp only [hFk, hFp, MvPolynomial.map_map]
    congr 1

  have hdim : ∀ d, Module.Projective A (piece (Ideal.span (Set.range F)) d) →
      (∀ q : PrimeSpectrum A, Module.rankAtStalk (piece (Ideal.span (Set.range F)) d) q = h d) →
      Module.finrank K (piece (Ideal.span (Set.range Fk)) d) = h d := by
    intro d hd hr
    rw [hFk_eq]
    exact (finrank_piece_residueField F hF p d hd).trans (hr p)
  have hKm := hdim m hm.1 hm.2
  have hKm₁ := hdim (m + 1) hm₁.1 hm₁.2

  have hrel : ∀ (d : ℕ) (c : Fin g → MvPolynomial (Fin (n + 1)) K), (∀ i, (c i).IsHomogeneous d) →
      ∑ i, c i * MvPolynomial.map (IsLocalRing.residue Ap) (Fp i) = 0 →
      c ∈ Submodule.span (MvPolynomial (Fin (n + 1)) K)
        {l : Fin g → MvPolynomial (Fin (n + 1)) K |
          (∃ d' ≤ 1, ∀ i, (l i).IsHomogeneous d') ∧
          ∑ i, l i * MvPolynomial.map (IsLocalRing.residue Ap) (Fp i) = 0} := by
    intro d c hc hcF
    refine MvPolynomial.relation_mem_span_of_forall_finrank_piece_succ_le n m g K Fk hFk' ?_ d c hc hcF
    intro J' hJ' hJ'm
    rw [hKm] at hJ'm
    rw [hKm₁]
    exact h₂ m le_rfl K J' hJ' hJ'm
  exact AlgebraicGeometry.HilbertFunctor.free_piece_of_isLocalRing_of_forall_relation_mem_span n m g Ap Fp hFp'
    h0 h1 hrel e

end AtPrime

end GotzH2a

open GotzH2a in
theorem solution
    (n m : ℕ) (h : ℕ → ℕ) (h₁ : ∀ d, d < m → h d = Nat.choose (n + d) n)
    (h₂ : ∀ e, m ≤ e → ∀ (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) →
      Module.finrank K (piece J e) = h e → Module.finrank K (piece J (e + 1)) ≤ h (e + 1))
    (h₃ : ∀ e, m ≤ e → ∃ (K : Type) (_ : Field K) (J : Ideal (MvPolynomial (Fin (n + 1)) K)),
      (∃ s : Set (MvPolynomial (Fin (n + 1)) K), (∀ p ∈ s, p.IsHomogeneous e) ∧ J = Ideal.span s) ∧
      Module.finrank K (piece J e) = h e ∧ Module.finrank K (piece J (e + 1)) = h (e + 1))
    (A : Type) [CommRing A] (I : Ideal (MvPolynomial (Fin (n + 1)) A))
    (hI : ∃ s : Set (MvPolynomial (Fin (n + 1)) A), (∀ p ∈ s, p.IsHomogeneous m) ∧ I = Ideal.span s)
    (hm : Module.Projective A (piece I m) ∧
      ∀ p : PrimeSpectrum A, Module.rankAtStalk (piece I m) p = h m)
    (hm₁ : Module.Projective A (piece I (m + 1)) ∧
      ∀ p : PrimeSpectrum A, Module.rankAtStalk (piece I (m + 1)) p = h (m + 1)) :
    ∃ P : Point A n h, P.I = I := by
  classical
  obtain ⟨s, hs, hIs⟩ := hI

  obtain ⟨g, F, hF, hIF⟩ : ∃ (g : ℕ) (F : Fin g → MvPolynomial (Fin (n + 1)) A),
      (∀ i, (F i).IsHomogeneous m) ∧ Ideal.span (Set.range F) = I := by
    haveI := hm.1
    haveI := finite_homogeneousSubmodule (n := n) A m
    let Km : Submodule A ↥(homogeneousSubmodule (Fin (n + 1)) A m) :=
      Submodule.comap (homogeneousSubmodule (Fin (n + 1)) A m).subtype (I.restrictScalars A)
    obtain ⟨E, -⟩ := exists_equiv_prod_ker Km.mkQ (Submodule.mkQ_surjective _)
    haveI : Module.Finite A (LinearMap.ker Km.mkQ) :=
      Module.Finite.of_surjective ((LinearMap.snd A _ _).comp E.toLinearMap) fun k => ⟨E.symm (0, k), by simp⟩
    obtain ⟨g, v, hv⟩ := Module.Finite.exists_fin (R := A) (M := ↥(LinearMap.ker Km.mkQ))
    have hvI : ∀ i, (((v i : ↥(LinearMap.ker Km.mkQ)) : ↥(homogeneousSubmodule (Fin (n + 1)) A m)) :
        MvPolynomial (Fin (n + 1)) A) ∈ I := by
      intro i
      have h1 : ((v i : ↥(LinearMap.ker Km.mkQ)) : ↥(homogeneousSubmodule (Fin (n + 1)) A m)) ∈ Km :=
        (Submodule.Quotient.mk_eq_zero Km).mp (LinearMap.mem_ker.mp (v i).2)
      exact h1
    refine ⟨g, fun i => (((v i : ↥(LinearMap.ker Km.mkQ)) : ↥(homogeneousSubmodule (Fin (n + 1)) A m)) :
        MvPolynomial (Fin (n + 1)) A), fun i => ((v i : ↥(LinearMap.ker Km.mkQ)) :
        ↥(homogeneousSubmodule (Fin (n + 1)) A m)).2, ?_⟩
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hvI i
    · rw [hIs, Ideal.span_le]
      intro q hq
      have hqI : q ∈ I := hIs ▸ Ideal.subset_span hq
      have hqKm : (⟨q, hs q hq⟩ : ↥(homogeneousSubmodule (Fin (n + 1)) A m)) ∈ LinearMap.ker Km.mkQ :=
        LinearMap.mem_ker.mpr ((Submodule.Quotient.mk_eq_zero Km).mpr
          (show ((⟨q, hs q hq⟩ : ↥(homogeneousSubmodule (Fin (n + 1)) A m)) : MvPolynomial (Fin (n + 1)) A) ∈ I
            from hqI))
      have hqK : (⟨⟨q, hs q hq⟩, hqKm⟩ : ↥(LinearMap.ker Km.mkQ)) ∈ Submodule.span A (Set.range v) := by
        rw [hv]; exact Submodule.mem_top

      let ψ : ↥(LinearMap.ker Km.mkQ) →ₗ[A] MvPolynomial (Fin (n + 1)) A :=
        (homogeneousSubmodule (Fin (n + 1)) A m).subtype ∘ₗ (LinearMap.ker Km.mkQ).subtype
      have hq' : q ∈ Submodule.span A (Set.range fun i => ψ (v i)) := by
        have := Submodule.mem_map_of_mem (f := ψ) hqK
        rw [Submodule.map_span, ← Set.range_comp] at this
        exact this
      exact Submodule.span_le_restrictScalars A (MvPolynomial (Fin (n + 1)) A) _ hq'
  subst hIF

  have hproj : ∀ d, Module.Projective A (piece (Ideal.span (Set.range F)) d) := by
    intro d
    haveI := finitePresentation_piece F hF d
    refine Module.projective_of_localization_maximal fun P hP => ?_
    let p : PrimeSpectrum A := ⟨P, hP.isPrime⟩
    have hfree := free_piece_atPrime h h₂ F hF hm hm₁ p d
    rw [← map_span_range F] at hfree
    haveI := hfree
    obtain ⟨-, hbc⟩ := AlgebraicGeometry.HilbertFunctor.exists_linearEquiv_baseChange_piece_map n A
      (Localization.AtPrime P) (Ideal.span (Set.range F)) (span_range_homogeneous F hF)
    obtain ⟨e, -⟩ := hbc d
    exact Module.Projective.of_equiv
      ((LocalizedModule.equivTensorProduct P.primeCompl (piece (Ideal.span (Set.range F)) d)).trans e).symm

  have hrank : ∀ (d : ℕ) (p : PrimeSpectrum A), Module.rankAtStalk (piece (Ideal.span (Set.range F)) d) p = h d := by
    intro d p
    rw [← finrank_piece_residueField F hF p d (hproj d)]
    set K := p.asIdeal.ResidueField
    set Fk : Fin g → MvPolynomial (Fin (n + 1)) K := fun i => MvPolynomial.map (algebraMap A K) (F i)
    have hFk : ∀ i, (Fk i).IsHomogeneous m := fun i => (hF i).map _
    by_cases hd : d < m
    · rw [finrank_piece_of_lt K Fk hFk hd, h₁ d hd]
    · have hKm : Module.finrank K (piece (Ideal.span (Set.range Fk)) m) = h m :=
        (finrank_piece_residueField F hF p m (hproj m)).trans (hm.2 p)
      have hKm₁ : Module.finrank K (piece (Ideal.span (Set.range Fk)) (m + 1)) = h (m + 1) :=
        (finrank_piece_residueField F hF p (m + 1) (hproj (m + 1))).trans (hm₁.2 p)
      exact MvPolynomial.finrank_piece_eq_of_maximal_growth n m h h₂ h₃ K (Ideal.span (Set.range Fk))
        (span_range_generated Fk hFk) hKm hKm₁ d (not_lt.mp hd)
  exact ⟨{ I := Ideal.span (Set.range F)
           homogeneous := span_range_homogeneous F hF
           finite_piece := fun d => finite_piece A _ d
           projective_piece := hproj
           rankAtStalk_piece := hrank }, rfl⟩

end S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_of_projective_piece_succ
end P2MW
export P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_of_projective_piece_succ (solution)
