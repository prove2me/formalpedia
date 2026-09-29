-- Prove2me | solution 1 for AlgebraicGeometry.HilbertFunctor.exists_point_I_eq_span_of_forall_surjective_of_forall_projective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/5476ebfd-f1d5-51e2-803b-5e1fe7ae7e9d

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_span_of_forall_surjective_of_forall_projective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct AlgebraicGeometry.HilbertFunctor

attribute [local instance] MvPolynomial.gradedAlgebra

namespace K4DSOL

variable {A : Type u} [CommRing A] {n : ℕ}

theorem finite_homogeneousSubmodule (d : ℕ) :
    Module.Finite A ↥(homogeneousSubmodule (Fin (n + 1)) A d) := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  haveI : Finite {x : Fin (n + 1) →₀ ℕ | x.degree = d} :=
    ((Finsupp.finite_of_degree_le d).subset fun x (hx : x.degree = d) => le_of_eq hx).to_subtype
  exact Module.Finite.of_basis (MvPolynomial.basisRestrictSupport A {x : Fin (n + 1) →₀ ℕ | x.degree = d})

theorem free_homogeneousSubmodule (d : ℕ) :
    Module.Free A ↥(homogeneousSubmodule (Fin (n + 1)) A d) := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  exact Module.Free.of_basis (MvPolynomial.basisRestrictSupport A {x : Fin (n + 1) →₀ ℕ | x.degree = d})

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

theorem finrank_homogeneousSubmodule [Nontrivial A] (d : ℕ) :
    Module.finrank A ↥(homogeneousSubmodule (Fin (n + 1)) A d) = (n + d).choose n := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  exact (Module.finrank_eq_nat_card_basis
    (MvPolynomial.basisRestrictSupport A {x : Fin (n + 1) →₀ ℕ | x.degree = d})).trans (natCard_degree_eq d)

theorem coe_decompose (φ : MvPolynomial (Fin (n + 1)) A) (i : ℕ) :
    ((DirectSum.decompose (homogeneousSubmodule (Fin (n + 1)) A) φ) i : MvPolynomial (Fin (n + 1)) A) =
      homogeneousComponent i φ :=
  MvPolynomial.decomposition.decompose'_apply φ i

theorem homogeneousComponent_mul_of_mem_right {e : ℕ} (a : MvPolynomial (Fin (n + 1)) A)
    {g : MvPolynomial (Fin (n + 1)) A} (hg : g ∈ homogeneousSubmodule (Fin (n + 1)) A e) (d : ℕ) :
    homogeneousComponent d (a * g) = if e ≤ d then homogeneousComponent (d - e) a * g else 0 := by
  classical
  have h := DirectSum.coe_decompose_mul_of_right_mem (homogeneousSubmodule (Fin (n + 1)) A) (a := a) d hg
  simpa only [coe_decompose] using h

theorem exists_finset_sum_mul_eq (J₀ : Set (MvPolynomial (Fin (n + 1)) A))
    (hJ₀ : ∀ G ∈ J₀, ∃ e : ℕ, G.IsHomogeneous e)
    {d : ℕ} {F : MvPolynomial (Fin (n + 1)) A} (hF : F.IsHomogeneous d) (hFJ : F ∈ Ideal.span J₀) :
    ∃ (s : Finset (MvPolynomial (Fin (n + 1)) A)) (e : MvPolynomial (Fin (n + 1)) A → ℕ)
      (c : MvPolynomial (Fin (n + 1)) A → MvPolynomial (Fin (n + 1)) A),
      ↑s ⊆ J₀ ∧
      (∀ G ∈ s, e G ≤ d ∧ G.IsHomogeneous (e G) ∧ (c G).IsHomogeneous (d - e G)) ∧
      F = ∑ G ∈ s, c G * G := by
  classical
  obtain ⟨a, t, ht, -, hsum⟩ := Submodule.mem_span_iff_exists_finset_subset.mp hFJ
  have hdeg : ∀ G : MvPolynomial (Fin (n + 1)) A, ∃ e : ℕ, G ∈ J₀ → G.IsHomogeneous e := by
    intro G
    by_cases hG : G ∈ J₀
    · obtain ⟨e, he⟩ := hJ₀ G hG; exact ⟨e, fun _ => he⟩
    · exact ⟨0, fun h => (hG h).elim⟩
  choose e he using hdeg
  refine ⟨t.filter (fun G => e G ≤ d), e, fun G => homogeneousComponent (d - e G) (a G), ?_, ?_, ?_⟩
  · intro G hG
    exact ht (Finset.mem_filter.mp hG).1
  · intro G hG
    obtain ⟨hGt, hGe⟩ := Finset.mem_filter.mp hG
    exact ⟨hGe, he G (ht hGt), homogeneousComponent_isHomogeneous _ _⟩
  · have hFd : homogeneousComponent d F = F := by
      rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule d F).mpr hF), if_pos rfl]
    rw [Finset.sum_filter, ← hFd, ← hsum, map_sum]
    refine Finset.sum_congr rfl fun G hG => ?_
    rw [smul_eq_mul,
      homogeneousComponent_mul_of_mem_right (a G) ((mem_homogeneousSubmodule (e G) G).mpr (he G (ht hG))) d]

end K4DSOL

open K4DSOL in

theorem solution
    (n m : ℕ) (A : Type u) [CommRing A] (h : ℕ → ℕ)
    (hlow : ∀ d : ℕ, d < m → h d = Nat.choose (n + d) n)
    (N : ℕ → Type u) [∀ d, AddCommGroup (N d)] [∀ d, Module A (N d)]
    (Θ : ∀ d : ℕ, ↥(MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A d) →ₗ[A] N d)
    (hfin : ∀ d : ℕ, m ≤ d → Module.Finite A (N d))
    (hproj : ∀ d : ℕ, m ≤ d → Module.Projective A (N d))
    (hrank : ∀ d : ℕ, m ≤ d → ∀ 𝔮 : PrimeSpectrum A, Module.rankAtStalk (N d) 𝔮 = h d)
    (hsurj : ∀ d : ℕ, m ≤ d → Function.Surjective (Θ d))
    (hmul : ∀ d : ℕ, m ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d)
      (e : ℕ) (G : MvPolynomial (Fin (n + 1)) A) (hG : G.IsHomogeneous e),
      Θ d ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩ = 0 →
        Θ (e + d) ⟨G * F, (MvPolynomial.mem_homogeneousSubmodule (e + d) (G * F)).mpr (hG.mul hF)⟩ = 0) :
    ∃ p : Point A n h,
      p.I = Ideal.span {F : MvPolynomial (Fin (n + 1)) A | ∃ (d : ℕ) (hF : F.IsHomogeneous d), m ≤ d ∧
        Θ d ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩ = 0} := by
  classical

  have hΘ_transport : ∀ (a b : ℕ) (hab : a = b) (x : ↥(homogeneousSubmodule (Fin (n + 1)) A a))
      (y : ↥(homogeneousSubmodule (Fin (n + 1)) A b)),
      (x : MvPolynomial (Fin (n + 1)) A) = y → Θ a x = 0 → Θ b y = 0 := by
    rintro a b rfl x y hxy hx
    rw [Subtype.ext hxy] at hx
    exact hx

  set V : Set (MvPolynomial (Fin (n + 1)) A) := {F : MvPolynomial (Fin (n + 1)) A | ∃ (d : ℕ) (hF : F.IsHomogeneous d),
      m ≤ d ∧ Θ d ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩ = 0} with hV
  have hVhom : ∀ G ∈ V, ∃ e : ℕ, G.IsHomogeneous e := fun G ⟨d, hG, _, _⟩ => ⟨d, hG⟩
  have hIhom : (Ideal.span V).IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) A) :=
    Ideal.homogeneous_span _ V fun G ⟨d, hG, _, _⟩ => ⟨d, (mem_homogeneousSubmodule d G).mpr hG⟩

  have key : ∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d), F ∈ Ideal.span V →
      (m ≤ d → Θ d ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩ = 0) ∧ (d < m → F = 0) := by
    intro d F hF hFI
    obtain ⟨s, e, c, hs, hprop, hsum⟩ := exists_finset_sum_mul_eq V hVhom hF hFI

    have hgen : ∀ (G : MvPolynomial (Fin (n + 1)) A) (hG : G ∈ s), G ≠ 0 →
        m ≤ e G ∧ Θ (e G) ⟨G, (MvPolynomial.mem_homogeneousSubmodule (e G) G).mpr (hprop G hG).2.1⟩ = 0 := by
      intro G hG hG0
      obtain ⟨dG, hGh, hmdG, hΘG⟩ := hs hG
      have hed : dG = e G := hGh.inj_right (hprop G hG).2.1 hG0
      subst hed
      exact ⟨hmdG, hΘG⟩
    constructor
    · intro hmd
      have hmemd : ∀ G ∈ s, c G * G ∈ homogeneousSubmodule (Fin (n + 1)) A d := fun G hG =>
        (MvPolynomial.mem_homogeneousSubmodule d (c G * G)).mpr (by
          have := (hprop G hG).2.2.mul (hprop G hG).2.1
          rwa [Nat.sub_add_cancel (hprop G hG).1] at this)
      have hterm : ∀ (G : MvPolynomial (Fin (n + 1)) A) (hG : G ∈ s), Θ d ⟨c G * G, hmemd G hG⟩ = 0 := by
        intro G hG
        by_cases hG0 : G = 0
        · have h0 : (⟨c G * G, hmemd G hG⟩ : ↥(homogeneousSubmodule (Fin (n + 1)) A d)) = 0 :=
            Subtype.ext (by simp [hG0])
          rw [h0, map_zero]
        · obtain ⟨hmeG, hΘG⟩ := hgen G hG hG0
          have h1 := hmul (e G) hmeG G (hprop G hG).2.1 (d - e G) (c G) (hprop G hG).2.2 hΘG
          exact hΘ_transport _ _ (Nat.sub_add_cancel (hprop G hG).1) _ _ rfl h1
      have hFsub : (⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩ :
          ↥(homogeneousSubmodule (Fin (n + 1)) A d)) = ∑ G ∈ s.attach, ⟨c G.1 * G.1, hmemd G.1 G.2⟩ := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        calc F = ∑ G ∈ s, c G * G := hsum
          _ = ∑ G ∈ s.attach, c G.1 * G.1 := (Finset.sum_attach s (fun G => c G * G)).symm
          _ = _ := rfl
      rw [hFsub, map_sum]
      exact Finset.sum_eq_zero fun G _ => hterm G.1 G.2
    · intro hdm
      rw [hsum]
      refine Finset.sum_eq_zero fun G hG => ?_
      by_cases hG0 : G = 0
      · rw [hG0, mul_zero]
      · exfalso
        have := (hgen G hG hG0).1
        have := (hprop G hG).1
        omega

  have hcomap_ge : ∀ d : ℕ, m ≤ d →
      Submodule.comap (homogeneousSubmodule (Fin (n + 1)) A d).subtype ((Ideal.span V).restrictScalars A) =
        LinearMap.ker (Θ d) := by
    intro d hd
    ext ⟨F, hF⟩
    have hF' : F.IsHomogeneous d := (MvPolynomial.mem_homogeneousSubmodule d F).mp hF
    simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.restrictScalars_mem, LinearMap.mem_ker]
    constructor
    · intro hFI; exact (key d F hF' hFI).1 hd
    · intro h0; exact Ideal.subset_span ⟨d, hF', hd, h0⟩
  have hcomap_lt : ∀ d : ℕ, d < m →
      Submodule.comap (homogeneousSubmodule (Fin (n + 1)) A d).subtype ((Ideal.span V).restrictScalars A) = ⊥ := by
    intro d hd
    rw [eq_bot_iff]
    rintro ⟨F, hF⟩ hFI
    have hF' : F.IsHomogeneous d := (MvPolynomial.mem_homogeneousSubmodule d F).mp hF
    simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.restrictScalars_mem] at hFI
    rw [Submodule.mem_bot]
    exact Subtype.ext ((key d F hF' hFI).2 hd)
  have e_ge : ∀ d : ℕ, m ≤ d → Nonempty (piece (Ideal.span V) d ≃ₗ[A] N d) := fun d hd =>
    ⟨(Submodule.quotEquivOfEq _ _ (hcomap_ge d hd)).trans ((Θ d).quotKerEquivOfSurjective (hsurj d hd))⟩
  have e_lt : ∀ d : ℕ, d < m →
      Nonempty (piece (Ideal.span V) d ≃ₗ[A] ↥(homogeneousSubmodule (Fin (n + 1)) A d)) := fun d hd =>
    ⟨Submodule.quotEquivOfEqBot _ (hcomap_lt d hd)⟩
  refine ⟨{ I := Ideal.span V
            homogeneous := fun p hp d => by
              have := hIhom d hp
              rwa [coe_decompose] at this
            finite_piece := fun d => ?_
            projective_piece := fun d => ?_
            rankAtStalk_piece := fun d 𝔮 => ?_ }, rfl⟩
  · rcases Nat.lt_or_ge d m with hd | hd
    · obtain ⟨e⟩ := e_lt d hd
      haveI := finite_homogeneousSubmodule (A := A) (n := n) d
      exact Module.Finite.equiv e.symm
    · obtain ⟨e⟩ := e_ge d hd
      haveI := hfin d hd
      exact Module.Finite.equiv e.symm
  · rcases Nat.lt_or_ge d m with hd | hd
    · obtain ⟨e⟩ := e_lt d hd
      haveI := free_homogeneousSubmodule (A := A) (n := n) d
      exact Module.Projective.of_equiv e.symm
    · obtain ⟨e⟩ := e_ge d hd
      haveI := hproj d hd
      exact Module.Projective.of_equiv e.symm
  · rcases Nat.lt_or_ge d m with hd | hd
    · obtain ⟨e⟩ := e_lt d hd
      haveI : Nontrivial A := ⟨⟨1, 0, fun h10 => 𝔮.2.ne_top
        ((Ideal.eq_top_iff_one _).mpr (h10.symm ▸ 𝔮.1.zero_mem))⟩⟩
      haveI := free_homogeneousSubmodule (A := A) (n := n) d
      rw [congrFun (Module.rankAtStalk_eq_of_equiv e) 𝔮,
        congrFun (Module.rankAtStalk_eq_finrank_of_free (R := A)
          (M := ↥(homogeneousSubmodule (Fin (n + 1)) A d))) 𝔮,
        finrank_homogeneousSubmodule, hlow d hd]
      simp only [Pi.natCast_apply, Nat.cast_id]
    · obtain ⟨e⟩ := e_ge d hd
      rw [congrFun (Module.rankAtStalk_eq_of_equiv e) 𝔮]
      exact hrank d hd 𝔮

end S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_span_of_forall_surjective_of_forall_projective
end P2MW
export P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_span_of_forall_surjective_of_forall_projective (solution)
