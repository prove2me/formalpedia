-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.mem_span_sup_linearForm_iff_forall_app_eq_zero_of_maximal_growth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/5e58655e-08f5-5a5f-80c9-282a205f554c

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_Nat_MacaulayPow
import Theorems.Thm_MvPolynomial_exists_finset_sum_mul_eq_of_isHomogeneous_of_mem_span
import Theorems.Thm_AlgebraicGeometry_ProjSpace_awayToSection_mk_mem_span_iff_exists_X_pow_mul_mem
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_idealSheafData_ideal_basicOpen_eq_span
import Theorems.Thm_AlgebraicGeometry_ProjSpace_eq_ker_of_ideal_basicOpen_eq_span_of_isClosedImmersion
import Theorems.Thm_MvPolynomial_mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ProjSpace_mem_span_sup_linearForm_iff_forall_app_eq_zero_of_maximal_growth

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial AlgebraicGeometry.HilbertFunctor

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RM2CSOL

section ChartIdeal

variable {A : Type} [CommRing A] {n : ℕ}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A

def xpow (i : Fin (n + 1)) (d : ℕ) : ↥(homogeneousSubmodule (Fin (n + 1)) A d) :=
  ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩

def frac (i : Fin (n + 1)) (d : ℕ) (F : ↥(homogeneousSubmodule (Fin (n + 1)) A d)) :
    HomogeneousLocalization.Away 𝒜 (MvPolynomial.X i) :=
  HomogeneousLocalization.mk
    { deg := d
      num := F
      den := xpow (A := A) i d
      den_mem := ⟨d, rfl⟩ }

theorem frac_zero (i : Fin (n + 1)) (d : ℕ) : frac (A := A) i d 0 = 0 := by
  apply HomogeneousLocalization.val_injective
  simp only [frac, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_zero, Submodule.coe_zero]
  exact Localization.mk_zero _

theorem frac_add (i : Fin (n + 1)) (d : ℕ) (F G : ↥(homogeneousSubmodule (Fin (n + 1)) A d)) :
    frac i d (F + G) = frac i d F + frac i d G := by
  apply HomogeneousLocalization.val_injective
  simp only [frac, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_add, Submodule.coe_add]
  rw [Localization.add_mk_self]

theorem frac_mul (i : Fin (n + 1)) (e d : ℕ) (G : ↥(homogeneousSubmodule (Fin (n + 1)) A e))
    (F : ↥(homogeneousSubmodule (Fin (n + 1)) A d)) :
    frac i (e + d) ⟨(G : MvPolynomial (Fin (n + 1)) A) * (F : MvPolynomial (Fin (n + 1)) A),
      SetLike.mul_mem_graded G.2 F.2⟩ = frac i e G * frac i d F := by
  apply HomogeneousLocalization.val_injective
  simp only [frac, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mul]
  rw [Localization.mk_mul]
  congr 1
  ext
  simp [xpow, pow_add]

def comp (d : ℕ) (p : MvPolynomial (Fin (n + 1)) A) : ↥(homogeneousSubmodule (Fin (n + 1)) A d) :=
  ⟨homogeneousComponent d p, homogeneousComponent_mem d p⟩

theorem comp_zero (d : ℕ) : comp (A := A) (n := n) d 0 = 0 := Subtype.ext (by simp [comp])

theorem comp_add (d : ℕ) (p q : MvPolynomial (Fin (n + 1)) A) : comp d (p + q) = comp d p + comp d q :=
  Subtype.ext (by simp [comp])

theorem coe_decompose (φ : MvPolynomial (Fin (n + 1)) A) (i : ℕ) :
    ((DirectSum.decompose 𝒜 φ) i : MvPolynomial (Fin (n + 1)) A) = homogeneousComponent i φ :=
  MvPolynomial.decomposition.decompose'_apply φ i

theorem homogeneousComponent_mul_of_mem_right {e : ℕ} (a : MvPolynomial (Fin (n + 1)) A)
    {g : MvPolynomial (Fin (n + 1)) A} (hg : g ∈ homogeneousSubmodule (Fin (n + 1)) A e) (d : ℕ) :
    homogeneousComponent d (a * g) = if e ≤ d then homogeneousComponent (d - e) a * g else 0 := by
  have h := DirectSum.coe_decompose_mul_of_right_mem 𝒜 (a := a) d hg
  simpa only [coe_decompose] using h

theorem comp_of_mem {e : ℕ} {F : MvPolynomial (Fin (n + 1)) A}
    (hF : F ∈ homogeneousSubmodule (Fin (n + 1)) A e) (d : ℕ) :
    comp d F = if h : d = e then ⟨F, h ▸ hF⟩ else 0 := by
  apply Subtype.ext
  simp only [comp, homogeneousComponent_of_mem hF]
  split_ifs <;> rfl

def fcHom (i : Fin (n + 1)) (d : ℕ) :
    MvPolynomial (Fin (n + 1)) A →+ HomogeneousLocalization.Away 𝒜 (MvPolynomial.X i) where
  toFun p := frac i d (comp d p)
  map_zero' := by simp only [comp_zero, frac_zero]
  map_add' p q := by simp only [comp_add, frac_add]

theorem fcHom_apply (i : Fin (n + 1)) (d : ℕ) (p : MvPolynomial (Fin (n + 1)) A) :
    fcHom (A := A) i d p = frac i d (comp d p) := rfl

theorem fcHom_mul_of_mem (i : Fin (n + 1)) (d e : ℕ) (a : MvPolynomial (Fin (n + 1)) A)
    {g : MvPolynomial (Fin (n + 1)) A} (hg : g ∈ homogeneousSubmodule (Fin (n + 1)) A e) :
    fcHom (A := A) i d (a * g) = if e ≤ d then fcHom (A := A) i (d - e) a * frac i e ⟨g, hg⟩ else 0 := by
  rcases Nat.lt_or_ge d e with hde | hed
  · rw [if_neg (not_le.mpr hde), fcHom_apply]
    have h0 : comp d (a * g) = 0 := Subtype.ext (by
      simp only [comp, homogeneousComponent_mul_of_mem_right a hg d, if_neg (not_le.mpr hde),
        Submodule.coe_zero])
    rw [h0, frac_zero]
  · obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le' hed
    rw [if_pos hed, fcHom_apply, fcHom_apply, Nat.add_sub_cancel]
    have h1 : comp (d' + e) (a * g) =
        ⟨(comp d' a : MvPolynomial (Fin (n + 1)) A) * ((⟨g, hg⟩ : ↥(𝒜 e)) : MvPolynomial (Fin (n + 1)) A),
          SetLike.mul_mem_graded (comp d' a).2 hg⟩ := Subtype.ext (by
      simp only [comp, homogeneousComponent_mul_of_mem_right a hg (d' + e), if_pos hed,
        Nat.add_sub_cancel])
    rw [h1, frac_mul]

theorem fg_span_chart (I : Ideal (MvPolynomial (Fin (n + 1)) A))
    (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) (hfg : I.FG) (i : Fin (n + 1)) :
    (Ideal.span { s | ∃ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d),
          F ∈ I ∧
          s = (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
              (HomogeneousLocalization.mk
                { deg := d
                  num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                  den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                  den_mem := ⟨d, rfl⟩ }) }).FG := by
  classical
  obtain ⟨s, hs⟩ := hfg

  set aTS := (Proj.awayToSection 𝒜 (MvPolynomial.X i)).hom with haTS

  let ι := Σ g : ↥s, Fin (g.1.totalDegree + 1)
  let w : ι → HomogeneousLocalization.Away 𝒜 (MvPolynomial.X i) := fun q => frac i q.2 (comp q.2 q.1.1)
  have hsI : ∀ g ∈ s, g ∈ I := fun g hg => hs ▸ Ideal.subset_span hg

  have key : ∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A), F ∈ I →
      fcHom (A := A) i d F ∈ Ideal.span (Set.range w) := by
    intro d F hF
    have hF' : F ∈ Ideal.span (Set.range (Subtype.val : ↥s → MvPolynomial (Fin (n + 1)) A)) := by
      have : Set.range (Subtype.val : ↥s → MvPolynomial (Fin (n + 1)) A) = ↑s := by
        ext x; simp
      rw [this, hs]; exact hF
    obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hF'
    rw [map_sum]
    refine Submodule.sum_mem _ fun g _ => ?_
    have hsplit : c g * (g : MvPolynomial (Fin (n + 1)) A) =
        ∑ e ∈ Finset.range ((g : MvPolynomial (Fin (n + 1)) A).totalDegree + 1),
          c g * homogeneousComponent e (g : MvPolynomial (Fin (n + 1)) A) := by
      conv_lhs => rw [← sum_homogeneousComponent (g : MvPolynomial (Fin (n + 1)) A)]
      rw [Finset.mul_sum]
    rw [hsplit, map_sum]
    refine Submodule.sum_mem _ fun e he => ?_
    rw [fcHom_mul_of_mem i d e (c g) (homogeneousComponent_mem e (g : MvPolynomial (Fin (n + 1)) A))]
    split_ifs with hed
    · apply Ideal.mul_mem_left
      refine Ideal.subset_span ⟨⟨g, ⟨e, Finset.mem_range.mp he⟩⟩, ?_⟩
      rfl
    · exact Submodule.zero_mem _

  have hEq : Ideal.span { s | ∃ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d),
          F ∈ I ∧
          s = (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
              (HomogeneousLocalization.mk
                { deg := d
                  num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                  den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                  den_mem := ⟨d, rfl⟩ }) } = Ideal.span (Set.range (aTS ∘ w)) := by
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨d, F, hF, hFI, rfl⟩
      have hmem := key d F hFI
      have hcF : comp d F = ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩ := by
        rw [comp_of_mem ((MvPolynomial.mem_homogeneousSubmodule d F).mpr hF), dif_pos rfl]
      rw [fcHom_apply, hcF] at hmem
      have := Ideal.mem_map_of_mem aTS hmem
      rw [Ideal.map_span, ← Set.range_comp] at this
      exact this
    · apply Ideal.span_mono
      rintro _ ⟨⟨⟨g, hg⟩, ⟨e, he⟩⟩, rfl⟩
      exact ⟨e, homogeneousComponent e g, homogeneousComponent_isHomogeneous e g, hI g (hsI g hg) e, rfl⟩
  rw [hEq]
  exact ⟨(Finset.univ : Finset ι).image (aTS ∘ w), by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]⟩

end ChartIdeal

section Alg

variable {K : Type} [Field K] {n : ℕ}

theorem hcomp_mem_of_homogeneousIdeal {I : Ideal (MvPolynomial (Fin (n + 1)) K)}
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) K)) {p : MvPolynomial (Fin (n + 1)) K}
    (hp : p ∈ I) (e : ℕ) : homogeneousComponent e p ∈ I := by
  have h := hI e hp
  rwa [coe_decompose] at h

theorem isHomogeneous_span {s : Set (MvPolynomial (Fin (n + 1)) K)}
    (hs : ∀ p ∈ s, ∃ e : ℕ, p.IsHomogeneous e) :
    (Ideal.span s).IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) K) :=
  Ideal.homogeneous_span _ s fun p hp => by
    obtain ⟨e, he⟩ := hs p hp
    exact ⟨e, (mem_homogeneousSubmodule e p).mpr he⟩

def ell (a : Fin (n + 1) → K) : MvPolynomial (Fin (n + 1)) K :=
  ∑ j : Fin (n + 1), MvPolynomial.C (a j) * MvPolynomial.X j

theorem ell_isHomogeneous (a : Fin (n + 1) → K) : (ell a).IsHomogeneous 1 := by
  unfold ell
  refine IsHomogeneous.sum _ _ _ fun j _ => ?_
  exact (isHomogeneous_C _ (a j)).mul (isHomogeneous_X K j)

theorem mem_span_monomial_of_isHomogeneous {c : MvPolynomial (Fin (n + 1)) K} {r t : ℕ}
    (hc : c.IsHomogeneous r) (ht : t ≤ r) :
    c ∈ Ideal.span ((fun μ => monomial μ (1 : K)) '' {μ : Fin (n + 1) →₀ ℕ | μ.degree = t}) := by
  rw [mem_ideal_span_monomial_image]
  intro xi hxi
  have hdeg : xi.degree = r := by
    have h := hc (mem_support_iff.mp hxi)
    rw [Finsupp.degree_eq_weight_one]
    exact h
  obtain ⟨g, hg, hgd⟩ := Finsupp.exists_le_degree_eq xi t (hdeg ▸ ht)
  exact ⟨g, hgd, hg⟩

theorem mem_span_homogPart {m : ℕ} (hm : 1 ≤ m) {s : Set (MvPolynomial (Fin (n + 1)) K)}
    (hs : ∀ p ∈ s, p.IsHomogeneous m) (ℓ : MvPolynomial (Fin (n + 1)) K) (hℓ : ℓ.IsHomogeneous 1)
    {G : MvPolynomial (Fin (n + 1)) K} {e : ℕ} (hG : G.IsHomogeneous e) (he : m ≤ e)
    (hGK : G ∈ Ideal.span s ⊔ Ideal.span {ℓ}) :
    G ∈ Ideal.span {f | f ∈ Ideal.span s ⊔ Ideal.span {ℓ} ∧ f.IsHomogeneous m} := by
  classical
  have hK : Ideal.span s ⊔ Ideal.span {ℓ} = Ideal.span (s ∪ {ℓ}) := (Submodule.span_union _ _).symm
  have hgen : ∀ g ∈ s ∪ {ℓ}, ∃ e : ℕ, g.IsHomogeneous e := by
    rintro g (hg | hg)
    · exact ⟨m, hs g hg⟩
    · exact ⟨1, by rw [Set.mem_singleton_iff.mp hg]; exact hℓ⟩
  rw [hK] at hGK
  obtain ⟨t, dg, c, hts, hprop, rfl⟩ :=
    MvPolynomial.exists_finset_sum_mul_eq_of_isHomogeneous_of_mem_span (s ∪ {ℓ}) hgen hG hGK
  refine Submodule.sum_mem _ fun g hg => ?_
  obtain ⟨hdle, hghom, hchom⟩ := hprop g hg
  by_cases hg0 : g = 0
  · rw [hg0, mul_zero]; exact Submodule.zero_mem _

  have hgK : g ∈ Ideal.span s ⊔ Ideal.span {ℓ} := by
    rw [hK]; exact Ideal.subset_span (hts hg)
  have hdgm : dg g ≤ m := by
    rcases hts hg with hgs | hgl
    · exact (hghom.inj_right (hs g hgs) hg0).le
    · rw [Set.mem_singleton_iff] at hgl
      have h1 : dg g = 1 := hghom.inj_right (hgl ▸ hℓ) hg0
      omega

  have hcmem := mem_span_monomial_of_isHomogeneous hchom (Nat.sub_le_sub_right he (dg g))

  refine Submodule.span_induction (p := fun x _ => x * g ∈ Ideal.span
      {f | f ∈ Ideal.span s ⊔ Ideal.span {ℓ} ∧ f.IsHomogeneous m}) ?_ ?_ ?_ ?_ hcmem
  · rintro _ ⟨μ, hμ, rfl⟩
    apply Ideal.subset_span
    refine ⟨Ideal.mul_mem_left _ _ hgK, ?_⟩
    have hmono : (monomial μ (1 : K)).IsHomogeneous (m - dg g) := isHomogeneous_monomial _ hμ
    have := hmono.mul hghom
    rwa [Nat.sub_add_cancel hdgm] at this
  · show (0 : MvPolynomial (Fin (n + 1)) K) * g ∈ _
    rw [zero_mul]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    show (x + y) * g ∈ _
    rw [add_mul]; exact Submodule.add_mem _ hx hy
  · intro r x _ hx
    show (r • x) * g ∈ _
    rw [smul_eq_mul, mul_assoc]; exact Ideal.mul_mem_left _ _ hx

end Alg

end RM2CSOL

open RM2CSOL in

theorem solution
    (n m : ℕ) (hm : 1 ≤ m) (k : Type) [Field k]
    (J : Ideal (MvPolynomial (Fin (n + 1)) k))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) k), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (Zk : Scheme.{0}) (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsClosedImmersion ιk]
    (hZ : (∀ (d : ℕ), m ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
        (F ∈ J ↔ ∀ i : Fin (n + 1), (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ }))) = 0)))
    (a : Fin (n + 1) → k)
    (hgrowth' :
      let J' : Ideal (MvPolynomial (Fin (n + 1)) k) :=
        Ideal.span {f | f ∈ J ⊔ Ideal.span {(∑ j : Fin (n + 1), MvPolynomial.C (a j) * MvPolynomial.X j)} ∧ f.IsHomogeneous m}
      Module.finrank k (piece J' (m + 1)) = Nat.macaulayPow m (Module.finrank k (piece J' m))) :
    ∀ (𝓘ℓ : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)).IdealSheafData),
        (∀ i : Fin (n + 1),
        𝓘ℓ.ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i),
          Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i) (ProjSpace.X_mem_one k n i) one_pos⟩ =
        Ideal.span { s | ∃ (d : ℕ) (G : MvPolynomial (Fin (n + 1)) k) (hG : G.IsHomogeneous d),
          G ∈ Ideal.span {(∑ j : Fin (n + 1), MvPolynomial.C (a j) * MvPolynomial.X j)} ∧
          s = Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
              (HomogeneousLocalization.mk
                { deg := d
                  num := ⟨G, (MvPolynomial.mem_homogeneousSubmodule d G).mpr hG⟩
                  den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                  den_mem := ⟨d, rfl⟩ }) }) →
        ∀ (Z' : Scheme.{0}) (ι' : Z' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsClosedImmersion ι'],
          ι'.ker = ιk.ker ⊔ 𝓘ℓ →
          let J' : Ideal (MvPolynomial (Fin (n + 1)) k) :=
            Ideal.span {f | f ∈ J ⊔ Ideal.span {(∑ j : Fin (n + 1), MvPolynomial.C (a j) * MvPolynomial.X j)} ∧ f.IsHomogeneous m}
          (∀ (d : ℕ), m ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
        (F ∈ J' ↔ ∀ i : Fin (n + 1), (ι'.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ }))) = 0)) := by
  classical
  intro 𝓘ℓ h𝓘ℓ Z' ι' _ hker
  dsimp only
  dsimp only at hgrowth'
  obtain ⟨s, hs, rfl⟩ := hJ
  intro d hd F hF

  set ℓ : MvPolynomial (Fin (n + 1)) k := ∑ j : Fin (n + 1), MvPolynomial.C (a j) * MvPolynomial.X j with hℓ
  have hℓ1 : ℓ.IsHomogeneous 1 := ell_isHomogeneous a
  let U : Fin (n + 1) → (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)).affineOpens := fun i =>
    ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i),
      Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
        (ProjSpace.X_mem_one k n i) one_pos⟩
  have hJhom : (Ideal.span s).IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) k) :=
    isHomogeneous_span fun p hp => ⟨m, hs p hp⟩
  have hLhom : (Ideal.span {ℓ}).IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) k) :=
    isHomogeneous_span fun p hp => ⟨1, by rw [Set.mem_singleton_iff.mp hp]; exact hℓ1⟩

  have memker : ∀ (i : Fin (n + 1)) (x : Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k),
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))),
      ι'.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)) x = 0 ↔
        x ∈ ιk.ker.ideal (U i) ⊔ 𝓘ℓ.ideal (U i) := by
    intro i x
    have h1 : ι'.ker.ideal (U i) = RingHom.ker (ι'.app (U i)).hom := Scheme.Hom.ker_apply ι' (U i)
    rw [hker] at h1
    constructor
    · intro hx
      have hx' : x ∈ RingHom.ker (ι'.app (U i)).hom := hx
      rw [← h1] at hx'
      exact hx'
    · intro hx
      have hx' : x ∈ (ιk.ker ⊔ 𝓘ℓ).ideal (U i) := hx
      rw [h1] at hx'
      exact hx'
  have memkerZ : ∀ (i : Fin (n + 1)) (x : Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k),
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))),
      ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)) x = 0 ↔
        x ∈ ιk.ker.ideal (U i) := by
    intro i x
    rw [Scheme.Hom.ker_apply ιk (U i)]
    exact Iff.rfl
  constructor
  ·
    intro hFJ' i
    have hFK : F ∈ Ideal.span s ⊔ Ideal.span {ℓ} := Ideal.span_le.mpr (fun f hf => hf.1) hFJ'
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hFK
    have hFeq : F = homogeneousComponent d p + homogeneousComponent d q := by
      rw [← map_add, hpq, homogeneousComponent_of_mem ((mem_homogeneousSubmodule d F).mpr hF), if_pos rfl]
    have hp' : homogeneousComponent d p ∈ Ideal.span s := hcomp_mem_of_homogeneousIdeal hJhom hp d
    have hq' : homogeneousComponent d q ∈ Ideal.span {ℓ} := hcomp_mem_of_homogeneousIdeal hLhom hq d
    have hsplit : (⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩ :
        ↥(homogeneousSubmodule (Fin (n + 1)) k d)) =
        ⟨homogeneousComponent d p, homogeneousComponent_mem d p⟩ +
          ⟨homogeneousComponent d q, homogeneousComponent_mem d q⟩ := Subtype.ext hFeq
    show (ι'.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
      ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))
        (frac i d ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩)) = 0
    rw [hsplit, frac_add, map_add, map_add]
    have hpmem : (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))
        (frac i d ⟨homogeneousComponent d p, homogeneousComponent_mem d p⟩) ∈
          ιk.ker.ideal (U i) ⊔ 𝓘ℓ.ideal (U i) := by
      apply Submodule.mem_sup_left
      exact (memkerZ i _).mp ((hZ d hd (homogeneousComponent d p) (homogeneousComponent_isHomogeneous d p)).mp hp' i)
    have hqmem : (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))
        (frac i d ⟨homogeneousComponent d q, homogeneousComponent_mem d q⟩) ∈
          ιk.ker.ideal (U i) ⊔ 𝓘ℓ.ideal (U i) := by
      apply Submodule.mem_sup_right
      rw [h𝓘ℓ i]
      exact Ideal.subset_span ⟨d, homogeneousComponent d q, homogeneousComponent_isHomogeneous d q, hq', rfl⟩
    rw [(memker i _).mpr hpmem, (memker i _).mpr hqmem, add_zero]
  ·
    intro hvan

    obtain ⟨𝓘V, h𝓘V⟩ := AlgebraicGeometry.ProjSpace.exists_idealSheafData_ideal_basicOpen_eq_span n k
      (Ideal.span { F : MvPolynomial (Fin (n + 1)) k | ∃ (d : ℕ) (hF : F.IsHomogeneous d), m ≤ d ∧
            ∀ i : Fin (n + 1),
            ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (X i))
              ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (X i))
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ })) = 0 })
    have hVker : 𝓘V = ιk.ker :=
      AlgebraicGeometry.ProjSpace.eq_ker_of_ideal_basicOpen_eq_span_of_isClosedImmersion n k Zk ιk inferInstance m 𝓘V h𝓘V
    have hIV_le : Ideal.span { F : MvPolynomial (Fin (n + 1)) k | ∃ (d : ℕ) (hF : F.IsHomogeneous d), m ≤ d ∧
            ∀ i : Fin (n + 1),
            ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (X i))
              ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (X i))
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ })) = 0 } ≤ Ideal.span s ⊔ Ideal.span {ℓ} :=
      Ideal.span_le.mpr fun G ⟨e, hG, hme, hv⟩ => Submodule.mem_sup_left ((hZ e hme G hG).mpr hv)
    have hchart : ∀ i : Fin (n + 1), ∃ N : ℕ, MvPolynomial.X i ^ N * F ∈ Ideal.span s ⊔ Ideal.span {ℓ} := by
      intro i
      apply (AlgebraicGeometry.ProjSpace.awayToSection_mk_mem_span_iff_exists_X_pow_mul_mem n k
        (Ideal.span s ⊔ Ideal.span {ℓ}) i d F hF).mp
      have hx := (memker i _).mp (hvan i)
      refine (show ιk.ker.ideal (U i) ⊔ 𝓘ℓ.ideal (U i) ≤ _ from sup_le ?_ ?_) hx
      · rw [← hVker, h𝓘V i]
        apply Ideal.span_mono
        rintro _ ⟨e, G, hG, hGV, rfl⟩
        exact ⟨e, G, hG, hIV_le hGV, rfl⟩
      · rw [h𝓘ℓ i]
        apply Ideal.span_mono
        rintro _ ⟨e, G, hG, hGL, rfl⟩
        exact ⟨e, G, hG, Submodule.mem_sup_right hGL, rfl⟩
    choose N hN using hchart
    exact MvPolynomial.mem_of_forall_exists_X_pow_mul_mem_of_finrank_piece_succ_eq_macaulayPow n m hm k _
      ⟨{f | f ∈ Ideal.span s ⊔ Ideal.span {ℓ} ∧ f.IsHomogeneous m}, fun p hp => hp.2, rfl⟩ hgrowth' d hd F hF
      (fun i => ⟨N i, mem_span_homogPart hm hs ℓ hℓ1 ((MvPolynomial.isHomogeneous_X_pow i (N i)).mul hF)
        (le_trans hd (Nat.le_add_left d (N i))) (hN i)⟩)

end

end S_AlgebraicGeometry_ProjSpace_mem_span_sup_linearForm_iff_forall_app_eq_zero_of_maximal_growth
end P2MW
export P2MW.S_AlgebraicGeometry_ProjSpace_mem_span_sup_linearForm_iff_forall_app_eq_zero_of_maximal_growth (solution)
