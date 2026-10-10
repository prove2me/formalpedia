-- Prove2me | solution 1 for ArtinPrimitiveRoots.kummer_zero_free_of_hecke
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T07:17:17.829756+00:00
-- url     : https://prove2.me/submissions/a57afcc1-684c-4b2b-a08d-f934dd50a5e4

import Mathlib
import Definitions.Def_ArtinHecke
import Theorems.Thm_ArtinPrimitiveRoots_exists_differentiable_dedekindZeta_eq_mul_of_isGalois
import Theorems.Thm_NumberField_exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero
import Theorems.Thm_ArtinPrimitiveRoots_dedekindZeta_eq_prod_heckeLSeries_of_abelian

section
/-! # L91G: the Kummer field over `F = ℚ(μ_{12q})`

For `F` cyclotomic of level `12q` and `K` a splitting field of `X^q - a` over `ℚ`, the splitting
field `L` of `X^q - a` over `F` is a number field, Galois over `F` with commutative Galois group,
and Galois over `K` (through an embedding `K → L`). -/

open NumberField Polynomial

namespace ArtinPrimitiveRoots

theorem L91G_exists_field (a : ℤ) (ha : a ≠ 0) (q : ℕ) (hq : q.Prime)
    (F : Type) [Field F] [NumberField F] [IsCyclotomicExtension {12 * q} ℚ F]
    (K : Type) [Field K] [NumberField K] [IsSplittingField ℚ K (X ^ q - C (a : ℚ))] :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra F L) (_ : Algebra K L),
      IsGalois F L ∧ IsGalois K L ∧ ∀ σ τ : L ≃ₐ[F] L, σ * τ = τ * σ := by
  classical
  set p : ℚ[X] := X ^ q - C (a : ℚ) with hp
  let L := SplittingField (p.map (algebraMap ℚ F))
  have : FiniteDimensional ℚ L := Module.Finite.trans F L
  have : NumberField L := ⟨⟩
  have hq0 : 0 < q := hq.pos
  have : NeZero (12 * q) := ⟨by positivity⟩
  have hp0 : p ≠ 0 := X_pow_sub_C_ne_zero hq.pos _
  have hc0 : (X ^ (12 * q) - 1 : ℚ[X]) ≠ 0 := X_pow_sub_C_ne_zero (by positivity) _
  have : IsSplittingField ℚ F (X ^ (12 * q) - 1) :=
    IsCyclotomicExtension.isSplittingField_X_pow_sub_one (12 * q) ℚ F
  have : IsSplittingField ℚ L ((X ^ (12 * q) - 1) * p) :=
    IsSplittingField.mul (K := F) L _ _ hc0 hp0
  have : Normal ℚ L := Normal.of_isSplittingField ((X ^ (12 * q) - 1) * p)
  have : IsGalois ℚ L := ⟨⟩
  have : IsGalois F L := IsGalois.tower_top_of_isGalois ℚ F L
  have hsplit : Splits (p.map (algebraMap ℚ L)) := by
    have := IsSplittingField.splits L (p.map (algebraMap ℚ F))
    rwa [map_map, ← IsScalarTower.algebraMap_eq] at this
  let ι : K →ₐ[ℚ] L := IsSplittingField.lift K p hsplit
  letI : Algebra K L := ι.toRingHom.toAlgebra
  have : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq (fun x => (ι.commutes x).symm)
  have : IsGalois K L := IsGalois.tower_top_of_isGalois ℚ K L
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_⟩
  intro σ τ
  have : NeZero q := ⟨hq.ne_zero⟩
  set ζ := IsCyclotomicExtension.zeta (12 * q) ℚ F
  have hζ : IsPrimitiveRoot ζ (12 * q) := IsCyclotomicExtension.zeta_spec (12 * q) ℚ F
  have hζq : IsPrimitiveRoot (ζ ^ 12) q := hζ.pow (by positivity) (by ring)
  have hζL : IsPrimitiveRoot (algebraMap F L (ζ ^ 12)) q :=
    hζq.map_of_injective (algebraMap F L).injective
  have haL : (a : L) ≠ 0 := by exact_mod_cast ha
  have key : ∀ (ρ : L ≃ₐ[F] L) (γ : L), γ ∈ (p.map (algebraMap ℚ F)).rootSet L →
      ∃ c : F, ρ γ = algebraMap F L c * γ := by
    intro ρ γ hγ
    have hγq : γ ^ q = (a : L) := by
      rw [mem_rootSet] at hγ
      simpa [hp, sub_eq_zero] using hγ.2
    have hργ : (ρ γ) ^ q = (a : L) := by rw [← map_pow, hγq, map_intCast]
    have hγ0 : γ ≠ 0 := by
      rintro rfl
      exact haL (by rw [← hγq, zero_pow hq.ne_zero])
    have h1 : (ρ γ / γ) ^ q = 1 := by rw [div_pow, hργ, hγq, div_self haL]
    obtain ⟨i, -, hi⟩ := hζL.eq_pow_of_pow_eq_one h1
    exact ⟨(ζ ^ 12) ^ i, by rw [map_pow, hi, div_mul_cancel₀ _ hγ0]⟩
  have hext : (σ * τ : L ≃ₐ[F] L).toAlgHom = (τ * σ : L ≃ₐ[F] L).toAlgHom := by
    apply AlgHom.ext_of_adjoin_eq_top (IsSplittingField.adjoin_rootSet L (p.map (algebraMap ℚ F)))
    intro γ hγ
    obtain ⟨cσ, hσ⟩ := key σ γ hγ
    obtain ⟨cτ, hτ⟩ := key τ γ hγ
    change σ (τ γ) = τ (σ γ)
    rw [hτ, map_mul, AlgEquiv.commutes, hσ, map_mul, AlgEquiv.commutes, hτ]
    ring
  exact AlgEquiv.coe_toAlgHom_injective hext

end ArtinPrimitiveRoots
end

section
/-! # L91G: descent of a zero-free region along a Galois extension

If `L/K` is Galois and `ζ_L` agrees on `Re s > 1` with a function `G` holomorphic and zero-free on
`Ω = {Re s > σ, s ≠ 1}`, then `ζ_K` continues to `Ω` without zeros: by Aramata–Brauer
`ζ_L = ζ_K · h` with `h` entire, `ζ_K` continues to `ℂ ∖ {1}` as `R(s)/(s - 1)`, and the identity
theorem on the connected set `Ω` gives `R(s)/(s - 1) · h(s) = G(s) ≠ 0` there. -/

open NumberField Complex

namespace ArtinPrimitiveRoots

/-- `{Re s > σ} ∖ {1}` is preconnected. -/
theorem L91G_isPreconnected (σ : ℝ) : IsPreconnected {s : ℂ | σ < s.re ∧ s ≠ 1} := by
  set c : ℝ := max σ 1 + 1 with hc
  have hc1 : 1 < c := by have := le_max_right σ 1; linarith
  have hcσ : σ < c := by have := le_max_left σ 1; linarith
  set H : Set ℂ := {s | σ < s.re}
  have hH : Convex ℝ H := convex_halfSpace_re_gt σ
  set V1 : Set ℂ := H ∩ {s | 0 < s.im}
  set V2 : Set ℂ := H ∩ {s | s.im < 0}
  set V3 : Set ℂ := H ∩ {s | 1 < s.re}
  set V4 : Set ℂ := H ∩ {s | s.re < 1}
  have p1 : IsPreconnected V1 := (hH.inter (convex_halfSpace_im_gt 0)).isPreconnected
  have p2 : IsPreconnected V2 := (hH.inter (convex_halfSpace_im_lt 0)).isPreconnected
  have p3 : IsPreconnected V3 := (hH.inter (convex_halfSpace_re_gt 1)).isPreconnected
  have p4 : IsPreconnected V4 := (hH.inter (convex_halfSpace_re_lt 1)).isPreconnected
  have sub : ∀ s : ℂ, σ < s.re → (0 < s.im ∨ s.im < 0 ∨ 1 < s.re ∨ s.re < 1) →
      s ∈ {s : ℂ | σ < s.re ∧ s ≠ 1} := by
    intro s hs h
    refine ⟨hs, ?_⟩
    rintro rfl
    simp at h
  have hV : ∀ (V : Set ℂ), V ⊆ H → (∀ s ∈ V, 0 < s.im ∨ s.im < 0 ∨ 1 < s.re ∨ s.re < 1) →
      V ⊆ {s : ℂ | σ < s.re ∧ s ≠ 1} := fun V hVH hV s hs => sub s (hVH hs) (hV s hs)
  refine isPreconnected_of_forall (⟨c, 1⟩ : ℂ) fun y hy => ?_
  obtain ⟨hyσ, hy1⟩ := hy
  rcases lt_trichotomy y.im 0 with him | him | him
  · -- lower half: V2 ∪ V3
    refine ⟨V2 ∪ V3, hV _ (Set.union_subset Set.inter_subset_left Set.inter_subset_left) ?_,
      Or.inr ⟨hcσ, hc1⟩, Or.inl ⟨hyσ, him⟩, p2.union (⟨c, -1⟩ : ℂ) ⟨hcσ, by simp⟩ ⟨hcσ, hc1⟩ p3⟩
    rintro s (hs | hs)
    · exact Or.inr (Or.inl hs.2)
    · exact Or.inr (Or.inr (Or.inl hs.2))
  · -- real axis
    have hyre : y.re ≠ 1 := by
      intro h; exact hy1 (Complex.ext (by simpa using h) (by simpa using him))
    rcases lt_or_gt_of_ne hyre with hlt | hgt
    · refine ⟨V1 ∪ V4, hV _ (Set.union_subset Set.inter_subset_left Set.inter_subset_left) ?_,
        Or.inl ⟨hcσ, by simp⟩, Or.inr ⟨hyσ, hlt⟩,
        p1.union (⟨y.re, 1⟩ : ℂ) ⟨hyσ, by simp⟩ ⟨hyσ, hlt⟩ p4⟩
      rintro s (hs | hs)
      · exact Or.inl hs.2
      · exact Or.inr (Or.inr (Or.inr hs.2))
    · exact ⟨V3, hV _ Set.inter_subset_left (fun s hs => Or.inr (Or.inr (Or.inl hs.2))),
        ⟨hcσ, hc1⟩, ⟨hyσ, hgt⟩, p3⟩
  · exact ⟨V1, hV _ Set.inter_subset_left (fun s hs => Or.inl hs.2), ⟨hcσ, by simp⟩,
      ⟨hyσ, him⟩, p1⟩

/-- The descent: a zero-free continuation of `ζ_L` gives one of `ζ_K` when `L/K` is Galois. -/
theorem L91G_descent (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (σ : ℝ) (G : ℂ → ℂ)
    (hG : DifferentiableOn ℂ G {s | σ < s.re ∧ s ≠ 1})
    (hG0 : ∀ s : ℂ, σ < s.re → s ≠ 1 → G s ≠ 0)
    (hGL : ∀ s : ℂ, 1 < s.re → G s = dedekindZeta L s) :
    DedekindZeroFreeRight K σ := by
  obtain ⟨h, hh, hLK⟩ := exists_differentiable_dedekindZeta_eq_mul_of_isGalois K L
  obtain ⟨R, hR, -, hRζ, -⟩ :=
    NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero K
  set Ω : Set ℂ := {s : ℂ | σ < s.re ∧ s ≠ 1} with hΩdef
  have hΩ : IsOpen Ω := (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
  set Z : ℂ → ℂ := fun s => R s / (s - 1) with hZdef
  have hZ : DifferentiableOn ℂ Z Ω := fun s hs =>
    ((hR s).div (differentiableAt_id.sub_const 1) (sub_ne_zero.2 hs.2)).differentiableWithinAt
  have hZζ : ∀ s : ℂ, 1 < s.re → Z s = dedekindZeta K s := by
    intro s hs
    have : s - 1 ≠ 0 := sub_ne_zero.2 (fun h => by simp [h] at hs)
    simp only [hZdef, hRζ s hs]
    field_simp
  set c : ℝ := max σ 1 + 1 with hc
  have hc1 : 1 < c := by have := le_max_right σ 1; linarith
  have hcσ : σ < c := by have := le_max_left σ 1; linarith
  have hcΩ : (c : ℂ) ∈ Ω := ⟨by simpa using hcσ, fun h => by
    have := congrArg Complex.re h; simp at this; linarith⟩
  have hEq : Set.EqOn (fun s => Z s * h s) G Ω := by
    refine ((hZ.mul hh.differentiableOn).analyticOnNhd hΩ).eqOn_of_preconnected_of_eventuallyEq
      (hG.analyticOnNhd hΩ) (L91G_isPreconnected σ) hcΩ ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (c : ℂ).re by simpa using hc1)] with s hs
    show Z s * h s = G s
    rw [hZζ s hs, hGL s hs, hLK s hs]
  refine ⟨Z, hZ, hZζ, fun s hs h1 h0 => hG0 s hs h1 ?_⟩
  rw [← hEq ⟨hs, h1⟩]
  simp [h0]

end ArtinPrimitiveRoots
end

section
/-! # L91G: `kummer_zero_free_of_hecke`

`L` = splitting field of `X^q - a` over `F = ℚ(μ_{12q})` is abelian over `F` (totally complex)
and Galois over `K`; `ζ_L` is a product of Hecke `L`-functions of `F`, each zero-free right of
`σ` by `hF`, and the zero-free region descends from `ζ_L` to `ζ_K` (Aramata–Brauer). -/

open NumberField Polynomial

namespace ArtinPrimitiveRoots

end ArtinPrimitiveRoots
end

section
open NumberField Polynomial
open ArtinPrimitiveRoots
theorem solution (a : ℤ) (ha : a ≠ 0) (q : ℕ) (hq : q.Prime) (σ : ℝ)
    (hσ : 0 < σ) (F : Type) [Field F] [NumberField F] [IsCyclotomicExtension {12 * q} ℚ F]
    (hF : ∀ (𝔪 : Ideal (𝓞 F)), 𝔪 ≠ ⊥ → ∀ χ : HeckeChar F 𝔪, χ.ZeroFreeRight σ)
    (K : Type) [Field K] [NumberField K] [IsSplittingField ℚ K (X ^ q - C (a : ℚ))] :
    DedekindZeroFreeRight K σ := by
  obtain ⟨L, _, _, _, _, _, _, hab⟩ := L91G_exists_field a ha q hq F K
  have : NeZero (12 * q) := ⟨by have := hq.pos; positivity⟩
  have : IsTotallyComplex F :=
    IsCyclotomicExtension.Rat.isTotallyComplex (n := 12 * q) (K := F)
      (by have := hq.two_le; omega)
  obtain ⟨n, 𝔪, h𝔪, η, hη⟩ := dedekindZeta_eq_prod_heckeLSeries_of_abelian F L hab
  choose g hg hgL hg0 using fun i => hF (𝔪 i) (h𝔪 i) (η i)
  refine L91G_descent K L σ (fun s => ∏ i, g i s)
    (DifferentiableOn.fun_finsetProd fun i _ => hg i) (fun s hs h1 => ?_) (fun s hs => ?_)
  · exact Finset.prod_ne_zero_iff.2 fun i _ => hg0 i s hs h1
  · rw [hη s hs]
    exact Finset.prod_congr rfl fun i _ => hgL i s hs
end
