-- Prove2me | Definitions.Def_RPLib_S4_EtShUnibranch
-- name    : RPLib_S4_EtShUnibranch
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:12:29.273202+00:00
-- url     : https://prove2.me/theorems/84af750c-1081-4886-8bed-cb9a7a6cb980
-- title:
--   Standard etale algebras over a normal domain are unibranch
-- statement:
--   Let $B$ be an integrally closed domain and $S$ a $B$-algebra with an element $x$ such that $f(x) = 0$ for a monic $f \in B[X]$ with $f'(x)$ a unit of $S$, and such that every $s \in S$ satisfies $s u = p(x)$ for some unit $u$ and some $p \in B[X]$ (the shape of a standard etale presentation). Then two primes of $S$ lying over $(0) \subset B$ that are contained in a common prime $\mathfrak q$ of $S$ coincide. The proof compares the minimal polynomials over $B$ of the images of $x$: if they differed they would be coprime over $\mathrm{Frac}\,B$ (Gauss), so their product would divide $f$ and $f'(x) \in \mathfrak q$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Raynaud, Anneaux locaux henseliens, Lecture Notes in Math. 169, Springer (1970), Chapters V and VIII; J. S. Milne, Etale Cohomology, Princeton University Press (1980), Chapter I, Section 3

import Mathlib

/-!
# S4-EtSheaves, O10c part 1: standard etale algebras over normal domains are unibranch

Let `B` be an integrally closed domain and `x : S` with `f(x) = 0` for a monic `f : B[X]`,
`f'(x)` a unit, and every `s : S` satisfying `s * u = p(x)` for some unit `u` and `p : B[X]`
(the shape of a standard etale presentation). Then two primes of `S` lying over `(0)` that are
contained in a common prime `𝔮` coincide.

Proof: the minimal polynomials `μᵢ` over `B` of the images of `x` in `S ⧸ 𝔭ᵢ` both divide `f`;
if they differ, they are coprime over `Frac B` (Gauss), so `μ₁ μ₂ ∣ f` in `B[X]` and `f'(x) ∈ 𝔮`,
which is impossible. With `μ₁ = μ₂`, `s ∈ 𝔭ᵢ ↔ μ ∣ p` for the same `p`.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtSheaves.Unibranch

variable {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]

theorem aeval_mk (𝔭 : Ideal S) (x : S) (p : B[X]) :
    aeval (Ideal.Quotient.mk 𝔭 x) p = Ideal.Quotient.mk 𝔭 (aeval x p) := by
  rw [← Ideal.Quotient.mkₐ_eq_mk B, aeval_algHom_apply]

theorem isIntegral_mk (𝔭 : Ideal S) (x : S) (f : B[X]) (hf : f.Monic) (hfx : aeval x f = 0) :
    IsIntegral B (Ideal.Quotient.mk 𝔭 x) :=
  ⟨f, hf, by rw [← aeval_def, aeval_mk, hfx, map_zero]⟩

theorem algebraMap_quot_injective (𝔭 : Ideal S) (h𝔭 : 𝔭.comap (algebraMap B S) = ⊥) :
    Function.Injective (algebraMap B (S ⧸ 𝔭)) := by
  rw [injective_iff_map_eq_zero]
  intro b hb
  have hb' : algebraMap B S b ∈ 𝔭 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_algebraMap]
    exact hb
  have hb'' : b ∈ 𝔭.comap (algebraMap B S) := hb'
  rw [h𝔭] at hb''
  exact Ideal.mem_bot.1 hb''

variable [IsDomain B] [IsIntegrallyClosed B]

/-- Membership of `p(x)` in a prime over `(0)` is divisibility by the minimal polynomial. -/
theorem mem_iff_minpoly_dvd (𝔭 : Ideal S) [𝔭.IsPrime] (h𝔭 : 𝔭.comap (algebraMap B S) = ⊥)
    (x : S) (f : B[X]) (hf : f.Monic) (hfx : aeval x f = 0) (p : B[X]) :
    aeval x p ∈ 𝔭 ↔ minpoly B (Ideal.Quotient.mk 𝔭 x) ∣ p := by
  have : Module.IsTorsionFree B (S ⧸ 𝔭) := Module.isTorsionFree_iff_faithfulSMul.2
    ((faithfulSMul_iff_algebraMap_injective B (S ⧸ 𝔭)).2 (algebraMap_quot_injective 𝔭 h𝔭))
  have hint := isIntegral_mk 𝔭 x f hf hfx
  constructor
  · intro hp
    apply minpoly.isIntegrallyClosed_dvd hint
    rw [aeval_mk, Ideal.Quotient.eq_zero_iff_mem.2 hp]
  · rintro ⟨q, rfl⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← aeval_mk, aeval_mul, minpoly.aeval, zero_mul]

section Main

variable (x : S) (f : B[X]) (hf : f.Monic) (hfx : aeval x f = 0)
  (hd : IsUnit (aeval x (derivative f)))
  {𝔮 𝔭₁ 𝔭₂ : Ideal S} [𝔮.IsPrime] [𝔭₁.IsPrime] [𝔭₂.IsPrime]
  (h₁ : 𝔭₁ ≤ 𝔮) (h₂ : 𝔭₂ ≤ 𝔮)
  (h₁0 : 𝔭₁.comap (algebraMap B S) = ⊥) (h₂0 : 𝔭₂.comap (algebraMap B S) = ⊥)

include hf hfx hd h₁ h₂ h₁0 h₂0 in
/-- The two minimal polynomials agree: otherwise `f'(x) ∈ 𝔮`. -/
theorem minpoly_eq_of_le :
    minpoly B (Ideal.Quotient.mk 𝔭₁ x) = minpoly B (Ideal.Quotient.mk 𝔭₂ x) := by
  by_contra hne
  have hint1 := isIntegral_mk 𝔭₁ x f hf hfx
  have hint2 := isIntegral_mk 𝔭₂ x f hf hfx
  have hm1 := minpoly.monic hint1
  have hm2 := minpoly.monic hint2
  have hf1 : minpoly B (Ideal.Quotient.mk 𝔭₁ x) ∣ f :=
    (mem_iff_minpoly_dvd 𝔭₁ h₁0 x f hf hfx f).1 (by rw [hfx]; exact 𝔭₁.zero_mem)
  have hf2 : minpoly B (Ideal.Quotient.mk 𝔭₂ x) ∣ f :=
    (mem_iff_minpoly_dvd 𝔭₂ h₂0 x f hf hfx f).1 (by rw [hfx]; exact 𝔭₂.zero_mem)
  have hinjK : Function.Injective (algebraMap B (FractionRing B)) :=
    IsFractionRing.injective B (FractionRing B)
  have irr1 : Irreducible ((minpoly B (Ideal.Quotient.mk 𝔭₁ x)).map
      (algebraMap B (FractionRing B))) :=
    (hm1.irreducible_iff_irreducible_map_fraction_map (K := FractionRing B)).1
      (minpoly.irreducible hint1)
  have irr2 : Irreducible ((minpoly B (Ideal.Quotient.mk 𝔭₂ x)).map
      (algebraMap B (FractionRing B))) :=
    (hm2.irreducible_iff_irreducible_map_fraction_map (K := FractionRing B)).1
      (minpoly.irreducible hint2)
  have ndvd : ¬ (minpoly B (Ideal.Quotient.mk 𝔭₁ x)).map (algebraMap B (FractionRing B)) ∣
      (minpoly B (Ideal.Quotient.mk 𝔭₂ x)).map (algebraMap B (FractionRing B)) := by
    intro h
    exact hne (map_injective _ hinjK
      (eq_of_monic_of_associated (hm1.map _) (hm2.map _) (irr1.associated_of_dvd irr2 h)))
  have cop := (irr1.coprime_iff_not_dvd).2 ndvd
  have hK := cop.mul_dvd (Polynomial.map_dvd (algebraMap B (FractionRing B)) hf1)
    (Polynomial.map_dvd (algebraMap B (FractionRing B)) hf2)
  rw [← Polynomial.map_mul] at hK
  obtain ⟨h, hh⟩ := (map_dvd_map _ hinjK (hm1.mul hm2)).1 hK
  have ha1 : aeval x (minpoly B (Ideal.Quotient.mk 𝔭₁ x)) ∈ 𝔮 :=
    h₁ ((mem_iff_minpoly_dvd 𝔭₁ h₁0 x f hf hfx _).2 dvd_rfl)
  have ha2 : aeval x (minpoly B (Ideal.Quotient.mk 𝔭₂ x)) ∈ 𝔮 :=
    h₂ ((mem_iff_minpoly_dvd 𝔭₂ h₂0 x f hf hfx _).2 dvd_rfl)
  have hmem : aeval x (derivative f) ∈ 𝔮 := by
    rw [hh, derivative_mul, derivative_mul]
    simp only [map_add, map_mul]
    exact 𝔮.add_mem (𝔮.mul_mem_right _ (𝔮.add_mem (𝔮.mul_mem_left _ ha2)
      (𝔮.mul_mem_right _ ha1))) (𝔮.mul_mem_right _ (𝔮.mul_mem_right _ ha1))
  exact Ideal.IsPrime.ne_top ‹𝔮.IsPrime› (Ideal.eq_top_of_isUnit_mem _ hmem hd)

end Main

/-- Equal minimal polynomials give `𝔭₁ ≤ 𝔭₂`, using the generation property. -/
theorem le_of_minpoly_eq (x : S) (f : B[X]) (hf : f.Monic) (hfx : aeval x f = 0)
    (hgen : ∀ s : S, ∃ p : B[X], ∃ u : S, IsUnit u ∧ s * u = aeval x p)
    {𝔭₁ 𝔭₂ : Ideal S} [𝔭₁.IsPrime] [𝔭₂.IsPrime]
    (h₁0 : 𝔭₁.comap (algebraMap B S) = ⊥) (h₂0 : 𝔭₂.comap (algebraMap B S) = ⊥)
    (heq : minpoly B (Ideal.Quotient.mk 𝔭₁ x) = minpoly B (Ideal.Quotient.mk 𝔭₂ x)) :
    𝔭₁ ≤ 𝔭₂ := by
  intro s hs
  obtain ⟨p, u, hu, hsu⟩ := hgen s
  have h1 : aeval x p ∈ 𝔭₁ := hsu ▸ 𝔭₁.mul_mem_right u hs
  have hdv : minpoly B (Ideal.Quotient.mk 𝔭₂ x) ∣ p :=
    heq ▸ (mem_iff_minpoly_dvd 𝔭₁ h₁0 x f hf hfx p).1 h1
  have h2 : s * u ∈ 𝔭₂ := hsu ▸ (mem_iff_minpoly_dvd 𝔭₂ h₂0 x f hf hfx p).2 hdv
  exact (Ideal.mul_unit_mem_iff_mem 𝔭₂ hu).1 h2

/-- HEADLINE (generic form): two primes over `(0)` below a common prime coincide. -/
theorem eq_of_le_of_comap_eq_bot (x : S) (f : B[X]) (hf : f.Monic) (hfx : aeval x f = 0)
    (hd : IsUnit (aeval x (derivative f)))
    (hgen : ∀ s : S, ∃ p : B[X], ∃ u : S, IsUnit u ∧ s * u = aeval x p)
    {𝔮 𝔭₁ 𝔭₂ : Ideal S} [𝔮.IsPrime] [𝔭₁.IsPrime] [𝔭₂.IsPrime]
    (h₁ : 𝔭₁ ≤ 𝔮) (h₂ : 𝔭₂ ≤ 𝔮)
    (h₁0 : 𝔭₁.comap (algebraMap B S) = ⊥) (h₂0 : 𝔭₂.comap (algebraMap B S) = ⊥) :
    𝔭₁ = 𝔭₂ := by
  have heq := minpoly_eq_of_le x f hf hfx hd h₁ h₂ h₁0 h₂0
  exact le_antisymm (le_of_minpoly_eq x f hf hfx hgen h₁0 h₂0 heq)
    (le_of_minpoly_eq x f hf hfx hgen h₂0 h₁0 heq.symm)

/-- HEADLINE: a standard etale algebra over an integrally closed domain is unibranch: two primes
lying over `(0)` and contained in a common prime coincide. -/
theorem unibranch (P : StandardEtalePresentation B S)
    {𝔮 𝔭₁ 𝔭₂ : Ideal S} [𝔮.IsPrime] [𝔭₁.IsPrime] [𝔭₂.IsPrime]
    (h₁ : 𝔭₁ ≤ 𝔮) (h₂ : 𝔭₂ ≤ 𝔮)
    (h₁0 : 𝔭₁.comap (algebraMap B S) = ⊥) (h₂0 : 𝔭₂.comap (algebraMap B S) = ⊥) :
    𝔭₁ = 𝔭₂ :=
  eq_of_le_of_comap_eq_bot P.x P.f P.monic_f P.hasMap.1 P.hasMap.isUnit_derivative_f
    (fun s => by
      obtain ⟨p, n, e⟩ := P.exists_mul_aeval_x_g_pow_eq_aeval_x s
      exact ⟨p, _, P.hasMap.2.pow n, e⟩) h₁ h₂ h₁0 h₂0

end RamanujanPetersson.EtSheaves.Unibranch


