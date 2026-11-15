-- Prove2me | Definitions.Def_RPLib_S4_SwanGlobF
-- name    : RPLib_S4_SwanGlobF
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T10:17:25.099405+00:00
-- url     : https://prove2.me/theorems/95a10698-aa96-4438-900d-741445bc602a
-- title:
--   Fixed rings of Dedekind domains under finite groups, and fixed fractions
-- statement:
--   Let a finite group $H$ act on a Dedekind domain $B$ by ring automorphisms. The file shows that the fixed subring $B^H$ is again a Dedekind domain, that $B$ is integral and finite over $B^H$, and that every $H$-fixed element of the fraction field of $B$ is a quotient of elements of $B^H$: $$\operatorname{Frac}(B)^H = \operatorname{Frac}(B^H).$$
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (Swan conductors and wild ramification at infinity, used for Weil-type bounds of exponential sums). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. Neukirch, Algebraic Number Theory, Grundlehren 322, Springer (1999), Chapter I, Section 9 (Hilbert's ramification theory), Chapter I

import Mathlib

/-!
# S4-Swan (K2), part 15: fixed rings of Dedekind domains, and fixed fractions

* `isDedekindDomain_fixed`: if `S` is a Dedekind domain, finite and torsion-free over a Dedekind domain `R`, and
  `H` is a group of `R`-automorphisms of `S`, then the fixed ring `S^H = FixedPoints.subalgebra R S H` is a
  Dedekind domain (Noetherian as an `R`-submodule of `S`, dimension one as an integral extension of `R`,
  integrally closed because `S` is and `H` fixes the integral closure inside `Frac (S^H)`), and `S` is finite
  over it.
* `exists_fixed_mul_eq`: for a finite group `H` acting compatibly on `S` and `L = Frac S`, every `H`-fixed
  `x ∈ L` is a quotient of `H`-fixed elements of `S` (multiply by the norm `∏_h h b` of a denominator `b`).
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.Swan

section FixedRing

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S] (H : Subgroup G)

theorem mem_fixedSubalgebra_iff (s : S) :
    s ∈ FixedPoints.subalgebra R S H ↔ ∀ h : H, h • s = s := Iff.rfl

variable [Module.Finite R S]

theorem isIntegral_fixedSubalgebra :
    Algebra.IsIntegral R (FixedPoints.subalgebra R S H) :=
  Algebra.IsIntegral.of_injective (FixedPoints.subalgebra R S H).val Subtype.val_injective

theorem finite_fixed : Module.Finite (FixedPoints.subalgebra R S H) S :=
  Module.Finite.of_restrictScalars_finite R _ S

variable [IsDedekindDomain R] [IsDedekindDomain S]

/-- The fixed ring of a group of automorphisms of a finite Dedekind extension is Dedekind. -/
theorem isDedekindDomain_fixed : IsDedekindDomain (FixedPoints.subalgebra R S H) := by
  set A := FixedPoints.subalgebra R S H
  have hN : IsNoetherian R A := isNoetherian_of_injective A.val.toLinearMap Subtype.val_injective
  have : Algebra.IsIntegral R A := isIntegral_fixedSubalgebra H
  refine (isDedekindDomain_iff A (FractionRing A)).2 ⟨inferInstance, isNoetherian_of_tower R hN,
    Ring.DimensionLEOne.of_isIntegral R A, ?_⟩
  intro x hx
  let FS := FractionRing S
  have hinj : Function.Injective (algebraMap A FS) := by
    rw [IsScalarTower.algebraMap_eq A S FS]
    exact (IsFractionRing.injective S FS).comp Subtype.val_injective
  let f : FractionRing A →ₐ[A] FS := IsFractionRing.liftAlgHom (g := Algebra.ofId A FS) hinj
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
    (IsIntegral.tower_top (A := S) (hx.map f))
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  have hb0 : (b : S) ≠ 0 := fun h => nonZeroDivisors.ne_zero hb (Subtype.ext h)
  have hfab : f (algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b) =
      algebraMap S FS a / algebraMap S FS b := by
    rw [map_div₀, AlgHom.commutes, AlgHom.commutes, IsScalarTower.algebraMap_apply A S FS,
      IsScalarTower.algebraMap_apply A S FS]
    rfl
  have hsb : s * b = a := by
    apply IsFractionRing.injective S FS
    have hb' : algebraMap S FS b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective S FS)).2 hb0
    rw [map_mul, hs, hfab, div_mul_cancel₀ _ hb']
  have hfix : ∀ σ : H, σ • s = s := by
    intro σ
    have h1 : σ • (s * (b : S)) = s * b := by rw [hsb]; exact a.2 σ
    rw [smul_mul', b.2 σ] at h1
    exact mul_right_cancel₀ hb0 h1
  refine ⟨⟨s, hfix⟩, f.toRingHom.injective ?_⟩
  change f (algebraMap A (FractionRing A) ⟨s, hfix⟩) = _
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A S FS]
  exact hs

end FixedRing

section NormTrick

variable {S : Type*} [CommRing S] [IsDomain S] {L : Type*} [Field L] [Algebra S L]
  [IsFractionRing S L] {G : Type*} [Group G] [MulSemiringAction G S] [MulSemiringAction G L]
  (hc : ∀ (σ : G) (s : S), σ • algebraMap S L s = algebraMap S L (σ • s))
  (H : Subgroup G) [Finite H]
include hc

/-- An `H`-fixed element of `L = Frac S` is a quotient of `H`-fixed elements of `S`. -/
theorem exists_fixed_mul_eq (x : L) (hx : ∀ h ∈ H, h • x = x) :
    ∃ c1 c2 : S, (∀ h ∈ H, h • c1 = c1) ∧ (∀ h ∈ H, h • c2 = c2) ∧ c2 ≠ 0 ∧
      x * algebraMap S L c2 = algebraMap S L c1 := by
  classical
  letI := Fintype.ofFinite H
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb' : algebraMap S L b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective S L)).2 hb0
  set P : S := ∏ h ∈ Finset.univ.erase (1 : H), (h : G) • b with hP
  have hc2 : ∏ h : H, (h : G) • b = b * P := by
    rw [hP, ← Finset.mul_prod_erase Finset.univ (fun h : H => (h : G) • b) (Finset.mem_univ 1)]
    simp
  have hfix2 : ∀ g ∈ H, g • ∏ h : H, (h : G) • b = ∏ h : H, (h : G) • b := by
    intro g hg
    rw [Finset.smul_prod']
    refine Fintype.prod_equiv (Equiv.mulLeft (⟨g, hg⟩ : H)) _ _ (fun h => ?_)
    rw [Equiv.coe_mulLeft, Subgroup.coe_mul, Subgroup.coe_mk, mul_smul]
  have hmul : algebraMap S L a / algebraMap S L b * algebraMap S L (∏ h : H, (h : G) • b) =
      algebraMap S L (a * P) := by
    rw [hc2, map_mul, map_mul, div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_left₀ _ hb']
  refine ⟨a * P, ∏ h : H, (h : G) • b, fun g hg => ?_, hfix2, ?_, hmul⟩
  · apply IsFractionRing.injective S L
    rw [← hc, ← hmul, smul_mul', hx g hg, hc, hfix2 g hg]
  · rw [Finset.prod_ne_zero_iff]
    exact fun h _ => (smul_ne_zero_iff_ne _).2 hb0

end NormTrick

end RamanujanPetersson.Swan


