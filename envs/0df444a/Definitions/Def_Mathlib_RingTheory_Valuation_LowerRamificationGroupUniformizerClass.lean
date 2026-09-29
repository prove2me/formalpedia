-- Prove2me | Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupUniformizerClass
-- name    : Mathlib_RingTheory_Valuation_LowerRamificationGroupUniformizerClass
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/f7bdb7b8-6e5b-54d4-aeaf-e8cd005e5ad5
-- title:
--   Uniformizer units for group actions on local rings
-- statement:
--   Standing context: a commutative local ring $R$ with a group $G$ acting by ring automorphisms (`MulSemiringAction`), and the project's lower ramification filtration $G_i=$ [`IsLocalRing.lowerRamificationGroup R G i`](../def/Mathlib_RingTheory_Valuation_LowerRamificationGroup.html#L58), which by definition is the inertia subgroup of $\mathfrak m^{i+1}$, i.e. the set of $\sigma$ with $\sigma\cdot x-x\in\mathfrak m^{i+1}$ for every $x\in R$. The module collects the elementary theory of the unit attached to a $G$-translate of a generator of the maximal ideal. First, [`Ideal.pointwise_smul_span_singleton`](../def/Mathlib_RingTheory_Valuation_LowerRamificationGroupUniformizerClass.html#L12) identifies $g\cdot(a)$ with $(g\cdot a)$ for the pointwise action on ideals, whence `maximalIdeal_eq_span_smul_of_eq_span`: if $\mathfrak m=(\varpi)$ then $\mathfrak m=(\sigma\cdot\varpi)$ for every $\sigma$, and, over a discrete valuation ring, `irreducible_smul`: translates of a uniformizer are uniformizers. For $R$ a domain, `exists_smul_uniformizer_eq_unit_mul` gives a unit $u\in R^\times$ with $\sigma\cdot\varpi=u\varpi$; `smul_uniformizer_unit_unique` and `smul_uniformizer_unit_one` show $u$ is determined by $\sigma$ (given $\varpi\neq0$) and equals $1$ for $\sigma=1$. In all later lemmas the unit is not constructed but passed as a hypothesis $\sigma\cdot\varpi=u\varpi$. The congruence layer: if $\sigma\in G_i$ then $u-1\in\mathfrak m^{i}$; the multiplicativity law $w=u\,\sigma(v)$ for $\sigma$, $\tau$, $\sigma\tau$ with units $u,v,w$, the consequence $u\,\sigma(v)=1$ for $\tau=\sigma^{-1}$, and, for $\sigma\in G_i$, the congruences $w\equiv uv$ and (for a second generator $\varpi'$ with unit $u'$) $u'\equiv u$, $u'u^{-1}\equiv1$ modulo $\mathfrak m^{i+1}$, so the class of $u$ modulo $\mathfrak m^{i+1}$ is independent of the chosen generator. Conversely, `mem_lowerRamificationGroup_of_smul_uniformizer_unit_sub_one_mem_pow` deduces $\sigma\in G_i$ from $u-1\in\mathfrak m^i$ under the explicit hypothesis $\sigma\cdot\varpi-\varpi\mid\sigma\cdot x-x$ for all $x$, giving the equivalence $\sigma\in G_i\iff u-1\in\mathfrak m^i$ in that situation. The final section transfers existence, the $\mathfrak m^i$-congruence and the multiplicativity law to a valuation subring $A$ of a field extension $L/K$, with $G$ the decomposition subgroup $\mathrm{Dec}(A/K)$ and $A$'s lower ramification filtration.
--
--   **Relation to Mathlib.** The lower ramification filtration used here is the project's [`IsLocalRing.lowerRamificationGroup`](../def/Mathlib_RingTheory_Valuation_LowerRamificationGroup.html#L58) / [`ValuationSubring.lowerRamificationGroup`](../def/Mathlib_RingTheory_Valuation_LowerRamificationGroup.html#L130), defined as the inertia of a power of the maximal ideal; everything else is stated in terms of Mathlib notions (the pointwise action on ideals, `IsDiscreteValuationRing`, `ValuationSubring.decompositionSubgroup`).
--
--   **Where it is used.** These lemmas supply the uniformizer-class description of the lower ramification filtration used in the local ramification theory underlying the study of the Galois representations attached to elliptic curves and modular forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_RingTheory_Valuation_LowerRamificationGroupUniformizerClass.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Pointwise

namespace Ideal

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [MulSemiringAction G R]

theorem pointwise_smul_span_singleton (g : G) (a : R) :
    g • Ideal.span {a} = Ideal.span {g • a} := by
  rw [Ideal.pointwise_smul_def, Ideal.map_span, Set.image_singleton]
  rfl

end Ideal

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

theorem maximalIdeal_eq_span_smul_of_eq_span {ϖ : R}
    (hϖ : maximalIdeal R = Ideal.span {ϖ}) (σ : G) :
    maximalIdeal R = Ideal.span {σ • ϖ} := by
  conv_lhs => rw [← pointwise_smul_maximalIdeal (G := G) σ, hϖ]
  rw [Ideal.pointwise_smul_span_singleton]

omit [IsLocalRing R] in

theorem irreducible_smul [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R}
    (hϖ : Irreducible ϖ) (σ : G) : Irreducible (σ • ϖ) :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
    (maximalIdeal_eq_span_smul_of_eq_span hϖ.maximalIdeal_eq σ)

theorem exists_smul_uniformizer_eq_unit_mul [IsDomain R] {ϖ : R}
    (hϖ : maximalIdeal R = Ideal.span {ϖ}) (σ : G) :
    ∃ u : Rˣ, σ • ϖ = (u : R) * ϖ := by
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp
    (hϖ.symm.trans (maximalIdeal_eq_span_smul_of_eq_span hϖ σ))
  exact ⟨u, by rw [← hu, mul_comm]⟩

omit [IsLocalRing R] in

theorem exists_smul_uniformizer_eq_unit_mul_of_irreducible [IsDomain R]
    [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ) (σ : G) :
    ∃ u : Rˣ, σ • ϖ = (u : R) * ϖ :=
  exists_smul_uniformizer_eq_unit_mul hϖ.maximalIdeal_eq σ

omit [IsLocalRing R] in

theorem smul_uniformizer_unit_unique [IsDomain R] {ϖ : R} (hϖ0 : ϖ ≠ 0) {σ : G} {u u' : Rˣ}
    (hu : σ • ϖ = (u : R) * ϖ) (hu' : σ • ϖ = (u' : R) * ϖ) : u = u' :=
  Units.ext (mul_right_cancel₀ hϖ0 (hu.symm.trans hu'))

omit [IsLocalRing R] in

theorem smul_uniformizer_unit_one [IsDomain R] {ϖ : R} (hϖ0 : ϖ ≠ 0) {u : Rˣ}
    (hu : (1 : G) • ϖ = (u : R) * ϖ) : u = 1 := by
  refine smul_uniformizer_unit_unique hϖ0 hu ?_
  rw [one_smul, Units.val_one, one_mul]

theorem smul_uniformizer_unit_sub_one_mem_pow_of_mem_lowerRamificationGroup [IsDomain R]
    {ϖ : R} (hϖ : maximalIdeal R = Ideal.span {ϖ}) (hϖ0 : ϖ ≠ 0) {σ : G} {u : Rˣ}
    (hu : σ • ϖ = (u : R) * ϖ) {i : ℕ} (hσ : σ ∈ lowerRamificationGroup R G i) :
    (u : R) - 1 ∈ maximalIdeal R ^ i := by
  have hmem : σ • ϖ - ϖ ∈ maximalIdeal R ^ (i + 1) := (mem_lowerRamificationGroup.mp hσ) ϖ
  rw [hϖ, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hkey : ((u : R) - 1) * ϖ = (ϖ ^ i * c) * ϖ := by
    have h1 : (u : R) * ϖ - ϖ = ϖ ^ (i + 1) * c := by rw [← hu]; exact hc
    calc ((u : R) - 1) * ϖ = (u : R) * ϖ - ϖ := by ring
      _ = ϖ ^ (i + 1) * c := h1
      _ = (ϖ ^ i * c) * ϖ := by ring
  rw [hϖ, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact ⟨c, mul_right_cancel₀ hϖ0 hkey⟩

theorem smul_uniformizer_unit_sub_one_mem_pow_succ_of_mem_lowerRamificationGroup_succ
    [IsDomain R] {ϖ : R} (hϖ : maximalIdeal R = Ideal.span {ϖ}) (hϖ0 : ϖ ≠ 0) {σ : G} {u : Rˣ}
    (hu : σ • ϖ = (u : R) * ϖ) {i : ℕ} (hσ : σ ∈ lowerRamificationGroup R G (i + 1)) :
    (u : R) - 1 ∈ maximalIdeal R ^ (i + 1) :=
  smul_uniformizer_unit_sub_one_mem_pow_of_mem_lowerRamificationGroup hϖ hϖ0 hu hσ

theorem smul_uniformizer_unit_sub_one_mem_pow_of_mem_lowerRamificationGroup_of_irreducible
    [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ) {σ : G} {u : Rˣ}
    (hu : σ • ϖ = (u : R) * ϖ) {i : ℕ} (hσ : σ ∈ lowerRamificationGroup R G i) :
    (u : R) - 1 ∈ maximalIdeal R ^ i :=
  smul_uniformizer_unit_sub_one_mem_pow_of_mem_lowerRamificationGroup hϖ.maximalIdeal_eq
    hϖ.ne_zero hu hσ

omit [IsLocalRing R] in

theorem smul_uniformizer_unit_cocycle [IsDomain R] {ϖ : R} (hϖ0 : ϖ ≠ 0) {σ τ : G}
    {u v w : Rˣ} (hu : σ • ϖ = (u : R) * ϖ) (hv : τ • ϖ = (v : R) * ϖ)
    (hw : (σ * τ) • ϖ = (w : R) * ϖ) :
    (w : R) = (u : R) * (σ • (v : R)) := by
  have h1 : (σ * τ) • ϖ = (σ • (v : R)) * ((u : R) * ϖ) := by
    rw [mul_smul, hv, smul_mul', hu]
  have h2 : (w : R) * ϖ = ((u : R) * (σ • (v : R))) * ϖ := by
    rw [← hw, h1]; ring
  exact mul_right_cancel₀ hϖ0 h2

omit [IsLocalRing R] in

theorem smul_uniformizer_unit_mul_smul_inv_unit [IsDomain R] {ϖ : R} (hϖ0 : ϖ ≠ 0) {σ : G}
    {u v : Rˣ} (hu : σ • ϖ = (u : R) * ϖ) (hv : σ⁻¹ • ϖ = (v : R) * ϖ) :
    (u : R) * (σ • (v : R)) = 1 := by
  have hw : (σ * σ⁻¹) • ϖ = ((1 : Rˣ) : R) * ϖ := by
    rw [mul_inv_cancel, one_smul, Units.val_one, one_mul]
  have := smul_uniformizer_unit_cocycle hϖ0 hu hv hw
  rw [← this, Units.val_one]

theorem smul_uniformizer_unit_mul_sub_mul_mem_pow_succ [IsDomain R] {ϖ : R} (hϖ0 : ϖ ≠ 0)
    {σ τ : G} {u v w : Rˣ} (hu : σ • ϖ = (u : R) * ϖ) (hv : τ • ϖ = (v : R) * ϖ)
    (hw : (σ * τ) • ϖ = (w : R) * ϖ) {i : ℕ} (hσ : σ ∈ lowerRamificationGroup R G i) :
    (w : R) - (u : R) * (v : R) ∈ maximalIdeal R ^ (i + 1) := by
  have hcoc := smul_uniformizer_unit_cocycle hϖ0 hu hv hw
  have hexp : (w : R) - (u : R) * (v : R) = (u : R) * (σ • (v : R) - (v : R)) := by
    rw [hcoc]; ring
  rw [hexp]
  exact Ideal.mul_mem_left _ _ ((mem_lowerRamificationGroup.mp hσ) (v : R))

theorem smul_uniformizer_unit_sub_mem_pow_succ_of_spans [IsDomain R] {ϖ ϖ' : R}
    (hϖ : maximalIdeal R = Ideal.span {ϖ}) (hϖ' : maximalIdeal R = Ideal.span {ϖ'})
    (hϖ0 : ϖ ≠ 0) {σ : G} {u u' : Rˣ} (hu : σ • ϖ = (u : R) * ϖ)
    (hu' : σ • ϖ' = (u' : R) * ϖ') {i : ℕ} (hσ : σ ∈ lowerRamificationGroup R G i) :
    (u' : R) - (u : R) ∈ maximalIdeal R ^ (i + 1) := by
  have hσ' : ∀ x : R, σ • x - x ∈ maximalIdeal R ^ (i + 1) := mem_lowerRamificationGroup.mp hσ

  obtain ⟨c, hc⟩ := Ideal.span_singleton_eq_span_singleton.mp (hϖ.symm.trans hϖ')

  have h1 : σ • ϖ' = ((u : R) * ϖ) * (σ • (c : R)) := by
    rw [← hc, smul_mul', hu]
  have hkey : ((u : R) * (σ • (c : R))) * ϖ = ((u' : R) * (c : R)) * ϖ := by
    calc ((u : R) * (σ • (c : R))) * ϖ = ((u : R) * ϖ) * (σ • (c : R)) := by ring
      _ = σ • ϖ' := h1.symm
      _ = (u' : R) * ϖ' := hu'
      _ = (u' : R) * (ϖ * (c : R)) := by rw [← hc]
      _ = ((u' : R) * (c : R)) * ϖ := by ring
  have hkey' : (u : R) * (σ • (c : R)) = (u' : R) * (c : R) := mul_right_cancel₀ hϖ0 hkey
  have hu'eq : (u' : R) = (u : R) * (σ • (c : R)) * ((c⁻¹ : Rˣ) : R) := by
    rw [hkey', mul_assoc, Units.mul_inv, mul_one]
  have hfinal : (u' : R) - (u : R) =
      ((u : R) * ((c⁻¹ : Rˣ) : R)) * (σ • (c : R) - (c : R)) := by
    calc (u' : R) - (u : R)
        = (u : R) * (σ • (c : R)) * ((c⁻¹ : Rˣ) : R)
            - (u : R) * (((c⁻¹ : Rˣ) : R) * (c : R)) := by
          rw [Units.inv_mul, mul_one, ← hu'eq]
      _ = ((u : R) * ((c⁻¹ : Rˣ) : R)) * (σ • (c : R) - (c : R)) := by ring
  rw [hfinal]
  exact Ideal.mul_mem_left _ _ (hσ' (c : R))

theorem smul_uniformizer_unit_mul_inv_sub_one_mem_pow_succ_of_spans [IsDomain R] {ϖ ϖ' : R}
    (hϖ : maximalIdeal R = Ideal.span {ϖ}) (hϖ' : maximalIdeal R = Ideal.span {ϖ'})
    (hϖ0 : ϖ ≠ 0) {σ : G} {u u' : Rˣ} (hu : σ • ϖ = (u : R) * ϖ)
    (hu' : σ • ϖ' = (u' : R) * ϖ') {i : ℕ} (hσ : σ ∈ lowerRamificationGroup R G i) :
    (u' : R) * ((u⁻¹ : Rˣ) : R) - 1 ∈ maximalIdeal R ^ (i + 1) := by
  have h := smul_uniformizer_unit_sub_mem_pow_succ_of_spans hϖ hϖ' hϖ0 hu hu' hσ
  have hexp : (u' : R) * ((u⁻¹ : Rˣ) : R) - 1 = ((u' : R) - (u : R)) * ((u⁻¹ : Rˣ) : R) := by
    calc (u' : R) * ((u⁻¹ : Rˣ) : R) - 1
        = (u' : R) * ((u⁻¹ : Rˣ) : R) - (u : R) * ((u⁻¹ : Rˣ) : R) := by rw [Units.mul_inv]
      _ = ((u' : R) - (u : R)) * ((u⁻¹ : Rˣ) : R) := by ring
  rw [hexp]
  exact Ideal.mul_mem_right _ _ h

theorem mem_lowerRamificationGroup_of_smul_uniformizer_unit_sub_one_mem_pow {ϖ : R}
    (hϖm : ϖ ∈ maximalIdeal R) {σ : G} (hdvd : ∀ x : R, σ • ϖ - ϖ ∣ σ • x - x) {u : Rˣ}
    (hu : σ • ϖ = (u : R) * ϖ) {i : ℕ} (hmem : (u : R) - 1 ∈ maximalIdeal R ^ i) :
    σ ∈ lowerRamificationGroup R G i := by
  have hϖstep : σ • ϖ - ϖ ∈ maximalIdeal R ^ (i + 1) := by
    have hexp : σ • ϖ - ϖ = ((u : R) - 1) * ϖ := by rw [hu]; ring
    rw [hexp, pow_succ]
    exact Ideal.mul_mem_mul hmem hϖm
  rw [mem_lowerRamificationGroup]
  intro x
  obtain ⟨d, hd⟩ := hdvd x
  rw [hd]
  exact Ideal.mul_mem_right _ _ hϖstep

theorem mem_lowerRamificationGroup_iff_smul_uniformizer_unit_sub_one_mem_pow [IsDomain R]
    {ϖ : R} (hϖ : maximalIdeal R = Ideal.span {ϖ}) (hϖ0 : ϖ ≠ 0) {σ : G}
    (hdvd : ∀ x : R, σ • ϖ - ϖ ∣ σ • x - x) {u : Rˣ} (hu : σ • ϖ = (u : R) * ϖ) {i : ℕ} :
    σ ∈ lowerRamificationGroup R G i ↔ (u : R) - 1 ∈ maximalIdeal R ^ i := by
  constructor
  · exact fun hσ =>
      smul_uniformizer_unit_sub_one_mem_pow_of_mem_lowerRamificationGroup hϖ hϖ0 hu hσ
  · refine fun hmem =>
      mem_lowerRamificationGroup_of_smul_uniformizer_unit_sub_one_mem_pow ?_ hdvd hu hmem
    rw [hϖ]
    exact Ideal.mem_span_singleton_self ϖ

theorem mem_lowerRamificationGroup_succ_iff_smul_uniformizer_unit_sub_one_mem_pow_succ
    [IsDomain R] {ϖ : R} (hϖ : maximalIdeal R = Ideal.span {ϖ}) (hϖ0 : ϖ ≠ 0) {σ : G}
    (hdvd : ∀ x : R, σ • ϖ - ϖ ∣ σ • x - x) {u : Rˣ} (hu : σ • ϖ = (u : R) * ϖ) {i : ℕ} :
    σ ∈ lowerRamificationGroup R G (i + 1) ↔ (u : R) - 1 ∈ maximalIdeal R ^ (i + 1) :=
  mem_lowerRamificationGroup_iff_smul_uniformizer_unit_sub_one_mem_pow hϖ hϖ0 hdvd hu

end IsLocalRing

namespace ValuationSubring

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {A : ValuationSubring L}

theorem exists_smul_uniformizer_eq_unit_mul {ϖ : A}
    (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ}) (σ : A.decompositionSubgroup K) :
    ∃ u : Aˣ, σ • ϖ = (u : A) * ϖ :=
  IsLocalRing.exists_smul_uniformizer_eq_unit_mul hϖ σ

theorem smul_uniformizer_unit_sub_one_mem_pow_of_mem_lowerRamificationGroup {ϖ : A}
    (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ}) (hϖ0 : ϖ ≠ 0)
    {σ : A.decompositionSubgroup K} {u : Aˣ} (hu : σ • ϖ = (u : A) * ϖ) {i : ℕ}
    (hσ : σ ∈ A.lowerRamificationGroup K i) :
    (u : A) - 1 ∈ IsLocalRing.maximalIdeal A ^ i :=
  IsLocalRing.smul_uniformizer_unit_sub_one_mem_pow_of_mem_lowerRamificationGroup hϖ hϖ0 hu hσ

theorem smul_uniformizer_unit_cocycle {ϖ : A} (hϖ0 : ϖ ≠ 0)
    {σ τ : A.decompositionSubgroup K} {u v w : Aˣ} (hu : σ • ϖ = (u : A) * ϖ)
    (hv : τ • ϖ = (v : A) * ϖ) (hw : (σ * τ) • ϖ = (w : A) * ϖ) :
    (w : A) = (u : A) * (σ • (v : A)) :=
  IsLocalRing.smul_uniformizer_unit_cocycle hϖ0 hu hv hw

end ValuationSubring

section Gates

example (σ : ℤ_[3] ≃ₐ[ℤ] ℤ_[3]) :
    ∃ u : ℤ_[3]ˣ, σ • ((3 : ℕ) : ℤ_[3]) = (u : ℤ_[3]) * ((3 : ℕ) : ℤ_[3]) :=
  IsLocalRing.exists_smul_uniformizer_eq_unit_mul PadicInt.maximalIdeal_eq_span_p σ

example :
    ((1 : ℤ_[3]ˣ) : ℤ_[3]) - 1 ∈ IsLocalRing.maximalIdeal ℤ_[3] ^ 5 :=
  IsLocalRing.smul_uniformizer_unit_sub_one_mem_pow_of_mem_lowerRamificationGroup
    (G := ℤ_[3] ≃ₐ[ℤ] ℤ_[3]) PadicInt.maximalIdeal_eq_span_p PadicInt.irreducible_p.ne_zero
    (σ := 1) (u := 1) (by rw [one_smul, Units.val_one, one_mul]) (one_mem _)

example {R : Type*} [CommRing R] [IsLocalRing R] [IsDomain R] {G : Type*} [Group G]
    [MulSemiringAction G R] {ϖ : R} (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (hϖ0 : ϖ ≠ 0) (i : ℕ) :
    (1 : G) ∈ IsLocalRing.lowerRamificationGroup R G i ↔
      ((1 : Rˣ) : R) - 1 ∈ IsLocalRing.maximalIdeal R ^ i :=
  IsLocalRing.mem_lowerRamificationGroup_iff_smul_uniformizer_unit_sub_one_mem_pow hϖ hϖ0
    (fun x => by simp) (by rw [one_smul, Units.val_one, one_mul])

example {R : Type*} [CommRing R] [IsLocalRing R] [IsDomain R] {G : Type*} [Group G]
    [MulSemiringAction G R] {ϖ : R} (hϖ0 : ϖ ≠ 0) :
    ((1 : Rˣ) : R) = ((1 : Rˣ) : R) * ((1 : G) • ((1 : Rˣ) : R)) :=
  IsLocalRing.smul_uniformizer_unit_cocycle (σ := (1 : G)) (τ := (1 : G)) hϖ0
    (by rw [one_smul, Units.val_one, one_mul]) (by rw [one_smul, Units.val_one, one_mul])
    (by rw [mul_one, one_smul, Units.val_one, one_mul])

end Gates

/--
info: 'IsLocalRing.exists_smul_uniformizer_eq_unit_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.exists_smul_uniformizer_eq_unit_mul

/--
info: 'IsLocalRing.smul_uniformizer_unit_sub_one_mem_pow_of_mem_lowerRamificationGroup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms IsLocalRing.smul_uniformizer_unit_sub_one_mem_pow_of_mem_lowerRamificationGroup

/--
info: 'IsLocalRing.smul_uniformizer_unit_cocycle' depends on axioms: [propext]
-/
#guard_msgs in #print axioms IsLocalRing.smul_uniformizer_unit_cocycle

/--
info: 'IsLocalRing.smul_uniformizer_unit_mul_sub_mul_mem_pow_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.smul_uniformizer_unit_mul_sub_mul_mem_pow_succ

/--
info: 'IsLocalRing.smul_uniformizer_unit_sub_mem_pow_succ_of_spans' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.smul_uniformizer_unit_sub_mem_pow_succ_of_spans

/--
info: 'IsLocalRing.mem_lowerRamificationGroup_of_smul_uniformizer_unit_sub_one_mem_pow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms IsLocalRing.mem_lowerRamificationGroup_of_smul_uniformizer_unit_sub_one_mem_pow

/--
info: 'IsLocalRing.mem_lowerRamificationGroup_iff_smul_uniformizer_unit_sub_one_mem_pow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms IsLocalRing.mem_lowerRamificationGroup_iff_smul_uniformizer_unit_sub_one_mem_pow

/--
info: 'IsLocalRing.irreducible_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.irreducible_smul

/--
info: 'ValuationSubring.smul_uniformizer_unit_sub_one_mem_pow_of_mem_lowerRamificationGroup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ValuationSubring.smul_uniformizer_unit_sub_one_mem_pow_of_mem_lowerRamificationGroup

/--
info: 'Ideal.pointwise_smul_span_singleton' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Ideal.pointwise_smul_span_singleton


