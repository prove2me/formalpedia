-- Prove2me | Definitions.Def_HaarMeasure_HaarChar_FiniteOrderAutomorphism
-- name    : HaarMeasure_HaarChar_FiniteOrderAutomorphism
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/76a07415-bd08-504d-a2f6-39e9c8a96d8c
-- title:
--   Haar character of finite-order continuous group automorphisms
-- statement:
--   Throughout, $G$ is a locally compact topological group with its Borel $\sigma$-algebra, and $\varphi : G \simeq_{t*} G$ is a continuous group automorphism with continuous inverse. The first result is that iterating multiplies the Haar character: for each $n$ there is a continuous automorphism whose underlying map is the $n$-fold iterate $\varphi^{[n]}$ and whose character is $\mathrm{mulEquivHaarChar}(\varphi)^n$. Hence if $\varphi^{[\ell]} = \mathrm{id}$ pointwise then $\mathrm{mulEquivHaarChar}(\varphi)^{\ell} = 1$, and for $\ell \neq 0$ the character itself is $1$, since the only $\ell$-th root of unity in $\mathbb{R}_{\geq 0}$ is $1$; the same holds for $\varphi^{-1}$. The consequences drawn, for a regular Haar measure $\mu$ on $G$ and $\varphi$ with $\varphi^{[\ell]} = \mathrm{id}$, $\ell \neq 0$, are: $\varphi_*\mu = \mu$ and $(\varphi^{-1})_*\mu = \mu$; $\varphi$ and $\varphi^{-1}$ are measure-preserving for $\mu$; $\mu(\varphi^{-1}X) = \mu(X)$ for every set $X$; and $\int f(\varphi g)\,d\mu = \int f\,d\mu$ for real-valued $f$. Two set-theoretic lemmas record that $\varphi^{-1}D = D$ implies stability under the inverse and follows from $\varphi(D) = D$; with these, a measurable $\varphi$-stable $D$ yields that $\varphi$ and $\varphi^{-1}$ preserve the restriction $\mu|_D$. Variants restate this for a bare group isomorphism together with continuity of it and of its inverse. Two automorphisms are defined: `invContinuousMulEquiv`, inversion $g \mapsto g^{-1}$ on a commutative topological group viewed as a continuous automorphism, with square the identity, whence $\mu$ is inversion-invariant; and `doublingContinuousAddEquiv`, the map $x \mapsto 2x$ on $\mathbb{R}$ with inverse $x \mapsto 2^{-1}x$, whose additive Haar character is shown to be $\neq 1$ because the preimage of $[0,1]$ is $[0,2^{-1}]$. Further small items treat negation on $\mathbb{R}$, its invariance of Lebesgue measure and of Lebesgue measure restricted to $[-1,1]$.
--
--   **Relation to Mathlib.** Built on Mathlib's `mulEquivHaarChar`/`addEquivAddHaarChar` and its API (behaviour under composition and inversion, and the scaling identities for pushforward and for measures of preimages); the finite-order vanishing statement is added here. The inversion and negation invariance statements also exist in Mathlib as `Measure.map_inv_eq_self` and `Measure.map_neg_eq_self`, and the statements `gate_inv_two_routes` and `gate_real_two_routes` assert the two formulations simultaneously.
--
--   **Where it is used.** These invariance statements are used downstream wherever a Haar measure has to be known invariant under an automorphism of finite order — typically inversion or negation — in the measure-theoretic input concerning Haar characters of rings and of adelic groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_HaarMeasure_HaarChar_FiniteOrderAutomorphism.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory.Measure
open scoped NNReal

namespace MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [BorelSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

private lemma nnreal_eq_one_of_pow_eq_one {x : ℝ≥0} {n : ℕ} (hn : n ≠ 0) (h : x ^ n = 1) :
    x = 1 := by
  rcases lt_trichotomy x 1 with hlt | heq | hgt
  · exact absurd h (pow_lt_one₀ zero_le hlt hn).ne
  · exact heq
  · exact absurd h (one_lt_pow₀ hgt hn).ne'

@[to_additive]
lemma exists_continuousMulEquiv_iterate_mulEquivHaarChar (φ : G ≃ₜ* G) (n : ℕ) :
    ∃ ψ : G ≃ₜ* G, ⇑ψ = (⇑φ)^[n] ∧ mulEquivHaarChar ψ = mulEquivHaarChar φ ^ n := by
  induction n with
  | zero =>
      refine ⟨ContinuousMulEquiv.refl G, funext fun g => ?_, ?_⟩
      · exact (ContinuousMulEquiv.refl_apply G g).trans (Function.iterate_zero_apply (⇑φ) g).symm
      · exact (mulEquivHaarChar_refl (G := G)).trans (pow_zero _).symm
  | succ n ih =>
      obtain ⟨ψ, hcoe, hchar⟩ := ih
      refine ⟨ψ.trans φ, funext fun g => ?_, ?_⟩
      · exact (ContinuousMulEquiv.trans_apply ψ φ g).trans
          ((congrArg (⇑φ) (congrFun hcoe g)).trans (Function.iterate_succ_apply' (⇑φ) n g).symm)
      · calc mulEquivHaarChar (ψ.trans φ)
              = mulEquivHaarChar ψ * mulEquivHaarChar φ := mulEquivHaarChar_trans
          _ = mulEquivHaarChar φ ^ n * mulEquivHaarChar φ := by rw [hchar]
          _ = mulEquivHaarChar φ ^ (n + 1) := (pow_succ _ n).symm

@[to_additive addEquivAddHaarChar_pow_eq_one_of_iterate_eq_id]
lemma mulEquivHaarChar_pow_eq_one_of_iterate_eq_id (φ : G ≃ₜ* G) {ℓ : ℕ}
    (h : ∀ g, (⇑φ)^[ℓ] g = g) : mulEquivHaarChar φ ^ ℓ = 1 := by
  obtain ⟨ψ, hcoe, hchar⟩ := exists_continuousMulEquiv_iterate_mulEquivHaarChar φ ℓ
  have hψ : ψ = ContinuousMulEquiv.refl G := by
    refine ContinuousMulEquiv.ext fun g => ?_
    rw [ContinuousMulEquiv.refl_apply]
    exact (congrFun hcoe g).trans (h g)
  rw [← hchar, hψ, mulEquivHaarChar_refl]

@[to_additive addEquivAddHaarChar_eq_one_of_iterate_eq_id]
theorem mulEquivHaarChar_eq_one_of_iterate_eq_id (φ : G ≃ₜ* G) {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (h : ∀ g, (⇑φ)^[ℓ] g = g) : mulEquivHaarChar φ = 1 :=
  nnreal_eq_one_of_pow_eq_one hℓ (mulEquivHaarChar_pow_eq_one_of_iterate_eq_id φ h)

@[to_additive addEquivAddHaarChar_symm_eq_one_of_iterate_eq_id]
theorem mulEquivHaarChar_symm_eq_one_of_iterate_eq_id (φ : G ≃ₜ* G) {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (h : ∀ g, (⇑φ)^[ℓ] g = g) : mulEquivHaarChar φ.symm = 1 := by
  rw [mulEquivHaarChar_symm, mulEquivHaarChar_eq_one_of_iterate_eq_id φ hℓ h, inv_one]

@[to_additive]
theorem map_haar_eq_self_of_iterate_eq_id (μ : Measure G) [IsHaarMeasure μ] [Regular μ]
    (φ : G ≃ₜ* G) {ℓ : ℕ} (hℓ : ℓ ≠ 0) (h : ∀ g, (⇑φ)^[ℓ] g = g) :
    μ.map φ = μ := by
  have h1 := mulEquivHaarChar_smul_map μ φ
  rwa [mulEquivHaarChar_eq_one_of_iterate_eq_id φ hℓ h, one_smul] at h1

@[to_additive]
theorem map_haar_symm_eq_self_of_iterate_eq_id (μ : Measure G) [IsHaarMeasure μ] [Regular μ]
    (φ : G ≃ₜ* G) {ℓ : ℕ} (hℓ : ℓ ≠ 0) (h : ∀ g, (⇑φ)^[ℓ] g = g) :
    μ.map φ.symm = μ := by
  have h1 := mulEquivHaarChar_smul_map μ φ.symm
  rwa [mulEquivHaarChar_symm_eq_one_of_iterate_eq_id φ hℓ h, one_smul] at h1

@[to_additive]
theorem measurePreserving_haar_of_iterate_eq_id (μ : Measure G) [IsHaarMeasure μ] [Regular μ]
    (φ : G ≃ₜ* G) {ℓ : ℕ} (hℓ : ℓ ≠ 0) (h : ∀ g, (⇑φ)^[ℓ] g = g) :
    MeasurePreserving (⇑φ) μ μ :=
  ⟨(map_continuous φ).measurable, map_haar_eq_self_of_iterate_eq_id μ φ hℓ h⟩

@[to_additive]
theorem measurePreserving_haar_symm_of_iterate_eq_id (μ : Measure G) [IsHaarMeasure μ]
    [Regular μ] (φ : G ≃ₜ* G) {ℓ : ℕ} (hℓ : ℓ ≠ 0) (h : ∀ g, (⇑φ)^[ℓ] g = g) :
    MeasurePreserving (⇑φ.symm) μ μ :=
  ⟨(map_continuous φ.symm).measurable, map_haar_symm_eq_self_of_iterate_eq_id μ φ hℓ h⟩

@[to_additive]
theorem measure_preimage_haar_eq_of_iterate_eq_id (μ : Measure G) [IsHaarMeasure μ] [Regular μ]
    (φ : G ≃ₜ* G) {ℓ : ℕ} (hℓ : ℓ ≠ 0) (h : ∀ g, (⇑φ)^[ℓ] g = g) (X : Set G) :
    μ (⇑φ ⁻¹' X) = μ X := by
  have h1 := mulEquivHaarChar_smul_preimage μ (X := X) φ
  rwa [mulEquivHaarChar_eq_one_of_iterate_eq_id φ hℓ h, one_smul] at h1

@[to_additive]
theorem integral_comp_haar_eq_of_iterate_eq_id (μ : Measure G) [IsHaarMeasure μ] [Regular μ]
    (φ : G ≃ₜ* G) {ℓ : ℕ} (hℓ : ℓ ≠ 0) (h : ∀ g, (⇑φ)^[ℓ] g = g) (f : G → ℝ) :
    ∫ g, f (φ g) ∂μ = ∫ g, f g ∂μ := by
  have hemb : MeasurableEmbedding (⇑φ) := φ.toHomeomorph.measurableEmbedding
  exact (measurePreserving_haar_of_iterate_eq_id μ φ hℓ h).integral_comp hemb f

section Stability

omit [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] in

@[to_additive]
theorem _root_.ContinuousMulEquiv.preimage_symm_eq_of_preimage_eq (φ : G ≃ₜ* G) {D : Set G}
    (hstable : ⇑φ ⁻¹' D = D) : ⇑φ.symm ⁻¹' D = D := by
  conv_lhs => rw [← hstable]
  ext g
  simp [ContinuousMulEquiv.apply_symm_apply]

omit [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] in

@[to_additive]
theorem _root_.ContinuousMulEquiv.preimage_eq_of_image_eq (φ : G ≃ₜ* G) {D : Set G}
    (hstable : ⇑φ '' D = D) : ⇑φ ⁻¹' D = D := by
  conv_lhs => rw [← hstable]
  rw [Set.preimage_image_eq D φ.injective]

end Stability

section Restricted

omit [IsTopologicalGroup G] [LocallyCompactSpace G] in

@[to_additive addEquiv_measurePreserving_restrict_of_map_eq_self]
theorem measurePreserving_restrict_of_map_eq_self (μ : Measure G) (φ : G ≃ₜ* G)
    (hmap : μ.map φ = μ) {D : Set G} (hD : MeasurableSet D) (hstable : ⇑φ ⁻¹' D = D) :
    MeasurePreserving (⇑φ) (μ.restrict D) (μ.restrict D) := by
  refine ⟨(map_continuous φ).measurable, ?_⟩
  conv_lhs => rw [← hstable]
  rw [← Measure.restrict_map (map_continuous φ).measurable hD, hmap]

@[to_additive]
theorem measurePreserving_restrict_haar_of_iterate_eq_id (μ : Measure G) [IsHaarMeasure μ]
    [Regular μ] (φ : G ≃ₜ* G) {ℓ : ℕ} (hℓ : ℓ ≠ 0) (h : ∀ g, (⇑φ)^[ℓ] g = g)
    {D : Set G} (hD : MeasurableSet D) (hstable : ⇑φ ⁻¹' D = D) :
    MeasurePreserving (⇑φ) (μ.restrict D) (μ.restrict D) :=
  measurePreserving_restrict_of_map_eq_self μ φ
    (map_haar_eq_self_of_iterate_eq_id μ φ hℓ h) hD hstable

@[to_additive]
theorem measurePreserving_restrict_haar_symm_of_iterate_eq_id (μ : Measure G) [IsHaarMeasure μ]
    [Regular μ] (φ : G ≃ₜ* G) {ℓ : ℕ} (hℓ : ℓ ≠ 0) (h : ∀ g, (⇑φ)^[ℓ] g = g)
    {D : Set G} (hD : MeasurableSet D) (hstable : ⇑φ ⁻¹' D = D) :
    MeasurePreserving (⇑φ.symm) (μ.restrict D) (μ.restrict D) :=
  measurePreserving_restrict_of_map_eq_self μ φ.symm
    (map_haar_symm_eq_self_of_iterate_eq_id μ φ hℓ h) hD
    (φ.preimage_symm_eq_of_preimage_eq hstable)

end Restricted

section MulEquivCurrency

@[to_additive]
theorem mulEquiv_measurePreserving_restrict_of_iterate_eq_id (μ : Measure G) [IsHaarMeasure μ]
    [Regular μ] (ψ : G ≃* G) (hc : Continuous ψ) (hc' : Continuous ψ.symm) {ℓ : ℕ}
    (hℓ : ℓ ≠ 0) (h : ∀ g, (fun x => ψ x)^[ℓ] g = g) {D : Set G} (hD : MeasurableSet D)
    (hstable : (fun x => ψ x) ⁻¹' D = D) :
    MeasurePreserving (fun x => ψ x) (μ.restrict D) (μ.restrict D) :=
  measurePreserving_restrict_haar_of_iterate_eq_id μ
    ({ ψ with continuous_toFun := hc, continuous_invFun := hc' } : G ≃ₜ* G) hℓ h hD hstable

@[to_additive]
theorem mulEquiv_measurePreserving_restrict_symm_of_iterate_eq_id (μ : Measure G)
    [IsHaarMeasure μ] [Regular μ] (ψ : G ≃* G) (hc : Continuous ψ) (hc' : Continuous ψ.symm)
    {ℓ : ℕ} (hℓ : ℓ ≠ 0) (h : ∀ g, (fun x => ψ x)^[ℓ] g = g) {D : Set G} (hD : MeasurableSet D)
    (hstable : (fun x => ψ x) ⁻¹' D = D) :
    MeasurePreserving (fun x => ψ.symm x) (μ.restrict D) (μ.restrict D) :=
  measurePreserving_restrict_haar_symm_of_iterate_eq_id μ
    ({ ψ with continuous_toFun := hc, continuous_invFun := hc' } : G ≃ₜ* G) hℓ h hD hstable

@[to_additive]
theorem mulEquiv_measurePreserving_restrict_pair_of_iterate_eq_id (μ : Measure G)
    [IsHaarMeasure μ] [Regular μ] (ψ : G ≃* G) (hc : Continuous ψ) (hc' : Continuous ψ.symm)
    {ℓ : ℕ} (hℓ : ℓ ≠ 0) (h : ∀ g, (fun x => ψ x)^[ℓ] g = g) {D : Set G} (hD : MeasurableSet D)
    (hstable : (fun x => ψ x) ⁻¹' D = D) :
    MeasurePreserving (fun x => ψ.symm x) (μ.restrict D) (μ.restrict D) ∧
      MeasurePreserving (fun x => ψ x) (μ.restrict D) (μ.restrict D) :=
  ⟨mulEquiv_measurePreserving_restrict_symm_of_iterate_eq_id μ ψ hc hc' hℓ h hD hstable,
    mulEquiv_measurePreserving_restrict_of_iterate_eq_id μ ψ hc hc' hℓ h hD hstable⟩

end MulEquivCurrency

end MeasureTheory

namespace FLT.HaarFiniteOrderGates

open MeasureTheory MeasureTheory.Measure
open scoped NNReal

section Inversion

variable (G : Type*) [CommGroup G] [TopologicalSpace G] [MeasurableSpace G]
    [BorelSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

@[to_additive

                                                   ]
def invContinuousMulEquiv : G ≃ₜ* G where
  toFun g := g⁻¹
  invFun g := g⁻¹
  left_inv g := inv_inv g
  right_inv g := inv_inv g
  map_mul' a b := mul_inv a b
  continuous_toFun := continuous_inv
  continuous_invFun := continuous_inv

omit [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] in
@[to_additive (attr := simp)]
lemma invContinuousMulEquiv_apply (g : G) : invContinuousMulEquiv G g = g⁻¹ := rfl

omit [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] in
@[to_additive]
lemma invContinuousMulEquiv_coe : ⇑(invContinuousMulEquiv G) = fun g : G => g⁻¹ := rfl

omit [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] in

@[to_additive]
lemma invContinuousMulEquiv_iterate_two (g : G) :
    (⇑(invContinuousMulEquiv G))^[2] g = g := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply, Function.iterate_one]
  simp

variable {G}

@[to_additive]
theorem gate_map_inv_eq_self (μ : Measure G) [IsHaarMeasure μ] [Regular μ] :
    μ.map (fun g : G => g⁻¹) = μ := by
  have h := MeasureTheory.map_haar_eq_self_of_iterate_eq_id μ (invContinuousMulEquiv G)
    (ℓ := 2) (by norm_num) (invContinuousMulEquiv_iterate_two G)
  rwa [invContinuousMulEquiv_coe] at h

@[to_additive]
theorem gate_inv_two_routes (μ : Measure G) [IsHaarMeasure μ] [Regular μ] :
    μ.map (fun g : G => g⁻¹) = μ ∧ Measure.map Inv.inv μ = μ :=
  ⟨gate_map_inv_eq_self μ, Measure.map_inv_eq_self μ⟩

end Inversion

section RealNegation

theorem gate_real_map_neg_volume :
    (volume : Measure ℝ).map (fun x : ℝ => -x) = volume :=
  gate_map_neg_eq_self (volume : Measure ℝ)

theorem gate_real_two_routes :
    (volume : Measure ℝ).map (fun x : ℝ => -x) = volume ∧
      Measure.map Neg.neg (volume : Measure ℝ) = volume :=
  ⟨gate_real_map_neg_volume, Measure.map_neg_eq_self (volume : Measure ℝ)⟩

theorem gate_neg_preimage_Icc :
    (fun x : ℝ => -x) ⁻¹' Set.Icc (-1 : ℝ) 1 = Set.Icc (-1 : ℝ) 1 := by
  ext x
  simp only [Set.mem_preimage, Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

theorem gate_real_neg_measurePreserving_restrict_Icc :
    MeasurePreserving (fun x : ℝ => -x)
      ((volume : Measure ℝ).restrict (Set.Icc (-1 : ℝ) 1))
      ((volume : Measure ℝ).restrict (Set.Icc (-1 : ℝ) 1)) := by
  have h := MeasureTheory.measurePreserving_restrict_addHaar_of_iterate_eq_id
    (volume : Measure ℝ) (negContinuousAddEquiv ℝ) (ℓ := 2) (by norm_num)
    (negContinuousAddEquiv_iterate_two ℝ) (D := Set.Icc (-1 : ℝ) 1) measurableSet_Icc
    (by rw [negContinuousAddEquiv_coe]; exact gate_neg_preimage_Icc)
  rwa [negContinuousAddEquiv_coe] at h

end RealNegation

section Separation

noncomputable def doublingContinuousAddEquiv : ℝ ≃ₜ+ ℝ where
  toFun x := 2 * x
  invFun x := 2⁻¹ * x
  left_inv x := by norm_num [← mul_assoc]
  right_inv x := by norm_num [← mul_assoc]
  map_add' a b := mul_add 2 a b
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] lemma doublingContinuousAddEquiv_apply (x : ℝ) :
    doublingContinuousAddEquiv x = 2 * x := rfl

lemma gate_doubling_preimage_Icc :
    (⇑doublingContinuousAddEquiv) ⁻¹' Set.Icc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 2⁻¹ := by
  ext x
  simp only [Set.mem_preimage, doublingContinuousAddEquiv_apply, Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

theorem gate_doubling_addHaarChar_ne_one :
    MeasureTheory.addEquivAddHaarChar doublingContinuousAddEquiv ≠ 1 := by
  intro hc
  have hpre := MeasureTheory.addEquivAddHaarChar_smul_preimage (volume : Measure ℝ)
    (X := Set.Icc (0 : ℝ) 1) doublingContinuousAddEquiv
  rw [hc, one_smul, gate_doubling_preimage_Icc, Real.volume_Icc, Real.volume_Icc,
    ENNReal.ofReal_eq_ofReal_iff (p := 2⁻¹ - 0) (q := 1 - 0) (by norm_num) (by norm_num)] at hpre
  norm_num at hpre

theorem gate_iterate_zero_trivial (A : Type*) [AddGroup A] [TopologicalSpace A]
    (φ : A ≃ₜ+ A) (a : A) : (⇑φ)^[0] a = a :=
  Function.iterate_zero_apply (⇑φ) a

end Separation

end FLT.HaarFiniteOrderGates

/--
info: 'MeasureTheory.mulEquivHaarChar_eq_one_of_iterate_eq_id' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.mulEquivHaarChar_eq_one_of_iterate_eq_id

/--
info: 'MeasureTheory.addEquivAddHaarChar_eq_one_of_iterate_eq_id' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.addEquivAddHaarChar_eq_one_of_iterate_eq_id

/--
info: 'MeasureTheory.map_haar_eq_self_of_iterate_eq_id' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.map_haar_eq_self_of_iterate_eq_id

/--
info: 'MeasureTheory.map_addHaar_eq_self_of_iterate_eq_id' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.map_addHaar_eq_self_of_iterate_eq_id

/--
info: 'MeasureTheory.measurePreserving_haar_of_iterate_eq_id' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.measurePreserving_haar_of_iterate_eq_id

/--
info: 'MeasureTheory.measure_preimage_haar_eq_of_iterate_eq_id' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.measure_preimage_haar_eq_of_iterate_eq_id

/--
info: 'MeasureTheory.integral_comp_haar_eq_of_iterate_eq_id' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.integral_comp_haar_eq_of_iterate_eq_id

/--
info: 'MeasureTheory.measurePreserving_restrict_of_map_eq_self' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.measurePreserving_restrict_of_map_eq_self

/--
info: 'MeasureTheory.measurePreserving_restrict_haar_of_iterate_eq_id' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.measurePreserving_restrict_haar_of_iterate_eq_id

/--
info: 'MeasureTheory.measurePreserving_restrict_haar_symm_of_iterate_eq_id' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.measurePreserving_restrict_haar_symm_of_iterate_eq_id

/--
info: 'MeasureTheory.mulEquiv_measurePreserving_restrict_pair_of_iterate_eq_id' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.mulEquiv_measurePreserving_restrict_pair_of_iterate_eq_id

/--
info: 'MeasureTheory.addEquiv_measurePreserving_restrict_pair_of_iterate_eq_id' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms MeasureTheory.addEquiv_measurePreserving_restrict_pair_of_iterate_eq_id

/--
info: 'FLT.HaarFiniteOrderGates.gate_inv_two_routes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLT.HaarFiniteOrderGates.gate_inv_two_routes

/--
info: 'FLT.HaarFiniteOrderGates.gate_real_two_routes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLT.HaarFiniteOrderGates.gate_real_two_routes

/--
info: 'FLT.HaarFiniteOrderGates.gate_real_neg_measurePreserving_restrict_Icc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FLT.HaarFiniteOrderGates.gate_real_neg_measurePreserving_restrict_Icc

/--
info: 'FLT.HaarFiniteOrderGates.gate_doubling_addHaarChar_ne_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLT.HaarFiniteOrderGates.gate_doubling_addHaarChar_ne_one


