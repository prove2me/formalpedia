-- Prove2me | Definitions.Def_HaarMeasure_HaarChar_Ring
-- name    : HaarMeasure_HaarChar_Ring
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/454c6096-54a7-5899-bc64-115b112791c9
-- title:
--   The Haar character of units of a locally compact ring
-- statement:
--   Throughout, $R$ is a ring with a topology making it a topological ring, locally compact, equipped with its Borel $\sigma$-algebra. For a unit $u \in R^\times$, multiplication by $u$ on the left is a homeomorphic automorphism of the additive group $(R,+)$, and `ringHaarChar u` is defined to be the additive Haar character `addEquivAddHaarChar` of that automorphism, i.e. the scalar in $\mathbb{R}_{\ge 0}$ by which an additive Haar measure on $R$ is scaled by left multiplication by $u$. The lemma `ringHaarChar_continuous` shows that $u \mapsto$ this scalar is continuous on $R^\times$, and `ringHaarChar` packages the map as a continuous monoid homomorphism $R^\times \to_{\mathrm{t}*} \mathbb{R}_{\ge 0}$ (so the target is the multiplicative monoid of non-negative reals, not a group of positive reals); `ringHaarChar_apply` records the defining formula.
--
--   The remaining declarations develop its properties. `ringHaarChar_eq_ringHaarChar_of_continuousAlgEquiv` transports the character along a continuous $\mathbb{Z}$-algebra equivalence $R \simeq S$ of two such rings. For a regular additive Haar measure $\mu$ on $R$ and measurable $f : R \to \mathbb{R}$, `ringHaarChar_mul_integral` gives $\mathrm{ringHaarChar}(u)\int f(u r)\,d\mu = \int f\,d\mu$, and `ringHaarChar_mul_volume` gives $\mu(u \cdot X) = \mathrm{ringHaarChar}(u)\,\mu(X)$ for every set $X$; `ringHaarChar_eq_of_measure_smul_eq_mul` conversely identifies the character from a single set of non-zero finite measure whose translate scales by $r$. `ringHaarChar_ker R` is the kernel of the underlying monoid homomorphism, with `mem_ringHaarChar_ker` its membership criterion.
--
--   Multiplicativity in the ring variable is then established: for a product of two such rings (`ringHaarChar_prod`, `ringHaarChar_prod'`, via the identification of $(R \times S)^\times$ with $R^\times \times S^\times$), for finite products (`ringHaarChar_pi`, `ringHaarChar_pi'`), and for a restricted product $\Pi^r_i [A_i, C_i]$ over a countable index set with respect to open compact subrings $C_i$, where `ringHaarChar_restrictedProduct` expresses the character as the multipliable product $\prod^f_i$ of the local characters of the components of the unit. Finally, for a field $K$ and a $K$-algebra $R$ finite as a $K$-module and carrying the module topology, `ringHaarChar_ModuleFinite` compares $R$ with $K^{\mathrm{finrank}_K R}$ along the basis homeomorphism, and `ringHaarChar_ModuleFinite_unit` deduces $\mathrm{ringHaarChar}(\mathrm{algebraMap}\,t) = \mathrm{ringHaarChar}(t)^{\mathrm{finrank}_K R}$ for $t \in K^\times$. A helper lemma records that the preimage of $u \cdot s$ under left multiplication by $u$ is $s$.
--
--   **Relation to Mathlib.** The additive Haar character `addEquivAddHaarChar` of a topological additive automorphism is taken from Mathlib; the ring character `ringHaarChar` on the unit group, its kernel, and the product, restricted-product and finite-module formulae are the project's own.
--
--   **Where it is used.** These characters give the local and adelic modulus maps used when Haar measures on adèle rings and their unit groups are compared, in particular towards the product formula underlying the adelic formulation of the automorphic side.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/HaarMeasure/HaarChar/Ring.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_HaarMeasure_HaarChar_Ring.lean

import Mathlib
import Definitions.Def_Mathlib_IsModuleTopology
import Definitions.Def_Mathlib_MeasureTheory_Constructions_BorelSpace_RestrictedProduct
import Definitions.Def_Mathlib_Topology_Algebra_RestrictedProduct_Equiv
import Definitions.Def_HaarMeasure_HaarChar_AddEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

section

open scoped NNReal

namespace ContinuousAddEquiv

variable {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]

open Pointwise in
@[simp]
lemma preimage_mulLeft_smul (r : Rˣ) (s : Set R) :
    ContinuousAddEquiv.mulLeft r ⁻¹' (r • s) = s := by ext; simp [Set.mem_smul_set, Units.smul_def]

end ContinuousAddEquiv

namespace MeasureTheory

open Measure

variable {R : Type*} [Ring R] [TopologicalSpace R]
  [IsTopologicalRing R] [LocallyCompactSpace R] [MeasurableSpace R] [BorelSpace R]

lemma ringHaarChar_continuous :
    Continuous (fun (u : Rˣ) ↦ addEquivAddHaarChar (ContinuousAddEquiv.mulLeft u)) := by
  suffices
    hf : Continuous (fun (u : Rˣ) ↦ (addEquivAddHaarChar (ContinuousAddEquiv.mulLeft u) : ℝ)) from
    continuous_induced_rng.mpr hf
  obtain ⟨⟨f, f_cont⟩, f_comp, f_nonneg, f_one⟩ :
    ∃ f : C(R, ℝ), HasCompactSupport f ∧ 0 ≤ f ∧ f 1 ≠ 0 := exists_continuous_nonneg_pos 1
  have int_f_ne_zero : ∫ x, f x ∂addHaar ≠ 0 :=
    ne_of_gt (f_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero f_comp f_nonneg f_one)
  have h (u : Rˣ) :=
      addEquivAddHaarChar_smul_integral_map addHaar (ContinuousAddEquiv.mulLeft u) (f := f)
  conv at h => ext; rw [integral_map (by fun_prop) (by fun_prop)]
  simp only [ContinuousAddEquiv.mulLeft_apply, NNReal.smul_def, smul_eq_mul] at h
  let g (u : Rˣ) (x : R) := f (u * x)
  have int_g_ne_zero (u : Rˣ) : ∫ (x : R), g u x ∂addHaar ≠ 0 := by
    have hu := h u
    contrapose! hu
    simp [g, hu, int_f_ne_zero.symm]
  rw [← funext (fun u ↦ div_eq_of_eq_mul (int_g_ne_zero u) (h u).symm)]
  refine Continuous.div continuous_const ?_ (fun u ↦ int_g_ne_zero u)
  rw [continuous_iff_continuousAt]
  intro u₀
  obtain ⟨K, hK, hu₀⟩ := exists_compact_mem_nhds (↑u₀⁻¹ : R)
  let s := (fun (u : Rˣ) ↦ (↑u⁻¹ : R)) ⁻¹' K
  refine ContinuousOn.continuousAt ?_
    (ContinuousAt.preimage_mem_nhds (by fun_prop) (by exact hu₀) : s ∈ nhds u₀)
  apply continuousOn_integral_of_compact_support (hK.mul f_comp) (by fun_prop)
  intro p x hps hx
  unfold g
  apply image_eq_zero_of_notMem_tsupport
  contrapose! hx
  exact ⟨(↑p⁻¹ : R) , hps, p * x, hx, by simp⟩

@[simps (isSimp := false)]
noncomputable def ringHaarChar : Rˣ →ₜ* ℝ≥0 where
  toFun r := addEquivAddHaarChar (ContinuousAddEquiv.mulLeft r)
  map_one' := by convert addEquivAddHaarChar_refl (G := R); ext; simp
  map_mul' φ ψ := by
    rw [mul_comm]
    convert addEquivAddHaarChar_trans (G := R); ext; simp [mul_assoc]
  continuous_toFun := ringHaarChar_continuous

lemma ringHaarChar_apply (r : Rˣ) :
    ringHaarChar r = addEquivAddHaarChar (ContinuousAddEquiv.mulLeft r) := rfl

lemma ringHaarChar_eq_ringHaarChar_of_continuousAlgEquiv {S : Type*} [Ring S] [TopologicalSpace S]
    [IsTopologicalRing S] [LocallyCompactSpace S] [MeasurableSpace S] [BorelSpace S]
    (f : R ≃A[ℤ] S) (r : Rˣ) :
    ringHaarChar r = ringHaarChar (Units.map f.toMonoidHom r) :=
  addEquivAddHaarChar_eq_addEquivAddHaarChar_of_continuousAddEquiv {__ := f} _ _
    (by simp [map_mul])

lemma ringHaarChar_mul_integral
    (μ : Measure R) [IsAddHaarMeasure μ] [μ.Regular]
    {f : R → ℝ} (hf : Measurable f) (u : Rˣ) :
    (ringHaarChar u) * ∫ (r : R), f (u * r) ∂μ = ∫ a, f a ∂μ := by
  symm
  convert (addEquivAddHaarChar_smul_integral_map μ (ContinuousAddEquiv.mulLeft u) (f := f)).symm
    using 1
  simp only [ringHaarChar_toFun, NNReal.smul_def, smul_eq_mul, mul_eq_mul_left_iff,
    NNReal.coe_eq_zero]
  rw [MeasureTheory.integral_map (by fun_prop) (by fun_prop)]
  simp

open Pointwise in
lemma ringHaarChar_mul_volume (μ : Measure R) [IsAddHaarMeasure μ] [μ.Regular]
    {X : Set R} (u : Rˣ) :
    μ (u • X) = ringHaarChar u * μ X := by
  rw [ringHaarChar_toFun, (addEquivAddHaarChar_smul_preimage _ (ContinuousAddEquiv.mulLeft u)).symm]
  simp

open Pointwise ENNReal in
lemma ringHaarChar_eq_of_measure_smul_eq_mul {μ : Measure R} [IsAddHaarMeasure μ] [μ.Regular]
    {s : Set R} (hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞) {r : ℝ≥0} {u : Rˣ}
    (hμgs : μ (u • s) = r * μ s) : ringHaarChar u = r := by
  rw [ringHaarChar_mul_volume μ u, ENNReal.mul_left_inj hs₀ hs] at hμgs
  assumption_mod_cast

variable (R) in

noncomputable def ringHaarChar_ker := MonoidHom.ker (ringHaarChar : Rˣ →ₜ* ℝ≥0).toMonoidHom

lemma mem_ringHaarChar_ker (x : Rˣ) : x ∈ ringHaarChar_ker R ↔ ringHaarChar x = 1 :=
  MonoidHom.mem_ker

section prod

variable {S : Type*} [Ring S] [TopologicalSpace S]
  [IsTopologicalRing S] [LocallyCompactSpace S] [MeasurableSpace S] [BorelSpace S]

lemma ringHaarChar_prod (u : Rˣ) (v : Sˣ) [SecondCountableTopologyEither R S] :
    ringHaarChar (MulEquiv.prodUnits.symm (u, v)) = ringHaarChar u * ringHaarChar v :=
  addEquivAddHaarChar_prodCongr (ContinuousAddEquiv.mulLeft u) (ContinuousAddEquiv.mulLeft v)

lemma ringHaarChar_prod' (uv : (R × S)ˣ) [SecondCountableTopologyEither R S] :
    ringHaarChar uv =
    ringHaarChar (MulEquiv.prodUnits uv).1 * ringHaarChar (MulEquiv.prodUnits uv).2 :=
  ringHaarChar_prod (MulEquiv.prodUnits uv).1 (MulEquiv.prodUnits uv).2

end prod

section pi

variable {ι : Type*} {A : ι → Type*} [Π i, Ring (A i)] [Π i, TopologicalSpace (A i)]
    [∀ i, IsTopologicalRing (A i)] [∀ i, LocallyCompactSpace (A i)]
    [∀ i, MeasurableSpace (A i)] [∀ i, BorelSpace (A i)]

lemma ringHaarChar_pi [Fintype ι] [∀ i, SecondCountableTopology (A i)] (u : Π i, (A i)ˣ) :
    ringHaarChar (MulEquiv.piUnits.symm u) = ∏ i, ringHaarChar (u i) :=
  addEquivAddHaarChar_piCongrRight (fun i ↦ ContinuousAddEquiv.mulLeft (u i))

lemma ringHaarChar_pi' [Fintype ι] [∀ i, SecondCountableTopology (A i)] (u : (Π i, (A i))ˣ) :
    ringHaarChar u = ∏ i, ringHaarChar (MulEquiv.piUnits u i) :=
  addEquivAddHaarChar_piCongrRight (fun i ↦ ContinuousAddEquiv.mulLeft (MulEquiv.piUnits u i))

end pi

section restrictedproduct

open scoped RestrictedProduct

variable {ι : Type*} {A : ι → Type*} [Π i, Ring (A i)] [Π i, TopologicalSpace (A i)]
    [∀ i, IsTopologicalRing (A i)] [∀ i, LocallyCompactSpace (A i)]
    [∀ i, MeasurableSpace (A i)] [∀ i, BorelSpace (A i)]
    {C : (i : ι) → Subring (A i)}
    [hCopen : Fact (∀ (i : ι), IsOpen (C i : Set (A i)))]
    [hCcompact : ∀ i, CompactSpace (C i)]
    [∀ (i : ι), SecondCountableTopology (A i)]
    [Countable ι]

lemma ringHaarChar_restrictedProduct (u : (Πʳ i, [A i, C i])ˣ) :
    ringHaarChar u = ∏ᶠ i, ringHaarChar (MulEquiv.restrictedProductUnits u i) := by
  set u := MulEquiv.restrictedProductUnits u
  apply addEquivAddHaarChar_restrictedProductCongrRight (C := (C · |>.toAddSubgroup))
    (ContinuousAddEquiv.mulLeft <| u ·)
  refine Filter.Eventually.and u.coe_prop u⁻¹.coe_prop |>.mono fun i ⟨hu, hv⟩ ↦ ⟨?_, ?_, ?_⟩
  · exact fun _ ↦ (C i).mul_mem ((C i).mem_units_iff _ |>.mp hu).1
  · exact Set.injOn_of_injective (ContinuousAddEquiv.injective _)
  · exact fun c hc ↦ ⟨(u i)⁻¹ * c, (C i).mul_mem ((C i).mem_units_iff _ |>.mp hv).1 hc, by simp⟩

end restrictedproduct

section ModuleFinite

variable {K R : Type*} [Field K] [Ring R] [Algebra K R] [Module.Finite K R]
    [TopologicalSpace K] [TopologicalSpace R] [IsTopologicalRing R] [IsModuleTopology K R]
    [LocallyCompactSpace R] [MeasurableSpace R] [BorelSpace R]
    [IsTopologicalRing K] [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
    [SecondCountableTopology K] (t : Kˣ)

theorem ringHaarChar_ModuleFinite :
    ringHaarChar (Units.map (algebraMap K R).toMonoidHom t) =
    ringHaarChar (R := (Fin (Module.finrank K R) → K))
      (Units.map (algebraMap K (Fin (Module.finrank K R) → K)).toMonoidHom t) := by
  apply addEquivAddHaarChar_eq_addEquivAddHaarChar_of_continuousAddEquiv
    ((IsModuleTopology.Module.Basis.equivFun_homeo _ _).toContinuousAddEquiv)
  intro x

  change (IsModuleTopology.Module.Basis.equivFun_homeo K R) _ =
    (ContinuousAddEquiv.mulLeft ((Units.map ↑(algebraMap K (Fin (Module.finrank K R) → K))) t))
    ((IsModuleTopology.Module.Basis.equivFun_homeo K R) x)
  simp [← Algebra.smul_def]

theorem ringHaarChar_ModuleFinite_unit :
    ringHaarChar (Units.map (algebraMap K R).toMonoidHom t) =
    (ringHaarChar t) ^ (Module.finrank K R) := by
  rw [ringHaarChar_ModuleFinite, ringHaarChar_pi']
  have h : ∀ i, MulEquiv.piUnits
      (Units.map (algebraMap K (Fin (Module.finrank K R) → K)).toMonoidHom t) i = t :=
    fun i => Units.ext rfl
  rw [Finset.prod_congr rfl (fun i _ => congrArg ringHaarChar (h i)), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

end ModuleFinite

end MeasureTheory


