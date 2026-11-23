-- Prove2me | Definitions.Def_DedekindZeta_Statements
-- name    : DedekindZeta_Statements
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T00:22:41.493179+00:00
-- url     : https://prove2.me/theorems/08b68e25-02c0-4ec6-852e-cd92c42b80c6
-- title:
--   Statements
-- statement:
--   Definitions and structural lemmas for Statements, from Mathlib Initiative and contributors's pinned A real sum-product counterexample conditional on Martinet’s tower theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/DedekindZeta/Statements.lean

import Mathlib
import Definitions.Def_DedekindZeta_Theta
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply


set_option autoImplicit true
open NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open Filter Finset Asymptotics Topology
open scoped Real nonZeroDivisors
namespace DedekindZeta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
abbrev NonzeroIdeal := {I : Ideal (𝓞 K) // I ≠ 0}
open scoped NNReal ENNReal
section ReIndex
noncomputable def idealExp (I : Ideal (𝓞 K)) (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  (FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)).toNat
lemma idealExp_eq {I : Ideal (𝓞 K)} (hI : I ≠ 0) (v : HeightOneSpectrum (𝓞 K)) :
    idealExp K I v = (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
  rw [idealExp, FractionalIdeal.count_coe K v hI, Int.toNat_natCast]
lemma idealExp_ne_zero_iff {I : Ideal (𝓞 K)} (hI : I ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) : idealExp K I v ≠ 0 ↔ v.asIdeal ∣ I := by
  rw [idealExp_eq K hI, Associates.count_ne_zero_iff_dvd hI v.irreducible]
lemma finite_idealExp_support {I : Ideal (𝓞 K)} (hI : I ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | idealExp K I v ≠ 0}.Finite := by
  apply (Ideal.finite_factors hI).subset
  intro v hv
  exact (idealExp_ne_zero_iff K hI v).mp hv
lemma finprod_asIdeal_pow_idealExp {I : Ideal (𝓞 K)} (hI : I ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), v.asIdeal ^ idealExp K I v = I := by
  conv_rhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI]
  refine finprod_congr (fun v => ?_)
  rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, idealExp_eq K hI]
noncomputable def nonzeroIdealEquivFinsupp :
    NonzeroIdeal K ≃ (HeightOneSpectrum (𝓞 K) →₀ ℕ) where
  toFun I :=
    { support := (finite_idealExp_support K I.2).toFinset
      toFun := idealExp K I.1
      mem_support_toFun := fun v => by rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] }
  invFun f := ⟨f.prod (fun v n => v.asIdeal ^ n), by
    rw [Finsupp.prod, Ne, Finset.prod_eq_zero_iff]
    rintro ⟨v, -, hv⟩
    exact pow_ne_zero _ (by simpa [Ideal.zero_eq_bot] using v.ne_bot) hv⟩
  left_inv := by
    rintro ⟨I, hI⟩
    apply Subtype.ext
    change (Finsupp.mk _ (idealExp K I) _).prod (fun v n => v.asIdeal ^ n) = I
    rw [Finsupp.prod]
    simp only [Finsupp.coe_mk]
    rw [← finprod_eq_prod_of_mulSupport_subset (fun v => v.asIdeal ^ idealExp K I v) ?_]
    · exact finprod_asIdeal_pow_idealExp K hI
    · intro v hv
      simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq,
        Function.mem_mulSupport] at *
      intro h
      exact hv (by rw [h, pow_zero])
  right_inv := by
    intro f
    ext v
    change idealExp K (f.prod (fun v n => v.asIdeal ^ n)) v = f v
    have hJ : f.prod (fun v n => v.asIdeal ^ n) ≠ 0 := by
      rw [Finsupp.prod, Ne, Finset.prod_eq_zero_iff]
      rintro ⟨w, -, hw⟩
      exact pow_ne_zero _ (by simpa [Ideal.zero_eq_bot] using w.ne_bot) hw
    rw [idealExp, ← Int.toNat_natCast (f v)]
    congr 1
    classical
    have hcoe : ((f.prod (fun v n => v.asIdeal ^ n) : Ideal (𝓞 K)) :
        FractionalIdeal (𝓞 K)⁰ K)
        = ∏ w ∈ f.support, ((w.asIdeal : FractionalIdeal (𝓞 K)⁰ K)) ^ (f w) := by
      rw [Finsupp.prod, ← FractionalIdeal.coeIdealHom_apply, map_prod]
      refine Finset.prod_congr rfl (fun w _ => ?_)
      rw [FractionalIdeal.coeIdealHom_apply, FractionalIdeal.coeIdeal_pow]
    rw [hcoe, FractionalIdeal.count_prod K v]
    · simp only [FractionalIdeal.count_pow, FractionalIdeal.count_maximal]
      rw [Finset.sum_congr rfl (fun w _ => by rw [mul_ite, mul_one, mul_zero])]
      rw [Finset.sum_ite_eq' f.support v]
      split_ifs with h
      · simp
      · simp only [Finsupp.mem_support_iff, not_not] at h
        simp [h]
    · exact fun w _ => pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot)
noncomputable def cpowHom (s : ℂ) : ℕ →* ℂ where
  toFun n := (n : ℂ) ^ (-s)
  map_one' := by simp
  map_mul' m n := by
    push_cast
    rw [Complex.natCast_mul_natCast_cpow]
end ReIndex
def LReal (s : ℂ) : ℂ := (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)
def LComplex (s : ℂ) : ℂ := 2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s
def ZInfty (s : ℂ) : ℂ :=
    ((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2)
      * LReal s ^ (nrRealPlaces K)
      * LComplex s ^ (nrComplexPlaces K)
open Classical in
/-- The standard multiplicative Haar measure `d^*x` on `K_ℝ^*`, written as a
density against the additive Lebesgue measure on `K_ℝ`:
`d^*x = (2/π)^{r₂} · |N(x)|^{-1} · dx`. The factor `|N(x)|^{-1}` turns the
additive `dx_w` into the one-dimensional multiplicative Haar measures
`dx_w/|x_w|` (real) and `dλ_w/|z_w|²` (complex), and the constant `(2/π)^{r₂}`
is the per-complex-place normalisation pinning the complex factor to `L_ℂ`. The
density vanishes on the measure-zero locus `N(x) = 0`, so the measure lives on
`K_ℝ^*`. -/
def mixedMulHaar : MeasureTheory.Measure (mixedEmbedding.mixedSpace K) :=
  MeasureTheory.volume.withDensity fun x =>
    ENNReal.ofReal ((2 / Real.pi) ^ nrComplexPlaces K * (mixedEmbedding.norm x)⁻¹)
section MulHaarRightInvariance
open MeasureTheory NumberField.mixedEmbedding
set_option maxHeartbeats 1000000 in
/-- **Right-multiplication change of variables for `d^*x`** (the lintegral core of
the per-element scale invariance): for `c` with `N(c) ≠ 0`, the translation
`x ↦ x·c` of `K_ℝ^*` preserves the multiplicative Haar measure `mixedMulHaar`, so
for any nonnegative measurable `h`, `∫⁻ h(y·c) d^*x = ∫⁻ h(y) d^*x`. Proof route:
unfold `mixedMulHaar = (2/π)^{r₂}·|N|⁻¹·volume`
and reduce to the *additive* Jacobian `map (·*c) volume = ofReal N(c)⁻¹ • volume`
(`map_linearMap_addHaar_eq_smul_addHaar`, `|LinearMap.det| = N(c)`: real places
contribute `|c_w|`, complex places `|c_w|²`); the density change
`|N(x·c)|⁻¹ = |N(x)|⁻¹·N(c)⁻¹` cancels that Jacobian exactly. -/
theorem lintegral_comp_mul_right_mixedMulHaar (h : mixedEmbedding.mixedSpace K → ℝ≥0∞)
    (hh : Measurable h) {c : mixedEmbedding.mixedSpace K}
    (hc : mixedEmbedding.norm c ≠ 0) :
    ∫⁻ y, h (y * c) ∂(mixedMulHaar K) = ∫⁻ y, h y ∂(mixedMulHaar K) := by
  classical
  -- Norm in factored form: `N(x) = (∏_{real} ‖x_w‖)·(∏_{complex} ‖z_w‖²)`.
  have hnormfac : ∀ x : mixedEmbedding.mixedSpace K,
      mixedEmbedding.norm x
        = (∏ w : {w : InfinitePlace K // IsReal w}, ‖x.1 w‖)
          * (∏ w : {w : InfinitePlace K // IsComplex w}, ‖x.2 w‖ ^ 2) := by
    intro x
    have hreal : (∏ w : {w : InfinitePlace K // IsReal w}, (normAtPlace w.1 x) ^ (mult w.1))
        = ∏ w : {w : InfinitePlace K // IsReal w}, ‖x.1 w‖ :=
      Finset.prod_congr rfl fun w _ => by
        rw [mult_isReal, pow_one, normAtPlace_apply_of_isReal w.prop]
    have hcpx : (∏ w : {w : InfinitePlace K // IsComplex w}, (normAtPlace w.1 x) ^ (mult w.1))
        = ∏ w : {w : InfinitePlace K // IsComplex w}, ‖x.2 w‖ ^ 2 :=
      Finset.prod_congr rfl fun w _ => by
        rw [mult_isComplex, normAtPlace_apply_of_isComplex w.prop]
    rw [mixedEmbedding.norm_apply, InfinitePlace.prod_eq_prod_mul_prod, hreal, hcpx]
  -- Every place-coordinate of `c` is nonzero (else a factor, hence `N(c)`, vanishes).
  have hr_ne : (∏ w : {w : InfinitePlace K // IsReal w}, ‖c.1 w‖) ≠ 0 := by
    intro h0; exact hc (by rw [hnormfac c, h0, zero_mul])
  have hcx_ne : (∏ w : {w : InfinitePlace K // IsComplex w}, ‖c.2 w‖ ^ 2) ≠ 0 := by
    intro h0; exact hc (by rw [hnormfac c, h0, mul_zero])
  have hc1 : ∀ w : {w : InfinitePlace K // IsReal w}, c.1 w ≠ 0 := by
    intro w hw
    exact hr_ne (Finset.prod_eq_zero (Finset.mem_univ w) (by rw [hw, norm_zero]))
  have hc2 : ∀ w : {w : InfinitePlace K // IsComplex w}, c.2 w ≠ 0 := by
    intro w hw
    exact hcx_ne (Finset.prod_eq_zero (Finset.mem_univ w) (by rw [hw, norm_zero]; ring))
  -- **Additive Jacobian (Step 1).** `x ↦ x·c` is the ℝ-linear automorphism built
  -- from the diagonal scaling on the real factor and (the ℝ-restriction of) the
  -- diagonal complex-scaling on the complex factor.
  set Lr : ({w : InfinitePlace K // IsReal w} → ℝ) →ₗ[ℝ]
      ({w : InfinitePlace K // IsReal w} → ℝ) := Matrix.toLin' (Matrix.diagonal c.1) with hLr
  set Lc0 : ({w : InfinitePlace K // IsComplex w} → ℂ) →ₗ[ℂ]
      ({w : InfinitePlace K // IsComplex w} → ℂ) := Matrix.toLin' (Matrix.diagonal c.2) with hLc0
  set Lc : ({w : InfinitePlace K // IsComplex w} → ℂ) →ₗ[ℝ]
      ({w : InfinitePlace K // IsComplex w} → ℂ) := Lc0.restrictScalars ℝ with hLc
  set L : mixedEmbedding.mixedSpace K →ₗ[ℝ] mixedEmbedding.mixedSpace K :=
    Lr.prodMap Lc with hL
  -- `⇑L = (·*c)` (componentwise multiplication).
  have hLfun : (⇑L) = fun x : mixedEmbedding.mixedSpace K => x * c := by
    funext x
    have h1 : (L x).1 = fun w => c.1 w * x.1 w := by
      simp only [hL, LinearMap.prodMap_apply, hLr, Matrix.toLin'_apply]
      funext w; rw [Matrix.mulVec_diagonal]
    have h2 : (L x).2 = fun w => c.2 w * x.2 w := by
      simp only [hL, LinearMap.prodMap_apply, hLc, LinearMap.coe_restrictScalars, hLc0,
        Matrix.toLin'_apply]
      funext w; rw [Matrix.mulVec_diagonal]
    apply Prod.ext
    · rw [h1]; funext w; exact mul_comm _ _
    · rw [h2]; funext w; exact mul_comm _ _
  -- Determinants of the three maps.
  have hdetLr : LinearMap.det Lr = ∏ w : {w : InfinitePlace K // IsReal w}, c.1 w := by
    rw [hLr, LinearMap.det_toLin', Matrix.det_diagonal]
  have hdetLc0 : LinearMap.det Lc0 = ∏ w : {w : InfinitePlace K // IsComplex w}, c.2 w := by
    rw [hLc0, LinearMap.det_toLin', Matrix.det_diagonal]
  have hdetLc : LinearMap.det Lc
      = ‖∏ w : {w : InfinitePlace K // IsComplex w}, c.2 w‖ ^ 2 := by
    rw [hLc, LinearMap.det_restrictScalars, hdetLc0, Algebra.norm_complex_apply,
      Complex.normSq_eq_norm_sq]
  have hdetL : LinearMap.det L
      = (∏ w : {w : InfinitePlace K // IsReal w}, c.1 w)
        * ‖∏ w : {w : InfinitePlace K // IsComplex w}, c.2 w‖ ^ 2 := by
    rw [hL, LinearMap.det_prodMap, hdetLr, hdetLc]
  -- `|det L| = N(c)`.
  have habs : |LinearMap.det L| = mixedEmbedding.norm c := by
    have hL_left : |∏ w : {w : InfinitePlace K // IsReal w}, c.1 w|
        = ∏ w : {w : InfinitePlace K // IsReal w}, ‖c.1 w‖ := by
      rw [Finset.abs_prod]
      exact Finset.prod_congr rfl fun w _ => (Real.norm_eq_abs _).symm
    have hL_right : ‖∏ w : {w : InfinitePlace K // IsComplex w}, c.2 w‖ ^ 2
        = ∏ w : {w : InfinitePlace K // IsComplex w}, ‖c.2 w‖ ^ 2 := by
      rw [norm_prod, ← Finset.prod_pow]
    rw [hdetL, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤
        ‖∏ w : {w : InfinitePlace K // IsComplex w}, c.2 w‖ ^ 2), hL_left, hL_right, hnormfac c]
  have hdetne : LinearMap.det L ≠ 0 := by
    intro h0; rw [h0, abs_zero] at habs; exact hc habs.symm
  -- Pushforward of `volume` under `x ↦ x·c`.
  have hmulmeas : Measurable (fun x : mixedEmbedding.mixedSpace K => x * c) :=
    (continuous_id.mul continuous_const).measurable
  have hmapvol :
      Measure.map (fun x : mixedEmbedding.mixedSpace K => x * c)
          (volume : Measure (mixedEmbedding.mixedSpace K))
        = ENNReal.ofReal (mixedEmbedding.norm c)⁻¹ • volume := by
    rw [← hLfun, Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdetne]
    congr 1
    rw [abs_inv, habs]
  -- Lebesgue change-of-variables form of the additive Jacobian.
  have hjac : ∀ H : mixedEmbedding.mixedSpace K → ℝ≥0∞, Measurable H →
      ∫⁻ y, H (y * c) ∂(volume : Measure (mixedEmbedding.mixedSpace K))
        = ENNReal.ofReal (mixedEmbedding.norm c)⁻¹ * ∫⁻ y, H y ∂volume := by
    intro H hH
    rw [← lintegral_map hH hmulmeas, hmapvol, lintegral_smul_measure, smul_eq_mul]
  -- **Density cancellation (Step 2).** `D` is the additive density of `mixedMulHaar`.
  set D : mixedEmbedding.mixedSpace K → ℝ≥0∞ :=
    fun x => ENNReal.ofReal ((2 / Real.pi) ^ nrComplexPlaces K * (mixedEmbedding.norm x)⁻¹)
    with hD
  have hDmeas : Measurable D :=
    (((mixedEmbedding.continuous_norm K).measurable.inv).const_mul _).ennreal_ofReal
  have hμ : mixedMulHaar K = volume.withDensity D := rfl
  -- Pointwise: `D x = D(x·c)·ofReal N(c)` (everywhere, incl. the `N(x)=0` null set).
  have hpt : ∀ x : mixedEmbedding.mixedSpace K,
      D x = D (x * c) * ENNReal.ofReal (mixedEmbedding.norm c) := by
    intro x
    have hnonneg : (0:ℝ) ≤ (2 / Real.pi) ^ nrComplexPlaces K * (mixedEmbedding.norm (x * c))⁻¹ :=
      mul_nonneg (by positivity) (inv_nonneg.mpr (mixedEmbedding.norm_nonneg _))
    simp only [hD]
    rw [← ENNReal.ofReal_mul hnonneg]
    congr 1
    rw [map_mul mixedEmbedding.norm x c]
    rcases eq_or_ne (mixedEmbedding.norm x) 0 with hx | hx
    · simp [hx]
    · field_simp
  -- Assembly.
  have hhc : Measurable (fun x : mixedEmbedding.mixedSpace K => h (x * c)) := hh.comp hmulmeas
  rw [hμ, lintegral_withDensity_eq_lintegral_mul volume hDmeas hhc,
    lintegral_withDensity_eq_lintegral_mul volume hDmeas hh]
  simp only [Pi.mul_apply]
  have hHmeas : Measurable
      (fun y : mixedEmbedding.mixedSpace K =>
        D y * ENNReal.ofReal (mixedEmbedding.norm c) * h y) :=
    (hDmeas.mul measurable_const).mul hh
  calc ∫⁻ x, D x * h (x * c) ∂(volume : Measure (mixedEmbedding.mixedSpace K))
      = ∫⁻ x, (fun y => D y * ENNReal.ofReal (mixedEmbedding.norm c) * h y) (x * c) ∂volume := by
        refine lintegral_congr fun x => ?_
        rw [hpt x]
    _ = ENNReal.ofReal (mixedEmbedding.norm c)⁻¹
          * ∫⁻ y, D y * ENNReal.ofReal (mixedEmbedding.norm c) * h y ∂volume :=
        hjac _ hHmeas
    _ = ENNReal.ofReal (mixedEmbedding.norm c)⁻¹
          * (ENNReal.ofReal (mixedEmbedding.norm c) * ∫⁻ y, D y * h y ∂volume) := by
        congr 1
        rw [← lintegral_const_mul' (ENNReal.ofReal (mixedEmbedding.norm c)) _
          ENNReal.ofReal_ne_top]
        refine lintegral_congr fun y => ?_; ring
    _ = ∫⁻ y, D y * h y ∂volume := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr (mixedEmbedding.norm_nonneg c)),
          inv_mul_cancel₀ hc, ENNReal.ofReal_one, one_mul]
theorem mixedMulHaar_map_mul_right {c : mixedEmbedding.mixedSpace K}
    (hc : mixedEmbedding.norm c ≠ 0) :
    Measure.map (fun x : mixedEmbedding.mixedSpace K => x * c) (mixedMulHaar K)
      = mixedMulHaar K := by
  have hfmeas : Measurable (fun x : mixedEmbedding.mixedSpace K => x * c) :=
    (continuous_id.mul continuous_const).measurable
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  rw [lintegral_map hg hfmeas]
  exact lintegral_comp_mul_right_mixedMulHaar K g hg hc
variable {K} in
/-- Right translation by `mixedEmbedding K u` (`= x ↦ u • x` by commutativity of
the mixed space) is measurable. -/
theorem measurable_unitSMul (u : (𝓞 K)ˣ) :
    Measurable (fun x : mixedEmbedding.mixedSpace K => u • x) := by
  simp only [unitSMul_smul]
  exact (continuous_const.mul continuous_id).measurable
variable {K} in
/-- **The unit action is `mixedMulHaar`-measure-preserving**: the pushforward of
`mixedMulHaar K` under `x ↦ u • x` is `mixedMulHaar K`.
Proof: `u • x = mixedEmbedding K u * x = x * mixedEmbedding K u` (mixed-space
multiplication is commutative), and `mixedEmbedding.norm (mixedEmbedding K u) = 1`
(`norm_unit`), so this is the right-translation invariance
`mixedMulHaar_map_mul_right`. -/
theorem mixedMulHaar_map_unitSMul (u : (𝓞 K)ˣ) :
    Measure.map (fun x : mixedEmbedding.mixedSpace K => u • x) (mixedMulHaar K)
      = mixedMulHaar K := by
  have hfun : (fun x : mixedEmbedding.mixedSpace K => u • x)
      = fun x => x * mixedEmbedding K (u : K) := by
    funext x; rw [unitSMul_smul, mul_comm]
  have hc : mixedEmbedding.norm (mixedEmbedding K (u : K)) ≠ 0 := by
    rw [norm_unit]; norm_num
  rw [hfun]
  exact mixedMulHaar_map_mul_right (K := K) hc
variable {K} in
/-- **The unit action is measure-preserving** for `mixedMulHaar K`,
packaged as `MeasureTheory.MeasurePreserving`
(the form consumed by Mathlib's `IsFundamentalDomain` machinery). -/
theorem measurePreserving_unitSMul (u : (𝓞 K)ˣ) :
    MeasurePreserving (fun x : mixedEmbedding.mixedSpace K => u • x)
      (mixedMulHaar K) (mixedMulHaar K) :=
  ⟨measurable_unitSMul u, mixedMulHaar_map_unitSMul u⟩
open NumberField.Units NumberField.Units.dirichletUnitTheorem
variable {K} in
/-- The monoid hom `ℤ^(rank K) → (𝓞 K)ˣ` sending `(eᵢ)` to `∏ᵢ (fundSystem K i)^(eᵢ)`.
Its image is a complement of `torsion K` in `(𝓞 K)ˣ` (Dirichlet's unit theorem),
so it realises the free part `(𝓞 K)ˣ ⧸ torsion K ≅ ℤ^(rank K)` as a genuine
subgroup acting on the mixed space. -/
def coneUnitHom : Multiplicative (Fin (NumberField.Units.rank K) → ℤ) →* (𝓞 K)ˣ where
  toFun g := ∏ i, fundSystem K i ^ (Multiplicative.toAdd g i)
  map_one' := by simp
  map_mul' g h := by
    simp only [toAdd_mul, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
variable {K} in
/-- The acting group `Multiplicative (Fin (NumberField.Units.rank K) → ℤ)` acts on the mixed space
through `coneUnitHom` and the unit action. -/
local instance coneMulAction :
    MulAction (Multiplicative (Fin (NumberField.Units.rank K) → ℤ)) (mixedEmbedding.mixedSpace K) :=
  MulAction.compHom _ (coneUnitHom (K := K))
variable {K} in
/-- The cone action is by measurable maps (`g • · = coneUnitHom g • ·`, and the unit
action is measurable), as required by Mathlib's `IsFundamentalDomain.setIntegral_eq`
machinery. -/
local instance coneMeasurableConstSMul :
    MeasurableConstSMul (Multiplicative (Fin (NumberField.Units.rank K) → ℤ)) (mixedEmbedding.mixedSpace K) :=
  ⟨fun g => measurable_unitSMul (coneUnitHom g)⟩
variable {K} in
/-- The acting group is countable (`Fin (rank K) → ℤ` with finite domain and
countable codomain), as required by the fundamental-domain tsum machinery. -/
local instance coneCountable : Countable (Multiplicative (Fin (NumberField.Units.rank K) → ℤ)) :=
  inferInstanceAs (Countable (Fin (rank K) → ℤ))
variable {K} in
/-- `mixedMulHaar K` is invariant under the cone action (the unit action is
measure-preserving, `measurePreserving_unitSMul`), as required by Mathlib's
`IsFundamentalDomain.setIntegral_eq` machinery. -/
local instance coneSMulInvariantMeasure :
    SMulInvariantMeasure (Multiplicative (Fin (NumberField.Units.rank K) → ℤ)) (mixedEmbedding.mixedSpace K)
      (mixedMulHaar K) :=
  ⟨fun g s hs =>
    (measurePreserving_unitSMul (coneUnitHom g)).measure_preimage hs.nullMeasurableSet⟩
end MulHaarRightInvariance
def completedPartialZeta (𝔞 : Ideal (𝓞 K)) (s : ℂ) : ℂ :=
  (1 / (Units.torsionOrder K : ℂ)) *
    (Ideal.absNorm 𝔞 : ℂ) ^ s *
      ((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2) *
        MeasureTheory.integral (mixedMulHaar K)
          (fun x => (mixedEmbedding.fundamentalCone K).indicator
            (fun x => Theta.idealThetaKernel K 𝔞 x * (mixedEmbedding.norm x : ℂ) ^ s) x)
open Classical in
/-- A choice of integral-ideal representative for each ideal class, via the
surjectivity of `ClassGroup.mk0` onto the (finite) class group `ClassGroup (𝓞 K)`. -/
def idealClassRep (c : ClassGroup (𝓞 K)) : Ideal (𝓞 K) :=
  ((Function.surjInv ClassGroup.mk0_surjective c : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))
def completedDedekindZeta (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  letI : NumberField K := ‹_›
  ∑ c : ClassGroup (𝓞 K), completedPartialZeta K (idealClassRep K c) s
open Classical in
/-- The ideal class of a nonzero integral ideal `𝔟`, as an element of
`ClassGroup (𝓞 K)`. -/
noncomputable def idealClass (𝔟 : NonzeroIdeal K) : ClassGroup (𝓞 K) :=
  ClassGroup.mk0 ⟨(𝔟 : Ideal (𝓞 K)), mem_nonZeroDivisors_iff_ne_zero.mpr 𝔟.2⟩
section GaussianMellinConvergence
open MeasureTheory NumberField.mixedEmbedding
end GaussianMellinConvergence
variable {K} in
/-- **The cone-action group acting on the nonzero elements of a fractional ideal.**
The cone-action group
`G = Multiplicative (Fin (rank K) → ℤ)` acts on
`S = {a : K // a ∈ I ∧ a ≠ 0}` by multiplication through `coneUnitHom`:
`g • a = ((coneUnitHom g : 𝓞 K) : K) * a`. Membership in `I` is preserved because
`I` is an `𝓞 K`-submodule (`Submodule.smul_mem`) and `coneUnitHom g` is a unit, so
the product stays nonzero. This is the algebraic input to the free-orbit collapse
of the dominating series. -/
instance coneFracSMul (I : FractionalIdeal (𝓞 K)⁰ K) :
    MulAction (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
      {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0} where
  smul g a := ⟨((coneUnitHom (K := K) g : 𝓞 K) : K) * a.1, by
    refine ⟨?_, ?_⟩
    · have h := (I : Submodule (𝓞 K) K).smul_mem (coneUnitHom (K := K) g : 𝓞 K) a.2.1
      rwa [Algebra.smul_def] at h
    · refine mul_ne_zero ?_ a.2.2
      simpa using (coneUnitHom (K := K) g).ne_zero⟩
  one_smul a := by
    apply Subtype.ext
    show ((coneUnitHom (K := K) 1 : 𝓞 K) : K) * a.1 = a.1
    simp
  mul_smul g h a := by
    apply Subtype.ext
    show ((coneUnitHom (K := K) (g * h) : 𝓞 K) : K) * a.1
        = ((coneUnitHom (K := K) g : 𝓞 K) : K)
            * (((coneUnitHom (K := K) h : 𝓞 K) : K) * a.1)
    rw [map_mul]
    push_cast
    ring
end
end DedekindZeta


