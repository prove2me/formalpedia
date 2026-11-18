-- Prove2me | solution 1 for ArtinKP.N2.cusp_integral_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:13:16.409965+00:00
-- url     : https://prove2.me/submissions/40e65712-d0e6-4682-aae9-03c1e99dedb4

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeSModel
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ArtinKPB017
import Theorems.Thm_ArtinKP_GL_eisEigen_of_two_lt_re
import Theorems.Thm_ArtinKP_N_cf_theta_translate
import Theorems.Thm_ArtinKP_N2_zRes_congr

section
-- module Solutions.Artin.KP.X_Quot
attribute [-instance] _root_.ArtinKP.B1.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatSub _root_.ArtinKP.N.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinKP.X.instMeasurableConstSMulGinfX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instSMulInvariantMeasureGinfXVol _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-X, file 5: quotient measures and unfolding without fundamental domains

Abstract setting: a countable group `G` acting measurably on `(α, μ)` and preserving `μ`.
A *partition of unity* for the action is a measurable `η : α → ℝ≥0∞` with
`∑_g η (g • a) = 1` for all `a` (the indicator of a strict fundamental domain is one; in a
properly discontinuous situation an everywhere positive one always exists, `exists_isPOU`).
The quotient measure on `G \ α` is the push-forward of `η μ`; it does not depend on `η`
(`quotMeasure_eq`).  Everything is Tonelli:

* `lintegral_tsum_swap` : `∫ φ · Σ_g ψ∘g = ∫ ψ · Σ_g φ∘g`;
* `lintegral_mul_pou_eq` : independence of `η`;
* `lintegral_autom_mul_eq` : unfolding `∫_{G\α} (Σ_{H\G} f∘γ) u = ∫_{H\α} f u`;
* `setLIntegral_le_mul_lintegral_pou` : a set meeting each orbit at most `m` times has
  `∫_B f ≤ m ∫_{G\α} f`.
-/

open scoped ENNReal
open MeasureTheory Set

set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]
  [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]

lemma tsum_smul_comp_smul (ψ : α → ℝ≥0∞) (g₀ : G) (a : α) :
    ∑' g : G, ψ (g • g₀ • a) = ∑' g : G, ψ (g • a) := by
  have := (Equiv.mulRight g₀).tsum_eq (fun g : G => ψ (g • a))
  simpa [mul_smul] using this

/-! ### The quotient measure -/

/-! ### Unfolding -/

theorem instCountableQuot (H : Subgroup G) : Countable (G ⧸ H) :=
  inferInstanceAs (Countable (Quotient (QuotientGroup.leftRel H)))

lemma quotProdEquiv_apply (H : Subgroup G) (p : (G ⧸ H) × H) :
    quotProdEquiv H p = p.1.out * (p.2 : G) := rfl

theorem isPOU_pouRestrict (H : Subgroup G) {η : α → ℝ≥0∞} (hη : IsPOU G η) :
    IsPOU H (pouRestrict H η) := by
  haveI _iCQ := instCountableQuot H
  refine ⟨Measurable.ennreal_tsum fun q => hη.measurable.comp (measurable_const_smul _), ?_⟩
  intro a
  unfold pouRestrict
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_prod (f := fun (q : G ⧸ H) (h : H) => η (q.out • h • a)),
    ← hη.tsum_eq a, ← (quotProdEquiv H).tsum_eq]
  refine tsum_congr fun p => ?_
  rw [quotProdEquiv_apply, mul_smul]
  rfl

/-- **Unfolding** (nonnegative form):
`∫_{G\α} (Σ_{γ ∈ H\G} f(γ a)) u(a) = ∫_{H\α} f(a) u(a)` for `f` `H`-invariant and `u`
`G`-invariant, the two quotient integrals being computed with any partitions of unity. -/
theorem lintegral_autom_mul_eq (H : Subgroup G) {η ηH : α → ℝ≥0∞} (hη : IsPOU G η)
    (hηH : IsPOU H ηH) {f u : α → ℝ≥0∞} (hf : Measurable f) (hu : Measurable u)
    (hfinv : ∀ (h : H) (a : α), f (h • a) = f a) (huinv : ∀ (g : G) (a : α), u (g • a) = u a) :
    ∫⁻ a, autom H f a * u a * η a ∂μ = ∫⁻ a, f a * u a * ηH a ∂μ := by
  haveI _iCQ := instCountableQuot H
  have hm : ∀ g : G, Measurable fun a : α => g • a := fun g => measurable_const_smul g
  calc ∫⁻ a, autom H f a * u a * η a ∂μ
      = ∑' q : G ⧸ H, ∫⁻ a, f (q.out⁻¹ • a) * u a * η a ∂μ := by
        unfold autom
        simp_rw [← ENNReal.tsum_mul_right]
        exact lintegral_tsum fun q =>
          (((hf.comp (hm _)).mul hu).mul hη.measurable).aemeasurable
    _ = ∑' q : G ⧸ H, ∫⁻ a, f a * u a * η (q.out • a) ∂μ := by
        refine tsum_congr fun q => ?_
        have hF : Measurable fun a => f (q.out⁻¹ • a) * u a * η a :=
          ((hf.comp (hm _)).mul hu).mul hη.measurable
        rw [← lintegral_comp_smul (μ := μ) q.out hF]
        refine lintegral_congr fun a => ?_
        simp [huinv]
    _ = ∫⁻ a, f a * u a * pouRestrict H η a ∂μ := by
        unfold pouRestrict
        simp_rw [← ENNReal.tsum_mul_left]
        exact (lintegral_tsum fun q =>
          ((hf.mul hu).mul (hη.measurable.comp (hm _))).aemeasurable).symm
    _ = ∫⁻ a, f a * u a * ηH a ∂μ := by
        have hfu : Measurable fun a => f a * u a := hf.mul hu
        exact lintegral_mul_pou_eq (G := H) (isPOU_pouRestrict H hη) hηH hfu
          (fun h a => by
            change f (h • a) * u ((h : G) • a) = _
            rw [hfinv, huinv])

/-! ### Multiplicity and existence of partitions of unity -/

/-- If the return set of `B` is contained in the finite set `R`, every orbit meets `B` at most
`R.card` times. -/
theorem tsum_indicator_le_card {B : Set α} (R : Finset G)
    (hR : ∀ g : G, (∃ a ∈ B, g • a ∈ B) → g ∈ R) (a : α) :
    ∑' g : G, B.indicator (fun _ => (1 : ℝ≥0∞)) (g • a) ≤ R.card := by
  classical
  by_cases h : ∃ g₀ : G, g₀ • a ∈ B
  · obtain ⟨g₀, hg₀⟩ := h
    have hzero : ∀ g ∉ R.image (· * g₀), B.indicator (fun _ => (1 : ℝ≥0∞)) (g • a) = 0 := by
      intro g hg
      refine indicator_of_notMem (fun hgB => hg ?_) _
      refine Finset.mem_image.mpr ⟨g * g₀⁻¹, hR _ ⟨g₀ • a, hg₀, ?_⟩, by simp⟩
      rwa [← mul_smul, inv_mul_cancel_right]
    rw [tsum_eq_sum hzero]
    calc ∑ g ∈ R.image (· * g₀), B.indicator (fun _ => (1 : ℝ≥0∞)) (g • a)
        ≤ ∑ _g ∈ R.image (· * g₀), (1 : ℝ≥0∞) :=
          Finset.sum_le_sum fun g _ => by by_cases hg : g • a ∈ B <;> simp [hg]
      _ = (R.image (· * g₀)).card := by simp
      _ ≤ R.card := by exact_mod_cast Finset.card_image_le
  · push Not at h
    have : ∀ g : G, B.indicator (fun _ => (1 : ℝ≥0∞)) (g • a) = 0 := fun g =>
      indicator_of_notMem (h g) _
    simp [this]

/-- The indicator of a strict fundamental set (every orbit meets it in exactly one point, with
multiplicity one) is a partition of unity. This links the present formalism with fundamental
domains. -/
theorem isPOU_indicator_of_existsUnique {D : Set α} (hD : MeasurableSet D)
    (h : ∀ a, ∃! g : G, g • a ∈ D) : IsPOU G (D.indicator fun _ => (1 : ℝ≥0∞)) := by
  refine ⟨measurable_const.indicator hD, fun a => ?_⟩
  obtain ⟨g₀, hg₀, huniq⟩ := h a
  rw [tsum_eq_single g₀ (fun g hg => indicator_of_notMem (fun hgD => hg (huniq g hgD)) _),
    indicator_of_mem hg₀]

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_H3
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulGinfX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatComplexH3 _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulGinfX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatComplexH3 _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instSMulInvariantMeasureGinfXVol _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatComplexH3Vol _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatXVol _root_.ArtinKP.X.instSigmaFiniteH3Vol _root_.ArtinKP.X.instSigmaFiniteXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-X, file 1: one factor — hyperbolic 3-space and the action of `SL(2,ℂ)`

`H3 = {(x, v) : ℂ × ℝ | 0 < v}` with the quaternionic Möbius action
`g • (x, v) = (((a x + b) conj(c x + d) + a conj(c) v²) / D, v / D)`,
`D = |c x + d|² + |c|² v²`.  The action axioms are proved through the quaternion `x + v j`:
`a P + b = (g • P) (c P + d)` in `ℍ[ℝ]`.
-/

open scoped MatrixGroups Quaternion ComplexConjugate

namespace ArtinKP.X

noncomputable section

open H3

lemma smul_def (g : SL(2, ℂ)) (P : H3) : g • P = mob g P := rfl

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Space
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.X.chart1_symm_fst _root_.ArtinKP.X.chart1_symm_snd _root_.ArtinKP.X.chart1_v _root_.ArtinKP.X.chart1_x _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
/-! # WP-X, file 3: the space `X = (H³)^r`

`X F = InfinitePlace F → H3`, the action of `G∞ = InfinitePlace F → SL(2,ℂ)` and of `SL(2,F)`
(through the embeddings `w.embedding`), heights, pair heights, the invariant measure and the
torus `a(y)`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

lemma sigma_apply (γ : SL(2, F)) (w : InfinitePlace F) (i j : Fin 2) :
    (sigma F γ w) i j = w.embedding (γ i j) := rfl

variable {F}

namespace X

lemma ht_pos (P : X F) : 0 < ht P := Finset.prod_pos fun w _ => P.v_pos w

lemma pairHt_eq_prod (c d : F) (P : X F) :
    pairHt c d P = ∏ w, P.v w / H3.rowDen (w.embedding c) (w.embedding d) (P w) := by
  unfold pairHt ht pairDen
  rw [Finset.prod_div_distrib]

/-- `ht (γ • P) = I_{(c,d)}(P)` for the bottom row `(c, d)` of `γ`. -/
theorem ht_smul (γ : SL(2, F)) (P : X F) : ht (γ • P) = pairHt (γ 1 0) (γ 1 1) P := by
  rw [pairHt_eq_prod]
  exact Finset.prod_congr rfl fun w _ => rfl

/-- The pair height of the pair `(c, d) γ` at `P` is the pair height of `(c, d)` at `γ • P`
(right action of `SL(2,F)` on pairs). -/
theorem pairHt_smul (c d : F) (γ : SL(2, F)) (P : X F) :
    pairHt c d (γ • P) = pairHt (c * γ 0 0 + d * γ 1 0) (c * γ 0 1 + d * γ 1 1) P := by
  rw [pairHt_eq_prod, pairHt_eq_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  have key : ∀ (g : SL(2, ℂ)) (c d : ℂ) (Q : H3),
      H3.rowDen c d (g • Q) * den g Q =
        H3.rowDen (c * g 0 0 + d * g 1 0) (c * g 0 1 + d * g 1 1) Q := by
    intro g c d Q
    rw [← H3.normSq_row, ← H3.normSq_row, den, ← H3.normSq_row, ← map_mul]
    congr 1
    have hq := q_mob g Q
    rw [← smul_def] at hq
    rw [add_mul, mul_assoc, ← hq]
    simp only [Quaternion.coeComplex_add, Quaternion.coeComplex_mul]
    noncomm_ring
  have h := key (sigma F γ w) (w.embedding c) (w.embedding d) (P w)
  change (P w).v / den (sigma F γ w) (P w) / H3.rowDen _ _ (sigma F γ w • P w) = _
  have hd := den_pos (sigma F γ w) (P w)
  simp only [sigma_apply] at h
  rw [map_add, map_add, map_mul, map_mul, map_mul, map_mul, ← h, div_div, mul_comm]
  rfl

end X

/-! ### Topology and measure -/

lemma X.continuous_ht : Continuous (X.ht : X F → ℝ) :=
  continuous_finsetProd _ fun w _ => X.continuous_v w

/-! ### Upper triangular elements, translations and the torus -/

/-- The action of an upper triangular element of `SL(2,ℂ)`. -/
lemma smul_of_lower_zero {g : SL(2, ℂ)} (hc : g 1 0 = 0) (P : H3) :
    (g • P).x = g 0 0 ^ 2 * P.x + g 0 0 * g 0 1 ∧ (g • P).v = Complex.normSq (g 0 0) * P.v := by
  have hd := det_eq g
  rw [hc, mul_zero, sub_zero] at hd
  have ha : g 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hd
  have hd1 : g 1 1 = (g 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hd
  have hden : den g P = (Complex.normSq (g 0 0))⁻¹ := by
    simp [den, H3.rowDen, hc, hd1]
  constructor
  · rw [smul_x, hden]
    simp only [H3.rowNum, hc, hd1, zero_mul, zero_add, map_zero, mul_zero, add_zero, map_inv₀,
      Complex.ofReal_inv, div_inv_eq_mul, Complex.normSq_eq_conj_mul_self]
    have : conj (g 0 0) ≠ 0 := by simpa using ha
    field_simp
  · rw [smul_v, hden, div_inv_eq_mul, mul_comm]

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Discrete
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
/-! # WP-X, file 6: discreteness of `SL(2, 𝓞_F)` on `X`, the quotient measure, `L²(Γ\X)`

* `entries_bounded`: if `Q` and `g • Q` lie in a box of `H3` the entries of `g` are bounded;
* `finite_return_box`: a box of `X` meets only finitely many of its `SL(2,𝓞_F)`-translates
  (`𝓞_F` is discrete in `ℂ^r`); the same for compact sets (`finite_return_of_isCompact`);
* a positive partition of unity for every subgroup `Γ ≤ SL(2,𝓞_F)`, the quotient measure
  `X.quotVol Γ` on `Γ \ X` (independent of the partition), `X.L2 Γ = L²(Γ\X)`;
* the cusp stabilizer `GammaInf Γ` and its action in coordinates.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

/-! ### One factor -/

/-! ### The integral group -/

variable {F : Type*} [Field F] [NumberField F]

lemma intSL_apply (γ : SL(2, 𝓞 F)) (i j : Fin 2) : (intSL F γ) i j = algebraMap (𝓞 F) F (γ i j) :=
  rfl

lemma intSL_smul (γ : SL(2, 𝓞 F)) (P : X F) : γ • P = intSL F γ • P := rfl

lemma X.exists_mem_box (P : X F) : ∃ n : ℕ, P ∈ X.box n := by
  have h1 : ∃ n : ℕ, ∀ w, ‖P.x w‖ ≤ n ∧ P.v w ≤ n ∧ 1 / P.v w ≤ n := by
    obtain ⟨n, hn⟩ := exists_nat_ge
      (∑ w : InfinitePlace F, (‖P.x w‖ + P.v w + 1 / P.v w))
    refine ⟨n, fun w => ?_⟩
    have hnn : ∀ w' ∈ (Finset.univ : Finset (InfinitePlace F)),
        0 ≤ ‖P.x w'‖ + P.v w' + 1 / P.v w' := fun w' _ => by
      have := P.v_pos w'
      positivity
    have := (Finset.single_le_sum hnn (Finset.mem_univ w)).trans hn
    have hv := P.v_pos w
    have h3 : 0 < 1 / P.v w := by positivity
    have h4 := norm_nonneg (P.x w)
    exact ⟨by linarith, by linarith, by linarith⟩
  obtain ⟨n, hn⟩ := h1
  refine ⟨n, fun w => ⟨(hn w).1, ?_, ?_⟩⟩
  · have hv := P.v_pos w
    have h3 := (hn w).2.2
    change 1 / ((n : ℝ) + 1) ≤ P.v w
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hv] at h3
    nlinarith
  · have := (hn w).2.1
    change P.v w ≤ (n : ℝ) + 1
    linarith

/-- **A compact set of `X` meets only finitely many `SL(2,𝓞_F)`-translates of itself.** -/
theorem finite_return_of_isCompact {K : Set (X F)} (hK : IsCompact K) :
    {γ : SL(2, 𝓞 F) | ∃ P ∈ K, γ • P ∈ K}.Finite := by
  obtain ⟨n, hn⟩ := X.exists_box_of_isCompact hK
  exact (finite_return_box n).subset fun γ ⟨P, hP, hγP⟩ => ⟨P, hn hP, hn hγP⟩

/-! ### Partition of unity, quotient measure, `L²(Γ\X)` -/

/-! ### The cusp stabilizer -/

/-- The action of an upper triangular integral matrix `[[ε, β], [0, ε⁻¹]]`:
`x_w ↦ ε_w² x_w + ε_w β_w`, `v_w ↦ |ε_w|² v_w`. -/
theorem smul_of_upper {γ : SL(2, 𝓞 F)} (h : γ 1 0 = 0) (P : X F) (w : InfinitePlace F) :
    (γ • P).x w = w.embedding (γ 0 0 : 𝓞 F) ^ 2 * P.x w +
        w.embedding (γ 0 0 : 𝓞 F) * w.embedding (γ 0 1 : 𝓞 F) ∧
      (γ • P).v w = Complex.normSq (w.embedding (γ 0 0 : 𝓞 F)) * P.v w := by
  have hc : (sigma F (intSL F γ) w) 1 0 = 0 := by
    rw [sigma_intSL_apply, h]; simp
  exact smul_of_lower_zero hc (P w)

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.B1_Pairs
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-B1, file 4: primitive pairs of `S`-integers modulo `S`-units; convergence and top height

`S` is any finite set of finite places of the totally complex field `F`; `IsSInt S`, `IsSUnit S`
describe the ring `R = 𝓞_S` and its units inside `F`.  `SPair S` = primitive pairs of `R²`
(`a c + b d = 1` solvable in `R`), `PairClass S = SPair S / U_S`, `PairClass.ht p P = ht_p(P)` the
`S`-normalized height, `PairClass.act` the right action of `SL₂(𝓞_F)`:
`(p.act γ).ht P = p.ht (γ • P)`.

* `summable_sHt_rpow`, `exists_summable_majorant_sHt`: (B1) for any family of pairwise
  `U_S`-inequivalent nonzero pairs of `S`-integers (primitive or not), `σ > 2`.
* `PairClass.summable_ht_rpow`, `PairClass.exists_summable_majorant`, `PairClass.exists_max_ht`.
* `PairClass.exists_ht_ge` (Lemma M): `sup_p ht_p(P) ≥ c₀ > 0`, under `SBezout S` (true when `R` is a PID).
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.B1

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

variable {S : Finset (FinitePlace F)}

/-! ### The raw right action of `SL₂(𝓞_F)` on pairs -/

lemma pairHt_actF (q : F × F) (γ : SL(2, 𝓞 F)) (P : X F) :
    X.pairHt (actF q γ).1 (actF q γ).2 P = X.pairHt q.1 q.2 (γ • P) := by
  rw [intSL_smul, X.pairHt_smul]; rfl

lemma sNorm_actF_le (q : F × F) (γ : SL(2, 𝓞 F)) :
    X.sNorm S (actF q γ).1 (actF q γ).2 ≤ X.sNorm S q.1 q.2 := by
  unfold X.sNorm
  refine Finset.prod_le_prod (fun v _ => le_max_of_le_left (apply_nonneg v _)) fun v _ => ?_
  have key : ∀ a b : 𝓞 F, v (q.1 * (a : F) + q.2 * (b : F)) ≤ max (v q.1) (v q.2) := by
    intro a b
    refine (FinitePlace.add_le v _ _).trans (max_le ?_ ?_)
    · rw [map_mul]
      exact (mul_le_of_le_one_right (apply_nonneg v _) (finitePlace_int_le_one v a)).trans
        (le_max_left _ _)
    · rw [map_mul]
      exact (mul_le_of_le_one_right (apply_nonneg v _) (finitePlace_int_le_one v b)).trans
        (le_max_right _ _)
  exact max_le (key _ _) (key _ _)

lemma sNorm_actF (q : F × F) (γ : SL(2, 𝓞 F)) :
    X.sNorm S (actF q γ).1 (actF q γ).2 = X.sNorm S q.1 q.2 := by
  refine le_antisymm (sNorm_actF_le q γ) ?_
  have := sNorm_actF_le (S := S) (actF q γ) γ⁻¹
  rwa [← actF_mul, mul_inv_cancel, actF_one] at this

lemma sHt_actF (q : F × F) (γ : SL(2, 𝓞 F)) (P : X F) :
    X.sHt S (actF q γ).1 (actF q γ).2 P = X.sHt S q.1 q.2 (γ • P) := by
  unfold X.sHt; rw [pairHt_actF, sNorm_actF]

/-! ### Primitive pairs and pair classes -/

namespace PairClass

variable [IsTotallyComplex F]

/-- **Equivariance**: `ht_{pγ}(P) = ht_p(γP)` for `γ ∈ SL₂(𝓞_F)`. -/
theorem ht_act (p : PairClass S) (γ : SL(2, 𝓞 F)) (P : X F) : (p.act γ).ht P = p.ht (γ • P) := by
  induction p using Quotient.inductionOn with
  | _ q => exact sHt_actF (q.c, q.d) γ P

end PairClass

/-! ### (B1) for families of `S`-integer pairs -/

/-! ### Lemma M for pair classes -/

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.B1_L2
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap _root_.ArtinKP.X.chart1_symm_fst _root_.ArtinKP.X.chart1_symm_snd _root_.ArtinKP.X.chart1_v _root_.ArtinKP.X.chart1_x _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
/-! # WP-B1, file 9: `G ∈ L¹ ∩ L²(Γ\X)`, and compactness of the truncated space at the cusp `∞`

* `measurable_G`; `lintegral_G_pow_lt_top`: `∫_{Γ\X} G^k dμ < ∞` (in the partition-of-unity form of
  WP-X) for every `k`, from the boundedness of `G` and **finite volume of `Γ\X`** (hypothesis `hvol`).
* `H3.isCompact_box`, `X.isCompact_box`.
* `exists_reduced`: every point of `X` is `Γ_∞`-equivalent (`Γ_∞ ⊂ SL₂(𝓞_F)` upper triangular) to a point
  with `x` in the fundamental cell and balanced `v`; `siegel S' T` is compact; hence
  `subset_orbit_siegel`: the points whose top class is in the `SL₂(𝓞_F)`-orbit of `∞` and whose top
  height is in `[c, T]` lie in `SL₂(𝓞_F) · (compact)`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.B1

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {S : Finset (FinitePlace F)}

/-! ### Compactness of the truncated space at the cusp `∞` (item 5) -/

omit [NumberField F] [IsTotallyComplex F] in
lemma H3.isCompact_box {m M B : ℝ} (hm : 0 < m) : IsCompact (H3.box m M B) := by
  have hind : Topology.IsInducing (Subtype.val : {p : ℂ × ℝ // 0 < p.2} → ℂ × ℝ) :=
    Topology.IsInducing.subtypeVal
  have himg : (Subtype.val : {p : ℂ × ℝ // 0 < p.2} → ℂ × ℝ) '' (H3.box m M B) =
      Metric.closedBall (0 : ℂ) B ×ˢ Set.Icc m M := by
    ext ⟨z, t⟩
    constructor
    · rintro ⟨Q, ⟨h1, h2, h3⟩, hQ⟩
      have hz : H3.x Q = z := congrArg Prod.fst hQ
      have ht : H3.v Q = t := congrArg Prod.snd hQ
      rw [hz] at h1
      rw [ht] at h2 h3
      exact ⟨by simpa using h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      have h1' : ‖z‖ ≤ B := by simpa using h1
      exact ⟨⟨(z, t), lt_of_lt_of_le hm h2⟩, ⟨h1', h2, h3⟩, rfl⟩
  exact hind.isCompact_iff.mpr (himg ▸ (isCompact_closedBall 0 B).prod isCompact_Icc)

omit [IsTotallyComplex F] in
theorem isCompact_siegelBox {m M B : ℝ} (hm : 0 < m) : IsCompact (siegelBox F m M B) := by
  have : siegelBox F m M B = Set.pi Set.univ fun _ : InfinitePlace F => H3.box m M B := by
    ext P; simp [siegelBox]
  rw [this]
  exact isCompact_univ_pi fun _ => H3.isCompact_box hm

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.RO_Bridge
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-RO, file 3: the bridge `S.Row 𝔪 / U_S ≃ B1.PairClass (SOf 𝔪)`

`h𝔪 : 𝔪 ≠ ⊥` throughout (no other hypothesis on `𝔪`).

* `rowPair`, `rowClass h𝔪 : Row 𝔪 → PairClass (SOf 𝔪)`; `rowClass_eq_iff` (fibres = `U_S`-orbits),
  `rowClass_surjective`, `rowClassEquiv : orbitRel.Quotient (SInt 𝔪)ˣ (Row 𝔪) ≃ PairClass (SOf 𝔪)`.
* actions: `intMat 𝔪 : SL₂(𝓞) →* SL₂(R)` (the map defining `Gamma 𝔪 𝔫`), `rowClass_act_intMat`
  (`SL₂(𝓞)`), `rowClass_act` (`SL₂(R)`, through `A.toF` and `B1.PairClass.actR`), `rowClass_bot`,
  `exists_toF_eq` (every `IsSMat` matrix comes from `SL₂(R)`).
* norms and heights: `sNorm_SOf` (`X.sNorm (SOf 𝔪) = S.normS 𝔪`), `ht_rowClass`
  (`ht_p(P) = I_p(P) / ‖p‖`), `prod_SOf_eq_absS`, and the product formula for `S`-units
  `prod_normSq_mul_absS : N_∞(ε) · |ε|_{S_f} = 1` (WP-S open issue 7), `pairHt_smul_row`.
-/

open scoped MatrixGroups
open NumberField IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.RO

open ArtinKP.A ArtinKP.B1 ArtinKP.X ArtinKP.S

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### Rows and pair classes -/

/-! ### Actions -/

theorem toF_intMat (γ : SL(2, 𝓞 F)) : toF 𝔪 (intMat 𝔪 γ) = intSL F γ := by
  ext i j
  rfl

/-- **Compatibility with the `SL₂(𝓞)`-actions.** -/
theorem rowClass_act_intMat (h𝔪 : 𝔪 ≠ ⊥) (p : Row 𝔪) (γ : SL(2, 𝓞 F)) :
    rowClass h𝔪 (p.act (intMat 𝔪 γ)) = (rowClass h𝔪 p).act γ := by
  change (⟦rowPair h𝔪 (p.act (intMat 𝔪 γ))⟧ : PairClass (SOf 𝔪)) = ⟦(rowPair h𝔪 p).act γ⟧
  congr 1

/-! ### Norms and heights -/

theorem finitePlace_mk_apply (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    FinitePlace.mk v x = NumberField.HeightOneSpectrum.adicAbv F v x := by
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding]

open scoped Classical in
theorem prod_SOf (f : FinitePlace F → ℝ) :
    ∏ v ∈ SOf 𝔪, f v = ∏ v ∈ CubicPkg.sFin 𝔪, f (FinitePlace.mk v) := by
  rw [SOf, Finset.prod_image]
  intro v _ v' _ h
  exact FinitePlace.mk_eq_iff.mp h

/-- `‖(c, d)‖` of WP-B1/WP-X is `normS` of WP-S. -/
theorem sNorm_SOf (c d : F) : X.sNorm (SOf 𝔪) c d = normS 𝔪 c d := by
  unfold X.sNorm normS
  rw [prod_SOf]
  exact Finset.prod_congr rfl fun v _ => by rw [finitePlace_mk_apply, finitePlace_mk_apply]

variable [IsTotallyComplex F]

/-- The height of a row class: `ht_p(P) = I_p(P) / ‖p‖`. -/
theorem ht_rowClass (h𝔪 : 𝔪 ≠ ⊥) (p : Row 𝔪) (P : X F) :
    (rowClass h𝔪 p).ht P = X.pairHt (p.c : F) (p.d : F) P / p.norm := by
  change X.sHt (SOf 𝔪) (p.c : F) (p.d : F) P = _
  unfold X.sHt Row.norm
  rw [sNorm_SOf]

end

end ArtinKP.RO
end

section
-- module Solutions.Artin.KP.X2_Chart
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-X2, file 1: the logarithmic chart of `X = (H³)^r`

`chart F : (InfinitePlace F → ℂ × ℝ) ≃ₜ X F`, `(x_w, t_w)_w ↦ (x_w, exp t_w)_w`.  In this chart
`X.vol F` is Lebesgue measure with the smooth density `rho y = exp (-2 ∑_w t_w)`
(`measurePreserving_chart`).  All calculus on `X` is done in this chart: a function on `X` is
smooth iff its pull-back to the vector space `Coord F` is.

Also: Tonelli for products of functions of one coordinate on a finite product
(`lintegral_fintype_prod_eq_prod`) and `pi_withDensity`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

/-! ### Products of densities -/

section PiDensity

set_option backward.isDefEq.respectTransparency false in
theorem lintegral_fin_nat_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : Fin n) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      calc
        _ = ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)),
            f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i ↦ μ i.succ))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, cast_eq, Fin.cons_zero]
        _ = (∫⁻ x, f 0 x ∂μ 0)
            * ∏ i : Fin n, ∫⁻ (x : E (Fin.succ i)), f (Fin.succ i) x ∂(μ i.succ) := by
          rw [← n_ih (fun i => f i.succ) (fun i => hf i.succ),
            ← lintegral_prod_mul (hf 0).aemeasurable]
          exact (Finset.measurable_prod _ fun i _ =>
            (hf i.succ).comp (measurable_pi_apply i)).aemeasurable
        _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]

variable {ι : Type*} [Fintype ι]

/-- Tonelli on a finite product, for a product of functions of one coordinate each. -/
theorem lintegral_fintype_prod_eq_prod {E : ι → Type*} (f : (i : ι) → E i → ℝ≥0∞)
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  rw [lintegral_fin_nat_prod_eq_prod (fun i => f (e i)) (fun i => hf (e i))]

/-- A product of measures with densities is the product measure with the product density. -/
theorem pi_withDensity {α : ι → Type*} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] (f : ∀ i, α i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i => (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have h : ∀ x : ∀ i, α i, (Set.pi univ s).indicator (fun x => ∏ i, f i (x i)) x =
      ∏ i, (s i).indicator (f i) (x i) := by
    intro x
    by_cases hx : x ∈ Set.pi univ s
    · rw [indicator_of_mem hx]
      exact Finset.prod_congr rfl fun i _ => (indicator_of_mem (hx i (mem_univ i)) _).symm
    · rw [indicator_of_notMem hx]
      simp only [mem_pi, mem_univ, forall_true_left, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _)).symm
  simp_rw [h]
  rw [lintegral_fintype_prod_eq_prod _ (fun i => (hf i).indicator (hs i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), lintegral_indicator (hs i)]

end PiDensity

/-! ### One factor -/

/-! ### The product -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_L2
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-X, file 7: `L²` of the quotient and local restriction maps (abstract)

For a partition of unity `η` and a measurable set `B` meeting each orbit at most `m < ∞` times,
pulling back and restricting is a bounded operator
`restrictL2 : L²(G \ α) →L[ℂ] L²(B, μ)` of norm `≤ √m`.  Every functional
`u ↦ ∫_B conj ψ · u` with `ψ ∈ L²(B)` is therefore continuous on `L²(G \ α)`
(`pairingL2`).  This is the continuity of Fourier-coefficient functionals (MATH (C6)).
-/

open scoped ENNReal ComplexConjugate InnerProductSpace
open MeasureTheory Set

set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]
  [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ] {η : α → ℝ≥0∞}

lemma liftQ_smul (u : Lp ℂ 2 (quotMeasure G η μ)) (g : G) (a : α) :
    liftQ u (g • a) = liftQ u a := by
  unfold liftQ; rw [mk_smul]

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Fourier
attribute [-instance] _root_.ArtinKP.B1.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatSub _root_.ArtinKP.N.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-X, file 9: local restriction and coefficient functionals on `L²(Γ\X)`

* `X.vol_box_lt_top`: boxes have finite measure;
* `X.restrictBox Γ n : L²(Γ\X) →L[ℂ] L²(box n)`, bounded;
* `X.coeffFunctional Γ n ψ … : L²(Γ\X) →L[ℂ] ℂ`, `u ↦ ∫_{box n} conj ψ · u`, for bounded measurable
  `ψ`.  The Fourier-coefficient functional `ℓ_{ν,φ}` of MATH (C6) is the case
  `ψ(P) = 1_D(x) · conj(e_∞(-ν x) φ(v))` with `D` a fundamental set of the translation lattice
  and `supp φ` compact (so that `D × supp φ` lies in a box).
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

lemma X.lift_smul (Γ : Subgroup (SL(2, 𝓞 F))) (u : X.L2 Γ) (γ : Γ) (P : X F) :
    X.lift Γ u (γ • P) = X.lift Γ u P :=
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  liftQ_smul u γ P

lemma X.stronglyMeasurable_lift (Γ : Subgroup (SL(2, 𝓞 F))) (u : X.L2 Γ) :
    StronglyMeasurable (X.lift Γ u) :=
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  stronglyMeasurable_liftQ u

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_QuotC
attribute [-instance] _root_.ArtinKP.B1.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatSub _root_.ArtinKP.N.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinKP.X.instMeasurableConstSMulGinfX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instSMulInvariantMeasureGinfXVol _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-X, file 8: unfolding for complex-valued functions (absolutely convergent case)

Complex versions of the Tonelli lemmas of `X_Quot`, under an absolute-integrability hypothesis
stated as finiteness of a lower integral.  Weights are the real numbers `(η a).toReal`.
-/

open scoped ENNReal
open MeasureTheory Set

set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]
  [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]

lemma IsPOU.le_one {η : α → ℝ≥0∞} (hη : IsPOU G η) (a : α) : η a ≤ 1 := by
  have h := ENNReal.le_tsum (f := fun g : G => η (g • a)) 1
  rwa [one_smul, hη.tsum_eq] at h

lemma IsPOU.ne_top {η : α → ℝ≥0∞} (hη : IsPOU G η) (a : α) : η a ≠ ⊤ :=
  ((hη.le_one a).trans_lt ENNReal.one_lt_top).ne

lemma IsPOU.enorm_toReal {η : α → ℝ≥0∞} (hη : IsPOU G η) (a : α) :
    ‖(((η a).toReal : ℝ) : ℂ)‖ₑ = η a := by
  rw [← ofReal_norm, Complex.norm_real, ofReal_norm]
  exact Real.enorm_toReal (hη.ne_top a)

lemma IsPOU.tsum_toReal {η : α → ℝ≥0∞} (hη : IsPOU G η) (a : α) :
    ∑' g : G, (((η (g • a)).toReal : ℝ) : ℂ) = 1 := by
  rw [← Complex.ofReal_tsum, ← ENNReal.tsum_toReal_eq (fun g => hη.ne_top _), hη.tsum_eq]
  simp

lemma IsPOU.measurable_toReal {η : α → ℝ≥0∞} (hη : IsPOU G η) :
    Measurable fun a => (((η a).toReal : ℝ) : ℂ) :=
  Complex.measurable_ofReal.comp hη.measurable.ennreal_toReal

/-- **Complex Tonelli swap**: `∫ φ · Σ_g ψ(g a) = ∫ ψ · Σ_g φ(g a)` when
`∫ |φ| Σ_g |ψ(g a)| < ∞`. -/
theorem integral_tsum_swap {φ ψ : α → ℂ} (hφ : Measurable φ) (hψ : Measurable ψ)
    (hfin : ∫⁻ a, ‖φ a‖ₑ * ∑' g : G, ‖ψ (g • a)‖ₑ ∂μ ≠ ⊤) :
    ∫ a, φ a * ∑' g : G, ψ (g • a) ∂μ = ∫ a, ψ a * ∑' g : G, φ (g • a) ∂μ := by
  have hm : ∀ g : G, Measurable fun a : α => g • a := fun g => measurable_const_smul g
  have h1 : ∑' g : G, ∫⁻ a, ‖φ a * ψ (g • a)‖ₑ ∂μ ≠ ⊤ := by
    have : ∑' g : G, ∫⁻ a, ‖φ a * ψ (g • a)‖ₑ ∂μ = ∫⁻ a, ‖φ a‖ₑ * ∑' g : G, ‖ψ (g • a)‖ₑ ∂μ := by
      simp_rw [enorm_mul, ← ENNReal.tsum_mul_left]
      exact (lintegral_tsum fun g =>
        (hφ.enorm.mul (hψ.comp (hm g)).enorm).aemeasurable).symm
    rwa [this]
  have h2 : ∀ g : G, ∫⁻ a, ‖ψ a * φ (g⁻¹ • a)‖ₑ ∂μ = ∫⁻ a, ‖φ a * ψ (g • a)‖ₑ ∂μ := by
    intro g
    have hF : Measurable fun a => ‖ψ a * φ (g⁻¹ • a)‖ₑ := (hψ.mul (hφ.comp (hm g⁻¹))).enorm
    rw [← lintegral_comp_smul (μ := μ) g hF]
    refine lintegral_congr fun a => ?_
    simp [mul_comm]
  calc ∫ a, φ a * ∑' g : G, ψ (g • a) ∂μ
      = ∫ a, ∑' g : G, φ a * ψ (g • a) ∂μ := by simp_rw [tsum_mul_left]
    _ = ∑' g : G, ∫ a, φ a * ψ (g • a) ∂μ :=
        integral_tsum (f := fun (g : G) a => φ a * ψ (g • a))
          (fun g => (hφ.mul (hψ.comp (hm g))).aestronglyMeasurable) h1
    _ = ∑' g : G, ∫ a, ψ a * φ (g⁻¹ • a) ∂μ := by
        refine tsum_congr fun g => ?_
        rw [← integral_smul_eq_self (μ := μ) (fun a => ψ a * φ (g⁻¹ • a)) (g := g)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
        change φ a * ψ (g • a) = ψ (g • a) * φ (g⁻¹ • g • a)
        rw [inv_smul_smul, mul_comm]
    _ = ∫ a, ∑' g : G, ψ a * φ (g⁻¹ • a) ∂μ :=
        (integral_tsum (f := fun (g : G) a => ψ a * φ (g⁻¹ • a))
          (fun g => (hψ.mul (hφ.comp (hm g⁻¹))).aestronglyMeasurable)
          (by simp_rw [h2]; exact h1)).symm
    _ = ∫ a, ψ a * ∑' g : G, φ (g⁻¹ • a) ∂μ := by simp_rw [tsum_mul_left]
    _ = ∫ a, ψ a * ∑' g : G, φ (g • a) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
        change ψ a * _ = ψ a * _
        congr 1
        exact (Equiv.inv G).tsum_eq (fun g : G => φ (g • a))

/-- **Independence of the partition of unity**, complex form. -/
theorem integral_mul_pou_eq {η η' : α → ℝ≥0∞} (hη : IsPOU G η) (hη' : IsPOU G η')
    {f : α → ℂ} (hf : Measurable f) (hinv : ∀ (g : G) (a : α), f (g • a) = f a)
    (hfin : ∫⁻ a, ‖f a‖ₑ * η a ∂μ ≠ ⊤) :
    ∫ a, f a * (((η a).toReal : ℝ) : ℂ) ∂μ = ∫ a, f a * (((η' a).toReal : ℝ) : ℂ) ∂μ := by
  have hφ : Measurable fun a => f a * (((η a).toReal : ℝ) : ℂ) := hf.mul hη.measurable_toReal
  have h := integral_tsum_swap (G := G) (μ := μ) hφ hη'.measurable_toReal (by
    simp_rw [hη'.enorm_toReal, hη'.tsum_eq, mul_one, enorm_mul, hη.enorm_toReal]
    exact hfin)
  simp only [hη'.tsum_toReal, mul_one, hinv, tsum_mul_left, hη.tsum_toReal] at h
  rw [h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun a => mul_comm _ _)

lemma IsPOU.pouRestrict_toReal (H : Subgroup G) {η : α → ℝ≥0∞} (hη : IsPOU G η) (a : α) :
    (((pouRestrict H η a).toReal : ℝ) : ℂ) = ∑' q : G ⧸ H, (((η (q.out • a)).toReal : ℝ) : ℂ) := by
  unfold pouRestrict
  rw [ENNReal.tsum_toReal_eq (fun q => hη.ne_top _), Complex.ofReal_tsum]

/-- **Unfolding** (absolutely convergent form):
`∫_{G\α} (Σ_{γ ∈ H\G} f(γ a)) u(a) = ∫_{H\α} f(a) u(a)` for measurable `f` `H`-invariant and `u`
`G`-invariant with `∫_{H\α} |f| |u| < ∞`. -/
theorem integral_automC_mul_eq (H : Subgroup G) {η ηH : α → ℝ≥0∞} (hη : IsPOU G η)
    (hηH : IsPOU H ηH) {f u : α → ℂ} (hf : Measurable f) (hu : Measurable u)
    (hfinv : ∀ (h : H) (a : α), f (h • a) = f a) (huinv : ∀ (g : G) (a : α), u (g • a) = u a)
    (hfin : ∫⁻ a, ‖f a‖ₑ * ‖u a‖ₑ * ηH a ∂μ ≠ ⊤) :
    ∫ a, automC H f a * u a * (((η a).toReal : ℝ) : ℂ) ∂μ =
      ∫ a, f a * u a * (((ηH a).toReal : ℝ) : ℂ) ∂μ := by
  haveI _iCQ := ArtinKP.X.instCountableQuot H
  have hm : ∀ g : G, Measurable fun a : α => g • a := fun g => measurable_const_smul g
  have hηc := hη.measurable_toReal
  have hR := isPOU_pouRestrict H hη
  -- absolute convergence, in two equivalent forms
  have hfin' : ∫⁻ a, ‖f a‖ₑ * ‖u a‖ₑ * pouRestrict H η a ∂μ ≠ ⊤ := by
    have hfu : Measurable fun a => ‖f a‖ₑ * ‖u a‖ₑ := hf.enorm.mul hu.enorm
    rw [lintegral_mul_pou_eq (G := H) (μ := μ) hR hηH hfu (fun h a => by
      change ‖f (h • a)‖ₑ * ‖u ((h : G) • a)‖ₑ = _
      rw [hfinv, huinv])]
    exact hfin
  have e2 : ∑' q : G ⧸ H, ∫⁻ a, ‖f a * u a * (((η (q.out • a)).toReal : ℝ) : ℂ)‖ₑ ∂μ =
      ∫⁻ a, ‖f a‖ₑ * ‖u a‖ₑ * pouRestrict H η a ∂μ := by
    unfold pouRestrict
    simp_rw [enorm_mul, hη.enorm_toReal, ← ENNReal.tsum_mul_left]
    exact (lintegral_tsum fun q =>
      ((hf.enorm.mul hu.enorm).mul (hη.measurable.comp (hm _))).aemeasurable).symm
  have e1 : ∀ q : G ⧸ H, ∫⁻ a, ‖f (q.out⁻¹ • a) * u a * (((η a).toReal : ℝ) : ℂ)‖ₑ ∂μ =
      ∫⁻ a, ‖f a * u a * (((η (q.out • a)).toReal : ℝ) : ℂ)‖ₑ ∂μ := by
    intro q
    have hF : Measurable fun a => ‖f (q.out⁻¹ • a) * u a * (((η a).toReal : ℝ) : ℂ)‖ₑ :=
      (((hf.comp (hm _)).mul hu).mul hηc).enorm
    rw [← lintegral_comp_smul (μ := μ) q.out hF]
    refine lintegral_congr fun a => ?_
    simp [huinv]
  calc ∫ a, automC H f a * u a * (((η a).toReal : ℝ) : ℂ) ∂μ
      = ∫ a, ∑' q : G ⧸ H, f (q.out⁻¹ • a) * u a * (((η a).toReal : ℝ) : ℂ) ∂μ := by
        unfold automC
        simp_rw [← tsum_mul_right]
    _ = ∑' q : G ⧸ H, ∫ a, f (q.out⁻¹ • a) * u a * (((η a).toReal : ℝ) : ℂ) ∂μ :=
        integral_tsum (f := fun (q : G ⧸ H) a => f (q.out⁻¹ • a) * u a * (((η a).toReal : ℝ) : ℂ))
          (fun q => (((hf.comp (hm _)).mul hu).mul hηc).aestronglyMeasurable)
          (by simp_rw [e1]; rw [e2]; exact hfin')
    _ = ∑' q : G ⧸ H, ∫ a, f a * u a * (((η (q.out • a)).toReal : ℝ) : ℂ) ∂μ := by
        refine tsum_congr fun q => ?_
        rw [← integral_smul_eq_self (μ := μ)
          (fun a => f (q.out⁻¹ • a) * u a * (((η a).toReal : ℝ) : ℂ)) (g := q.out)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
        simp [huinv]
    _ = ∫ a, ∑' q : G ⧸ H, f a * u a * (((η (q.out • a)).toReal : ℝ) : ℂ) ∂μ :=
        (integral_tsum (f := fun (q : G ⧸ H) a => f a * u a * (((η (q.out • a)).toReal : ℝ) : ℂ))
          (fun q => ((hf.mul hu).mul (hηc.comp (hm _))).aestronglyMeasurable)
          (by rw [e2]; exact hfin')).symm
    _ = ∫ a, f a * u a * (((pouRestrict H η a).toReal : ℝ) : ℂ) ∂μ := by
        simp_rw [hη.pouRestrict_toReal H, tsum_mul_left]
    _ = ∫ a, f a * u a * (((ηH a).toReal : ℝ) : ℂ) ∂μ := by
        have hfu : Measurable fun a => f a * u a := hf.mul hu
        refine integral_mul_pou_eq (G := H) hR hηH hfu (fun h a => ?_) ?_
        · change f (h • a) * u ((h : G) • a) = _
          rw [hfinv, huinv]
        · simp_rw [enorm_mul]; exact hfin'

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.RC_Cusp
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-RC, file 1: reduction at a general cusp (stub R1 of WP-B1)

For an arbitrary `τ ∈ SL₂(F)` the group `τ SL₂(𝓞_F) τ⁻¹` contains the translations by `m𝓞_F` and
the diagonal matrices of the units `≡ 1 mod m`, where `m ∈ 𝓞_F ∖ 0` clears the denominators of the
products `τ_ij τ_kl`.  Hence (Dirichlet's unit theorem applied to `v^{1/k}`, `k = |(𝓞/m)^×|`) every
point of `X` has a translate under an upper triangular element of `τ SL₂(𝓞_F) τ⁻¹` with bounded `x`
and balanced `v`.

* `conjSub τ`: the subgroup `{γ' ∈ SL₂(𝓞) : τ⁻¹ γ' τ ∈ SL₂(𝓞)}`.
* `exists_reduced_conj`: the reduction statement.
* `reduction_cusp` (= **R1**), `reduction_cusp_siegelSet` (the same without an upper bound for the
  height; `siegelSet` is the unbounded Siegel set).
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.RC

open ArtinKP.X ArtinKP.B1

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- A matrix of `SL₂(F)` with integral entries is in the image of `SL₂(𝓞_F)`. -/
lemma exists_intSL_eq (M : SL(2, F)) (h : ∀ i j, ∃ a : 𝓞 F, algebraMap (𝓞 F) F a = M i j) :
    ∃ γ : SL(2, 𝓞 F), intSL F γ = M := by
  choose a ha using h
  have hdet : (Matrix.of a).det = 1 := by
    apply IsFractionRing.injective (𝓞 F) F
    rw [RingHom.map_det, map_one]
    have : (algebraMap (𝓞 F) F).mapMatrix (Matrix.of a) = (M : Matrix (Fin 2) (Fin 2) F) := by
      ext i j
      simp [ha]
    rw [this]
    exact M.2
  refine ⟨(⟨Matrix.of a, hdet⟩ : SL(2, 𝓞 F)), ?_⟩
  ext i j
  exact (intSL_apply _ i j).trans (ha i j)

lemma mem_conjSub {τ : SL(2, F)} {γ' : SL(2, 𝓞 F)} :
    γ' ∈ conjSub τ ↔ ∃ γ : SL(2, 𝓞 F), τ * intSL F γ = intSL F γ' * τ := by
  unfold conjSub
  simp only [Subgroup.mem_comap, MonoidHom.mem_range, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨γ, h⟩
    exact ⟨γ, by rw [h]; group⟩
  · rintro ⟨γ, h⟩
    exact ⟨γ, by rw [mul_assoc, ← h]; group⟩

lemma mem_conjSub_of_entries {τ : SL(2, F)} {γ' : SL(2, 𝓞 F)}
    (h : ∀ i j, ∃ a : 𝓞 F, algebraMap (𝓞 F) F a = (τ⁻¹ * intSL F γ' * τ) i j) :
    γ' ∈ conjSub τ := by
  obtain ⟨γ, hγ⟩ := exists_intSL_eq _ h
  exact mem_conjSub.mpr ⟨γ, by rw [hγ]; group⟩

/-- Entries of `τ⁻¹ g τ` for upper triangular `g`. -/
lemma conj_entries (τ g : SL(2, F)) (hg : g 1 0 = 0) :
    (τ⁻¹ * g * τ) 0 0 = τ 1 1 * (g 0 0 * τ 0 0 + g 0 1 * τ 1 0) - τ 0 1 * g 1 1 * τ 1 0 ∧
    (τ⁻¹ * g * τ) 0 1 = τ 1 1 * (g 0 0 * τ 0 1 + g 0 1 * τ 1 1) - τ 0 1 * g 1 1 * τ 1 1 ∧
    (τ⁻¹ * g * τ) 1 0 = -τ 1 0 * (g 0 0 * τ 0 0 + g 0 1 * τ 1 0) + τ 0 0 * g 1 1 * τ 1 0 ∧
    (τ⁻¹ * g * τ) 1 1 = -τ 1 0 * (g 0 0 * τ 0 1 + g 0 1 * τ 1 1) + τ 0 0 * g 1 1 * τ 1 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, hg]
    ring

lemma det_eq (τ : SL(2, F)) : τ 0 0 * τ 1 1 - τ 0 1 * τ 1 0 = 1 := by
  have := τ.2
  rwa [Matrix.det_fin_two] at this

/-- A common denominator of the products `τ_ij τ_kl`. -/
lemma exists_denominator (τ : SL(2, F)) : ∃ m : 𝓞 F, m ≠ 0 ∧ ∀ i j k l : Fin 2,
    ∃ a : 𝓞 F, algebraMap (𝓞 F) F a = algebraMap (𝓞 F) F m * (τ i j * τ k l) := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 F))
    ((Finset.univ : Finset ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))).image
      fun p => τ p.1.1 p.1.2 * τ p.2.1 p.2.2)
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, fun i j k l => ?_⟩
  obtain ⟨a, ha⟩ := hb _ (Finset.mem_image.mpr ⟨((i, j), (k, l)), Finset.mem_univ _, rfl⟩)
  exact ⟨a, by rw [ha, Algebra.smul_def]⟩

/-- Translations by multiples of the denominator are in `conjSub τ`. -/
lemma nInt_mem_conjSub {τ : SL(2, F)} {m : 𝓞 F}
    (hm : ∀ i j k l : Fin 2,
      ∃ a : 𝓞 F, algebraMap (𝓞 F) F a = algebraMap (𝓞 F) F m * (τ i j * τ k l)) (β : 𝓞 F) :
    nInt (m * β) ∈ conjSub τ := by
  have hdet := det_eq τ
  obtain ⟨xcd, hcd⟩ := hm 1 0 1 1
  obtain ⟨xdd, hdd⟩ := hm 1 1 1 1
  obtain ⟨xcc, hcc⟩ := hm 1 0 1 0
  obtain ⟨e00, e01, e10, e11⟩ := conj_entries τ (intSL F (nInt (m * β)))
    (by simp [intSL_apply, nInt_coe])
  have g00 : (intSL F (nInt (m * β))) 0 0 = 1 := by simp [intSL_apply, nInt_coe]
  have g01 : (intSL F (nInt (m * β))) 0 1 = algebraMap (𝓞 F) F m * algebraMap (𝓞 F) F β := by
    simp [intSL_apply, nInt_coe]
  have g11 : (intSL F (nInt (m * β))) 1 1 = 1 := by simp [intSL_apply, nInt_coe]
  refine mem_conjSub_of_entries fun i j => ?_
  fin_cases i <;> fin_cases j
  · refine ⟨1 + β * xcd, ?_⟩
    change _ = (τ⁻¹ * intSL F (nInt (m * β)) * τ) 0 0
    rw [e00, g00, g01, g11, map_add, map_mul, map_one, hcd]
    linear_combination -hdet
  · refine ⟨β * xdd, ?_⟩
    change _ = (τ⁻¹ * intSL F (nInt (m * β)) * τ) 0 1
    rw [e01, g00, g01, g11, map_mul, hdd]
    ring
  · refine ⟨-(β * xcc), ?_⟩
    change _ = (τ⁻¹ * intSL F (nInt (m * β)) * τ) 1 0
    rw [e10, g00, g01, g11, map_neg, map_mul, hcc]
    ring
  · refine ⟨1 - β * xcd, ?_⟩
    change _ = (τ⁻¹ * intSL F (nInt (m * β)) * τ) 1 1
    rw [e11, g00, g01, g11, map_sub, map_mul, map_one, hcd]
    linear_combination -hdet

end

end ArtinKP.RC
end

section
-- module Solutions.Artin.KP.X2_Prod
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
/-! # WP-X2, file 9: product coordinates `(x, v)` on `X` (stub S3 of WP-X)

`X.measurePreserving_xv`: the map `P ↦ (P.x, P.v) : X F → (ι → ℂ) × (ι → ℝ)` carries `X.vol F`
to `volume.prod (X.nuV F)`, `X.nuV F = ∏_w dv_w / v_w³` on `(0,∞)^ι`.  Hence integrals over `X`
and over strips `{x ∈ D}` are iterated integrals (`X.lintegral_xv`, `X.setLIntegral_strip`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

lemma amb_eq_prod : amb = (volume : Measure ℂ).prod nu1 := by
  have h2 : (volume : Measure ℂ).prod ((volume : Measure ℝ).restrict (Ioi 0)) =
      (volume : Measure (ℂ × ℝ)).restrict upper := by
    have hu : upper = (univ : Set ℂ) ×ˢ Ioi (0 : ℝ) := by
      ext p; simp [upper]
    rw [hu, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  unfold nu1
  rw [prod_withDensity_right (by fun_prop), h2]
  rfl

lemma measurePreserving_coe : MeasurePreserving H3.coe H3.vol ((volume : Measure ℂ).prod nu1) :=
  ⟨H3.measurableEmbedding_coe.measurable, map_val_vol.trans amb_eq_prod⟩

variable (F : Type*) [Field F] [NumberField F]

lemma X.nuV_eq : X.nuV F =
    (Measure.pi fun _ : InfinitePlace F => (volume : Measure ℝ).restrict (Ioi 0)).withDensity
      (fun v => ∏ w, ENNReal.ofReal ((v w ^ 3)⁻¹)) := by
  unfold X.nuV nu1
  exact pi_withDensity _ _ (fun _ => by fun_prop)

/-- **Product coordinates**: `P ↦ (x, v)` carries the invariant measure to
`dx ⊗ ∏_w dv_w / v_w³`. -/
theorem X.measurePreserving_xv :
    MeasurePreserving (fun P : X F => (P.x, P.v)) (X.vol F)
      ((volume : Measure (InfinitePlace F → ℂ)).prod (X.nuV F)) := by
  have h2 : MeasurePreserving (fun (P : X F) w => H3.coe (P w)) (X.vol F)
      (Measure.pi fun _ : InfinitePlace F => (volume : Measure ℂ).prod nu1) :=
    measurePreserving_pi (fun _ => H3.vol) (fun _ => (volume : Measure ℂ).prod nu1)
      (fun _ => measurePreserving_coe)
  have h3 := measurePreserving_arrowProdEquivProdArrow ℂ ℝ (InfinitePlace F)
    (fun _ => (volume : Measure ℂ)) (fun _ => nu1)
  exact h3.comp h2

variable {F}

lemma X.measurable_xv : Measurable fun P : X F => (P.x, P.v) :=
  (X.measurePreserving_xv F).measurable

/-- Integrals over `X` in product coordinates. -/
theorem X.lintegral_xv {f : (InfinitePlace F → ℂ) × (InfinitePlace F → ℝ) → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ P, f (P.x, P.v) ∂X.vol F = ∫⁻ x, ∫⁻ v, f (x, v) ∂X.nuV F := by
  rw [← lintegral_prod _ hf.aemeasurable]
  exact (X.measurePreserving_xv F).lintegral_comp hf

/-- Integrals over a strip `{x ∈ D}` are iterated integrals `∫_D dx ∫ ∏ dv/v³`. -/
theorem X.setLIntegral_strip {D : Set (InfinitePlace F → ℂ)} (hD : MeasurableSet D)
    {f : (InfinitePlace F → ℂ) × (InfinitePlace F → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ P in (X.x ⁻¹' D : Set (X F)), f (P.x, P.v) ∂X.vol F =
      ∫⁻ x in D, ∫⁻ v, f (x, v) ∂X.nuV F := by
  have hm : MeasurableSet (X.x ⁻¹' D : Set (X F)) :=
    (measurable_fst.comp X.measurable_xv) hD
  rw [← lintegral_indicator hm, ← lintegral_indicator hD]
  have h1 : ∀ P : X F, (X.x ⁻¹' D : Set (X F)).indicator (fun P => f (P.x, P.v)) P =
      (fun p : (InfinitePlace F → ℂ) × (InfinitePlace F → ℝ) =>
        D.indicator (fun _ => (1 : ℝ≥0∞)) p.1 * f p) (P.x, P.v) := by
    intro P
    by_cases h : P.x ∈ D
    · simp [h]
    · simp [h]
  simp_rw [h1]
  refine (X.lintegral_xv (f := fun p => D.indicator (fun _ => (1 : ℝ≥0∞)) p.1 * f p)
    (((measurable_const.indicator hD).comp measurable_fst).mul hf)).trans ?_
  refine lintegral_congr fun x => ?_
  by_cases h : x ∈ D
  · simp [h]
  · simp [h]

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.RF_Strip
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-RF, part 3: Fourier uniqueness on a strip of `X` (core of stub S1 (b))

Product coordinates `P ↦ (x, v) : X F → XV F = (ι → ℂ) × (ι → ℝ)` carry `X.vol` to Lebesgue
measure with density `dens v = ∏_w v_w⁻³` on `v > 0` (`map_xv`).  For a basis `bV` of `ι → ℂ`
(the lattice basis of the translations) and `n : ℕ`, the box
`{x ∈ cell bV} × [1/(n+1), n+1]^ι` lies in the cell of the basis `bE bV n = bV ⊕ (n+2)·e_w` of
`XV F`, whose characters are `chi bV m x · phiK n k v`.  Hence (`RF_Torus.ae_eq_zero_of_coeff`):

`measure_ne_zero_null`: a function on `X`, square integrable on that box, all of whose
coefficients against `chi bV m (x) · phiK n k (v)` over the box vanish, is `0` a.e. on the box.
No Fubini and no slicing: the `v`-directions are treated as further circle directions.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace ArtinKP.RF

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-! ### The density of `X.vol` in product coordinates -/

lemma measurableSet_posSet : MeasurableSet (posSet F) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioi

lemma measurable_dens : Measurable (dens : (InfinitePlace F → ℝ) → ℝ≥0∞) := by
  unfold dens
  refine Measurable.indicator ?_ measurableSet_posSet
  exact Finset.measurable_prod _ fun w _ => by fun_prop

lemma nuV_eq_withDensity : X.nuV F = (volume : Measure (InfinitePlace F → ℝ)).withDensity dens := by
  rw [X.nuV_eq]
  have h1 : (Measure.pi fun _ : InfinitePlace F => (volume : Measure ℝ).restrict (Ioi 0))
      = (volume : Measure (InfinitePlace F → ℝ)).restrict (posSet F) :=
    (Measure.restrict_pi_pi (fun _ : InfinitePlace F => (volume : Measure ℝ))
      (fun _ => Ioi (0 : ℝ))).symm
  rw [h1, ← withDensity_indicator measurableSet_posSet]
  rfl

/-! ### Boxes in `v` -/

lemma measurableSet_vBox (n : ℕ) : MeasurableSet (vBox F n) := by
  have : vBox F n = ⋂ w, {v : InfinitePlace F → ℝ | 1 / ((n : ℝ) + 1) ≤ v w} ∩
      {v | v w ≤ (n : ℝ) + 1} := by
    ext v; simp [vBox, forall_and]
  rw [this]
  exact MeasurableSet.iInter fun w =>
    (measurableSet_le measurable_const (measurable_pi_apply w)).inter
      (measurableSet_le (measurable_pi_apply w) measurable_const)

lemma vBox_subset_posSet (n : ℕ) : vBox F n ⊆ posSet F := fun v hv w _ =>
  lt_of_lt_of_le (by positivity) (hv w).1

lemma dens_ne_zero {n : ℕ} {v : InfinitePlace F → ℝ} (hv : v ∈ vBox F n) : dens v ≠ 0 := by
  unfold dens
  rw [indicator_of_mem (vBox_subset_posSet n hv)]
  refine Finset.prod_ne_zero_iff.mpr fun w _ => ?_
  have h0 : 0 < v w := vBox_subset_posSet n hv w (mem_univ w)
  exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'

/-! ### The basis of `XV F` adapted to a box -/

end

end ArtinKP.RF
end

section
-- module Solutions.Artin.KP.X_Cusp
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
/-! # WP-X, file 12: the translation subgroup of the cusp and unfolding to a strip

`GammaN Γ ≤ Γ` is the group of translations `[[1, β], [0, 1]]` in `Γ`; it acts on `X` by
`x ↦ x + β` (through the embeddings) and fixes `v`.  If `D ⊂ ℂ^r` is a strict fundamental set for
the translation lattice, `P ↦ 1_D(x(P))` is a partition of unity for `GammaN Γ`, and the
unfolding theorem reads
`∫_{Γ\X} (Σ_{γ ∈ N\Γ} f(γP)) u(P) = ∫_{x ∈ D} f u dμ` (`X.lintegral_unfold_N`).
Fourier analysis along `x` (frequencies in the dual lattice) takes place on the strip `{x ∈ D}`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- `GammaN Γ` acts by translations. -/
theorem GammaN.smul_eq {Γ : Subgroup (SL(2, 𝓞 F))} (γ : GammaN Γ) (P : X F) :
    γ • P = X.trans (GammaN.shift γ) P := by
  have h := smul_of_upper (γ := ((γ : Γ) : SL(2, 𝓞 F))) γ.2.1 P
  have h2 : (((γ : Γ) : SL(2, 𝓞 F)) 0 0 : 𝓞 F) = 1 := γ.2.2
  refine X.ext' (funext fun w => ?_) (funext fun w => ?_)
  · change (((γ : Γ) : SL(2, 𝓞 F)) • P).x w = P.x w + GammaN.shift γ w
    rw [(h w).1, h2]
    simp [GammaN.shift]
  · change (((γ : Γ) : SL(2, 𝓞 F)) • P).v w = P.v w
    rw [(h w).2, h2]
    simp

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.RF_Fourier
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-RF, part 4: Fourier series along `x` on `Γ\X` (stub S1 of WP-X)

Setting of WP-X "Remaining stubs": `F` totally complex, `Γ ≤ SL(2,𝓞_F)` containing the
translations `n(β)`, `β ∈ 𝔫`; `Λ = {GammaN.shift γ}` the translation lattice in `ι → ℂ`;

* `pair ν x = Σ_w Re(ν_w x_w)`, `eChar ν x = exp(2πi · pair ν x)`,
  `dualLat Γ = {ν | pair ν λ ∈ ℤ for all λ ∈ Λ}`;
* `stripFn D ν φ P = 1_D(P.x) · e_ν(P.x) · φ(P.v)`, the function `ψ` of
  `X.coeffFunctional Γ n ψ …` for the `(ν, φ)`-Fourier coefficient;
* `exists_latBasis`: a basis of `ι → ℂ` whose `ℤ`-span is `Λ`; the characters `chi bV m` of
  `RF_Torus` are the `eChar ν`, `ν ∈ dualLat Γ` (`exists_dual_of_chi`);
* **`eq_zero_of_coeff`** (S1 (b)): `u : X.L2 Γ` with all coefficient functionals zero is zero;
* `ae_eq_zero_of_strip`: the same for any measurable `GammaN Γ`-invariant function which is
  square integrable on boxes.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace ArtinKP.RF

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-! ### The pairing and the characters -/

/-! ### A basis of the translation lattice -/

lemma mem_box_iff (n : ℕ) (P : X F) :
    P ∈ (X.box n : Set (X F)) ↔ (∀ w, ‖P.x w‖ ≤ n) ∧ P.v ∈ vBox F n := by
  simp only [X.box, H3.box, vBox, mem_ofPred_eq, X.x, X.v]
  exact forall_and

end

end ArtinKP.RF
end

section
-- module Solutions.Artin.KP.N_Shape
attribute [-instance] _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
/-! # WP-N, file 2: the shape of the constant term of `E_Ψ` at `∞` for `Re s > 2` (MATH2 §2.1(b))

* `Cell Γ D n₀`: `D` is a measurable fundamental domain of the translation lattice of `Γ`, contained
  in `{‖x_w‖ ≤ n₀}`.  `Cell.of_hfund` converts from the form used by WP-X/WP-RF (`hfund`);
  `exists_cell` gives one for every `Γ` of finite index.
* `cf D n φ f = ∫_{box n} conj (1_D(x) φ(v)) f`: the constant-term functional (it is
  `X.coeffFunctional Γ n (RF.stripFn D 0 φ) …` on `L²(Γ\X)`, `coeffFunctional_eq_cf`).
* `mD D Ψ s = vol(D)⁻¹ ∫_D tail Ψ s (x, 1) dx`: the coefficient of `ht^{2−s}`.
* **`cf_eis`**: for `Re s > 2`, `n ≥ n₀`,
  `cf D n φ (E_Ψ(·,s)) = Ψ_s(0,1) · cf D n φ (ht^s) + mD D Ψ s · cf D n φ (ht^{2−s})`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {Γ : Subgroup (SL(2, 𝓞 F))}

/-! ### Cells -/

lemma Cell.vol_ne_zero {D : Set (InfinitePlace F → ℂ)} {n₀ : ℕ} (h : Cell Γ D n₀) :
    volume D ≠ 0 :=
  h.fund.measure_ne_zero (NeZero.ne _)

lemma Cell.mono {D : Set (InfinitePlace F → ℂ)} {n₀ n : ℕ} (h : Cell Γ D n₀) (hn : n₀ ≤ n) :
    Cell Γ D n :=
  ⟨h.meas, h.fund, fun x hx w => (h.bdd x hx w).trans (by exact_mod_cast hn)⟩

/-! ### The constant-term functional -/

lemma eChar_zero (x : InfinitePlace F → ℂ) : eChar 0 x = 1 := by
  simp [eChar, pair]

lemma stripFn_zero (D : Set (InfinitePlace F → ℂ)) (φ : (InfinitePlace F → ℝ) → ℂ) (P : X F) :
    stripFn D 0 φ P = D.indicator (fun _ => (1 : ℂ)) P.x * φ P.v := by
  rw [stripFn, eChar_zero, one_mul]

/-! ### Fubini: a function with vanishing `x`-integrals over `D` is killed by `cf` -/

/-! ### The shape -/

lemma isCompact_box (n : ℕ) : IsCompact (X.box n : Set (X F)) :=
  isCompact_siegelBox (F := F) (m := 1 / ((n : ℝ) + 1)) (M := (n : ℝ) + 1) (B := n)
    (by positivity)

lemma continuous_htC (s : ℂ) : Continuous (htC s : X F → ℂ) := by
  unfold htC
  refine (Complex.continuous_ofReal.comp X.continuous_ht).cpow continuous_const fun P => ?_
  exact Or.inl (by simpa using X.ht_pos P)

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.N_Res
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
/-! # WP-N, file 4: the continued coefficient `mext`, its residue `zRes`, the constant term of `θ_Ψ`

MATH2 §2.1(c),(d) and the first step of §2.2, for a cell `D` of `Γ` and a box index `n ≥ 1`:

* `phase s₁`, `cf_phase_ne_zero`: a test function `φ` with `cf D n φ (ht^{s₁}) ≠ 0`.
* `Acoef Γ Ψ D n φ s = cf(Eext) − Ψ_s(0,1)·cf(ht^s)` (written with `resPart` and `hInt`), holomorphic
  on `E.slit`; `Acoef_cross`: `A_φ(s)·⟨ht^{2−s},φ'⟩ = A_{φ'}(s)·⟨ht^{2−s},φ⟩` on `E.slit`.
* `mext Γ Ψ D n`: holomorphic on `E.slit` (`differentiableOn_mext`), equal to `mD D Ψ` for `Re s > 2`
  (`mext_eq_mD`), and `Acoef = mext · ⟨ht^{2−s}, φ⟩` on `E.slit` (`Acoef_eq_mext`) — the shape of the
  constant term of the continuation.
* `zRes Γ Ψ D n = lim (s_t − s₀)·mext(s_t)` (`tendsto_ray_mext`), and
  **`cf_theta`**: `cf D n' φ' (θ_Ψ) = zRes · cf D n' φ' (ht^{2/3})`.
* `zRes_eq_of_continuation`, `zRes_eq_zero_of_theta`, `cf_theta_eq_zero`.
* **`theta_eq_zero_of_inner`**: `⟪[F_{4/3}], θ_Ψ⟫ = 0 → θ_Ψ = 0` (`‖θ‖² = −c₀⟪F, θ⟫`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {Γ : Subgroup (SL(2, 𝓞 F))}

/-! ### A test function that sees `ht^{s₁}` -/

lemma measurable_phase (s₁ : ℂ) : Measurable (phase (F := F) s₁) := by
  unfold phase
  have h : Measurable fun v : InfinitePlace F → ℝ => ((∏ w, v w : ℝ) : ℂ) ^ s₁ :=
    (Complex.measurable_ofReal.comp
      (Finset.measurable_prod _ fun w _ => measurable_pi_apply w)).pow_const s₁
  exact h.div (Complex.measurable_ofReal.comp h.norm)

lemma norm_phase_le (s₁ : ℂ) (v : InfinitePlace F → ℝ) : ‖phase s₁ v‖ ≤ 1 := by
  unfold phase
  rw [norm_div, Complex.norm_real, norm_norm]
  exact div_self_le_one _

lemma norm_htC_pos (s₁ : ℂ) (P : X F) : 0 < ‖htC s₁ P‖ := by
  unfold htC
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (X.ht_pos P)]
  exact Real.rpow_pos_of_pos (X.ht_pos P) _

lemma conj_phase_mul (s₁ : ℂ) (P : X F) :
    conj (phase s₁ P.v) * htC s₁ P = ((‖htC s₁ P‖ : ℝ) : ℂ) := by
  have hu : ((∏ w, P.v w : ℝ) : ℂ) ^ s₁ = htC s₁ P := rfl
  unfold phase
  rw [hu, map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, Complex.conj_mul']
  have h0 : ((‖htC s₁ P‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_htC_pos s₁ P).ne'
  field_simp

lemma volume_vBox_ne_zero {n : ℕ} (hn : 1 ≤ n) :
    (volume : Measure (InfinitePlace F → ℝ)) (vBox F n) ≠ 0 := by
  have h : vBox F n = Icc (fun _ : InfinitePlace F => 1 / ((n : ℝ) + 1))
      (fun _ : InfinitePlace F => (n : ℝ) + 1) := by
    ext v
    simp only [vBox, mem_ofPred_eq, mem_Icc, Pi.le_def]
    exact forall_and
  rw [h, Real.volume_Icc_pi]
  refine Finset.prod_ne_zero_iff.mpr fun w _ => ?_
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : 1 / ((n : ℝ) + 1) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  exact (ENNReal.ofReal_pos.mpr (by linarith)).ne'

lemma nuV_vBox_ne_zero {n : ℕ} (hn : 1 ≤ n) : X.nuV F (vBox F n) ≠ 0 := by
  rw [RF.nuV_eq_withDensity, withDensity_apply _ (measurableSet_vBox n)]
  intro h
  rw [lintegral_eq_zero_iff RF.measurable_dens] at h
  have h1 : ∀ᵐ v ∂(volume : Measure (InfinitePlace F → ℝ)), v ∉ vBox F n := by
    have h2 := (ae_restrict_iff' (measurableSet_vBox n)).mp h
    filter_upwards [h2] with v hv hmem
    exact RF.dens_ne_zero hmem (hv hmem)
  exact volume_vBox_ne_zero hn (measure_eq_zero_iff_ae_notMem.mpr h1)

lemma vol_box_strip_ne_zero {D : Set (InfinitePlace F → ℂ)} {n : ℕ} (hD : Cell Γ D n)
    (hn : 1 ≤ n) : X.vol F ((X.box n : Set (X F)) ∩ X.x ⁻¹' D) ≠ 0 := by
  have hset : ((X.box n : Set (X F)) ∩ X.x ⁻¹' D) = X.v ⁻¹' vBox F n ∩ X.x ⁻¹' D := by
    ext P
    simp only [mem_inter_iff, mem_preimage, mem_box_iff]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hD.bdd _ h.2, h.1⟩, h.2⟩⟩
  have hVm : MeasurableSet (X.v ⁻¹' vBox F n : Set (X F)) := X.measurable_v (measurableSet_vBox n)
  have h1 := X.setLIntegral_strip (F := F) hD.meas
    (f := fun p => (vBox F n).indicator (fun _ => (1 : ℝ≥0∞)) p.2)
    ((measurable_const.indicator (measurableSet_vBox n)).comp measurable_snd)
  have h2 : ∫⁻ P in (X.x ⁻¹' D : Set (X F)), (vBox F n).indicator (fun _ => (1 : ℝ≥0∞)) P.v
      ∂X.vol F = X.vol F (X.v ⁻¹' vBox F n ∩ X.x ⁻¹' D) := by
    have e : (fun P : X F => (vBox F n).indicator (fun _ => (1 : ℝ≥0∞)) P.v)
        = (X.v ⁻¹' vBox F n : Set (X F)).indicator 1 := by
      funext P
      by_cases hP : P.v ∈ vBox F n
      · rw [indicator_of_mem hP, indicator_of_mem (show P ∈ X.v ⁻¹' vBox F n from hP)]; rfl
      · rw [indicator_of_notMem hP, indicator_of_notMem (show P ∉ X.v ⁻¹' vBox F n from hP)]
    rw [e, lintegral_indicator_one hVm, Measure.restrict_apply hVm]
  have h3 : ∀ x : InfinitePlace F → ℂ,
      ∫⁻ v, (fun p : (InfinitePlace F → ℂ) × (InfinitePlace F → ℝ) =>
        (vBox F n).indicator (fun _ => (1 : ℝ≥0∞)) p.2) (x, v) ∂X.nuV F
        = X.nuV F (vBox F n) := fun _ => by
    simp only
    rw [lintegral_indicator (measurableSet_vBox n), setLIntegral_const, one_mul]
  rw [hset, ← h2, h1, lintegral_congr h3, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
    univ_inter]
  exact mul_ne_zero (nuV_vBox_ne_zero hn) hD.vol_ne_zero

/-- The functional `cf D n (phase s₁)` does not vanish on `ht^{s₁}`. -/
theorem cf_phase_ne_zero {D : Set (InfinitePlace F → ℂ)} {n : ℕ} (hD : Cell Γ D n) (hn : 1 ≤ n)
    (s₁ : ℂ) : cf D n (phase s₁) (htC s₁) ≠ 0 := by
  have hSm : MeasurableSet (X.x ⁻¹' D : Set (X F)) := X.measurable_x hD.meas
  have e : ∀ P : X F, conj (stripFn D 0 (phase s₁) P) * htC s₁ P
      = (X.x ⁻¹' D : Set (X F)).indicator (fun P => ((‖htC s₁ P‖ : ℝ) : ℂ)) P := by
    intro P
    rw [stripFn_zero]
    by_cases hP : P.x ∈ D
    · rw [indicator_of_mem hP, indicator_of_mem (show P ∈ X.x ⁻¹' D from hP), one_mul,
        conj_phase_mul]
    · rw [indicator_of_notMem hP, indicator_of_notMem (show P ∉ X.x ⁻¹' D from hP)]
      simp
  unfold cf
  simp only [e]
  rw [setIntegral_indicator hSm, integral_complex_ofReal, Ne, Complex.ofReal_eq_zero]
  have hint : IntegrableOn (fun P : X F => ‖htC s₁ P‖) ((X.box n : Set (X F)) ∩ X.x ⁻¹' D)
      (X.vol F) :=
    ((continuous_htC s₁).norm.continuousOn.integrableOn_compact (isCompact_box n)).mono_set
      inter_subset_left
  have hpos : 0 < ∫ P in (X.box n : Set (X F)) ∩ X.x ⁻¹' D, ‖htC s₁ P‖ ∂X.vol F := by
    rw [integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall fun P => norm_nonneg _) hint]
    have hsupp : Function.support (fun P : X F => ‖htC s₁ P‖) = univ := by
      ext P
      simp only [Function.mem_support, mem_univ, iff_true]
      exact (norm_htC_pos s₁ P).ne'
    rw [hsupp, Measure.restrict_apply_univ]
    exact pos_iff_ne_zero.mpr (vol_box_strip_ne_zero hD hn)
  exact hpos.ne'

/-! ### The coefficient function `Acoef` and the cross identity -/

/-! ### `‖θ‖² = −c₀⟪F, θ⟫` -/

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.N2_Unfold
attribute [-instance] _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
/-! # WP-N2, file 2: the analysis at a cusp (step 4 of stub N-1)

Setting (`CuspSetup`): `τ ∈ SL₂(F)`, a subgroup `K ≤ Γ` such that `τ K τ⁻¹` is upper triangular
and preserves the height (the stabilizer of the cusp `τ⁻¹∞`), and a group `Γ₂` with a bounded
strict fundamental set `D₂` of its translations, all of whose translations `n(β)` are of the form
`τ k τ⁻¹`, `k ∈ K`.

**`integral_cusp_eq_zero`**: if `u` is `K`-invariant and all constant-term functionals
`cf D₂ n φ` kill `u ∘ τ⁻¹`, then `∫_{K\X} c(ht(τP)) u(P) = 0` for every bounded measurable profile
`c` (the integral over `K\X` taken with any partition of unity of `K`).

Proof: unfold from `K` to the translation subgroup `K₂ = K ∩ τ⁻¹ N(Γ₂) τ` (`transSub`), whose
partition of unity is the indicator of the strip `{x(τP) ∈ D₂}`.  In place of a partition of unity
for the unit part acting on `v` (WP-N's route) the test function is
`ψ_n(P) = 1[v(τP) ∈ vBox n] / B_n(v(τP))`, `B_n(v) = #{q ∈ K/K₂ : q⁻¹·v ∈ vBox n}`; then
`Σ_{K₂\K} ψ_n = 1[0 < B_n < ∞]`, `B_n` is finite by proper discontinuity and positive for large
`n`, and `ψ_n` is a function of `v(τP)` alone.  Dominated convergence in `n`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N2

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

/-! ### Pointwise unfolding -/

section abstract

variable {G α : Type*} [Group G] [Countable G] [MulAction G α]

/-- For a subgroup `H` with a strict fundamental set `S` and an `H`-invariant `f`:
`Σ_{g ∈ G} 1_S(g a) f(g a) = Σ_{q ∈ H\G} f(q a)`. -/
lemma tsum_indicator_mul_eq_autom (H : Subgroup G) {S : Set α} (hS : ∀ a, ∃! h : H, h • a ∈ S)
    {f : α → ℝ≥0∞} (hf : ∀ (h : H) (a : α), f (h • a) = f a) (a : α) :
    ∑' g : G, S.indicator (fun _ => (1 : ℝ≥0∞)) (g • a) * f (g • a) = autom H f a := by
  have hone : ∀ b : α, ∑' h : H, S.indicator (fun _ => (1 : ℝ≥0∞)) ((h : G)⁻¹ • b) = 1 := by
    intro b
    have e := (Equiv.inv H).tsum_eq (fun h : H => S.indicator (fun _ => (1 : ℝ≥0∞)) (h • b))
    have e' : ∑' h : H, S.indicator (fun _ => (1 : ℝ≥0∞)) ((h : G)⁻¹ • b)
        = ∑' h : H, S.indicator (fun _ => (1 : ℝ≥0∞)) (h • b) := e
    rw [e']
    obtain ⟨h₀, hh₀, huniq⟩ := hS b
    rw [tsum_eq_single h₀ (fun h hh => indicator_of_notMem (fun hm => hh (huniq h hm)) _),
      indicator_of_mem hh₀]
  rw [← (Equiv.inv G).tsum_eq, ← (quotProdEquiv H).tsum_eq, ENNReal.tsum_prod']
  unfold autom
  refine tsum_congr fun q => ?_
  have h1 : ∀ h : H, S.indicator (fun _ => (1 : ℝ≥0∞))
      ((Equiv.inv G) (quotProdEquiv H (q, h)) • a) * f ((Equiv.inv G) (quotProdEquiv H (q, h)) • a)
      = S.indicator (fun _ => (1 : ℝ≥0∞)) ((h : G)⁻¹ • (q.out⁻¹ • a)) * f (q.out⁻¹ • a) := by
    intro h
    have e : (Equiv.inv G) (quotProdEquiv H (q, h)) • a = (h : G)⁻¹ • (q.out⁻¹ • a) := by
      rw [quotProdEquiv_apply, Equiv.inv_apply, mul_inv_rev, mul_smul]
    rw [e]
    congr 1
    exact hf h⁻¹ (q.out⁻¹ • a)
  simp only [h1]
  rw [ENNReal.tsum_mul_right, hone, one_mul]

end abstract

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F]
  {Γ : Subgroup (SL(2, 𝓞 F))}

lemma intSL_injective : Function.Injective (intSL F) := by
  intro a b h
  ext i j
  have h1 : algebraMap (𝓞 F) F (a i j) = algebraMap (𝓞 F) F (b i j) := by
    rw [← intSL_apply, ← intSL_apply, h]
  exact h1

/-- The action of an upper triangular element of `SL₂(F)` on the heights. -/
lemma v_smul_upper {g : SL(2, F)} (hc : g 1 0 = 0) (Q : X F) :
    (g • Q).v = fun w => Complex.normSq (w.embedding (g 0 0)) * Q.v w := by
  funext w
  have hc' : (sigma F g w) 1 0 = 0 := by rw [sigma_apply, hc, map_zero]
  exact (smul_of_lower_zero hc' (Q w)).2

/-! ### The translation subgroup of a cusp stabilizer -/

variable {τ : SL(2, F)} {K : Subgroup Γ} {Γ₂ : Subgroup (SL(2, 𝓞 F))}
  {D₂ : Set (InfinitePlace F → ℂ)} {n₂ : ℕ}

lemma smul_conj (τ : SL(2, F)) (k : K) (P : X F) :
    τ • (k • P) = (τ * intSL F ((k : Γ) : SL(2, 𝓞 F)) * τ⁻¹) • (τ • P) := by
  rw [mul_smul, mul_smul, inv_smul_smul]
  rfl

lemma sc_smul (h : CuspSetup τ K Γ₂ D₂ n₂) (k : K) (P : X F) :
    (τ • (k • P)).v = fun w => sc τ k w * (τ • P).v w := by
  rw [smul_conj, v_smul_upper (h.upper k)]
  rfl

lemma trans_of_mem (k : K) (γ : GammaN Γ₂)
    (hk : τ * intSL F ((k : Γ) : SL(2, 𝓞 F)) = intSL F ((γ : Γ₂) : SL(2, 𝓞 F)) * τ) (P : X F) :
    τ • (k • P) = X.trans (GammaN.shift γ) (τ • P) := by
  have h1 : τ • (k • P) = (τ * intSL F ((k : Γ) : SL(2, 𝓞 F))) • P := by
    rw [mul_smul]; rfl
  have h2 : (intSL F ((γ : Γ₂) : SL(2, 𝓞 F)) * τ) • P = γ • (τ • P) := by
    rw [mul_smul]; rfl
  rw [h1, hk, h2]
  exact GammaN.smul_eq γ _

lemma measurableSet_stripS (τ : SL(2, F)) (hD : MeasurableSet D₂) :
    MeasurableSet (stripS τ D₂) :=
  (X.measurable_x.comp (measurable_const_smul τ)) hD

lemma measurableSet_Sv (τ : SL(2, F)) (n : ℕ) : MeasurableSet (Sv τ n) :=
  (X.measurable_v.comp (measurable_const_smul τ)) (measurableSet_vBox n)

lemma existsUnique_strip (h : CuspSetup τ K Γ₂ D₂ n₂) (P : X F) :
    ∃! k : transSub τ K Γ₂, k • P ∈ stripS τ D₂ := by
  obtain ⟨γ, hγ, huniq⟩ := h.fund (τ • P).x
  obtain ⟨k, hk⟩ := h.lift γ
  refine ⟨⟨k, γ, hk⟩, ?_, ?_⟩
  · change (τ • (k • P)).x ∈ D₂
    rw [trans_of_mem k γ hk]
    exact hγ
  · rintro ⟨k', γ', hk'⟩ hmem
    have h1 : (τ • (k' • P)).x ∈ D₂ := hmem
    rw [trans_of_mem k' γ' hk'] at h1
    have h2 : γ' = γ := huniq γ' h1
    subst h2
    have h3 : intSL F ((k' : Γ) : SL(2, 𝓞 F)) = intSL F ((k : Γ) : SL(2, 𝓞 F)) :=
      mul_left_cancel (hk'.trans hk.symm)
    exact Subtype.ext (Subtype.ext (Subtype.ext (intSL_injective h3)))

lemma v_transSub (k : transSub τ K Γ₂) (P : X F) : (τ • ((k : K) • P)).v = (τ • P).v := by
  obtain ⟨γ, hγ⟩ := k.2
  rw [trans_of_mem _ γ hγ]
  rfl

lemma Sv_inv (n : ℕ) (k : transSub τ K Γ₂) (P : X F) :
    (Sv τ n).indicator (fun _ => (1 : ℝ≥0∞)) (k • P)
      = (Sv τ n).indicator (fun _ => (1 : ℝ≥0∞)) P := by
  have e : (k • P ∈ Sv τ n) ↔ (P ∈ Sv τ n) := by
    change (τ • ((k : K) • P)).v ∈ vBox F n ↔ (τ • P).v ∈ vBox F n
    rw [v_transSub]
  by_cases hP : P ∈ Sv τ n
  · rw [indicator_of_mem hP, indicator_of_mem (e.mpr hP)]
  · rw [indicator_of_notMem hP, indicator_of_notMem (fun hc => hP (e.mp hc))]

/-! ### The multiplicity `B_n` -/

lemma measurable_Bn (τ : SL(2, F)) (K : Subgroup Γ) (Γ₂ : Subgroup (SL(2, 𝓞 F))) (n : ℕ) :
    Measurable (Bn τ K Γ₂ n) :=
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  haveI _iCQ := ArtinKP.X.instCountableQuot (transSub τ K Γ₂)
  Measurable.tsum fun _ => (measurable_const.indicator (measurableSet_vBox n)).comp
    (measurable_pi_lambda _ fun w => measurable_const.mul (measurable_pi_apply w))

lemma Bn_apply (h : CuspSetup τ K Γ₂ D₂ n₂) (n : ℕ) (P : X F) :
    Bn τ K Γ₂ n (τ • P).v = ∑' q : K ⧸ transSub τ K Γ₂,
      (Sv τ n).indicator (fun _ => (1 : ℝ≥0∞)) ((q.out)⁻¹ • P) := by
  unfold Bn
  refine tsum_congr fun q => ?_
  rw [← sc_smul h]
  rfl

lemma Bn_eq_tsum (h : CuspSetup τ K Γ₂ D₂ n₂) (n : ℕ) (P : X F) :
    Bn τ K Γ₂ n (τ • P).v = ∑' k : K,
      (stripS τ D₂ ∩ Sv τ n).indicator (fun _ => (1 : ℝ≥0∞)) (k • P) := by
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  rw [Bn_apply h]
  have h1 := tsum_indicator_mul_eq_autom (G := K) (transSub τ K Γ₂) (existsUnique_strip h)
    (f := (Sv τ n).indicator fun _ => (1 : ℝ≥0∞)) (Sv_inv n) P
  unfold autom at h1
  rw [← h1]
  refine tsum_congr fun k => ?_
  by_cases h2 : k • P ∈ stripS τ D₂
  · by_cases h3 : k • P ∈ Sv τ n
    · rw [indicator_of_mem h2, indicator_of_mem h3, indicator_of_mem (Set.mem_inter h2 h3),
        one_mul]
    · rw [indicator_of_notMem h3, indicator_of_notMem
        (fun hc : k • P ∈ stripS τ D₂ ∩ Sv τ n => h3 hc.2), mul_zero]
  · rw [indicator_of_notMem h2, indicator_of_notMem
      (fun hc : k • P ∈ stripS τ D₂ ∩ Sv τ n => h2 hc.1), zero_mul]

lemma vBox_mono {m n : ℕ} (hmn : m ≤ n) : vBox F m ⊆ vBox F n := by
  intro v hv w
  have hm : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  refine ⟨le_trans ?_ (hv w).1, (hv w).2.trans (by linarith)⟩
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

lemma Bn_lt_top (h : CuspSetup τ K Γ₂ D₂ n₂) (n : ℕ) (P : X F) :
    Bn τ K Γ₂ n (τ • P).v < ⊤ := by
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  classical
  rw [Bn_eq_tsum h]
  set m : ℕ := max n n₂ with hm
  set Kc : Set (X F) := (fun Q : X F => τ⁻¹ • Q) '' (X.box m : Set (X F)) with hKc
  have hKcc : IsCompact Kc := (isCompact_box (F := F) m).image (continuous_const_smul τ⁻¹)
  have hsub : stripS τ D₂ ∩ Sv τ n ⊆ Kc := by
    rintro Q ⟨hx, hv⟩
    refine ⟨τ • Q, (mem_box_iff m _).mpr ⟨fun w => ?_, vBox_mono (le_max_left _ _) hv⟩,
      inv_smul_smul τ Q⟩
    exact (h.bdd _ hx w).trans (by exact_mod_cast le_max_right n n₂)
  have hret := finite_return_of_isCompact hKcc
  have hinj : Function.Injective fun k : K => ((k : Γ) : SL(2, 𝓞 F)) :=
    fun a b hab => Subtype.ext (Subtype.ext hab)
  set R : Finset K := (hret.preimage hinj.injOn).toFinset with hR
  refine lt_of_le_of_lt (tsum_indicator_le_card (G := K) R (fun g hg => ?_) P)
    (ENNReal.natCast_lt_top _)
  obtain ⟨a, ha, hga⟩ := hg
  rw [hR, Set.Finite.mem_toFinset]
  exact ⟨a, hsub ha, hsub hga⟩

lemma Bn_inv (h : CuspSetup τ K Γ₂ D₂ n₂) (n : ℕ) (k : K) (P : X F) :
    Bn τ K Γ₂ n (τ • (k • P)).v = Bn τ K Γ₂ n (τ • P).v := by
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  rw [Bn_eq_tsum h, Bn_eq_tsum h]
  exact tsum_smul_comp_smul (G := K)
    ((stripS τ D₂ ∩ Sv τ n).indicator fun _ => (1 : ℝ≥0∞)) k P

lemma one_le_Bn (h : CuspSetup τ K Γ₂ D₂ n₂) {n : ℕ} {P : X F} (hP : P ∈ Sv τ n) :
    1 ≤ Bn τ K Γ₂ n (τ • P).v := by
  rw [Bn_eq_tsum h]
  obtain ⟨k, hk, -⟩ := existsUnique_strip h P
  have hmem : (k : K) • P ∈ stripS τ D₂ ∩ Sv τ n := by
    refine ⟨hk, ?_⟩
    change (τ • ((k : K) • P)).v ∈ vBox F n
    rw [v_transSub]
    exact hP
  calc (1 : ℝ≥0∞) = (stripS τ D₂ ∩ Sv τ n).indicator (fun _ => (1 : ℝ≥0∞)) ((k : K) • P) := by
        rw [indicator_of_mem hmem]
    _ ≤ _ := ENNReal.le_tsum (k : K)

/-! ### The test functions -/

lemma measurable_Bn_comp (τ : SL(2, F)) (K : Subgroup Γ) (Γ₂ : Subgroup (SL(2, 𝓞 F))) (n : ℕ) :
    Measurable fun P : X F => Bn τ K Γ₂ n (τ • P).v :=
  (measurable_Bn τ K Γ₂ n).comp (X.measurable_v.comp (measurable_const_smul τ))

lemma measurable_psiN (τ : SL(2, F)) (K : Subgroup Γ) (Γ₂ : Subgroup (SL(2, 𝓞 F))) (n : ℕ) :
    Measurable (psiN τ K Γ₂ n) :=
  (measurable_const.indicator (measurableSet_Sv τ n)).mul
    (Complex.measurable_ofReal.comp (measurable_Bn_comp τ K Γ₂ n).inv.ennreal_toReal)

lemma measurable_chiN (τ : SL(2, F)) (K : Subgroup Γ) (Γ₂ : Subgroup (SL(2, 𝓞 F))) (n : ℕ) :
    Measurable (chiN τ K Γ₂ n) :=
  Complex.measurable_ofReal.comp ((measurable_Bn_comp τ K Γ₂ n).ennreal_toReal.mul
    (measurable_Bn_comp τ K Γ₂ n).inv.ennreal_toReal)

lemma indicator_toReal (s : Set (X F)) (P : X F) :
    s.indicator (fun _ => (1 : ℂ)) P
      = (((s.indicator (fun _ => (1 : ℝ≥0∞)) P).toReal : ℝ) : ℂ) := by
  by_cases hP : P ∈ s
  · simp [hP]
  · simp [hP]

lemma psiN_inv (n : ℕ) (k : transSub τ K Γ₂) (P : X F) :
    psiN τ K Γ₂ n (k • P) = psiN τ K Γ₂ n P := by
  unfold psiN
  have e1 : (τ • (k • P)).v = (τ • P).v := v_transSub k P
  rw [e1, indicator_toReal, indicator_toReal, Sv_inv]

/-- `Σ_{K₂\K} ψ_n = χ_n`. -/
lemma automC_psiN (h : CuspSetup τ K Γ₂ D₂ n₂) (n : ℕ) (P : X F) :
    automC (transSub τ K Γ₂) (psiN τ K Γ₂ n) P = chiN τ K Γ₂ n P := by
  unfold automC psiN chiN
  simp only [Bn_inv h, indicator_toReal]
  rw [tsum_mul_right, ← Complex.ofReal_tsum,
    ← ENNReal.tsum_toReal_eq (fun q => by
      by_cases hq : (q.out)⁻¹ • P ∈ Sv τ n
      · simp [hq]
      · simp [hq]), ← Bn_apply h]
  push_cast
  ring

lemma norm_chiN_le (τ : SL(2, F)) (K : Subgroup Γ) (Γ₂ : Subgroup (SL(2, 𝓞 F))) (n : ℕ)
    (P : X F) : ‖chiN τ K Γ₂ n P‖ ≤ 1 := by
  unfold chiN
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by
    rw [ENNReal.ofReal_one]; exact ENNReal.mul_inv_le_one _)

lemma chiN_eq_one (h : CuspSetup τ K Γ₂ D₂ n₂) {n : ℕ} {P : X F} (hP : P ∈ Sv τ n) :
    chiN τ K Γ₂ n P = 1 := by
  unfold chiN
  have h0 : Bn τ K Γ₂ n (τ • P).v ≠ 0 := fun hc => by
    have := one_le_Bn h hP
    rw [hc] at this
    exact absurd this (by norm_num)
  have ht : Bn τ K Γ₂ n (τ • P).v ≠ ⊤ := (Bn_lt_top h n P).ne
  rw [← ENNReal.toReal_mul, ENNReal.mul_inv_cancel h0 ht]
  simp

/-- `Σ_{K₂\K} |ψ_n| ≤ 1`. -/
lemma autom_enorm_psiN_le (h : CuspSetup τ K Γ₂ D₂ n₂) (n : ℕ) (P : X F) :
    autom (transSub τ K Γ₂) (fun P => ‖psiN τ K Γ₂ n P‖ₑ) P ≤ 1 := by
  unfold autom
  have h1 : ∀ q : K ⧸ transSub τ K Γ₂, ‖psiN τ K Γ₂ n ((q.out)⁻¹ • P)‖ₑ
      ≤ (Sv τ n).indicator (fun _ => (1 : ℝ≥0∞)) ((q.out)⁻¹ • P)
        * (Bn τ K Γ₂ n (τ • P).v)⁻¹ := by
    intro q
    unfold psiN
    rw [Bn_inv h, enorm_mul]
    refine mul_le_mul' (le_of_eq ?_) ?_
    · by_cases hq : (q.out)⁻¹ • P ∈ Sv τ n
      · simp [hq]
      · simp [hq]
    · rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.ofReal_toReal_le
  refine (ENNReal.tsum_le_tsum h1).trans ?_
  rw [ENNReal.tsum_mul_right, ← Bn_apply h]
  exact ENNReal.mul_inv_le_one _

/-! ### The main statement at a cusp -/

/-- The unfolded integral against `ψ_n` is a constant-term functional. -/
lemma integral_psiN_strip (h : CuspSetup τ K Γ₂ D₂ n₂) {c : ℝ → ℂ} (hc : Measurable c)
    (hc1 : ∀ t, ‖c t‖ ≤ 1) (u : X F → ℂ) {n : ℕ} (hn : n₂ ≤ n) :
    ∃ φ : (InfinitePlace F → ℝ) → ℂ, Measurable φ ∧ (∀ v, ‖φ v‖ ≤ 1) ∧
      ∫ P, psiN τ K Γ₂ n P * (c (X.ht (τ • P)) * u P)
          * ((((stripS τ D₂).indicator (fun _ => (1 : ℝ≥0∞)) P).toReal : ℝ) : ℂ) ∂X.vol F
        = cf D₂ n φ (fun Q => u (τ⁻¹ • Q)) := by
  set φ : (InfinitePlace F → ℝ) → ℂ := fun v =>
    conj ((vBox F n).indicator (fun _ => (1 : ℂ)) v
      * ((((Bn τ K Γ₂ n v)⁻¹).toReal : ℝ) : ℂ) * c (∏ w, v w)) with hφ
  have hφm : Measurable φ := by
    refine Complex.continuous_conj.measurable.comp ?_
    exact ((measurable_const.indicator (measurableSet_vBox n)).mul
      (Complex.measurable_ofReal.comp (measurable_Bn τ K Γ₂ n).inv.ennreal_toReal)).mul
      (hc.comp (Finset.measurable_prod _ fun w _ => measurable_pi_apply w))
  have hB1 : ∀ v ∈ vBox F n, ((Bn τ K Γ₂ n v)⁻¹).toReal ≤ 1 := by
    intro v hv
    have hpos : ∀ w, 0 < v w := fun w => vBox_subset_posSet n hv w (mem_univ w)
    have hQ : τ • (τ⁻¹ • X.mk 0 v hpos) = X.mk 0 v hpos := smul_inv_smul τ _
    have hmem : τ⁻¹ • X.mk 0 v hpos ∈ Sv τ n := by
      change (τ • (τ⁻¹ • X.mk 0 v hpos)).v ∈ vBox F n
      rw [hQ]; exact hv
    have h1 := one_le_Bn h hmem
    rw [hQ] at h1
    change 1 ≤ Bn τ K Γ₂ n v at h1
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by
      rw [ENNReal.ofReal_one]; exact ENNReal.inv_le_one.mpr h1)
  have hφ1 : ∀ v, ‖φ v‖ ≤ 1 := by
    intro v
    rw [hφ]
    simp only [RCLike.norm_conj, norm_mul]
    by_cases hv : v ∈ vBox F n
    · rw [indicator_of_mem hv, norm_one, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ENNReal.toReal_nonneg]
      exact mul_le_one₀ (hB1 v hv) (norm_nonneg _) (hc1 _)
    · rw [indicator_of_notMem hv, norm_zero, zero_mul, zero_mul]; exact zero_le_one
  refine ⟨φ, hφm, hφ1, ?_⟩
  set Hn : X F → ℂ := fun Q => conj (stripFn D₂ 0 φ Q) * u (τ⁻¹ • Q) with hHn
  have key : ∀ P : X F, psiN τ K Γ₂ n P * (c (X.ht (τ • P)) * u P)
      * ((((stripS τ D₂).indicator (fun _ => (1 : ℝ≥0∞)) P).toReal : ℝ) : ℂ) = Hn (τ • P) := by
    intro P
    have e1 : (stripS τ D₂).indicator (fun _ => (1 : ℝ≥0∞)) P
        = D₂.indicator (fun _ => (1 : ℝ≥0∞)) (τ • P).x := rfl
    have e2 : (Sv τ n).indicator (fun _ => (1 : ℂ)) P
        = (vBox F n).indicator (fun _ => (1 : ℂ)) (τ • P).v := rfl
    have e3 : ∏ w, (τ • P).v w = X.ht (τ • P) := rfl
    simp only [hHn, stripFn_zero, hφ, psiN, inv_smul_smul]
    rw [e1, e2, e3]
    by_cases hx : (τ • P).x ∈ D₂
    · rw [indicator_of_mem hx, indicator_of_mem hx]
      simp only [map_mul, one_mul, ENNReal.toReal_one, Complex.ofReal_one, mul_one,
        Complex.conj_conj]
      ring
    · rw [indicator_of_notMem hx, indicator_of_notMem hx]
      simp
  rw [integral_congr_ae (Eventually.of_forall key)]
  refine ((measurePreserving_smul τ).integral_comp (MeasurableEquiv.smul τ).measurableEmbedding
    Hn).trans ?_
  unfold cf
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun Q hQ => ?_).symm
  have hz : stripFn D₂ 0 φ Q = 0 := by
    rw [stripFn_zero]
    by_cases hx : Q.x ∈ D₂
    · have hv : Q.v ∉ vBox F n := fun hv => hQ ((mem_box_iff n Q).mpr
        ⟨fun w => (h.bdd _ hx w).trans (by exact_mod_cast hn), hv⟩)
      rw [hφ]
      simp only [indicator_of_notMem hv, zero_mul, map_zero, mul_zero]
    · rw [indicator_of_notMem hx, zero_mul]
  rw [hHn]
  simp only [hz, map_zero, zero_mul]

/-- **Vanishing of the unfolded integral at a cusp.** -/
theorem integral_cusp_eq_zero (h : CuspSetup τ K Γ₂ D₂ n₂) {c : ℝ → ℂ} (hc : Measurable c)
    (hc1 : ∀ t, ‖c t‖ ≤ 1) {u : X F → ℂ} (hu : Measurable u)
    (huinv : ∀ (k : K) (P : X F), u (k • P) = u P) {ηK : X F → ℝ≥0∞} (hηK : IsPOU K ηK)
    (hfin : ∫⁻ P, ‖c (X.ht (τ • P))‖ₑ * ‖u P‖ₑ * ηK P ∂X.vol F ≠ ⊤)
    (hcf : ∀ n : ℕ, n₂ ≤ n → ∀ φ : (InfinitePlace F → ℝ) → ℂ, Measurable φ →
      (∀ v, ‖φ v‖ ≤ 1) → cf D₂ n φ (fun Q => u (τ⁻¹ • Q)) = 0) :
    ∫ P, c (X.ht (τ • P)) * u P * (((ηK P).toReal : ℝ) : ℂ) ∂X.vol F = 0 := by
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  set U : X F → ℂ := fun P => c (X.ht (τ • P)) * u P with hU
  have hUm : Measurable U :=
    (hc.comp (X.continuous_ht.measurable.comp (measurable_const_smul τ))).mul hu
  have hUinv : ∀ (k : K) (P : X F), U (k • P) = U P := fun k P => by
    simp only [hU]; rw [h.ht_inv, huinv]
  have hSm := measurableSet_stripS τ h.meas
  have hSpou : IsPOU (transSub τ K Γ₂) ((stripS τ D₂).indicator fun _ => (1 : ℝ≥0∞)) :=
    isPOU_indicator_of_existsUnique hSm (existsUnique_strip h)
  have hfinU : ∫⁻ P, ‖U P‖ₑ * ηK P ∂X.vol F ≠ ⊤ := by
    simp only [hU, enorm_mul]; exact hfin
  -- each truncated integral vanishes
  have hzero : ∀ n : ℕ, n₂ ≤ n →
      ∫ P, chiN τ K Γ₂ n P * U P * (((ηK P).toReal : ℝ) : ℂ) ∂X.vol F = 0 := by
    intro n hn
    have hfin_n : ∫⁻ P, ‖psiN τ K Γ₂ n P‖ₑ * ‖U P‖ₑ
        * (stripS τ D₂).indicator (fun _ => (1 : ℝ≥0∞)) P ∂X.vol F ≠ ⊤ := by
      rw [← lintegral_autom_mul_eq (G := K) (μ := X.vol F) (transSub τ K Γ₂) hηK hSpou
        (f := fun P => ‖psiN τ K Γ₂ n P‖ₑ) (u := fun P => ‖U P‖ₑ)
        (measurable_psiN τ K Γ₂ n).enorm hUm.enorm
        (fun k P => by rw [psiN_inv]) (fun k P => by rw [hUinv])]
      refine ne_top_of_le_ne_top hfinU (lintegral_mono fun P => ?_)
      calc autom (transSub τ K Γ₂) (fun P => ‖psiN τ K Γ₂ n P‖ₑ) P * ‖U P‖ₑ * ηK P
          ≤ 1 * ‖U P‖ₑ * ηK P := by
            gcongr
            exact autom_enorm_psiN_le h n P
        _ = ‖U P‖ₑ * ηK P := by rw [one_mul]
    have h1 := integral_automC_mul_eq (G := K) (μ := X.vol F) (transSub τ K Γ₂) hηK hSpou
      (f := psiN τ K Γ₂ n) (u := U) (measurable_psiN τ K Γ₂ n) hUm
      (fun k P => psiN_inv n k P) hUinv hfin_n
    simp only [automC_psiN h] at h1
    rw [h1]
    obtain ⟨φ, hφm, hφ1, hφ⟩ := integral_psiN_strip h hc hc1 u hn
    have h2 : ∀ P : X F, psiN τ K Γ₂ n P * U P
        * ((((stripS τ D₂).indicator (fun _ => (1 : ℝ≥0∞)) P).toReal : ℝ) : ℂ)
        = psiN τ K Γ₂ n P * (c (X.ht (τ • P)) * u P)
          * ((((stripS τ D₂).indicator (fun _ => (1 : ℝ≥0∞)) P).toReal : ℝ) : ℂ) := fun _ => rfl
    rw [integral_congr_ae (Eventually.of_forall h2), hφ]
    exact hcf n hn φ hφm hφ1
  -- dominated convergence
  have hint : Integrable (fun P => U P * (((ηK P).toReal : ℝ) : ℂ)) (X.vol F) := by
    refine ⟨(hUm.mul hηK.measurable_toReal).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    simp only [enorm_mul, hηK.enorm_toReal]
    exact lt_of_le_of_ne le_top hfinU
  have hlim := tendsto_integral_of_dominated_convergence
    (F := fun (n : ℕ) (P : X F) => chiN τ K Γ₂ n P * U P * (((ηK P).toReal : ℝ) : ℂ))
    (f := fun P => U P * (((ηK P).toReal : ℝ) : ℂ))
    (fun P => ‖U P * (((ηK P).toReal : ℝ) : ℂ)‖)
    (fun n => (((measurable_chiN τ K Γ₂ n).mul hUm).mul
      hηK.measurable_toReal).aestronglyMeasurable)
    hint.norm
    (fun n => Eventually.of_forall fun P => by
      rw [mul_assoc, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (norm_chiN_le τ K Γ₂ n P))
    (Eventually.of_forall fun P => by
      obtain ⟨m, hm⟩ := X.exists_mem_box (τ • P)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop m] with n hn
      have hP : P ∈ Sv τ n := vBox_mono hn ((mem_box_iff m _).mp hm).2
      rw [chiN_eq_one h hP, one_mul])
  have hev : (fun n : ℕ => ∫ P, chiN τ K Γ₂ n P * U P * (((ηK P).toReal : ℝ) : ℂ) ∂X.vol F)
      =ᶠ[atTop] fun _ => (0 : ℂ) := by
    filter_upwards [eventually_ge_atTop n₂] with n hn
    exact hzero n hn
  exact tendsto_nhds_unique (hlim.congr' hev) tendsto_const_nhds

end

end ArtinKP.N2
end

section
-- module Solutions.Artin.KP.N2_Cusp
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
/-! # WP-N2, file 3: the cusp `σ⁻¹∞` of a finite-index `Γ` (step 3 of stub N-1)

For `σ ∈ SL₂(R)`, `p₀ = rowClass (Row.bot σ)` (the class with `ht_{p₀}(P) = ht(σP)/‖p₀‖`) and
`K = stab Γ p₀`:

* `exists_ideal_conj`: `σ Γ σ⁻¹` contains the translations by a nonzero ideal of `𝓞_F`.
* `cuspSetup`: the `CuspSetup` of file 2 for `τ = σ`, `K`, the group
  `Γ₂ = Γ' ⊓ Γ(𝔫)` and a strict cell of it (`Γ'` any group, `𝔫` from `exists_ideal_conj`).
* **`cusp_integral_eq_zero`**: if the constant term of `θ_Γ(Ψ)` vanishes at the cusp `σ⁻¹∞`
  (`N.CuspVanish`), then `∫_{K\X} c(ht(σP)) θ(P) = 0` for every bounded measurable `c`.
  The passage from the cell of `CuspVanish` to the cell of `Γ₂` is `zRes_congr`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N2

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ}

/-- **`τ Γ τ⁻¹` contains the translations by a nonzero ideal.** -/
theorem exists_ideal_conj (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex] (τ : SL(2, F)) :
    ∃ 𝔫 : Ideal (𝓞 F), 𝔫 ≠ ⊥ ∧
      ∀ β ∈ 𝔫, ∃ δ ∈ Γ, τ * intSL F δ = intSL F (nInt β) * τ := by
  obtain ⟨m, hm0, hm⟩ := RC.exists_denominator τ
  set k : ℕ := (Γ.index).factorial with hk
  have hk0 : ((k : ℕ) : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  refine ⟨Ideal.span {((k : ℕ) : 𝓞 F) * m}, by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact mul_ne_zero hk0 hm0, fun β hβ => ?_⟩
  obtain ⟨β', rfl⟩ := Ideal.mem_span_singleton'.mp hβ
  obtain ⟨γ, hγ⟩ := RC.mem_conjSub.mp (RC.nInt_mem_conjSub hm β')
  refine ⟨γ ^ k, RC.pow_factorial_index_mem Γ γ, ?_⟩
  have h1 : SemiconjBy τ (intSL F γ) (intSL F (nInt (m * β'))) := hγ
  have h2 := h1.pow_right k
  rw [← map_pow, ← map_pow, RC.nInt_pow] at h2
  have e : β' * (((k : ℕ) : 𝓞 F) * m) = ((k : ℕ) : 𝓞 F) * (m * β') := by ring
  rw [e]
  exact h2

/-! ### The class of a bottom row -/

lemma ht_rowClass_bot (h𝔪 : 𝔪 ≠ ⊥) (σ : SL(2, SInt 𝔪)) (P : X F) :
    (RO.rowClass h𝔪 (Row.bot σ)).ht P = X.ht (toF 𝔪 σ • P) / (Row.bot σ).norm := by
  rw [RO.ht_rowClass, X.ht_smul]
  rfl

/-- An element of the stabilizer multiplies the bottom row of `σ` by an `S`-unit. -/
lemma stab_row (h𝔪 : 𝔪 ≠ ⊥) (σ : SL(2, SInt 𝔪)) {γ : SL(2, 𝓞 F)}
    (hγ : (RO.rowClass h𝔪 (Row.bot σ)).act γ = RO.rowClass h𝔪 (Row.bot σ)) :
    ∃ ε : (SInt 𝔪)ˣ, ∀ j : Fin 2,
      (toF 𝔪 σ * intSL F γ) 1 j = ((ε : SInt 𝔪) : F) * (toF 𝔪 σ) 1 j := by
  rw [← RO.rowClass_act_intMat, eq_comm, RO.rowClass_eq_iff, ← Row.bot_mul] at hγ
  obtain ⟨ε, hε⟩ := hγ
  refine ⟨ε, fun j => ?_⟩
  have hmul : toF 𝔪 σ * intSL F γ = toF 𝔪 (σ * RO.intMat 𝔪 γ) := by
    rw [map_mul, RO.toF_intMat]
  rw [hmul]
  fin_cases j
  · have := congrArg Row.c hε
    rw [Row.bot_c, Row.smul_c, Row.bot_c] at this
    change (((σ * RO.intMat 𝔪 γ).1 1 0 : SInt 𝔪) : F) = ((ε : SInt 𝔪) : F) * ((σ.1 1 0 : SInt 𝔪) : F)
    rw [this]
    rfl
  · have := congrArg Row.d hε
    rw [Row.bot_d, Row.smul_d, Row.bot_d] at this
    change (((σ * RO.intMat 𝔪 γ).1 1 1 : SInt 𝔪) : F) = ((ε : SInt 𝔪) : F) * ((σ.1 1 1 : SInt 𝔪) : F)
    rw [this]
    rfl

lemma mul_inv_one_zero (A τ : SL(2, F)) : (A * τ⁻¹) 1 0 = A 1 0 * τ 1 1 - A 1 1 * τ 1 0 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- An element of `Γ` conjugate under `σ` to a translation fixes the class of `Row.bot σ`. -/
lemma act_eq_of_conj (h𝔪 : 𝔪 ≠ ⊥) (σ : SL(2, SInt 𝔪)) {δ γ : SL(2, 𝓞 F)} (h10 : γ 1 0 = 0)
    (h11 : γ 1 1 = 1) (hδ : toF 𝔪 σ * intSL F δ = intSL F γ * toF 𝔪 σ) :
    (RO.rowClass h𝔪 (Row.bot σ)).act δ = RO.rowClass h𝔪 (Row.bot σ) := by
  have hrow : ∀ j : Fin 2, (toF 𝔪 (σ * RO.intMat 𝔪 δ)) 1 j = (toF 𝔪 σ) 1 j := by
    intro j
    rw [map_mul, RO.toF_intMat, hδ]
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, intSL_apply,
      h10, h11]
  have hbot : (Row.bot σ).act (RO.intMat 𝔪 δ) = Row.bot σ := by
    rw [← Row.bot_mul]
    refine Row.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact hrow 0
    · exact hrow 1
  rw [← RO.rowClass_act_intMat, hbot]

/-- The `CuspSetup` at the cusp `σ⁻¹∞` of `Γ`, for the group `Γ' ⊓ Γ(𝔫)`. -/
theorem cuspSetup (h𝔪 : 𝔪 ≠ ⊥) (Γ : Subgroup (SL(2, 𝓞 F))) (σ : SL(2, SInt 𝔪))
    (Γ' : Subgroup (SL(2, 𝓞 F))) {𝔫 : Ideal (𝓞 F)}
    (hconj : ∀ β ∈ 𝔫, ∃ δ ∈ Γ, toF 𝔪 σ * intSL F δ = intSL F (nInt β) * toF 𝔪 σ)
    {D₂ : Set (InfinitePlace F → ℂ)} {n₂ : ℕ} (hD₂ : MeasurableSet D₂)
    (hfund : ∀ x : InfinitePlace F → ℂ, ∃! γ : GammaN (Γ' ⊓ RO.princCong 𝔫),
      (fun w => x w + GammaN.shift γ w) ∈ D₂)
    (hbdd : ∀ x ∈ D₂, ∀ w, ‖x w‖ ≤ n₂) :
    CuspSetup (toF 𝔪 σ) (stab Γ (RO.rowClass h𝔪 (Row.bot σ))) (Γ' ⊓ RO.princCong 𝔫) D₂ n₂ where
  upper := fun k => by
    obtain ⟨ε, hε⟩ := stab_row h𝔪 σ k.2
    rw [mul_inv_one_zero, hε 0, hε 1]
    ring
  ht_inv := fun k P => by
    have h1 := PairClass.ht_act (RO.rowClass h𝔪 (Row.bot σ)) ((k : Γ) : SL(2, 𝓞 F)) P
    rw [k.2, ht_rowClass_bot, ht_rowClass_bot] at h1
    exact ((div_left_inj' (Row.norm_pos _).ne').mp h1).symm
  meas := hD₂
  fund := hfund
  bdd := hbdd
  lift := fun γ => by
    set g : SL(2, 𝓞 F) := (((γ : (Γ' ⊓ RO.princCong 𝔫 : Subgroup (SL(2, 𝓞 F)))) :
      SL(2, 𝓞 F))) with hg
    have hmem : g ∈ RO.princCong 𝔫 := (γ : (Γ' ⊓ RO.princCong 𝔫 : Subgroup (SL(2, 𝓞 F)))).2.2
    have hker : Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk 𝔫) g = 1 :=
      MonoidHom.mem_ker.mp hmem
    have h01 : Ideal.Quotient.mk 𝔫 (g 0 1) = 0 := by
      have := congrArg (fun M : SL(2, 𝓞 F ⧸ 𝔫) => M 0 1) hker
      simpa using this
    have hβ : g 0 1 ∈ 𝔫 := Ideal.Quotient.eq_zero_iff_mem.mp h01
    obtain ⟨δ, hδΓ, hδ⟩ := hconj _ hβ
    have hgeq : nInt (g 0 1) = g := nInt_eq_of_GammaN γ
    rw [hgeq] at hδ
    have h10 : g 1 0 = 0 := γ.2.1
    have h11 : g 1 1 = 1 := GammaN.coe_one_one γ
    exact ⟨⟨⟨δ, hδΓ⟩, act_eq_of_conj h𝔪 σ h10 h11 hδ⟩, hδ⟩

/-- **Step 3+4 of stub N-1**: vanishing of the unfolded integral at a cusp where the constant
term of `θ` vanishes. -/
theorem cusp_integral_eq_zero_oai (Pk : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F}
    (hz6 : IsPrimitiveRoot z6 6) {Γ : Subgroup (SL(2, 𝓞 F))} [Γ.FiniteIndex]
    {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) (σ : SL(2, SInt 𝔪))
    (hv : CuspVanish Pk hG hz6 Γ Ψ σ) {c : ℝ → ℂ} (hc : Measurable c) (hc1 : ∀ t, ‖c t‖ ≤ 1)
    {ηK : X F → ℝ≥0∞} (hηK : IsPOU (stab Γ (RO.rowClass hG.ne_bot (Row.bot σ))) ηK)
    (hfin : ∫⁻ P, ‖c (X.ht (toF 𝔪 σ • P))‖ₑ * ‖X.lift Γ (theta Γ Ψ) P‖ₑ * ηK P ∂X.vol F ≠ ⊤) :
    ∫ P, c (X.ht (toF 𝔪 σ • P)) * X.lift Γ (theta Γ Ψ) P * (((ηK P).toReal : ℝ) : ℂ)
      ∂X.vol F = 0 := by
  obtain ⟨Γ', D', n₀, hfi, hΓ', hD', hvan⟩ := hv
  have := hfi
  obtain ⟨𝔫, h𝔫, hconj⟩ := exists_ideal_conj Γ (toF 𝔪 σ)
  have := RO.princCong_finiteIndex h𝔫
  have hΓ₂ : Inv (Γ' ⊓ RO.princCong 𝔫) (TSection.translate Pk hG hz6 σ Ψ) :=
    fun γ hγ => hΓ' γ hγ.1
  obtain ⟨D₂, n₂, hD₂m, hfund, hbdd, hn₂, hcell⟩ := exists_strict_cell (Γ' ⊓ RO.princCong 𝔫)
  have hE : ∀ (Ψ' : TSection ι 𝔪) (s : ℂ), 2 < s.re → EisEigen Ψ' s :=
    fun Ψ' s hs => GL.eisEigen_of_two_lt_re hG.ne_bot Ψ' hs
  -- the residue vanishes for the cell of `CuspVanish`, hence for the cell of `Γ₂`
  have hN1 : 1 ≤ max n₀ 1 := le_max_right _ _
  have hD'N : Cell Γ' D' (max n₀ 1) := hD'.mono (le_max_left _ _)
  have hz' : zRes Γ' (TSection.translate Pk hG hz6 σ Ψ) D' (max n₀ 1) = 0 := by
    have h1 := cf_theta_translate Pk hG hz6 σ hΓ hΓ' (hE Ψ) (hE _) hD'N hN1 hD'N
      (measurable_phase (F := F) (2 / 3)) (norm_phase_le (2 / 3))
    rw [hvan _ (le_max_left _ _) _ (measurable_phase (2 / 3)) (norm_phase_le (2 / 3))] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_right (cf_phase_ne_zero hD'N hN1 (2 / 3 : ℂ))
  have hz₂ : zRes (Γ' ⊓ RO.princCong 𝔫) (TSection.translate Pk hG hz6 σ Ψ) D₂ n₂ = 0 :=
    (zRes_congr hG hΓ₂ hΓ' hcell hn₂ hD'N hN1).trans hz'
  have hsetup := cuspSetup hG.ne_bot Γ σ Γ' hconj hD₂m hfund hbdd
  refine integral_cusp_eq_zero hsetup hc hc1 (X.stronglyMeasurable_lift Γ _).measurable
    (fun k P => X.lift_smul Γ _ (k : Γ) P) hηK hfin (fun n hn φ hφ hφ1 => ?_)
  rw [← map_inv, cf_theta_translate Pk hG hz6 σ hΓ hΓ₂ (hE Ψ) (hE _) hcell hn₂ (hcell.mono hn)
    hφ hφ1, hz₂, zero_mul]

end

end ArtinKP.N2
end

theorem solution.{u_1} : type_of% @ArtinKP.N2.cusp_integral_eq_zero_oai.{u_1} := @ArtinKP.N2.cusp_integral_eq_zero_oai.{u_1}
