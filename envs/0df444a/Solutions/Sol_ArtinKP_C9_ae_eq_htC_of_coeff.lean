-- Prove2me | solution 1 for ArtinKP.C9.ae_eq_htC_of_coeff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:04:00.430504+00:00
-- url     : https://prove2.me/submissions/ea10321b-1507-4089-acca-ec69d3958e50

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
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_ArtinKPB017

section
-- module Solutions.Artin.KP.X_Quot
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-! ### The quotient measure -/

/-! ### Unfolding -/

/-! ### Multiplicity and existence of partitions of unity -/

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

variable {F}

namespace X

lemma ht_pos (P : X F) : 0 < ht P := Finset.prod_pos fun w _ => P.v_pos w

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
-- module Solutions.Artin.KP.B_FourArch
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-B, part 2: the characters and the archimedean integral

* `eInf x = ∏_w archChar (-x_w)` on `ℂ^r`; `eInf (emb a) = exp(-2πi Tr a)` for `a ∈ F`.
* `psiS h𝔪 : SfChar 𝔪`, `ψ_{S_f}(x) = sAddChar 𝔪 x · conj (eInf (emb x))`; it is trivial on
  `𝔩_0`, and `eInf (emb x) = sAddChar 𝔪 x · conj ψ_{S_f}(x)` (`eInf_emb_eq`).
* `kerA v x = ∏_w v_w / (|x_w|² + v_w²)`; `I_{(c,d)}(x, v) = N_∞(c)⁻¹ · kerA v (x + d/c)`.
* `Winf s ν v = ∏_w jacquet s (-σ_w ν) v_w`; the integral of a shifted kernel against
  `conj eInf(ν x)` (`integral_shift_kernel`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.K

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### The archimedean character -/

/-! ### The `S_f`-character -/

/-! ### The archimedean kernel -/

theorem cpow_prod_nonneg {α : Type*} (t : Finset α) (f : α → ℝ) (hf : ∀ i, 0 ≤ f i) (s : ℂ) :
    (((∏ i ∈ t, f i : ℝ)) : ℂ) ^ s = ∏ i ∈ t, ((f i : ℝ) : ℂ) ^ s := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf a) (Finset.prod_nonneg fun i _ => hf i), ih]

/-! ### Shifted kernels -/

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.X2_Chart
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

variable (F : Type*) [Field F] [NumberField F]

variable {F}

lemma chart_x (y : Coord F) (w : InfinitePlace F) : (chart F y).x w = (y w).1 := rfl
lemma chart_v (y : Coord F) (w : InfinitePlace F) : (chart F y).v w = Real.exp (y w).2 := rfl

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Prod
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.N_Orbit
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-N, file 1: the `x`-integral of the tail of `E_Ψ` over a cell of the translations of `Γ`

For `Γ ≤ SL₂(𝓞_F)` fixing the twisted section `Ψ`, `Λ_Γ = {β : n(β) ∈ Γ}` (`lamN Γ`, embedded in
`ℂ^r` as `latN Γ`) and `D` a fundamental domain of `latN Γ`:

* `tail Ψ s Q = E_Ψ(Q, s) − Ψ_s(0,1)·ht(Q)^s` (no hypotheses in the definition);
* `exists_integral_tail`: for `Re s > 2` there is a constant `C` with
  `∫_D tail Ψ s (x, v) dx = C · ∏_w v_w^{2−s}` for **all** `v`
  (the classes `≠ ∞` are unfolded along the free action of `Λ_Γ`, `orbN`; each full-space integral
  is a Jacquet integral at frequency `0`, WP-B's `integral_hKer` and WP-K's `jacquet_zero`);
* `integrableOn_tail`: the tail is integrable over `D`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ}

/-! ### The translation lattice of `Γ` -/

/-! ### Orbits of `Λ_Γ` on the classes `≠ ∞` -/

variable {S : Finset (FinitePlace F)}

/-! ### The terms as shifted kernels -/

variable {Γ : Subgroup (SL(2, 𝓞 F))}

/-! ### The tail -/

/-! ### Finiteness of the unfolded `L¹` norm -/

lemma ht_mk (x : InfinitePlace F → ℂ) {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w) :
    X.ht (X.mk x v hv) = ∏ w, v w := by
  simp [X.ht]

/-! ### The integral over a cell -/

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.RF_Torus
attribute [-instance] _root_.ArtinKP.B1.instDiscreteTopologySubtypeE₂MemSubmoduleIntPairLattice _root_.ArtinKP.X.instDiscreteTopologySubtypeMixedSpaceMemSubmoduleIntLattice _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instSigmaFiniteE1Mu1 _root_.ArtinKP.X.instSigmaFiniteXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-RF, part 2: Fourier series on a fundamental cell of a lattice (abstract part of stub S1)

`E` a finite-dimensional real vector space with a Haar measure `μ`, `b : Basis J ℝ E`, lattice
`L = span ℤ (range b)`, cell `D₀ = ZSpan.fundamentalDomain b = {x | ∀ j, b.repr x j ∈ [0,1)}`,
characters `chi b n x = exp(2πi Σ_j n_j · b.repr x j)`, `n : J → ℤ` (these are exactly the
characters of `E` trivial on `L`).

* `map_toTorus`: `x ↦ (b.repr x j mod 1)_j` carries `μ|D₀` to `μ(D₀)` times the probability Haar
  measure of `UnitAddTorus J`.
* `hasSum_sq_coeff` (**Parseval**): `Σ_n |∫_{D₀} conj χ_n · g|² = μ(D₀) · ∫_{D₀} |g|²`.
* `ae_eq_zero_of_coeff` (**uniqueness**): if all coefficients of `g ∈ L²(D₀)` vanish then `g = 0`
  a.e. on `D₀`.

Everything is transported to Mathlib's `UnitAddTorus.mFourierBasis`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ComplexConjugate ENNReal
open MeasureTheory Set

noncomputable section

namespace ArtinKP.RF

attribute [local instance] ArtinKP.RF.instMeasureSpaceUnitAddCircle_solutions
local instance instIsAddHaarMeasureUnitAddCircleVolume_solutions_r87d249_1 : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance instIsProbabilityMeasureUnitAddCircleVolume_solutions : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {J : Type*} [Fintype J]

omit [Fintype J] in
lemma measurable_piMk : Measurable (piMk : (J → ℝ) → UnitAddTorus J) :=
  measurable_pi_lambda _ fun i => AddCircle.measurable_mk'.comp (measurable_pi_apply i)

omit [Fintype J] in
lemma measurable_piSec : Measurable (piSec : UnitAddTorus J → J → ℝ) :=
  measurable_pi_lambda _ fun i => measurable_subtype_coe.comp
    ((AddCircle.measurableEquivIco 1 0).measurable.comp (measurable_pi_apply i))

omit [Fintype J] in
lemma piSec_piMk {y : J → ℝ} (hy : y ∈ cube J) : piSec (piMk y) = y :=
  funext fun j => AddCircle.equivIco_coe_of_mem (p := 1) (a := 0) (by
    rw [zero_add]; exact hy j (mem_univ j))

lemma map_piMk :
    Measure.map piMk ((volume : Measure (J → ℝ)).restrict (cube J)) = volume := by
  ext s hs
  rw [Measure.map_apply measurable_piMk hs, Measure.restrict_apply (measurable_piMk hs)]
  have h := UnitAddTorus.lintegral_preimage (s.indicator fun _ => (1 : ℝ≥0∞)) (0 : J → ℝ)
  rw [lintegral_indicator hs, setLIntegral_one] at h
  rw [h]
  have hae : ({x : J → ℝ | ∀ i, x i ∈ Ioc ((0 : J → ℝ) i) ((0 : J → ℝ) i + 1)} : Set (J → ℝ))
      =ᵐ[volume] cube J := by
    have e1 : {x : J → ℝ | ∀ i, x i ∈ Ioc ((0 : J → ℝ) i) ((0 : J → ℝ) i + 1)}
        = Set.univ.pi fun _ : J => Ioc (0 : ℝ) 1 := by
      ext x; simp [Set.mem_pi]
    rw [e1, cube]
    exact (Measure.univ_pi_Ioc_ae_eq_Icc (f := fun _ : J => (0 : ℝ)) (g := fun _ => 1)).trans
      (Measure.univ_pi_Ico_ae_eq_Icc (f := fun _ : J => (0 : ℝ)) (g := fun _ => 1)).symm
  rw [Measure.restrict_congr_set hae, ← Measure.restrict_apply (measurable_piMk hs),
    ← lintegral_indicator_one (measurable_piMk hs)]
  rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (b : Module.Basis J ℝ E)

lemma continuous_equivFun : Continuous b.equivFun :=
  b.equivFun.toLinearMap.continuous_of_finiteDimensional

lemma continuous_equivFun_symm : Continuous b.equivFun.symm :=
  b.equivFun.symm.toLinearMap.continuous_of_finiteDimensional

lemma measurable_toTorus : Measurable (toTorus b) :=
  measurable_piMk.comp (continuous_equivFun b).measurable

lemma measurable_ofTorus : Measurable (ofTorus b) :=
  (continuous_equivFun_symm b).measurable.comp measurable_piSec

lemma cell_eq : ZSpan.fundamentalDomain b = b.equivFun ⁻¹' cube J := by
  ext x
  simp [ZSpan.mem_fundamentalDomain, cube, Set.mem_pi]

lemma ofTorus_toTorus {x : E} (hx : x ∈ ZSpan.fundamentalDomain b) :
    ofTorus b (toTorus b x) = x := by
  rw [cell_eq, mem_preimage] at hx
  rw [ofTorus, toTorus, piSec_piMk hx, LinearEquiv.symm_apply_apply]

lemma measure_cell_ne_top (μ : Measure E) [μ.IsAddHaarMeasure] :
    μ (ZSpan.fundamentalDomain b) ≠ ⊤ :=
  (ZSpan.fundamentalDomain_isBounded b).measure_lt_top.ne

/-- The cell with `μ` is `μ(cell)` times the probability torus. -/
theorem map_toTorus (μ : Measure E) [μ.IsAddHaarMeasure] :
    Measure.map (toTorus b) (μ.restrict (ZSpan.fundamentalDomain b)) =
      μ (ZSpan.fundamentalDomain b) • (volume : Measure (UnitAddTorus J)) := by
  set A : E ≃L[ℝ] (J → ℝ) := b.equivFun.toContinuousLinearEquiv with hA
  have hAm : Measurable A := A.continuous.measurable
  have hcube : MeasurableSet (cube J) := MeasurableSet.univ_pi fun _ => measurableSet_Ico
  have : (μ.map A).IsAddHaarMeasure := A.isAddHaarMeasure_map μ
  have hc := Measure.isAddLeftInvariant_eq_smul (μ.map A) (volume : Measure (J → ℝ))
  set c := Measure.addHaarScalarFactor (μ.map A) (volume : Measure (J → ℝ)) with hcdef
  have key : Measure.map (toTorus b) (μ.restrict (ZSpan.fundamentalDomain b)) =
      (c : ℝ≥0∞) • (volume : Measure (UnitAddTorus J)) := by
    have e1 : toTorus b = piMk ∘ A := rfl
    have e2 : ZSpan.fundamentalDomain b = A ⁻¹' cube J := cell_eq b
    rw [e1, ← Measure.map_map measurable_piMk hAm, e2, ← Measure.restrict_map hAm hcube, hc,
      Measure.restrict_smul, Measure.map_smul, map_piMk]
    rfl
  have hval : μ (ZSpan.fundamentalDomain b) = c := by
    have := congrArg (fun m : Measure (UnitAddTorus J) => m Set.univ) key
    simp only [Measure.map_apply (measurable_toTorus b) MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply MeasurableSet.univ, univ_inter, Measure.smul_apply, measure_univ,
      smul_eq_mul, mul_one] at this
    exact this
  rw [key, hval]

lemma chi_eq (n : J → ℤ) (x : E) :
    chi b n x = Complex.exp (2 * Real.pi * Complex.I * ∑ j, (n j : ℂ) * (b.repr x j : ℂ)) := by
  rw [chi, UnitAddTorus.mFourier, ContinuousMap.coe_mk, Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [toTorus, piMk, fourier_coe_apply]
  simp only [Module.Basis.equivFun_apply, Complex.ofReal_one, div_one]
  congr 1; ring

lemma measurable_chi (n : J → ℤ) : Measurable (chi b n) :=
  (UnitAddTorus.mFourier n).continuous.measurable.comp (measurable_toTorus b)

section transport

attribute [local instance] ArtinKP.RF.instMeasureSpaceUnitAddCircle_solutions
local instance instIsAddHaarMeasureUnitAddCircleVolume_solutions_r87d249_2 : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
variable (μ : Measure E) [μ.IsAddHaarMeasure]

lemma volume_torus_eq :
    (volume : Measure (UnitAddTorus J)) = (μ (ZSpan.fundamentalDomain b))⁻¹ •
      Measure.map (toTorus b) (μ.restrict (ZSpan.fundamentalDomain b)) := by
  rw [map_toTorus, smul_smul, ENNReal.inv_mul_cancel (ZSpan.measure_fundamentalDomain_ne_zero b)
    (measure_cell_ne_top b μ), one_smul]

/-- Integrals over the torus are normalized integrals over the cell. -/
lemma integral_torus {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (H : UnitAddTorus J → G) (hH : StronglyMeasurable H) :
    ∫ t, H t = (μ (ZSpan.fundamentalDomain b)).toReal⁻¹ •
      ∫ x in ZSpan.fundamentalDomain b, H (toTorus b x) ∂μ := by
  conv_lhs => rw [volume_torus_eq b μ]
  rw [integral_smul_measure, integral_map (measurable_toTorus b).aemeasurable
    hH.aestronglyMeasurable, ENNReal.toReal_inv]

variable {g : E → ℂ}

lemma comp_ofTorus_toTorus_ae (g : E → ℂ) :
    (fun x => g (ofTorus b (toTorus b x))) =ᵐ[μ.restrict (ZSpan.fundamentalDomain b)] g := by
  filter_upwards [ae_restrict_mem (ZSpan.fundamentalDomain_measurableSet b)] with x hx
  rw [ofTorus_toTorus b hx]

lemma memLp_comp_ofTorus (hg : Measurable g)
    (hL2 : MemLp g 2 (μ.restrict (ZSpan.fundamentalDomain b))) :
    MemLp (fun t => g (ofTorus b t)) 2 (volume : Measure (UnitAddTorus J)) := by
  rw [volume_torus_eq b μ]
  refine MemLp.smul_measure ?_ (ENNReal.inv_ne_top.mpr (ZSpan.measure_fundamentalDomain_ne_zero b))
  refine (memLp_map_measure_iff (hg.comp (measurable_ofTorus b)).aestronglyMeasurable
    (measurable_toTorus b).aemeasurable).mpr ?_
  exact hL2.ae_eq (comp_ofTorus_toTorus_ae b μ g).symm

lemma mFourierCoeff_comp_ofTorus (hg : Measurable g) (n : J → ℤ) :
    UnitAddTorus.mFourierCoeff (fun t => g (ofTorus b t)) n =
      (μ (ZSpan.fundamentalDomain b)).toReal⁻¹ •
        ∫ x in ZSpan.fundamentalDomain b, conj (chi b n x) * g x ∂μ := by
  rw [UnitAddTorus.mFourierCoeff, integral_torus b μ
    (fun t => UnitAddTorus.mFourier (-n) t • g (ofTorus b t))
    (((UnitAddTorus.mFourier (-n)).continuous.measurable.smul
      (hg.comp (measurable_ofTorus b))).stronglyMeasurable)]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [comp_ofTorus_toTorus_ae b μ g] with x hx
  rw [hx, UnitAddTorus.mFourier_neg, smul_eq_mul, chi]

/-- **Uniqueness of Fourier series on a cell**: a square-integrable function on the cell all of
whose Fourier coefficients vanish is `0` almost everywhere on the cell. -/
theorem ae_eq_zero_of_coeff (hg : Measurable g)
    (hL2 : MemLp g 2 (μ.restrict (ZSpan.fundamentalDomain b)))
    (h : ∀ n : J → ℤ, ∫ x in ZSpan.fundamentalDomain b, conj (chi b n x) * g x ∂μ = 0) :
    ∀ᵐ x ∂μ.restrict (ZSpan.fundamentalDomain b), g x = 0 := by
  have hmem := memLp_comp_ofTorus b μ hg hL2
  set f := hmem.toLp _ with hf
  have hcoef : ∀ n, UnitAddTorus.mFourierCoeff f n = 0 := by
    intro n
    have : UnitAddTorus.mFourierCoeff f n
        = UnitAddTorus.mFourierCoeff (fun t => g (ofTorus b t)) n := by
      refine integral_congr_ae ?_
      filter_upwards [hmem.coeFn_toLp] with t ht
      rw [ht]
    rw [this, mFourierCoeff_comp_ofTorus b μ hg, h n, smul_zero]
  have hrepr : UnitAddTorus.mFourierBasis.repr f = 0 := by
    ext n
    rw [UnitAddTorus.mFourierBasis_repr, hcoef n]
    rfl
  have hf0 : f = 0 := (LinearIsometryEquiv.map_eq_zero_iff _).mp hrepr
  have h0 : (fun t => g (ofTorus b t)) =ᵐ[(volume : Measure (UnitAddTorus J))] 0 := by
    have h1 := hmem.coeFn_toLp
    rw [← hf, hf0] at h1
    exact h1.symm.trans (Lp.coeFn_zero _ _ _)
  have h2 : ∀ᵐ t ∂Measure.map (toTorus b) (μ.restrict (ZSpan.fundamentalDomain b)),
      g (ofTorus b t) = 0 := by
    rw [map_toTorus]
    exact Measure.ae_smul_measure h0 _
  have h3 := ae_of_ae_map (measurable_toTorus b).aemeasurable h2
  filter_upwards [h3, comp_ofTorus_toTorus_ae b μ g] with x hx1 hx2
  rw [← hx2]; exact hx1

end transport

end ArtinKP.RF
end
end

section
-- module Solutions.Artin.KP.RF_Strip
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
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

theorem instHaarXV : (volume : Measure (XV F)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure volume volume

/-! ### The density of `X.vol` in product coordinates -/

lemma measurableSet_posSet : MeasurableSet (posSet F) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioi

lemma measurable_dens : Measurable (dens : (InfinitePlace F → ℝ) → ℝ≥0∞) := by
  unfold dens
  refine Measurable.indicator ?_ measurableSet_posSet
  exact Finset.measurable_prod _ fun w _ => by fun_prop

lemma dens_lt_top (v : InfinitePlace F → ℝ) : dens v < ⊤ := by
  unfold dens
  by_cases h : v ∈ posSet F
  · rw [indicator_of_mem h]
    exact ENNReal.prod_lt_top fun w _ => ENNReal.ofReal_lt_top
  · rw [indicator_of_notMem h]; exact ENNReal.zero_lt_top

lemma nuV_eq_withDensity : X.nuV F = (volume : Measure (InfinitePlace F → ℝ)).withDensity dens := by
  rw [X.nuV_eq]
  have h1 : (Measure.pi fun _ : InfinitePlace F => (volume : Measure ℝ).restrict (Ioi 0))
      = (volume : Measure (InfinitePlace F → ℝ)).restrict (posSet F) :=
    (Measure.restrict_pi_pi (fun _ : InfinitePlace F => (volume : Measure ℝ))
      (fun _ => Ioi (0 : ℝ))).symm
  rw [h1, ← withDensity_indicator measurableSet_posSet]
  rfl

lemma ofXV_toXV (P : X F) : ofXV (toXV P) = P := (chart F).apply_symm_apply P

lemma measurable_toXV : Measurable (toXV : X F → XV F) := X.measurable_xv

lemma measurable_ofXV : Measurable (ofXV : XV F → X F) := by
  refine (chart F).continuous.measurable.comp (measurable_pi_lambda _ fun w => ?_)
  exact ((measurable_pi_apply w).comp measurable_fst).prodMk
    (Real.measurable_log.comp ((measurable_pi_apply w).comp measurable_snd))

/-- `X.vol` in product coordinates is Lebesgue measure with density `dens`. -/
theorem map_xv : Measure.map (toXV : X F → XV F) (X.vol F) =
    (volume : Measure (XV F)).withDensity fun p => dens p.2 := by
  have h := (X.measurePreserving_xv F).map_eq
  rw [nuV_eq_withDensity, prod_withDensity_right measurable_dens] at h
  exact h

lemma integral_vol_xv (H : XV F → ℂ) (hH : Measurable H) :
    ∫ P, H (toXV P) ∂X.vol F = ∫ p : XV F, ((dens p.2).toReal : ℂ) * H p := by
  have hm : Measurable fun p : XV F => dens p.2 := measurable_dens.comp measurable_snd
  rw [← integral_map measurable_toXV.aemeasurable hH.aestronglyMeasurable, map_xv,
    integral_withDensity_eq_integral_toReal_smul hm
      (Filter.Eventually.of_forall fun p => dens_lt_top _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [Complex.real_smul]

lemma lintegral_vol_xv (H : XV F → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ P, H (toXV P) ∂X.vol F = ∫⁻ p : XV F, dens p.2 * H p := by
  have hm : Measurable fun p : XV F => dens p.2 := measurable_dens.comp measurable_snd
  rw [← lintegral_map hH measurable_toXV, map_xv,
    lintegral_withDensity_eq_lintegral_mul _ hm hH]
  rfl

lemma enorm_dens (v : InfinitePlace F → ℝ) : ‖((dens v).toReal : ℂ)‖ₑ = dens v := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (dens_lt_top v).ne]

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

lemma densBound_ne_top (n : ℕ) : densBound F n ≠ ⊤ :=
  ENNReal.pow_ne_top ENNReal.ofReal_ne_top

lemma dens_le {n : ℕ} {v : InfinitePlace F → ℝ} (hv : v ∈ vBox F n) : dens v ≤ densBound F n := by
  unfold dens densBound
  rw [indicator_of_mem (vBox_subset_posSet n hv)]
  refine le_trans (Finset.prod_le_prod' (g := fun _ => ENNReal.ofReal (((n : ℝ) + 1) ^ 3))
    fun w _ => ENNReal.ofReal_le_ofReal ?_) (by rw [Finset.prod_const, Finset.card_univ])
  have h0 : 0 < v w := vBox_subset_posSet n hv w (mem_univ w)
  have h1 := (hv w).1
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : ((n : ℝ) + 1)⁻¹ ≤ v w := by rwa [one_div] at h1
  have h3 : (v w)⁻¹ ≤ (n : ℝ) + 1 := by
    rw [inv_le_comm₀ h0 hn]; exact h2
  rw [← inv_pow]
  exact pow_le_pow_left₀ (inv_nonneg.mpr h0.le) h3 3

/-! ### The basis of `XV F` adapted to a box -/

lemma bT_repr (n : ℕ) (v : InfinitePlace F → ℝ) (w : InfinitePlace F) :
    (bT F n).repr v w = ((n : ℝ) + 2)⁻¹ * v w := by
  rw [bT, Module.Basis.ofEquivFun_repr_apply]
  rfl

variable {J : Type*} [Fintype J] (bV : Module.Basis J ℝ (InfinitePlace F → ℂ))

lemma norm_phiK (n : ℕ) (k : InfinitePlace F → ℤ) (v : InfinitePlace F → ℝ) :
    ‖phiK n k v‖ = 1 := by
  have e : 2 * Real.pi * Complex.I * ∑ w, (k w : ℂ) * ((((n : ℝ) + 2)⁻¹ * v w : ℝ) : ℂ)
      = ((2 * Real.pi * ∑ w, (k w : ℝ) * (((n : ℝ) + 2)⁻¹ * v w) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [phiK, e, Complex.norm_exp_ofReal_mul_I]

lemma measurable_phiK (n : ℕ) (k : InfinitePlace F → ℤ) :
    Measurable (phiK (F := F) n k) := by
  unfold phiK
  refine Complex.measurable_exp.comp (measurable_const.mul ?_)
  refine Finset.measurable_sum _ fun w _ => measurable_const.mul ?_
  exact Complex.measurable_ofReal.comp (measurable_const.mul (measurable_pi_apply w))

lemma chi_bE (n : ℕ) (M : J ⊕ InfinitePlace F → ℤ) (p : XV F) :
    chi (bE bV n) M p = chi bV (fun j => M (Sum.inl j)) p.1 *
      phiK n (fun w => M (Sum.inr w)) p.2 := by
  rw [chi_eq, chi_eq, phiK, ← Complex.exp_add, Fintype.sum_sum_type]
  congr 1
  simp only [bE, Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr, bT_repr]
  ring

lemma mem_cell_bE (n : ℕ) (p : XV F) :
    p ∈ ZSpan.fundamentalDomain (bE bV n) ↔
      p.1 ∈ ZSpan.fundamentalDomain bV ∧ ∀ w, ((n : ℝ) + 2)⁻¹ * p.2 w ∈ Ico (0 : ℝ) 1 := by
  simp only [ZSpan.mem_fundamentalDomain, Sum.forall, bE, Module.Basis.prod_repr_inl,
    Module.Basis.prod_repr_inr, bT_repr]

lemma scaled_mem_Ico {n : ℕ} {v : InfinitePlace F → ℝ} (hv : v ∈ vBox F n) (w : InfinitePlace F) :
    ((n : ℝ) + 2)⁻¹ * v w ∈ Ico (0 : ℝ) 1 := by
  have h0 : 0 < v w := vBox_subset_posSet n hv w (mem_univ w)
  have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  refine ⟨by positivity, ?_⟩
  rw [inv_mul_lt_iff₀ hn, mul_one]
  linarith [(hv w).2]

/-- **Fourier uniqueness on a box of a strip.**  `D₀ = ZSpan.fundamentalDomain bV`. -/
theorem measure_ne_zero_null (n : ℕ) (f : X F → ℂ) (hf : Measurable f)
    (hL2 : MemLp f 2 ((X.vol F).restrict
      (X.x ⁻¹' ZSpan.fundamentalDomain bV ∩ X.v ⁻¹' vBox F n)))
    (h : ∀ (m : J → ℤ) (k : InfinitePlace F → ℤ),
      ∫ P in (X.x ⁻¹' ZSpan.fundamentalDomain bV ∩ X.v ⁻¹' vBox F n : Set (X F)),
        conj (chi bV m P.x * phiK n k P.v) * f P ∂X.vol F = 0) :
    X.vol F ((X.x ⁻¹' ZSpan.fundamentalDomain bV ∩ X.v ⁻¹' vBox F n) ∩ {P | f P ≠ 0}) = 0 := by
  haveI _iHXV := ArtinKP.RF.instHaarXV (F := F)
  classical
  set D₀ := ZSpan.fundamentalDomain bV with hD₀
  have hD₀m : MeasurableSet D₀ := ZSpan.fundamentalDomain_measurableSet bV
  set S : Set (X F) := X.x ⁻¹' D₀ ∩ X.v ⁻¹' vBox F n with hS
  set S' : Set (XV F) := D₀ ×ˢ vBox F n with hS'
  have hS'm : MeasurableSet S' := hD₀m.prod (measurableSet_vBox n)
  have hSS' : S = toXV ⁻¹' S' := by ext P; simp [hS, hS', toXV]
  have hSm : MeasurableSet S := hSS' ▸ measurable_toXV hS'm
  set cellE := ZSpan.fundamentalDomain (bE bV n) with hcellE
  have hcellm : MeasurableSet cellE := ZSpan.fundamentalDomain_measurableSet _
  have hS'cell : S' ⊆ cellE := fun p hp =>
    (mem_cell_bE bV n p).mpr ⟨hp.1, fun w => scaled_mem_Ico hp.2 w⟩
  set f' : XV F → ℂ := fun p => f (ofXV p) with hf'
  have hf'm : Measurable f' := hf.comp measurable_ofXV
  have hf'P : ∀ P : X F, f' (toXV P) = f P := fun P => by
    show f (ofXV (toXV P)) = f P
    rw [ofXV_toXV]
  set g : XV F → ℂ := (Prod.snd ⁻¹' vBox F n).indicator
    (fun p => ((dens p.2).toReal : ℂ) * f' p) with hg
  have hgm : Measurable g :=
    ((Complex.measurable_ofReal.comp (measurable_dens.comp measurable_snd).ennreal_toReal).mul
      hf'm).indicator (measurable_snd (measurableSet_vBox n))
  -- the coefficients of `g` vanish
  have hcoef : ∀ M : J ⊕ InfinitePlace F → ℤ,
      ∫ p in cellE, conj (chi (bE bV n) M p) * g p = 0 := by
    intro M
    have h0 := h (fun j => M (Sum.inl j)) (fun w => M (Sum.inr w))
    rw [← integral_indicator hSm] at h0
    set H : XV F → ℂ := S'.indicator fun p =>
      conj (chi bV (fun j => M (Sum.inl j)) p.1 * phiK n (fun w => M (Sum.inr w)) p.2) * f' p
      with hH
    have hHm : Measurable H := by
      refine Measurable.indicator ?_ hS'm
      exact (Complex.continuous_conj.measurable.comp
        (((measurable_chi bV _).comp measurable_fst).mul
          ((measurable_phiK n _).comp measurable_snd))).mul hf'm
    have e1 : ∀ P : X F, S.indicator (fun P : X F => conj (chi bV (fun j => M (Sum.inl j)) P.x *
        phiK n (fun w => M (Sum.inr w)) P.v) * f P) P = H (toXV P) := by
      intro P
      by_cases hP : P ∈ S
      · have hP' : toXV P ∈ S' := by rwa [hSS'] at hP
        rw [indicator_of_mem hP, hH, indicator_of_mem hP', hf'P]
        rfl
      · have hP' : toXV P ∉ S' := by rwa [hSS'] at hP
        rw [indicator_of_notMem hP, hH, indicator_of_notMem hP']
    rw [integral_congr_ae (Filter.Eventually.of_forall e1), integral_vol_xv H hHm] at h0
    rw [← integral_indicator hcellm, ← h0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    by_cases hp2 : p.2 ∈ vBox F n
    · by_cases hp1 : p.1 ∈ D₀
      · have hpS : p ∈ S' := ⟨hp1, hp2⟩
        simp only [indicator_of_mem (hS'cell hpS), hH, indicator_of_mem hpS, hg]
        rw [indicator_of_mem (show p ∈ Prod.snd ⁻¹' vBox F n from hp2), chi_bE]
        ring
      · have hpS : p ∉ S' := fun hc => hp1 hc.1
        have hpc : p ∉ cellE := fun hc => hp1 ((mem_cell_bE bV n p).mp hc).1
        simp only [indicator_of_notMem hpc, hH, indicator_of_notMem hpS, mul_zero]
    · have hpS : p ∉ S' := fun hc => hp2 hc.2
      have hg0 : g p = 0 := by
        rw [hg, indicator_of_notMem (show p ∉ Prod.snd ⁻¹' vBox F n from hp2)]
      by_cases hpc : p ∈ cellE
      · simp only [indicator_of_mem hpc, hg0, mul_zero, hH, indicator_of_notMem hpS]
      · simp only [indicator_of_notMem hpc, hH, indicator_of_notMem hpS, mul_zero]
  -- `g` is square integrable on the cell
  have hfin : ∫⁻ P in S, ‖f P‖ₑ ^ (2 : ℝ) ∂X.vol F < ⊤ := by
    have := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)).mp hL2.2
    simpa using this
  have hgL2 : MemLp g 2 ((volume : Measure (XV F)).restrict cellE) := by
    refine ⟨hgm.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
    have e2 : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by simp
    rw [e2, ← lintegral_indicator hcellm]
    set K : XV F → ℝ≥0∞ := S'.indicator fun p => ‖f' p‖ₑ ^ (2 : ℝ) with hK
    have hKm : Measurable K := (hf'm.enorm.pow_const _).indicator hS'm
    have hle : ∀ p : XV F, cellE.indicator (fun p => ‖g p‖ₑ ^ (2 : ℝ)) p
        ≤ densBound F n * (dens p.2 * K p) := by
      intro p
      by_cases hpc : p ∈ cellE
      · rw [indicator_of_mem hpc]
        by_cases hp2 : p.2 ∈ vBox F n
        · have hpS : p ∈ S' := ⟨((mem_cell_bE bV n p).mp hpc).1, hp2⟩
          rw [hg, indicator_of_mem (show p ∈ Prod.snd ⁻¹' vBox F n from hp2), hK,
            indicator_of_mem hpS, enorm_mul, enorm_dens,
            ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
          have e3 : dens p.2 ^ (2 : ℝ) = dens p.2 * dens p.2 := by
            rw [ENNReal.rpow_two, sq]
          rw [e3, mul_assoc]
          gcongr
          exact dens_le hp2
        · rw [hg, indicator_of_notMem (show p ∉ Prod.snd ⁻¹' vBox F n from hp2)]
          simp
      · rw [indicator_of_notMem hpc]; exact bot_le
    refine (lintegral_mono hle).trans_lt ?_
    have hmK : Measurable fun a : XV F => dens a.2 * K a :=
      (measurable_dens.comp measurable_snd).mul hKm
    rw [lintegral_const_mul _ hmK, ← lintegral_vol_xv K hKm]
    refine ENNReal.mul_lt_top (densBound_ne_top n).lt_top ?_
    have e4 : ∀ P : X F, K (toXV P) = S.indicator (fun P => ‖f P‖ₑ ^ (2 : ℝ)) P := by
      intro P
      by_cases hP : P ∈ S
      · have hP' : toXV P ∈ S' := by rwa [hSS'] at hP
        rw [hK, indicator_of_mem hP', indicator_of_mem hP, hf'P]
      · have hP' : toXV P ∉ S' := by rwa [hSS'] at hP
        rw [hK, indicator_of_notMem hP', indicator_of_notMem hP]
    rw [lintegral_congr e4, lintegral_indicator hSm]
    exact hfin
  have hg0 := ae_eq_zero_of_coeff (bE bV n) (volume : Measure (XV F)) hgm hgL2 hcoef
  -- back to `X`
  set N' : Set (XV F) := S' ∩ {p | f' p ≠ 0} with hN'
  have hN'm : MeasurableSet N' :=
    hS'm.inter (hf'm (measurableSet_singleton (0 : ℂ)).compl)
  have hN'0 : (volume : Measure (XV F)) N' = 0 := by
    have h1 : ((volume : Measure (XV F)).restrict cellE) {p | ¬ g p = 0} = 0 := ae_iff.mp hg0
    rw [Measure.restrict_apply' hcellm] at h1
    refine measure_mono_null (fun p hp => ?_) h1
    refine ⟨?_, hS'cell hp.1⟩
    show ¬ g p = 0
    rw [hg, indicator_of_mem (show p ∈ Prod.snd ⁻¹' vBox F n from hp.1.2)]
    refine mul_ne_zero ?_ hp.2
    rw [Ne, Complex.ofReal_eq_zero, ENNReal.toReal_eq_zero_iff]
    exact fun hc => hc.elim (dens_ne_zero hp.1.2) (dens_lt_top _).ne
  have e5 : (S ∩ {P | f P ≠ 0}) = toXV ⁻¹' N' := by
    ext P
    simp only [hN', hSS', mem_inter_iff, mem_preimage, mem_ofPred_eq, hf'P]
  rw [e5, ← Measure.map_apply measurable_toXV hN'm, map_xv]
  exact withDensity_absolutelyContinuous _ _ hN'0

end

end ArtinKP.RF
end

section
-- module Solutions.Artin.KP.X_Cusp
attribute [-instance] _root_.ArtinKP.B1.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatSub _root_.ArtinKP.N.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-- A strict fundamental set `D ⊂ ℂ^r` for the translation lattice gives the partition of unity
`P ↦ 1_D(x(P))` for `GammaN Γ`. -/
theorem isPOU_strip (Γ : Subgroup (SL(2, 𝓞 F))) {D : Set (InfinitePlace F → ℂ)}
    (hD : MeasurableSet D)
    (hfund : ∀ x : InfinitePlace F → ℂ, ∃! γ : GammaN Γ, (fun w => x w + GammaN.shift γ w) ∈ D) :
    IsPOU (GammaN Γ) ((X.x ⁻¹' D : Set (X F)).indicator fun _ => (1 : ℝ≥0∞)) := by
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  refine isPOU_indicator_of_existsUnique (X.measurable_x hD) fun P => ?_
  obtain ⟨γ, hγ, huniq⟩ := hfund P.x
  refine ⟨γ, ?_, fun γ' hγ' => huniq γ' ?_⟩
  · change (γ • P).x ∈ D
    rw [GammaN.smul_eq]; exact hγ
  · have : (γ' • P).x ∈ D := hγ'
    rwa [GammaN.smul_eq] at this

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.RF_Fourier
attribute [-instance] _root_.ArtinKP.B1.PairClass.instNonempty _root_.ArtinKP.B1.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatSub _root_.ArtinKP.B1.instDiscreteTopologySubtypeE₂MemSubmoduleIntPairLattice _root_.ArtinKP.N.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma eChar_add_of_int {ν y : InfinitePlace F → ℂ} (h : ∃ m : ℤ, pair ν y = m)
    (x : InfinitePlace F → ℂ) : eChar ν (x + y) = eChar ν x := by
  obtain ⟨m, hm⟩ := h
  rw [eChar, eChar, pair_add, hm]
  have e : 2 * Real.pi * Complex.I * ((pair ν x + (m : ℝ) : ℝ) : ℂ)
      = 2 * Real.pi * Complex.I * (pair ν x : ℂ) + (m : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Every real linear functional on `ι → ℂ` is `pair ν`. -/
lemma exists_pair_eq (ℓ : (InfinitePlace F → ℂ) →ₗ[ℝ] ℝ) :
    ∃ ν : InfinitePlace F → ℂ, ∀ x, pair ν x = ℓ x := by
  classical
  refine ⟨fun w => (ℓ (Pi.single w 1) : ℂ) - (ℓ (Pi.single w Complex.I) : ℂ) * Complex.I,
    fun x => ?_⟩
  have hx : x = ∑ w, ((x w).re • (Pi.single w (1 : ℂ) : InfinitePlace F → ℂ)
      + (x w).im • (Pi.single w Complex.I : InfinitePlace F → ℂ)) := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    refine Finset.sum_congr rfl fun w _ => ?_
    funext w'
    by_cases hw : w' = w
    · subst hw
      simp only [Pi.single_eq_same, Pi.add_apply, Pi.smul_apply, Complex.real_smul, mul_one]
      exact (Complex.re_add_im (x w')).symm
    · simp [Pi.single_eq_of_ne hw]
  conv_rhs => rw [hx]
  rw [map_sum, pair]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [map_add, map_smul, map_smul]
  simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_im, Complex.I_re, Complex.I_im, smul_eq_mul]
  ring

/-! ### A basis of the translation lattice -/

lemma shift_injective (Γ : Subgroup (SL(2, 𝓞 F))) :
    Function.Injective (GammaN.shift : GammaN Γ → InfinitePlace F → ℂ) := by
  intro γ γ' h
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have h1 := congrFun h w
  simp only [GammaN.shift] at h1
  exact GammaN.ext_of_zero_one (RingOfIntegers.coe_injective (w.embedding.injective h1))

lemma toMixed_shift [IsTotallyComplex F] {Γ : Subgroup (SL(2, 𝓞 F))} (γ : GammaN Γ) :
    toMixed F (GammaN.shift γ) = GammaN.mixed Γ (Additive.ofMul γ) := by
  have h := toMixed_add_shift (Γ := Γ) (0 : InfinitePlace F → ℂ) γ
  simp only [Pi.zero_apply, zero_add, map_zero, add_zero] at h
  exact h

open Classical in
theorem exists_latBasis [IsTotallyComplex F] (Γ : Subgroup (SL(2, 𝓞 F)))
    (h𝔫 : ∃ 𝔫 : Ideal (𝓞 F), 𝔫 ≠ ⊥ ∧
      ∀ β ∈ 𝔫, ∃ γ : GammaN Γ, ((γ : Γ) : SL(2, 𝓞 F)) 0 1 = β) :
    ∃ (d : ℕ) (bV : Module.Basis (Fin d) ℝ (InfinitePlace F → ℂ)), IsLatBasis Γ bV := by
  have := GammaN.isZLattice h𝔫
  set e : (InfinitePlace F → ℂ) ≃L[ℝ] mixedEmbedding.mixedSpace F :=
    (toMixed F).toContinuousLinearEquiv with he
  set L : Submodule ℤ (InfinitePlace F → ℂ) :=
    ZLattice.comap ℝ (E := mixedEmbedding.mixedSpace F) (GammaN.lattice Γ) e.toLinearMap with hL
  have hmem : ∀ x, x ∈ L ↔ ∃ γ : GammaN Γ, x = GammaN.shift γ := by
    intro x
    have h1 : x ∈ L ↔ toMixed F x ∈ GammaN.lattice Γ := Iff.rfl
    rw [h1, GammaN.mem_lattice]
    constructor
    · rintro ⟨γa, hγ⟩
      refine ⟨Additive.toMul γa, (toMixed F).injective ?_⟩
      rw [toMixed_shift, ofMul_toMul, hγ]
    · rintro ⟨γ, rfl⟩
      exact ⟨Additive.ofMul γ, (toMixed_shift γ).symm⟩
  have : Module.Free ℤ L := ZLattice.module_free ℝ L
  have : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  let b0 := (Module.Free.chooseBasis ℤ L).reindex (Fintype.equivFin _)
  refine ⟨_, b0.ofZLatticeBasis ℝ L, fun x => ?_⟩
  rw [b0.ofZLatticeBasis_span ℝ, hmem]

section basis

variable {Γ : Subgroup (SL(2, 𝓞 F))} {J : Type*} [Fintype J]
  {bV : Module.Basis J ℝ (InfinitePlace F → ℂ)}

/-- The characters `chi bV m` of the cell are the `e_ν`, `ν ∈ Λ^⊥`. -/
lemma exists_dual_of_chi (hb : IsLatBasis Γ bV) (m : J → ℤ) :
    ∃ ν ∈ dualLat Γ, ∀ x, eChar ν x = chi bV m x := by
  let ℓ : (InfinitePlace F → ℂ) →ₗ[ℝ] ℝ :=
    ∑ j, (m j : ℝ) • (Finsupp.lapply j ∘ₗ bV.repr.toLinearMap)
  have hℓ : ∀ x, ℓ x = ∑ j, (m j : ℝ) * bV.repr x j := fun x => by
    simp [ℓ, LinearMap.sum_apply]
  obtain ⟨ν, hν⟩ := exists_pair_eq ℓ
  refine ⟨ν, fun γ => ?_, fun x => ?_⟩
  · have hmem : (GammaN.shift γ : InfinitePlace F → ℂ) ∈ Submodule.span ℤ (Set.range bV) :=
      (hb _).mpr ⟨γ, rfl⟩
    rw [bV.mem_span_iff_repr_mem ℤ] at hmem
    choose c hc using hmem
    refine ⟨∑ j, m j * c j, ?_⟩
    rw [hν, hℓ]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hc j]; rfl
  · rw [eChar, chi_eq, hν, hℓ]
    congr 1
    push_cast
    ring

/-- The cell of a lattice basis is a strict fundamental set (hypothesis `hfund` of
`isPOU_strip`). -/
lemma hfund_cell (hb : IsLatBasis Γ bV) (x : InfinitePlace F → ℂ) :
    ∃! γ : GammaN Γ, (fun w => x w + GammaN.shift γ w) ∈ ZSpan.fundamentalDomain bV := by
  obtain ⟨v, hv, hvu⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain bV x
  obtain ⟨γ, hγ⟩ := (hb _).mp v.2
  have key : ∀ γ' : GammaN Γ, (fun w => x w + GammaN.shift γ' w)
      = (GammaN.shift γ' : InfinitePlace F → ℂ) + x := fun γ' => by
    funext w; simp [add_comm]
  refine ⟨γ, ?_, fun γ' hγ' => ?_⟩
  · show (fun w => x w + GammaN.shift γ w) ∈ ZSpan.fundamentalDomain bV
    rw [key, ← hγ]; exact hv
  · have hmem : (GammaN.shift γ' : InfinitePlace F → ℂ) ∈ Submodule.span ℤ (Set.range bV) :=
      (hb _).mpr ⟨γ', rfl⟩
    have h1 : (⟨GammaN.shift γ', hmem⟩ : Submodule.span ℤ (Set.range bV)) +ᵥ x
        ∈ ZSpan.fundamentalDomain bV := by
      have h2 : (fun w => x w + GammaN.shift γ' w) ∈ ZSpan.fundamentalDomain bV := hγ'
      rw [key] at h2; exact h2
    have h3 := congrArg Subtype.val (hvu _ h1)
    exact shift_injective Γ (h3.trans hγ)

end basis

/-- A strict fundamental set of the translations gives a fundamental domain of `GammaN Γ`
on `X`. -/
lemma isFundamentalDomain_strip (Γ : Subgroup (SL(2, 𝓞 F))) {D : Set (InfinitePlace F → ℂ)}
    (hD : MeasurableSet D)
    (hfund : ∀ x : InfinitePlace F → ℂ, ∃! γ : GammaN Γ, (fun w => x w + GammaN.shift γ w) ∈ D) :
    IsFundamentalDomain (GammaN Γ) (X.x ⁻¹' D : Set (X F)) (X.vol F) := by
  refine IsFundamentalDomain.mk' (X.measurable_x hD).nullMeasurableSet fun P => ?_
  obtain ⟨γ, hγ, huniq⟩ := hfund P.x
  refine ⟨γ, ?_, fun γ' hγ' => huniq γ' ?_⟩
  · change (γ • P).x ∈ D
    rw [GammaN.smul_eq]; exact hγ
  · have : (γ' • P).x ∈ D := hγ'
    rwa [GammaN.smul_eq] at this

lemma vBox_mono {n n' : ℕ} (h : n ≤ n') : vBox F n ⊆ vBox F n' := by
  intro v hv w
  have h1 : (n : ℝ) ≤ n' := by exact_mod_cast h
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  refine ⟨le_trans ?_ (hv w).1, (hv w).2.trans (by linarith)⟩
  exact one_div_le_one_div_of_le hn (by linarith)

lemma mem_box_iff (n : ℕ) (P : X F) :
    P ∈ (X.box n : Set (X F)) ↔ (∀ w, ‖P.x w‖ ≤ n) ∧ P.v ∈ vBox F n := by
  simp only [X.box, H3.box, vBox, mem_ofPred_eq, X.x, X.v]
  exact forall_and

/-- **Fourier uniqueness along `x`** for invariant functions: a measurable function on `X`,
invariant under the translations of `Γ` and square integrable on boxes, all of whose Fourier
coefficients along a strip `{x ∈ D}` vanish (frequencies `ν ∈ Λ^⊥`, including `0`; bounded
measurable `φ`; boxes `n ≥ n₀` in `v`), vanishes almost everywhere. -/
theorem ae_eq_zero_of_strip [IsTotallyComplex F] (Γ : Subgroup (SL(2, 𝓞 F)))
    (h𝔫 : ∃ 𝔫 : Ideal (𝓞 F), 𝔫 ≠ ⊥ ∧
      ∀ β ∈ 𝔫, ∃ γ : GammaN Γ, ((γ : Γ) : SL(2, 𝓞 F)) 0 1 = β)
    {D : Set (InfinitePlace F → ℂ)} (hD : MeasurableSet D)
    (hfund : ∀ x : InfinitePlace F → ℂ, ∃! γ : GammaN Γ, (fun w => x w + GammaN.shift γ w) ∈ D)
    (f : X F → ℂ) (hf : Measurable f) (hinv : ∀ (γ : GammaN Γ) (P : X F), f (γ • P) = f P)
    (hL2 : ∀ n : ℕ, MemLp f 2 ((X.vol F).restrict (X.box n)))
    (n₀ : ℕ)
    (h : ∀ ν ∈ dualLat Γ, ∀ n : ℕ, n₀ ≤ n → ∀ φ : (InfinitePlace F → ℝ) → ℂ, Measurable φ →
      (∀ v, ‖φ v‖ ≤ 1) →
      ∫ P in (X.x ⁻¹' D ∩ X.v ⁻¹' vBox F n : Set (X F)),
        conj (eChar ν P.x * φ P.v) * f P ∂X.vol F = 0) :
    f =ᵐ[X.vol F] 0 := by
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  obtain ⟨d, bV, hb⟩ := exists_latBasis Γ h𝔫
  set D₀ := ZSpan.fundamentalDomain bV with hD₀
  have hD₀m : MeasurableSet D₀ := ZSpan.fundamentalDomain_measurableSet bV
  have hfund₀ := hfund_cell hb
  have hvm : ∀ n, MeasurableSet (X.v ⁻¹' vBox F n : Set (X F)) := fun n =>
    X.measurable_v (measurableSet_vBox n)
  -- boundedness of the cell
  obtain ⟨R, hR⟩ := (ZSpan.fundamentalDomain_isBounded bV).exists_norm_le
  -- the null sets on boxes
  have hnull : ∀ n : ℕ, n₀ ≤ n →
      X.vol F ((X.x ⁻¹' D₀ ∩ X.v ⁻¹' vBox F n) ∩ {P | f P ≠ 0}) = 0 := by
    intro n hn
    refine measure_ne_zero_null bV n f hf ?_ ?_
    · obtain ⟨N, hN⟩ := exists_nat_ge R
      refine (hL2 (max n N)).mono_measure (Measure.restrict_mono (fun P hP => ?_) le_rfl)
      rw [mem_box_iff]
      refine ⟨fun w => ?_, vBox_mono (le_max_left n N) hP.2⟩
      have h1 : ‖P.x w‖ ≤ ‖P.x‖ := norm_le_pi_norm _ w
      have h2 : ‖P.x‖ ≤ R := hR _ hP.1
      have h3 : (N : ℝ) ≤ ((max n N : ℕ) : ℝ) := by exact_mod_cast le_max_right n N
      linarith
    · intro m k
      obtain ⟨ν, hν, hνe⟩ := exists_dual_of_chi hb m
      have h0 := h ν hν n hn (phiK n k) (measurable_phiK n k) (fun v => (norm_phiK n k v).le)
      set G : X F → ℂ := fun P => conj (eChar ν P.x * phiK n k P.v) * f P with hG
      have hGinv : ∀ (γ : GammaN Γ) (P : X F),
          (X.v ⁻¹' vBox F n : Set (X F)).indicator G (γ • P)
            = (X.v ⁻¹' vBox F n : Set (X F)).indicator G P := by
        intro γ P
        have hv : (γ • P).v = P.v := by rw [GammaN.smul_eq]; rfl
        have hx : (γ • P).x = P.x + GammaN.shift γ := by rw [GammaN.smul_eq]; rfl
        have hGP : G (γ • P) = G P := by
          simp only [hG, hv, hx, eChar_add_of_int (hν γ), hinv]
        by_cases hP : P.v ∈ vBox F n
        · rw [indicator_of_mem (show γ • P ∈ X.v ⁻¹' vBox F n by rw [mem_preimage, hv]; exact hP),
            indicator_of_mem (show P ∈ X.v ⁻¹' vBox F n from hP), hGP]
        · rw [indicator_of_notMem (show γ • P ∉ X.v ⁻¹' vBox F n by
              rw [mem_preimage, hv]; exact hP),
            indicator_of_notMem (show P ∉ X.v ⁻¹' vBox F n from hP)]
      have hsw := (isFundamentalDomain_strip Γ hD₀m hfund₀).setIntegral_eq
        (isFundamentalDomain_strip Γ hD hfund) hGinv
      rw [setIntegral_indicator (hvm n), setIntegral_indicator (hvm n)] at hsw
      have e : ∀ P : X F, conj (chi bV m P.x * phiK n k P.v) * f P = G P := fun P => by
        simp only [hG, hνe]
      rw [integral_congr_ae (Filter.Eventually.of_forall e), hsw]
      exact h0
  -- the union over boxes
  set N : Set (X F) := {P | f P ≠ 0} with hN
  have hNm : MeasurableSet N := hf (measurableSet_singleton (0 : ℂ)).compl
  have hstrip : X.vol F (X.x ⁻¹' D₀ ∩ N) = 0 := by
    have hcov : (X.x ⁻¹' D₀ ∩ N : Set (X F))
        ⊆ ⋃ n : ℕ, (X.x ⁻¹' D₀ ∩ X.v ⁻¹' vBox F (n + n₀)) ∩ N := by
      intro P hP
      obtain ⟨n₁, hn₁⟩ := X.exists_mem_box P
      exact mem_iUnion.mpr ⟨n₁, ⟨hP.1, vBox_mono (Nat.le_add_right n₁ n₀)
        ((mem_box_iff n₁ P).mp hn₁).2⟩, hP.2⟩
    exact measure_mono_null hcov
      (measure_iUnion_null fun n => hnull (n + n₀) (Nat.le_add_left n₀ n))
  have hNinv : ∀ (γ : GammaN Γ) (P : X F), γ • P ∈ N ↔ P ∈ N := fun γ P => by
    simp only [hN, mem_ofPred_eq, hinv]
  have hNull : X.vol F N = 0 := by
    refine measure_eq_zero_of_invariant (isPOU_strip Γ hD₀m hfund₀) hNm hNinv ?_
    rw [lintegral_indicator (X.measurable_x hD₀m), setLIntegral_one,
      Measure.restrict_apply (X.measurable_x hD₀m)]
    exact hstrip
  exact ae_iff.mpr hNull

end

end ArtinKP.RF
end

section
-- module Solutions.Artin.KP.N_Shape
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-! ### The constant-term functional -/

lemma eChar_zero (x : InfinitePlace F → ℂ) : eChar 0 x = 1 := by
  simp [eChar, pair]

lemma stripFn_zero (D : Set (InfinitePlace F → ℂ)) (φ : (InfinitePlace F → ℝ) → ℂ) (P : X F) :
    stripFn D 0 φ P = D.indicator (fun _ => (1 : ℂ)) P.x * φ P.v := by
  rw [stripFn, eChar_zero, one_mul]

section lin

variable {D : Set (InfinitePlace F → ℂ)} {n : ℕ} {φ : (InfinitePlace F → ℝ) → ℂ}

lemma cf_integrable (hD : MeasurableSet D) (hφ : Measurable φ) (hφ1 : ∀ v, ‖φ v‖ ≤ 1)
    {f : X F → ℂ} (hf : IntegrableOn f (X.box n) (X.vol F)) :
    IntegrableOn (fun P => conj (stripFn D 0 φ P) * f P) (X.box n) (X.vol F) := by
  refine Integrable.bdd_mul (c := 1) hf
    (Complex.continuous_conj.measurable.comp (measurable_stripFn hD 0 hφ)).aestronglyMeasurable ?_
  exact Eventually.of_forall fun P => by
    rw [RCLike.norm_conj]; exact norm_stripFn_le D 0 hφ1 P

end lin

/-! ### Fubini: a function with vanishing `x`-integrals over `D` is killed by `cf` -/

lemma ofXV_eq_mk (x : InfinitePlace F → ℂ) {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w) :
    ofXV (x, v) = X.mk x v hv := by
  refine X.ext' (funext fun w => ?_) (funext fun w => ?_)
  · simp [ofXV, chart_x]
  · simp [ofXV, chart_v, Real.exp_log (hv w)]

theorem cf_eq_zero_of_fibers {D : Set (InfinitePlace F → ℂ)} (hD : MeasurableSet D) {n : ℕ}
    (hn : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) {φ : (InfinitePlace F → ℝ) → ℂ} (hφ : Measurable φ)
    (hφ1 : ∀ v, ‖φ v‖ ≤ 1) {R : X F → ℂ} (hR : Measurable R)
    (hint : IntegrableOn R (X.box n) (X.vol F))
    (h0 : ∀ (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w), ∫ x in D, R (X.mk x v hv) = 0) :
    cf D n φ R = 0 := by
  classical
  set G : X F → ℂ := (X.box n : Set (X F)).indicator
    (fun P => conj (stripFn D 0 φ P) * R P) with hG
  have hGm : Measurable G :=
    ((Complex.continuous_conj.measurable.comp (measurable_stripFn hD 0 hφ)).mul hR).indicator
      (X.measurableSet_box n)
  have hGint : Integrable G (X.vol F) :=
    (cf_integrable hD hφ hφ1 hint).integrable_indicator (X.measurableSet_box n)
  set H : XV F → ℂ := fun p => if p.2 ∈ vBox F n then G (ofXV p) else 0 with hH
  have hHm : Measurable H :=
    Measurable.ite (measurable_snd (measurableSet_vBox n)) (hGm.comp measurable_ofXV)
      measurable_const
  have hmp := X.measurePreserving_xv (F := F)
  have hGH : ∀ P : X F, H (P.x, P.v) = G P := by
    intro P
    have hP : ofXV (P.x, P.v) = P := ofXV_toXV P
    simp only [hH, hP]
    split_ifs with hv
    · rfl
    · rw [hG, indicator_of_notMem]
      intro hbox
      exact hv ((mem_box_iff n P).mp hbox).2
  have e1 : cf D n φ R = ∫ p, H p ∂((volume : Measure (InfinitePlace F → ℂ)).prod (X.nuV F)) := by
    unfold cf
    rw [← integral_indicator (X.measurableSet_box n), ← hmp.map_eq,
      integral_map hmp.aemeasurable hHm.aestronglyMeasurable]
    exact integral_congr_ae (Eventually.of_forall fun P => (hGH P).symm)
  have hHint : Integrable H ((volume : Measure (InfinitePlace F → ℂ)).prod (X.nuV F)) := by
    rw [← hmp.integrable_comp hHm.aestronglyMeasurable]
    exact hGint.congr (Eventually.of_forall fun P => (hGH P).symm)
  rw [e1, integral_prod_symm H hHint]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun v => ?_)
  change ∫ x, H (x, v) = 0
  by_cases hv : v ∈ vBox F n
  · have hpos : ∀ w, 0 < v w := fun w => vBox_subset_posSet n hv w (mem_univ _)
    have h1 : ∀ x : InfinitePlace F → ℂ,
        H (x, v) = D.indicator (fun x => conj (φ v) * R (X.mk x v hpos)) x := by
      intro x
      simp only [hH, if_pos hv, ofXV_eq_mk x hpos, hG]
      by_cases hx : x ∈ D
      · have hb : X.mk x v hpos ∈ (X.box n : Set (X F)) := by
          rw [mem_box_iff]
          exact ⟨by simpa using hn x hx, by simpa using hv⟩
        rw [indicator_of_mem hb, indicator_of_mem hx, stripFn_zero]
        simp [indicator_of_mem hx]
      · rw [indicator_of_notMem hx]
        by_cases hb : X.mk x v hpos ∈ (X.box n : Set (X F))
        · rw [indicator_of_mem hb, stripFn_zero]
          simp [indicator_of_notMem hx]
        · rw [indicator_of_notMem hb]
    simp only [h1]
    rw [integral_indicator hD, integral_const_mul, h0 v hpos, mul_zero]
  · simp [hH, if_neg hv]

/-! ### The shape -/

lemma isCompact_box (n : ℕ) : IsCompact (X.box n : Set (X F)) :=
  isCompact_siegelBox (F := F) (m := 1 / ((n : ℝ) + 1)) (M := (n : ℝ) + 1) (B := n)
    (by positivity)

lemma continuous_htC (s : ℂ) : Continuous (htC s : X F → ℂ) := by
  unfold htC
  refine (Complex.continuous_ofReal.comp X.continuous_ht).cpow continuous_const fun P => ?_
  exact Or.inl (by simpa using X.ht_pos P)

lemma integrableOn_htC (s : ℂ) (n : ℕ) : IntegrableOn (htC s : X F → ℂ) (X.box n) (X.vol F) :=
  (continuous_htC s).continuousOn.integrableOn_compact (isCompact_box n)

lemma htC_mk (s : ℂ) (x : InfinitePlace F → ℂ) {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w) :
    htC s (X.mk x v hv) = ∏ w, ((v w : ℝ) : ℂ) ^ s := by
  rw [htC, ht_mk]
  exact cpow_prod_nonneg _ _ (fun w => (hv w).le) s

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.T_Mean
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-T, file 1: strict cells of commensurable lattices (Mathlib only)

`PCell L D`: `D` is a measurable *strict* fundamental set of the subgroup `L` of `E` (every point
has exactly one translate in `D`) — the `hfund` form of WP-X2/WP-RF.

* `PCell.union`: if `L ≤ L₁` and `rep : κ → L₁` is a finite system of representatives of `L₁/L`,
  then `⋃_k (rep k + D)` is a strict cell of `L`.
* `exists_reps`: representatives from `L.relIndex L₁ ≠ 0`.
* **`mean_eq`**: let `D₁`, `D₂` be strict cells of `L₁`, `L₂`, `L ≤ L₁ ⊓ L₂` of finite index in
  both, `f` an `L₁`-periodic function, and suppose `∫_{t + D₂} f = I` for the representatives `t`
  of `L₂/L`.  Then `vol(D₂)·∫_{D₁} f = vol(D₁)·I`.
-/

open MeasureTheory Set

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.T

noncomputable section

universe u

variable {E : Type u} [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd₂ E] [MeasurableNeg E]

variable {L L₁ L₂ : AddSubgroup E} {D D₁ D₂ : Set E}

theorem PCell.isAddFundamentalDomain (h : PCell L D) (μ : Measure E) :
    IsAddFundamentalDomain L D μ :=
  IsAddFundamentalDomain.mk' h.meas.nullMeasurableSet fun x => h.fund x

theorem PCell.shift (h : PCell L D) (t : E) : PCell L (shiftSet t D) := by
  refine ⟨measurableSet_shiftSet t h.meas, fun x => ?_⟩
  obtain ⟨g, hg, hu⟩ := h.fund (x - t)
  refine ⟨g, ?_, fun g' hg' => hu g' ?_⟩
  · change (g : E) + x - t ∈ D
    rwa [add_sub_assoc]
  · have : (g' : E) + x - t ∈ D := hg'
    rwa [add_sub_assoc] at this

section shift

variable {μ : Measure E} [μ.IsAddRightInvariant]

theorem integral_shiftSet (t : E) {D : Set E} (hD : MeasurableSet D) (f : E → ℂ) :
    ∫ x in shiftSet t D, f x ∂μ = ∫ y in D, f (y + t) ∂μ := by
  have h := (measurePreserving_sub_right μ t).setIntegral_preimage_emb
    (MeasurableEquiv.subRight t).measurableEmbedding (fun y => f (y + t)) D
  rw [← h]
  refine setIntegral_congr_fun (measurableSet_shiftSet t hD) fun x _ => ?_
  simp

end shift

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.C9_Const
attribute [-instance] _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-C9, part 2: a `Γ`-invariant function with the constant-term shape is zero

Analytic core of (C10′) (MATH3 §5.1), independent of sections and of θ.

* `integral_conj_eChar_eq_zero`: orthogonality of a nonzero character of the dual lattice over a
  strict cell of `Λ_Γ`.
* **`ae_eq_htC_of_coeff`**: let `f` be measurable, `GammaN Γ`-invariant, `L²` on boxes.  If the
  frequency-`0` functionals of `f` are those of `z·ht^{s₁}` and all functionals at nonzero
  frequencies `ν ∈ Λ_Γ^⊥` vanish, then `f = z·ht^{s₁}` a.e.  (This contains WP-RF's optional
  lemma "nonzero frequencies vanish ⇒ independent of `x`", and its Fubini step, in one
  application of `RF.ae_eq_zero_of_strip` to `f − z·ht^{s₁}`.)
* `isOpenPosMeasure_vol`: `X.vol` is positive on nonempty open sets (chart + positive density).
* `lowInt`, `exists_lower_mem`: a finite-index `Γ` contains `[[1,0],[k,1]]`, `k ≠ 0`.
* `not_ae_ht_smul`: `ht(γP) = ht(P)` a.e. is impossible when the lower left entry of `γ` is
  nonzero (`X.pairHt_mul_pairHt_le`: then `ht² ≤ 1/|N(c)|²` everywhere).
* **`eq_zero_of_lift_ae_eq_htC`**: `u ∈ L²(Γ\X)` with `lift u = z·ht^{s₁}` a.e., `Re s₁ ≠ 0`, is `0`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C9

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F]
  {Γ : Subgroup (SL(2, 𝓞 F))}

/-! ### Characters -/

lemma eChar_add (ν x y : InfinitePlace F → ℂ) : eChar ν (x + y) = eChar ν x * eChar ν y := by
  unfold eChar
  rw [RF.pair_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- A nonzero frequency has a point where the character is `-1`. -/
lemma exists_eChar_ne_one {ν : InfinitePlace F → ℂ} (hν : ν ≠ 0) :
    ∃ b : InfinitePlace F → ℂ, eChar ν b ≠ 1 := by
  set S : ℝ := ∑ w, Complex.normSq (ν w) with hS
  have hSpos : 0 < S := by
    obtain ⟨w, hw⟩ := Function.ne_iff.mp hν
    exact Finset.sum_pos' (fun w _ => Complex.normSq_nonneg _)
      ⟨w, Finset.mem_univ w, Complex.normSq_pos.mpr hw⟩
  refine ⟨fun w => ((1 / (2 * S) : ℝ) : ℂ) * conj (ν w), ?_⟩
  have hp : pair ν (fun w => ((1 / (2 * S) : ℝ) : ℂ) * conj (ν w)) = 1 / 2 := by
    unfold pair
    have h1 : ∀ w, (ν w * (((1 / (2 * S) : ℝ) : ℂ) * conj (ν w))).re
        = 1 / (2 * S) * Complex.normSq (ν w) := fun w => by
      have e : ν w * (((1 / (2 * S) : ℝ) : ℂ) * conj (ν w))
          = ((1 / (2 * S) : ℝ) : ℂ) * (ν w * conj (ν w)) := by ring
      rw [e, Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re]
    simp only [h1]
    rw [← Finset.mul_sum, ← hS]
    field_simp
  unfold eChar
  rw [hp]
  have e : 2 * (Real.pi : ℂ) * Complex.I * (((1 / 2 : ℝ)) : ℂ) = Real.pi * Complex.I := by
    push_cast; ring
  rw [e, Complex.exp_pi_mul_I]
  norm_num

/-- **Orthogonality**: a nonzero character of the dual lattice integrates to `0` over a strict
cell of `Λ_Γ`. -/
theorem integral_conj_eChar_eq_zero {D : Set (InfinitePlace F → ℂ)} (hD : T.PCell (latN Γ) D)
    {ν : InfinitePlace F → ℂ} (hν : ν ∈ dualLat Γ) (h0 : ν ≠ 0) :
    ∫ x in D, conj (eChar ν x) = 0 := by
  obtain ⟨b, hb⟩ := exists_eChar_ne_one h0
  have hinv : ∀ (g : latN Γ) (x : InfinitePlace F → ℂ),
      conj (eChar ν (g +ᵥ x)) = conj (eChar ν x) := by
    intro g x
    obtain ⟨β, hβ, hg⟩ := g.2
    have hint := hν (ofLam ⟨β, hβ⟩)
    rw [shift_ofLam] at hint
    change conj (eChar ν ((g : InfinitePlace F → ℂ) + x)) = _
    rw [add_comm, ← hg, eChar_add_of_int hint]
  have h1 := (hD.isAddFundamentalDomain volume).setIntegral_eq
    ((hD.shift b).isAddFundamentalDomain volume) (f := fun x => conj (eChar ν x)) hinv
  rw [T.integral_shiftSet b hD.meas] at h1
  have h2 : ∫ y in D, conj (eChar ν (y + b))
      = conj (eChar ν b) * ∫ y in D, conj (eChar ν y) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [eChar_add, map_mul]
    ring
  rw [h2] at h1
  have hc : conj (eChar ν b) ≠ 1 := fun h => hb (by
    have := congrArg conj h
    simpa using this)
  have h3 : (1 - conj (eChar ν b)) * ∫ y in D, conj (eChar ν y) = 0 := by
    rw [sub_mul, one_mul, ← h1, sub_self]
  exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr (Ne.symm hc))

/-! ### Strip integrals as box integrals -/

/-- For `n ≥ n₀` (a bound of `D`) the strip integral is the box integral against `stripFn`. -/
lemma strip_eq_box {D : Set (InfinitePlace F → ℂ)} (hD : MeasurableSet D) {n₀ : ℕ}
    (hn₀ : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n₀) {n : ℕ} (hn : n₀ ≤ n) (ν : InfinitePlace F → ℂ)
    (φ : (InfinitePlace F → ℝ) → ℂ) (f : X F → ℂ) :
    ∫ P in (X.x ⁻¹' D ∩ X.v ⁻¹' vBox F n : Set (X F)),
        conj (eChar ν P.x * φ P.v) * f P ∂X.vol F
      = ∫ P in X.box n, conj (stripFn D ν φ P) * f P ∂X.vol F := by
  rw [← integral_indicator (X.measurableSet_box n),
    ← integral_indicator ((X.measurable_x hD).inter (X.measurable_v (measurableSet_vBox n)))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun P => ?_)
  by_cases hx : P.x ∈ D
  · have hiff : P ∈ (X.box n : Set (X F)) ↔ P ∈ (X.x ⁻¹' D ∩ X.v ⁻¹' vBox F n : Set (X F)) := by
      rw [mem_box_iff]
      constructor
      · exact fun hP => ⟨hx, hP.2⟩
      · refine fun hP => ⟨fun w => (hn₀ _ hx w).trans ?_, hP.2⟩
        exact_mod_cast hn
    by_cases hP : P ∈ (X.box n : Set (X F))
    · simp only [indicator_of_mem hP, indicator_of_mem (hiff.mp hP), stripFn,
        indicator_of_mem hx, one_mul]
    · simp only [indicator_of_notMem hP, indicator_of_notMem (fun hc => hP (hiff.mpr hc))]
  · have hP : P ∉ (X.x ⁻¹' D ∩ X.v ⁻¹' vBox F n : Set (X F)) := fun hc => hx hc.1
    simp only [indicator_of_notMem hP]
    by_cases hP' : P ∈ (X.box n : Set (X F))
    · simp only [indicator_of_mem hP', stripFn, indicator_of_notMem hx, zero_mul, map_zero]
    · simp only [indicator_of_notMem hP']

lemma integrableOn_conj_stripFn_mul {D : Set (InfinitePlace F → ℂ)} (hD : MeasurableSet D)
    (ν : InfinitePlace F → ℂ) {φ : (InfinitePlace F → ℝ) → ℂ} (hφ : Measurable φ)
    (hφ1 : ∀ v, ‖φ v‖ ≤ 1) {n : ℕ} {f : X F → ℂ} (hf : IntegrableOn f (X.box n) (X.vol F)) :
    IntegrableOn (fun P => conj (stripFn D ν φ P) * f P) (X.box n) (X.vol F) := by
  refine Integrable.bdd_mul (c := 1) hf
    (Complex.continuous_conj.measurable.comp (measurable_stripFn hD ν hφ)).aestronglyMeasurable ?_
  exact Eventually.of_forall fun P => by
    rw [RCLike.norm_conj]; exact norm_stripFn_le D ν hφ1 P

/-- The functionals of `ht^{s₁}` at nonzero frequencies vanish. -/
theorem coeff_htC_eq_zero {D : Set (InfinitePlace F → ℂ)} (hD : MeasurableSet D)
    (hfund : ∀ x : InfinitePlace F → ℂ, ∃! γ : GammaN Γ, (fun w => x w + GammaN.shift γ w) ∈ D)
    {n : ℕ} (hn : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) {ν : InfinitePlace F → ℂ} (hν : ν ∈ dualLat Γ)
    (h0 : ν ≠ 0) {φ : (InfinitePlace F → ℝ) → ℂ} (hφ : Measurable φ) (hφ1 : ∀ v, ‖φ v‖ ≤ 1)
    (s₁ : ℂ) :
    ∫ P in X.box n, conj (stripFn D ν φ P) * htC s₁ P ∂X.vol F = 0 := by
  set R : X F → ℂ := fun P => conj (eChar ν P.x) * htC s₁ P with hR
  have hRm : Measurable R :=
    (Complex.continuous_conj.measurable.comp ((measurable_eChar ν).comp X.measurable_x)).mul
      (continuous_htC s₁).measurable
  have hRint : IntegrableOn R (X.box n) (X.vol F) := by
    refine Integrable.bdd_mul (c := 1) (integrableOn_htC s₁ n)
      (Complex.continuous_conj.measurable.comp
        ((measurable_eChar ν).comp X.measurable_x)).aestronglyMeasurable ?_
    exact Eventually.of_forall fun P => by
      rw [RCLike.norm_conj, norm_eChar]
  have hfib : ∀ (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w),
      ∫ x in D, R (X.mk x v hv) = 0 := by
    intro v hv
    simp only [hR, X.x_mk, htC_mk]
    rw [integral_mul_const, integral_conj_eChar_eq_zero (T.pcell_of_hfund hD hfund) hν h0,
      zero_mul]
  have h := cf_eq_zero_of_fibers hD hn hφ hφ1 hRm hRint hfib
  rw [← h]
  unfold cf
  refine integral_congr_ae (Eventually.of_forall fun P => ?_)
  simp only [hR, stripFn, eChar_zero, one_mul, map_mul]
  ring

/-! ### The constant-term shape forces the function -/

/-- **A function with the constant-term shape.**  `f` measurable, `GammaN Γ`-invariant, `L²` on
boxes; frequency `0`: `cf D n φ f = z · cf D n φ (ht^{s₁})`; nonzero frequencies of the dual
lattice: all functionals vanish.  Then `f = z·ht^{s₁}` a.e. -/
theorem ae_eq_htC_of_coeff_oai (Γ : Subgroup (SL(2, 𝓞 F)))
    (h𝔫 : ∃ 𝔫 : Ideal (𝓞 F), 𝔫 ≠ ⊥ ∧
      ∀ β ∈ 𝔫, ∃ γ : GammaN Γ, ((γ : Γ) : SL(2, 𝓞 F)) 0 1 = β)
    {D : Set (InfinitePlace F → ℂ)} (hD : MeasurableSet D)
    (hfund : ∀ x : InfinitePlace F → ℂ, ∃! γ : GammaN Γ, (fun w => x w + GammaN.shift γ w) ∈ D)
    (n₀ : ℕ) (hn₀ : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n₀)
    (f : X F → ℂ) (hf : Measurable f) (hinv : ∀ (γ : GammaN Γ) (P : X F), f (γ • P) = f P)
    (hL2 : ∀ n : ℕ, MemLp f 2 ((X.vol F).restrict (X.box n)))
    (hint : ∀ n : ℕ, IntegrableOn f (X.box n) (X.vol F)) (z s₁ : ℂ)
    (h0 : ∀ n : ℕ, n₀ ≤ n → ∀ φ : (InfinitePlace F → ℝ) → ℂ, Measurable φ → (∀ v, ‖φ v‖ ≤ 1) →
      cf D n φ f = z * cf D n φ (htC s₁))
    (h1 : ∀ ν ∈ dualLat Γ, ν ≠ 0 → ∀ n : ℕ, n₀ ≤ n → ∀ φ : (InfinitePlace F → ℝ) → ℂ,
      Measurable φ → (∀ v, ‖φ v‖ ≤ 1) →
      ∫ P in X.box n, conj (stripFn D ν φ P) * f P ∂X.vol F = 0) :
    f =ᵐ[X.vol F] fun P => z * htC s₁ P := by
  set g : X F → ℂ := fun P => f P - z * htC s₁ P with hg
  have hhm : Measurable fun P : X F => z * htC s₁ P :=
    (continuous_htC s₁).measurable.const_mul z
  have hgm : Measurable g := hf.sub hhm
  have hginv : ∀ (γ : GammaN Γ) (P : X F), g (γ • P) = g P := by
    intro γ P
    have hh : htC s₁ (γ • P) = htC s₁ P := by
      rw [GammaN.smul_eq]; rfl
    simp only [hg, hinv, hh]
  have hhint : ∀ n : ℕ, IntegrableOn (fun P : X F => z * htC s₁ P) (X.box n) (X.vol F) :=
    fun n => (integrableOn_htC s₁ n).const_mul z
  have hgL2 : ∀ n : ℕ, MemLp g 2 ((X.vol F).restrict (X.box n)) := by
    intro n
    refine (hL2 n).sub ?_
    obtain ⟨C, hC⟩ := (isCompact_box (F := F) n).exists_bound_of_continuousOn
      (continuous_htC s₁).continuousOn
    have : IsFiniteMeasure ((X.vol F).restrict (X.box n)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact X.vol_box_lt_top n⟩
    refine (MemLp.of_bound (continuous_htC s₁).measurable.aestronglyMeasurable C ?_).const_mul z
    exact (ae_restrict_iff' (X.measurableSet_box n)).mpr (Eventually.of_forall hC)
  have key := ae_eq_zero_of_strip Γ h𝔫 hD hfund g hgm hginv hgL2 n₀ ?_
  · filter_upwards [key] with P hP
    exact sub_eq_zero.mp hP
  intro ν hν n hn φ hφ hφ1
  have hDn : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ (n : ℝ) := fun x hx w =>
    (hn₀ x hx w).trans (by exact_mod_cast hn)
  rw [strip_eq_box hD hn₀ hn]
  have hsplit : ∫ P in X.box n, conj (stripFn D ν φ P) * g P ∂X.vol F
      = (∫ P in X.box n, conj (stripFn D ν φ P) * f P ∂X.vol F)
        - z * ∫ P in X.box n, conj (stripFn D ν φ P) * htC s₁ P ∂X.vol F := by
    rw [← integral_const_mul, ← integral_sub (integrableOn_conj_stripFn_mul hD ν hφ hφ1 (hint n))
      ((integrableOn_conj_stripFn_mul hD ν hφ hφ1 (integrableOn_htC s₁ n)).const_mul z)]
    refine integral_congr_ae (Eventually.of_forall fun P => ?_)
    simp only [hg]
    ring
  rw [hsplit]
  by_cases hν0 : ν = 0
  · subst hν0
    have := h0 n hn φ hφ hφ1
    unfold cf at this
    rw [this, sub_self]
  · rw [h1 ν hν hν0 n hn φ hφ hφ1, coeff_htC_eq_zero hD hfund hDn hν hν0 hφ hφ1, mul_zero,
      sub_zero]

/-! ### `X.vol` is positive on open sets -/

/-! ### Lower unipotent elements -/

/-! ### Step (iii) -/

end

end ArtinKP.C9
end

theorem solution.{u_1} : type_of% @ArtinKP.C9.ae_eq_htC_of_coeff_oai.{u_1} := @ArtinKP.C9.ae_eq_htC_of_coeff_oai.{u_1}
