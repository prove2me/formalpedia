-- Prove2me | solution 1 for ArtinKP.N.Acoef_cross
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:10:43.663086+00:00
-- url     : https://prove2.me/submissions/e6ca5cb4-f7b9-49e3-9bdd-fb8ef2662400

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
import Theorems.Thm_ArtinKP_N_Acoef_eq
import Theorems.Thm_ArtinKP_N_differentiableOn_Acoef

section
-- module Solutions.Artin.KP.X_Space
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
-- module Solutions.Artin.KP.C5_Holo
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-C5, file 2: bounded holomorphic families are holomorphic into `L²(Γ\X)`

Finite volume is a hypothesis here (`hvol : X.quotVol Γ univ < ⊤`; WP-RC's `quotVol_univ_lt_top`).

* `l2Rep_of_bdd`, `norm_toL2_le`: a bounded measurable `Γ`-invariant function is in `L²(Γ\X)`,
  with norm `≤ vol^{1/2} · sup`.
* `norm_sub_sub_le`: second-order Cauchy/Schwarz estimate
  `|f(z) − f(c) − (z−c) f'(c)| ≤ 4B R⁻² |z−c|²` for `f` holomorphic and bounded by `B` on `B(c,R)`.
* `differentiable_toL2`: if `s ↦ f_s(P)` is entire for every `P` and `f` is bounded on
  `ball × X` near every `s₀`, then `s ↦ [f_s] ∈ L²(Γ\X)` is entire.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C5

open ArtinKP.X

noncomputable section

/-- Second-order estimate for a bounded holomorphic function on a disc. -/
lemma norm_sub_sub_le {f : ℂ → ℂ} {c : ℂ} {R B : ℝ} (hR : 0 < R)
    (hd : DifferentiableOn ℂ f (ball c R)) (hB : ∀ z ∈ ball c R, ‖f z‖ ≤ B) {z : ℂ}
    (hz : z ∈ ball c R) :
    ‖f z - f c - (z - c) * deriv f c‖ ≤ 4 * B / R ^ 2 * ‖z - c‖ ^ 2 := by
  have hc : c ∈ ball c R := mem_ball_self hR
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB c hc)
  have hm1 : MapsTo f (ball c R) (closedBall (f c) (2 * B)) := fun w hw => by
    rw [mem_closedBall, dist_eq_norm]
    calc ‖f w - f c‖ ≤ ‖f w‖ + ‖f c‖ := norm_sub_le _ _
      _ ≤ 2 * B := by linarith [hB w hw, hB c hc]
  have hD : ∀ w ∈ ball c R, ‖dslope f c w‖ ≤ 2 * B / R := fun w hw =>
    Complex.norm_dslope_le_div_of_mapsTo_ball hd hm1 hw
  have hdD : DifferentiableOn ℂ (dslope f c) (ball c R) :=
    (Complex.differentiableOn_dslope (ball_mem_nhds c hR)).mpr hd
  have hm2 : MapsTo (dslope f c) (ball c R) (closedBall (dslope f c c) (4 * B / R)) :=
    fun w hw => by
      rw [mem_closedBall, dist_eq_norm]
      calc ‖dslope f c w - dslope f c c‖ ≤ ‖dslope f c w‖ + ‖dslope f c c‖ := norm_sub_le _ _
        _ ≤ 2 * B / R + 2 * B / R := add_le_add (hD w hw) (hD c hc)
        _ = 4 * B / R := by ring
  have h2 := Complex.dist_le_div_mul_dist_of_mapsTo_ball hdD hm2 hz
  rw [dist_eq_norm, dist_eq_norm, dslope_same] at h2
  rcases eq_or_ne z c with rfl | hne
  · simp
  · have hzc : z - c ≠ 0 := sub_ne_zero.mpr hne
    have e : f z - f c - (z - c) * deriv f c = (z - c) * (dslope f c z - deriv f c) := by
      rw [dslope_of_ne _ hne, slope_def_module, smul_eq_mul]
      field_simp
    rw [e, norm_mul]
    calc ‖z - c‖ * ‖dslope f c z - deriv f c‖ ≤ ‖z - c‖ * (4 * B / R / R * ‖z - c‖) :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = 4 * B / R ^ 2 * ‖z - c‖ ^ 2 := by ring

/-- The derivative of a bounded holomorphic function at the centre of a disc. -/
lemma norm_deriv_le {f : ℂ → ℂ} {c : ℂ} {R B : ℝ} (hR : 0 < R)
    (hd : DifferentiableOn ℂ f (ball c R)) (hB : ∀ z ∈ ball c R, ‖f z‖ ≤ B) :
    ‖deriv f c‖ ≤ 2 * B / R := by
  have hc : c ∈ ball c R := mem_ball_self hR
  have hm1 : MapsTo f (ball c R) (closedBall (f c) (2 * B)) := fun w hw => by
    rw [mem_closedBall, dist_eq_norm]
    calc ‖f w - f c‖ ≤ ‖f w‖ + ‖f c‖ := norm_sub_le _ _
      _ ≤ 2 * B := by linarith [hB w hw, hB c hc]
  have := Complex.norm_dslope_le_div_of_mapsTo_ball hd hm1 hc
  rwa [dslope_same] at this

end

end ArtinKP.C5
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
-- module Solutions.Artin.KP.N_Cont
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
/-! # WP-N, file 3: coefficients of `θ_Ψ` from continuations (MATH2 §2.1(c),(d); item 5)

* `differentiableAt_setIntegral`: a bounded holomorphic family integrates to a holomorphic function
  over a set of finite measure.
* `hInt Ψ n ψ s = ∫_{box n} conj ψ · h_s` is entire (`differentiable_hInt`).
* **`coeff_theta_of_continuation`** (all frequencies): if `a` is holomorphic on `E.slit`, equals
  `∫_{box n} conj ψ · E_Ψ(·, s)` for `Re s > 2`, and `(s_t − s₀) a(s_t) → r` along C5's ray, then
  `∫_{box n} conj ψ · θ_Ψ = r`.
* **`cf_theta_of_continuation`** (frequency `0`, MATH2 §2.1(d)): if `m'` is holomorphic on `E.slit`,
  equals `mD D Ψ` for `Re s > 2` and `(s_t − s₀) m'(s_t) → z`, then
  `cf D n φ (θ_Ψ) = z · cf D n φ (ht^{2/3})` for all `(n, φ)`.

`EisEigen Ψ s` (owner WP-RF) enters as the hypothesis `hE : ∀ s, 2 < s.re → EisEigen Ψ s`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF

noncomputable section

/-! ### Holomorphic dependence of integrals on a parameter -/

/-- A family `f s`, measurable in `a`, holomorphic in `s` on a disc and bounded there uniformly
on `K`, has a holomorphic integral over `K` (`μ K < ∞`). -/
theorem differentiableAt_setIntegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {K : Set α} (hK : MeasurableSet K) (hμ : μ K ≠ ⊤) {f : ℂ → α → ℂ} {s₀ : ℂ} {R B₀ : ℝ}
    (hR : 0 < R) (hmeas : ∀ s ∈ ball s₀ R, Measurable (f s))
    (hdiff : ∀ a ∈ K, DifferentiableOn ℂ (fun s => f s a) (ball s₀ R))
    (hB₀ : ∀ s ∈ ball s₀ R, ∀ a ∈ K, ‖f s a‖ ≤ B₀) :
    DifferentiableAt ℂ (fun s => ∫ a in K, f s a ∂μ) s₀ := by
  have : IsFiniteMeasure (μ.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]; exact hμ.lt_top⟩
  have hs₀ : s₀ ∈ ball s₀ R := mem_ball_self hR
  set B : ℝ := max B₀ 0 with hBdef
  have hB0 : 0 ≤ B := le_max_right _ _
  have hB : ∀ s ∈ ball s₀ R, ∀ a ∈ K, ‖f s a‖ ≤ B := fun s hs a ha =>
    (hB₀ s hs a ha).trans (le_max_left _ _)
  set g : α → ℂ := fun a => deriv (fun s => f s a) s₀ with hg
  have hgb : ∀ a ∈ K, ‖g a‖ ≤ 2 * B / R := fun a ha =>
    C5.norm_deriv_le hR (hdiff a ha) fun z hz => hB z hz a ha
  -- measurability of the derivative on `K`
  set k : ℕ → ℂ := fun n => ((R / 2 : ℝ) : ℂ) / ((n : ℂ) + 1) with hk
  have hk0 : ∀ n, k n ≠ 0 := fun n => by
    rw [hk]
    exact div_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) (Nat.cast_add_one_ne_zero n)
  have hkR : ∀ n, s₀ + k n ∈ ball s₀ R := fun n => by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, hk, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < R / 2)]
    have h1 : (1 : ℝ) ≤ ‖((n : ℂ) + 1)‖ := by
      have : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    calc R / 2 / ‖((n : ℂ) + 1)‖ ≤ R / 2 / 1 :=
          div_le_div_of_nonneg_left (by positivity) one_pos h1
      _ < R := by linarith
  have hkt : Tendsto k atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)).const_mul (((R / 2 : ℝ) : ℂ))
    simpa [hk, div_eq_mul_inv] using this
  have hgK : Measurable (K.indicator g) := by
    refine measurable_of_tendsto_metrizable
      (f := fun n => K.indicator fun a => (k n)⁻¹ * (f (s₀ + k n) a - f s₀ a))
      (fun n => (((hmeas _ (hkR n)).sub (hmeas _ hs₀)).const_mul _).indicator hK) ?_
    rw [tendsto_pi_nhds]
    intro a
    by_cases ha : a ∈ K
    · simp only [indicator_of_mem ha]
      have h1 := ((hdiff a ha).differentiableAt (ball_mem_nhds s₀ hR)).hasDerivAt.tendsto_slope
      have h2 : Tendsto (fun n => s₀ + k n) atTop (𝓝[≠] s₀) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
        · simpa using (tendsto_const_nhds (x := s₀)).add hkt
        · simpa using hk0 n
      refine (h1.comp h2).congr fun n => ?_
      simp [slope_def_module]
    · simp only [indicator_of_notMem ha]
      exact tendsto_const_nhds
  have hgint : Integrable g (μ.restrict K) :=
    Integrable.of_bound (hgK.aestronglyMeasurable.congr (indicator_ae_eq_restrict hK))
      (2 * B / R) (ae_restrict_of_forall_mem hK hgb)
  have hfint : ∀ s ∈ ball s₀ R, Integrable (f s) (μ.restrict K) := fun s hs =>
    Integrable.of_bound (hmeas s hs).aestronglyMeasurable B
      (ae_restrict_of_forall_mem hK (hB s hs))
  refine (HasDerivAt.differentiableAt (f' := ∫ a in K, g a ∂μ) ?_)
  rw [hasDerivAt_iff_isLittleO]
  set V : ℝ := (μ.restrict K).real univ with hV
  have key : ∀ z ∈ ball s₀ R,
      ‖(∫ a in K, f z a ∂μ) - (∫ a in K, f s₀ a ∂μ) - (z - s₀) • ∫ a in K, g a ∂μ‖ ≤
        (4 * B / R ^ 2) * V * ‖z - s₀‖ ^ 2 := by
    intro z hz
    have e : (∫ a in K, f z a ∂μ) - (∫ a in K, f s₀ a ∂μ) - (z - s₀) • ∫ a in K, g a ∂μ
        = ∫ a in K, (f z a - f s₀ a - (z - s₀) * g a) ∂μ := by
      have i1 : Integrable (fun a => f z a - f s₀ a) (μ.restrict K) :=
        (hfint z hz).sub (hfint s₀ hs₀)
      have i2 : Integrable (fun a => (z - s₀) * g a) (μ.restrict K) := hgint.const_mul _
      rw [integral_sub i1 i2, integral_sub (hfint z hz) (hfint s₀ hs₀), integral_const_mul,
        smul_eq_mul]
    rw [e]
    have hb' : ∀ a ∈ K, ‖f z a - f s₀ a - (z - s₀) * g a‖ ≤ 4 * B / R ^ 2 * ‖z - s₀‖ ^ 2 :=
      fun a ha => C5.norm_sub_sub_le hR (hdiff a ha) (fun w hw => hB w hw a ha) hz
    have := norm_integral_le_of_norm_le_const (μ := μ.restrict K)
      (ae_restrict_of_forall_mem hK hb')
    calc _ ≤ 4 * B / R ^ 2 * ‖z - s₀‖ ^ 2 * V := this
      _ = _ := by ring
  have hO : (fun z => (∫ a in K, f z a ∂μ) - (∫ a in K, f s₀ a ∂μ)
      - (z - s₀) • ∫ a in K, g a ∂μ) =O[𝓝 s₀] fun z => ‖z - s₀‖ ^ 2 := by
    refine Asymptotics.IsBigO.of_bound ((4 * B / R ^ 2) * V) ?_
    filter_upwards [ball_mem_nhds s₀ hR] with z hz
    rw [norm_pow, norm_norm]
    exact key z hz
  exact hO.trans_isLittleO (Asymptotics.isLittleO_pow_sub_sub s₀ one_lt_two)

/-! ### The ray and the slit -/

lemma isOpen_slit : IsOpen E.slit := by
  have h : E.slit = {s : ℂ | 1 < s.re} ∩ ({s : ℂ | s.im ≠ 0} ∪ {s : ℂ | 2 < s.re}) := by
    ext s
    simp only [E.slit, mem_ofPred_eq, mem_inter_iff, mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by by_cases h : s.im = 0; exacts [Or.inr (h2 h), Or.inl h]⟩
    · rintro ⟨h1, h2 | h2⟩
      · exact ⟨h1, fun h => absurd h h2⟩
      · exact ⟨h1, fun _ => h2⟩
  rw [h]
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_ne_fun Complex.continuous_im continuous_const).union
      (isOpen_lt continuous_const Complex.continuous_re))

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {Γ : Subgroup (SL(2, 𝓞 F))}

/-! ### The cut-off part against a bounded test function -/

/-! ### Coefficients of `θ_Ψ` from a continuation (all test functions) -/

/-! ### Frequency `0`: the residue of the `ht^{2−s}`-coefficient -/

theorem differentiable_cf_htC {D : Set (InfinitePlace F → ℂ)} (hD : MeasurableSet D) (n : ℕ)
    {φ : (InfinitePlace F → ℝ) → ℂ} (hφ : Measurable φ) (hφ1 : ∀ v, ‖φ v‖ ≤ 1) :
    Differentiable ℂ fun s : ℂ => cf D n φ (htC s) := by
  intro s₀
  have hcont : Continuous fun z : ℂ × X F => ‖((X.ht z.2 : ℝ) : ℂ) ^ z.1‖ :=
    ((Complex.continuous_ofReal.comp (X.continuous_ht.comp continuous_snd)).cpow continuous_fst
      fun z => Or.inl (by simpa using X.ht_pos z.2)).norm
  obtain ⟨B, hB⟩ := ((isCompact_closedBall s₀ 1).prod (isCompact_box (F := F) n)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine differentiableAt_setIntegral (X.measurableSet_box n) (X.vol_box_lt_top n).ne
    (R := 1) (B₀ := B) one_pos
    (fun s _ => (Complex.continuous_conj.measurable.comp (measurable_stripFn hD 0 hφ)).mul
      (continuous_htC s).measurable)
    (fun P _ => ?_) (fun s hs P hP => ?_)
  · refine (Differentiable.const_mul ?_ _).differentiableOn
    unfold htC
    exact differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr (X.ht_pos P).ne'))
  · rw [norm_mul, RCLike.norm_conj]
    have h1 := hB (s, P) ⟨ball_subset_closedBall hs, hP⟩
    rw [norm_norm] at h1
    calc ‖stripFn D 0 φ P‖ * ‖htC s P‖ ≤ 1 * ‖htC s P‖ :=
          mul_le_mul_of_nonneg_right (norm_stripFn_le D 0 hφ1 P) (norm_nonneg _)
      _ ≤ B := by rw [one_mul]; exact h1

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.N_Res
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.S2.cubicSymbol_sym
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

/-! ### The coefficient function `Acoef` and the cross identity -/

section

variable (hG : Good 𝔪) [Γ.FiniteIndex] {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ)
  (hE : ∀ s : ℂ, 2 < s.re → EisEigen Ψ s) {D : Set (InfinitePlace F → ℂ)} {n n' : ℕ}
  {φ φ' : (InfinitePlace F → ℝ) → ℂ}

include hG hΓ hE in
/-- **The cross identity on `E.slit`** (MATH2 §2.1(c)). -/
theorem Acoef_cross_oai (hD : Cell Γ D n) (hφ : Measurable φ) (hφ1 : ∀ v, ‖φ v‖ ≤ 1)
    (hD' : Cell Γ D n') (hφ' : Measurable φ') (hφ1' : ∀ v, ‖φ' v‖ ≤ 1) {s : ℂ}
    (hs : s ∈ E.slit) :
    Acoef Γ Ψ D n φ s * cf D n' φ' (htC (2 - s))
      = Acoef Γ Ψ D n' φ' s * cf D n φ (htC (2 - s)) := by
  have hP : Differentiable ℂ fun s : ℂ => cf D n φ (htC (2 - s)) :=
    (differentiable_cf_htC hD.meas n hφ hφ1).comp ((differentiable_const (2 : ℂ)).sub
      differentiable_id)
  have hP' : Differentiable ℂ fun s : ℂ => cf D n' φ' (htC (2 - s)) :=
    (differentiable_cf_htC hD'.meas n' hφ' hφ1').comp ((differentiable_const (2 : ℂ)).sub
      differentiable_id)
  have hl : DifferentiableOn ℂ (fun s => Acoef Γ Ψ D n φ s * cf D n' φ' (htC (2 - s))) E.slit :=
    (differentiableOn_Acoef hG hΓ hD.meas n hφ hφ1).mul hP'.differentiableOn
  have hr : DifferentiableOn ℂ (fun s => Acoef Γ Ψ D n' φ' s * cf D n φ (htC (2 - s))) E.slit :=
    (differentiableOn_Acoef hG hΓ hD'.meas n' hφ' hφ1').mul hP.differentiableOn
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ) (z₀ := (3 : ℂ))
    (hl.analyticOnNhd isOpen_slit) (hr.analyticOnNhd isOpen_slit)
    E.isPreconnected_slit ⟨by norm_num, fun _ => by norm_num⟩ ?_ hs
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show (2 : ℝ) < (3 : ℂ).re by norm_num)] with s hs
  have hs' : 2 < s.re := hs
  simp only [Acoef_eq hG hΓ hD hφ hφ1 hs' (hE s hs'),
    Acoef_eq hG hΓ hD' hφ' hφ1' hs' (hE s hs')]
  ring

/-! ### The continued coefficient and its residue -/

end

/-! ### `‖θ‖² = −c₀⟪F, θ⟫` -/

end

end ArtinKP.N
end

theorem solution.{u_1} : type_of% @ArtinKP.N.Acoef_cross_oai.{u_1} := @ArtinKP.N.Acoef_cross_oai.{u_1}
