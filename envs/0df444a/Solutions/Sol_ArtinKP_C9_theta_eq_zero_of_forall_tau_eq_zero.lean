-- Prove2me | solution 1 for ArtinKP.C9.theta_eq_zero_of_forall_tau_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:10:38.135944+00:00
-- url     : https://prove2.me/submissions/fba7b20d-e859-4ed5-b623-d42ec33d94f6

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
import Theorems.Thm_ArtinKP_C9_ae_eq_htC_of_coeff
import Theorems.Thm_ArtinKP_GL_eisEigen_of_two_lt_re
import Theorems.Thm_ArtinKP_N_cf_theta
import Theorems.Thm_ArtinKP_T_coeffFunctional_theta_twist_eq
import Theorems.Thm_ArtinKP_X_X_isPOU_pou
import Theorems.Thm_ArtinKP_X_X_tsum_indicator_box_le_boxMult

section
-- module Solutions.Artin.KP.X_H3
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulGinfX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatComplexH3 _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulGinfX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatComplexH3 _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instSMulInvariantMeasureGinfXVol _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatComplexH3Vol _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatXVol _root_.ArtinKP.X.instSigmaFiniteH3Vol _root_.ArtinKP.X.instSigmaFiniteXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-X, file 1: one factor — hyperbolic 3-space and the action of `SL(2,ℂ)`

`H3 = {(x, v) : ℂ × ℝ | 0 < v}` with the quaternionic Möbius action
`g • (x, v) = (((a x + b) conj(c x + d) + a conj(c) v²) / D, v / D)`,
`D = |c x + d|² + |c|² v²`.  The action axioms are proved through the quaternion `x + v j`:
`a P + b = (g • P) (c P + d)` in `ℍ[ℝ]`.
-/

open scoped MatrixGroups Quaternion ComplexConjugate

namespace ArtinKP.X

noncomputable section

namespace H3

lemma rowDen_nonneg (c d : ℂ) (P : H3) : 0 ≤ rowDen c d P :=
  add_nonneg (Complex.normSq_nonneg _) (mul_nonneg (Complex.normSq_nonneg _) (sq_nonneg _))

end H3

open H3

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Space
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap _root_.ArtinKP.X.chart1_symm_fst _root_.ArtinKP.X.chart1_symm_snd _root_.ArtinKP.X.chart1_v _root_.ArtinKP.X.chart1_x _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
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

lemma pairHt_eq_prod (c d : F) (P : X F) :
    pairHt c d P = ∏ w, P.v w / H3.rowDen (w.embedding c) (w.embedding d) (P w) := by
  unfold pairHt ht pairDen
  rw [Finset.prod_div_distrib]

lemma pairHt_zero_one (P : X F) : pairHt 0 1 P = ht P := by
  simp [pairHt, pairDen, H3.rowDen]

/-- `ht (γ • P) = I_{(c,d)}(P)` for the bottom row `(c, d)` of `γ`. -/
theorem ht_smul (γ : SL(2, F)) (P : X F) : ht (γ • P) = pairHt (γ 1 0) (γ 1 1) P := by
  rw [pairHt_eq_prod]
  exact Finset.prod_congr rfl fun w _ => rfl

end X

/-! ### Topology and measure -/

lemma X.continuous_ht : Continuous (X.ht : X F → ℝ) :=
  continuous_finsetProd _ fun w _ => X.continuous_v w

/-! ### Upper triangular elements, translations and the torus -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Discrete
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma intSL_smul (γ : SL(2, 𝓞 F)) (P : X F) : γ • P = intSL F γ • P := rfl

/-! ### Partition of unity, quotient measure, `L²(Γ\X)` -/

/-! ### The cusp stabilizer -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Disjoint
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap _root_.ArtinKP.X.chart1_symm_snd _root_.ArtinKP.X.chart1_v _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
/-! # WP-X, file 4: disjointness of cusp neighbourhoods

For two pairs `(c,d)`, `(c',d')` with `Δ = c d' - c' d ≠ 0`:
`I_{(c,d)}(P) · I_{(c',d')}(P) ≤ 1 / ∏_w |Δ_w|²`.  With the `S`-normalized heights
`ht^S_{(c,d)} = I_{(c,d)} / ∏_{v ∈ S} max(|c|_v, |d|_v)` and `Δ` an `S`-integer the product formula
gives `ht^S_{(c,d)} · ht^S_{(c',d')} ≤ 1`: the regions `{ht^S_{(c,d)} > 1}` of non-proportional
pairs are disjoint.  No reduction theory is used.
-/

open scoped MatrixGroups ComplexConjugate
open NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

/-- The local inequality: `|c d' - c' d|² v² ≤ (|cx+d|² + |c|²v²)(|c'x+d'|² + |c'|²v²)`. -/
lemma H3.normSq_det_mul_sq_le (c d c' d' : ℂ) (P : H3) :
    Complex.normSq (c * d' - c' * d) * P.v ^ 2 ≤ H3.rowDen c d P * H3.rowDen c' d' P := by
  have hv := P.v_pos
  set A := c * P.x + d with hA
  set A' := c' * P.x + d' with hA'
  have hΔ : c * d' - c' * d = c * A' - c' * A := by rw [hA, hA']; ring
  have h1 : ‖c * d' - c' * d‖ ≤ ‖c‖ * ‖A'‖ + ‖c'‖ * ‖A‖ := by
    rw [hΔ]
    calc ‖c * A' - c' * A‖ ≤ ‖c * A'‖ + ‖c' * A‖ := norm_sub_le _ _
      _ = _ := by rw [norm_mul, norm_mul]
  unfold H3.rowDen
  rw [← hA, ← hA']
  simp only [Complex.normSq_eq_norm_sq]
  have h0 := norm_nonneg (c * d' - c' * d)
  have hc := norm_nonneg c
  have hc' := norm_nonneg c'
  have hAn := norm_nonneg A
  have hAn' := norm_nonneg A'
  have h2 : ‖c * d' - c' * d‖ * P.v ≤ ‖c‖ * P.v * ‖A'‖ + ‖c'‖ * P.v * ‖A‖ := by
    nlinarith
  have h3 : (‖c * d' - c' * d‖ * P.v) ^ 2 ≤ (‖c‖ * P.v * ‖A'‖ + ‖c'‖ * P.v * ‖A‖) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2 2
  nlinarith [sq_nonneg (‖c‖ * P.v * (‖c'‖ * P.v) - ‖A‖ * ‖A'‖)]

variable {F : Type*} [Field F] [NumberField F]

namespace X

/-- **Product of two pair heights** (complex-normalized):
`I_{(c,d)}(P) · I_{(c',d')}(P) ≤ 1 / ∏_w |Δ_w|²`, `Δ = c d' - c' d ≠ 0`. -/
theorem pairHt_mul_pairHt_le {c d c' d' : F} (hΔ : c * d' - c' * d ≠ 0) (P : X F) :
    pairHt c d P * pairHt c' d' P ≤
      (∏ w : InfinitePlace F, Complex.normSq (w.embedding (c * d' - c' * d)))⁻¹ := by
  have h1 : c ≠ 0 ∨ d ≠ 0 := by
    by_contra h; push Not at h; exact hΔ (by rw [h.1, h.2]; ring)
  have h2 : c' ≠ 0 ∨ d' ≠ 0 := by
    by_contra h; push Not at h; exact hΔ (by rw [h.1, h.2]; ring)
  rw [pairHt_eq_prod, pairHt_eq_prod, ← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib]
  refine Finset.prod_le_prod (fun w _ => ?_) (fun w _ => ?_)
  · exact mul_nonneg (div_nonneg (P.v_pos w).le (H3.rowDen_nonneg _ _ _))
      (div_nonneg (P.v_pos w).le (H3.rowDen_nonneg _ _ _))
  · have hD := H3.rowDen_pos (c := w.embedding c) (d := w.embedding d) (by simpa using h1) (P w)
    have hD' := H3.rowDen_pos (c := w.embedding c') (d := w.embedding d') (by simpa using h2) (P w)
    have hN : 0 < Complex.normSq (w.embedding (c * d' - c' * d)) :=
      Complex.normSq_pos.mpr ((map_ne_zero _).mpr hΔ)
    have key := H3.normSq_det_mul_sq_le (w.embedding c) (w.embedding d) (w.embedding c')
      (w.embedding d') (P w)
    rw [← map_mul, ← map_mul, ← map_sub] at key
    change (P w).v / _ * ((P w).v / _) ≤ _
    rw [div_mul_div_comm, div_le_iff₀ (mul_pos hD hD'), inv_mul_eq_div, le_div_iff₀ hN]
    nlinarith

end X

end

end ArtinKP.X
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

theorem archChar_neg (z : ℂ) : archChar (-z) = conj (archChar z) := by
  rw [archChar_eq_re, archChar_eq_re, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.neg_re, map_ofNat]
  push_cast
  ring

/-! ### The `S_f`-character -/

/-! ### The archimedean kernel -/

theorem chiInf_eq_prod (ν : F) (x : InfinitePlace F → ℂ) :
    chiInf ν x = ∏ w, archChar (-(-(w.embedding ν)) * x w) := by
  rw [chiInf, eInf, map_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← archChar_neg, Pi.mul_apply, emb_apply]
  congr 1
  ring

/-! ### Shifted kernels -/

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.B_Kub
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-B, part 9: the Kubota series — convergence, holomorphy, the `E.Kubota` instance

* `kTerm`, `aCoeff`: `𝔞_Φ(ν, s) = ∑_{c ∈ (R∖0)/Rˣ} g(ν, c) · Lam Φ c ν s · N(c)^{-s}`, for every
  `ν ∈ R` (`ν = 0` gives the Dirichlet series of the constant term), with
  `Lam = S2.LamR ψ_{S_f}` (WP-S2's normalized finite Jacquet functional at a valid depth).
* `exists_majorant_kTerm`: locally uniform absolute convergence on `Re s > 2`
  (`|g(ν,c)| ≤ N(c)`, `S2.norm_Lam_le`, S-1, `∑ N(c)^{1-σ} < ∞`).
* `differentiableOn_aCoeff`: holomorphy on `Re s > 2`.
* `kubota hG hz6 : E.Kubota (S2.cubicSymbol …) (B7.sAdd 𝔪 _) (GSection ι P 𝔪)` — no hypothesis left.
* `fourier_coeff_aSer`, `const_term_aCoeff`: the Fourier coefficients in this normalization.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E ArtinKP.K ArtinKP.B7

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

variable [IsTotallyComplex F] (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  (Φ : GSection ι P 𝔪) (ν : SInt 𝔪)

/-- A valid depth exists for every section and frequency. -/
theorem exists_validDepth (ν : F) : ∃ M : ℤ, ValidDepth hG Φ ν M := by
  obtain ⟨M, h1, h2⟩ := S2.exists_valid hG (psiS hG.ne_bot) Φ ν
  exact ⟨M, h1, h2⟩

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.X2_Chart
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.X.e1_one _root_.ArtinKP.X.e1_two _root_.ArtinKP.X.e1_zero
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

lemma map_exp_withDensity :
    Measure.map Real.exp
        ((volume : Measure ℝ).withDensity fun t => ENNReal.ofReal (Real.exp (-2 * t))) =
      ((volume : Measure ℝ).restrict (Ioi 0)).withDensity fun v => ENNReal.ofReal ((v ^ 3)⁻¹) := by
  ext s hs
  rw [Measure.map_apply Real.measurable_exp hs, withDensity_apply _ (Real.measurable_exp hs),
    withDensity_apply _ hs, Measure.restrict_restrict hs]
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := Real.exp ⁻¹' s) (f := Real.exp)
    (f' := Real.exp) (Real.measurable_exp hs)
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun v => ENNReal.ofReal ((v ^ 3)⁻¹))
  rw [image_preimage_eq_inter_range, Real.range_exp] at h
  rw [h]
  refine setLIntegral_congr_fun (Real.measurable_exp hs) fun t _ => ?_
  rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (Real.exp_pos t), ← Real.exp_nat_mul,
    ← Real.exp_neg, ← Real.exp_add]
  congr 2
  push_cast
  ring

lemma map_coe_chart1 : Measure.map (fun p : E1 => (p.1, Real.exp p.2)) mu1 = amb := by
  have h0 : mu1 = (volume : Measure ℂ).prod
      ((volume : Measure ℝ).withDensity fun t => ENNReal.ofReal (Real.exp (-2 * t))) := by
    rw [prod_withDensity_right (by fun_prop)]
    rfl
  have h2 : (volume : Measure ℂ).prod ((volume : Measure ℝ).restrict (Ioi 0)) =
      (volume : Measure (ℂ × ℝ)).restrict upper := by
    have hu : upper = (univ : Set ℂ) ×ˢ Ioi (0 : ℝ) := by
      ext p; simp [upper]
    rw [hu, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have h3 : (fun p : E1 => (p.1, Real.exp p.2)) = Prod.map id Real.exp := rfl
  rw [h0, h3, ← Measure.map_prod_map _ _ measurable_id Real.measurable_exp, Measure.map_id,
    map_exp_withDensity, prod_withDensity_right (by fun_prop), h2]
  rfl

/-- `H3.vol` is the image of `exp (-2t) dx dt` under the chart. -/
theorem map_chart1 : Measure.map chart1 mu1 = H3.vol := by
  have h := map_coe_chart1
  have hc : (fun p : E1 => (p.1, Real.exp p.2)) = H3.coe ∘ chart1 := rfl
  rw [hc, ← Measure.map_map H3.measurableEmbedding_coe.measurable chart1.continuous.measurable] at h
  unfold H3.vol
  rw [← h, H3.measurableEmbedding_coe.comap_map]

/-! ### The product -/

variable (F : Type*) [Field F] [NumberField F]

variable {F}

lemma rho_pos (y : Coord F) : 0 < rho y := Real.exp_pos _

lemma rho_eq_prod (y : Coord F) : rho y = ∏ w, rho1 (y w) := by
  unfold rho rho1
  rw [Finset.mul_sum, Real.exp_sum]

lemma continuous_rho : Continuous (rho : Coord F → ℝ) := by
  unfold rho; fun_prop

variable (F)

lemma muE_eq_pi : muE F = Measure.pi fun _ : InfinitePlace F => mu1 := by
  unfold mu1
  rw [pi_withDensity _ _ (fun _ => by unfold rho1; fun_prop)]
  unfold muE
  congr 1
  funext y
  rw [rho_eq_prod]
  exact ENNReal.ofReal_prod_of_nonneg fun w _ => (Real.exp_pos (-2 * (y w).2)).le

/-- **The chart carries `exp (-2 ∑ t_w) dy` to the invariant measure.** -/
theorem measurePreserving_chart : MeasurePreserving (chart F) (muE F) (X.vol F) := by
  rw [muE_eq_pi]
  exact measurePreserving_pi (fun _ => mu1) (fun _ => H3.vol)
    (fun _ => ⟨chart1.continuous.measurable, map_chart1⟩)

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

lemma coeFn_restrictL2 (hη : IsPOU G η) {B : Set α} (hB : MeasurableSet B) {m : ℝ≥0∞}
    (hmtop : m ≠ ⊤) (hm : ∀ a, ∑' g : G, B.indicator (fun _ => (1 : ℝ≥0∞)) (g • a) ≤ m)
    (u : Lp ℂ 2 (quotMeasure G η μ)) :
    restrictL2 hη hB hmtop hm u =ᵐ[μ.restrict B] liftQ u :=
  MemLp.coeFn_toLp (memLp_liftQ_restrict hη hB hmtop hm u)

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Fourier
attribute [-instance] _root_.ArtinKP.B1.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatSub _root_.ArtinKP.N.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap _root_.ArtinKP.X.chart1_symm_fst _root_.ArtinKP.X.chart1_symm_snd _root_.ArtinKP.X.chart1_v _root_.ArtinKP.X.chart1_x _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
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

lemma X.coeFn_restrictBox (Γ : Subgroup (SL(2, 𝓞 F))) (n : ℕ) (u : X.L2 Γ) :
    X.restrictBox Γ n u =ᵐ[(X.vol F).restrict (X.box n)] X.lift Γ u :=
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  coeFn_restrictL2 _ _ _ _ u

lemma X.coeFn_boxLp (n : ℕ) (ψ : X F → ℂ) (hψ : Measurable ψ) (C : ℝ) (hC : ∀ P, ‖ψ P‖ ≤ C) :
    X.boxLp n ψ hψ C hC =ᵐ[(X.vol F).restrict (X.box n)] ψ :=
  MemLp.coeFn_toLp _

theorem X.coeffFunctional_apply (Γ : Subgroup (SL(2, 𝓞 F))) (n : ℕ) (ψ : X F → ℂ)
    (hψ : Measurable ψ) (C : ℝ) (hC : ∀ P, ‖ψ P‖ ≤ C) (u : X.L2 Γ) :
    X.coeffFunctional Γ n ψ hψ C hC u = ∫ P in X.box n, conj (ψ P) * X.lift Γ u P ∂X.vol F := by
  unfold X.coeffFunctional
  rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [X.coeFn_restrictBox Γ n u, X.coeFn_boxLp n ψ hψ C hC] with P h1 h2
  rw [h1, h2]
  simp [mul_comm]

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_H1
attribute [-instance] _root_.ArtinKP.B1.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatSub _root_.ArtinKP.N.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-X2, file 5: the geometric core and the energy space `H¹(Γ \ X)`

* `X.toL2 Γ f h : L²(Γ\X)` — the class of a measurable `Γ`-invariant function that is square
  integrable modulo `Γ` (`X.L2Rep Γ f`), with `X.inner_toL2`, `X.norm_sq_toL2`;
* `X.core Γ` — the functions `∑_{γ ∈ Γ} φ ∘ γ`, `φ ∈ C_c^∞(X)` (equivalently: smooth,
  `Γ`-invariant, support compact modulo `Γ`; see `X.mem_core_of_tsupport` in `X2_Weak`);
* `X.symmOp Γ : SymmOp (L²(Γ\X))` — the Laplacian on the core: dense domain, symmetric,
  nonnegative, with `⟪w, Δw⟫ = ∫_{Γ\X} ∑_w v_w² |∇_w w|²` (`X.inner_coreL2_coreLap_self`);
* `X.H1 Γ`, `X.energy Γ : CAbs.EnergySpace (X.H1 Γ) (X.L2 Γ)`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F] (Γ : Subgroup (SL(2, 𝓞 F)))

/-! ### Classes of invariant functions -/

variable {Γ}

variable (Γ)

variable {Γ}

variable (Γ)

variable {Γ}

/-- An element of `L²(Γ\X)` whose pull-back vanishes almost everywhere is zero. -/
lemma X.eq_zero_of_lift_ae_eq_zero (v : X.L2 Γ) (h : X.lift Γ v =ᵐ[X.vol F] 0) : v = 0 := by
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have hm : MeasurableSet {q : Quotient (MulAction.orbitRel Γ (X F)) | v q = (0 : ℂ)} :=
    (Lp.stronglyMeasurable v).measurable (measurableSet_singleton 0)
  have key : ∀ᵐ q ∂(Measure.map (Quotient.mk (MulAction.orbitRel Γ (X F)))
      ((X.vol F).withDensity (X.pou Γ))),
      q ∈ {q : Quotient (MulAction.orbitRel Γ (X F)) | v q = (0 : ℂ)} :=
    (ae_map_iff measurable_mk.aemeasurable hm).2
      ((withDensity_absolutelyContinuous _ _).ae_le h)
  exact key

/-! ### Local integrability of pull-backs -/

/-! ### The core -/

/-! ### Density of the core -/

/-! ### The symmetric operator and the energy space -/

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
-- module Solutions.Artin.KP.N_Shape
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma Cell.mono {D : Set (InfinitePlace F → ℂ)} {n₀ n : ℕ} (h : Cell Γ D n₀) (hn : n₀ ≤ n) :
    Cell Γ D n :=
  ⟨h.meas, h.fund, fun x hx w => (h.bdd x hx w).trans (by exact_mod_cast hn)⟩

/-! ### The constant-term functional -/

/-! ### Fubini: a function with vanishing `x`-integrals over `D` is killed by `cf` -/

/-! ### The shape -/

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.N_Level
attribute [-instance] _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-N, file 5: `θ_Ψ` under change of `Γ` and under `SL₂(R)` (C5's open item 3; MATH2 §2.1 end)

* `ae_eq_zero_of_box_tests`: a locally integrable function killed by all bounded test functions on
  all boxes vanishes almost everywhere.
* **`lift_theta_of_eis_smul`**: if `E_{Ψ'}(Q, s) = E_Ψ(τQ, s)` for `Re s > 2` (`τ ∈ SL₂(F)`), then
  `θ_{Γ'}(Ψ') = θ_Γ(Ψ) ∘ τ` almost everywhere, for any finite-index `Γ`, `Γ'` fixing `Ψ`, `Ψ'`.
* `lift_theta_congr`: `θ_Γ(Ψ)` does not depend on `Γ` (as a function on `X`, a.e.).
* `lift_theta_translate`: `θ(σ·Ψ)(Q) = θ(Ψ)(σ⁻¹Q)` for `σ ∈ SL₂(R)`.
* `cf_theta_translate`: the constant term of `θ_Ψ` at the cusp `σ⁻¹∞`, i.e. of `Q ↦ θ_Ψ(σ⁻¹Q)` at
  `∞`, is `zRes(σ·Ψ)·ht^{2/3}`.
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
  {ι : F →+* ℂ}

/-! ### Test functions on boxes -/

lemma integrableOn_lift (Γ : Subgroup (SL(2, 𝓞 F))) (n : ℕ) (u : X.L2 Γ) :
    IntegrableOn (X.lift Γ u) (X.box n) (X.vol F) :=
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  (memLp_liftQ_restrict (X.isPOU_pou Γ) (X.measurableSet_box n) (ENNReal.natCast_ne_top _)
    (X.tsum_indicator_box_le_boxMult Γ n) u).integrable one_le_two

/-! ### Transport of a box integral by `τ ∈ SL₂(F)` -/

/-! ### `θ` under a transformation of the series -/

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.C9_Const
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
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

/-! ### Strip integrals as box integrals -/

/-! ### The constant-term shape forces the function -/

/-! ### `X.vol` is positive on open sets -/

theorem isOpenPosMeasure_vol : (X.vol F).IsOpenPosMeasure := by
  refine ⟨fun U hU hne h0 => ?_⟩
  have h1 : muE F (chart F ⁻¹' U) = 0 := by
    rw [(measurePreserving_chart F).measure_preimage hU.nullMeasurableSet]
    exact h0
  have hac : (volume : Measure (Coord F)) ≪ muE F := by
    unfold muE
    refine withDensity_absolutelyContinuous' ?_ ?_
    · exact (ENNReal.measurable_ofReal.comp continuous_rho.measurable).aemeasurable
    · exact Eventually.of_forall fun y => by
        simpa using rho_pos y
  have h2 : (volume : Measure (Coord F)) (chart F ⁻¹' U) = 0 := hac h1
  have hopen : IsOpen (chart F ⁻¹' U) := hU.preimage (chart F).continuous
  have hne' : (chart F ⁻¹' U).Nonempty := by
    obtain ⟨P, hP⟩ := hne
    exact ⟨(chart F).symm P, by simpa using hP⟩
  exact (hopen.measure_pos volume hne').ne' h2

/-! ### Lower unipotent elements -/

lemma lowInt_coe (β : 𝓞 F) : (lowInt β : Matrix (Fin 2) (Fin 2) (𝓞 F)) = !![1, 0; β, 1] := rfl

lemma lowInt_add (β β' : 𝓞 F) : lowInt (β + β') = lowInt β * lowInt β' := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowInt_coe, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

lemma lowInt_zero : lowInt (0 : 𝓞 F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowInt_coe]

lemma lowInt_pow (β : 𝓞 F) (n : ℕ) : lowInt β ^ n = lowInt ((n : 𝓞 F) * β) := by
  induction n with
  | zero => simp [lowInt_zero]
  | succ n ih =>
    rw [pow_succ, ih, ← lowInt_add]
    congr 1
    push_cast
    ring

/-- A finite-index subgroup contains a lower unipotent element with nonzero corner. -/
theorem exists_lower_mem (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex] :
    ∃ γ ∈ Γ, (γ 1 0 : 𝓞 F) ≠ 0 := by
  refine ⟨lowInt 1 ^ (Γ.index).factorial, RC.pow_factorial_index_mem Γ _, ?_⟩
  rw [lowInt_pow, mul_one]
  change (((Γ.index).factorial : ℕ) : 𝓞 F) ≠ 0
  exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)

/-- `ht ∘ γ = ht` a.e. is impossible when the lower left entry of `γ` is nonzero. -/
theorem not_ae_ht_smul (γ : SL(2, 𝓞 F)) (hc : (γ 1 0 : 𝓞 F) ≠ 0) :
    ¬ ∀ᵐ P ∂X.vol F, X.ht (γ • P) = X.ht P := by
  intro h
  have := isOpenPosMeasure_vol (F := F)
  have hcont : Continuous fun P : X F => X.ht (γ • P) :=
    X.continuous_ht.comp (continuous_const_smul γ)
  have hall : (fun P : X F => X.ht (γ • P)) = fun P : X F => X.ht P :=
    (hcont.ae_eq_iff_eq (X.vol F) X.continuous_ht).mp h
  set c : F := algebraMap (𝓞 F) F (γ 1 0) with hcdef
  set d : F := algebraMap (𝓞 F) F (γ 1 1) with hddef
  have hc' : c ≠ 0 := by
    rw [hcdef]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr hc
  have hΔ : (0 : F) * d - c * 1 ≠ 0 := by
    rw [zero_mul, zero_sub, mul_one]
    exact neg_ne_zero.mpr hc'
  set B : ℝ := (∏ w : InfinitePlace F, Complex.normSq (w.embedding ((0 : F) * d - c * 1)))⁻¹
    with hB
  have hbound : ∀ P : X F, X.ht P * X.ht P ≤ B := by
    intro P
    have h1 := X.pairHt_mul_pairHt_le hΔ P
    have h2 : X.ht (γ • P) = X.pairHt c d P := by
      rw [intSL_smul, X.ht_smul]
      rfl
    have h3 : X.ht (γ • P) = X.ht P := congrFun hall P
    rw [X.pairHt_zero_one, ← h2, h3] at h1
    exact h1
  set t : ℝ := max 1 (B + 1) with ht
  have ht1 : 1 ≤ t := le_max_left _ _
  have htpos : ∀ w : InfinitePlace F, 0 < (fun _ : InfinitePlace F => t) w :=
    fun _ => lt_of_lt_of_le one_pos ht1
  have hP := hbound (X.mk 0 (fun _ => t) htpos)
  rw [ht_mk, Finset.prod_const] at hP
  have hcard : (Finset.univ : Finset (InfinitePlace F)).card ≠ 0 :=
    Finset.card_ne_zero.mpr Finset.univ_nonempty
  have h4 : t ≤ t ^ (Finset.univ : Finset (InfinitePlace F)).card := le_self_pow₀ ht1 hcard
  have h5 : t * 1 ≤ t ^ (Finset.univ : Finset (InfinitePlace F)).card
      * t ^ (Finset.univ : Finset (InfinitePlace F)).card :=
    mul_le_mul h4 (ht1.trans h4) zero_le_one (le_trans (by positivity) h4)
  have h6 : B + 1 ≤ t := le_max_right _ _
  linarith

/-! ### Step (iii) -/

/-- **`z·ht^{s₁}` is not `Γ`-invariant.**  If `u ∈ L²(Γ\X)` has `lift u = z·ht^{s₁}` a.e. with
`Re s₁ ≠ 0`, then `u = 0`. -/
theorem eq_zero_of_lift_ae_eq_htC (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex] (u : X.L2 Γ)
    (z : ℂ) {s₁ : ℂ} (hs₁ : s₁.re ≠ 0)
    (h : X.lift Γ u =ᵐ[X.vol F] fun P => z * htC s₁ P) : u = 0 := by
  apply X.eq_zero_of_lift_ae_eq_zero
  by_cases hz : z = 0
  · filter_upwards [h] with P hP
    rw [hP, hz, zero_mul]
    rfl
  exfalso
  obtain ⟨γ, hγ, hc⟩ := exists_lower_mem Γ
  refine not_ae_ht_smul γ hc ?_
  have hγae : ∀ᵐ P ∂X.vol F, X.lift Γ u (γ • P) = z * htC s₁ (γ • P) :=
    (X.measurePreserving_smul (intSL F γ)).quasiMeasurePreserving.ae h
  filter_upwards [h, hγae] with P hP hγP
  have hinv : X.lift Γ u (γ • P) = X.lift Γ u P := X.lift_smul Γ u ⟨γ, hγ⟩ P
  rw [hγP, hP] at hinv
  have h1 : htC s₁ (γ • P) = htC s₁ P := mul_left_cancel₀ hz hinv
  have h2 := congrArg norm h1
  unfold htC at h2
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (X.ht_pos _),
    Complex.norm_cpow_eq_rpow_re_of_pos (X.ht_pos _)] at h2
  exact Real.rpow_left_injOn hs₁ (X.ht_pos _).le (X.ht_pos _).le h2

end

end ArtinKP.C9
end

section
-- module Solutions.Artin.KP.C9_Main
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
/-!
# WP-C9, part 3: (C10′) in terms of coefficient functionals; a single big cell with `θ ≠ 0`

* **`eq_zero_of_coeff_shape`**: `u ∈ L²(Γ\X)` whose frequency-`0` functionals are those of
  `z·ht^{s₁}` (`Re s₁ ≠ 0`) and whose functionals at all nonzero frequencies of `Λ_Γ^⊥` vanish
  is `0`.
* **`theta_eq_zero_of_coeff`** — (C10′), the core: if all nonzero-frequency coefficient
  functionals of `θ_Ψ` at `∞` vanish, then `θ_Ψ = 0` (and `zRes_eq_zero_of_coeff`: `z_Ψ = 0`).
  Stated for a twisted section `Ψ` and WP-RF's functionals; no dependence on WP-T.
* `lift_zero_ae`, `theta_eq_zero_congr`: `θ_Ψ = 0` does not depend on the group `Γ`.
* `twist_add`, `twist_zero`, `exists_inv_finset`, `theta_sum_eq_zero`: linearity bookkeeping.
* **`exists_theta_bigCell_ne_zero`**: some single big-cell section `Φ^big_η`, `η ∈ T`, has
  `θ ≠ 0` (for every finite-index `Γ` fixing its twist).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C9

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

/-! ### (C10′), the core -/

/-- **An `L²` class with the constant-term shape and no other frequency is zero.** -/
theorem eq_zero_of_coeff_shape (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    {D : Set (InfinitePlace F → ℂ)} (hD : MeasurableSet D)
    (hfund : ∀ x : InfinitePlace F → ℂ, ∃! γ : GammaN Γ, (fun w => x w + GammaN.shift γ w) ∈ D)
    {n₀ : ℕ} (hn₀ : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n₀) (u : X.L2 Γ) (z : ℂ) {s₁ : ℂ} (hs₁ : s₁.re ≠ 0)
    (h0 : ∀ n : ℕ, n₀ ≤ n → ∀ φ : (InfinitePlace F → ℝ) → ℂ, Measurable φ → (∀ v, ‖φ v‖ ≤ 1) →
      cf D n φ (X.lift Γ u) = z * cf D n φ (htC s₁))
    (h : ∀ ν ∈ dualLat Γ, ν ≠ 0 → ∀ n : ℕ, n₀ ≤ n → ∀ (φ : (InfinitePlace F → ℝ) → ℂ)
      (hφ : Measurable φ) (hφ1 : ∀ v, ‖φ v‖ ≤ 1),
      X.coeffFunctional Γ n (stripFn D ν φ) (measurable_stripFn hD ν hφ) 1
        (norm_stripFn_le D ν hφ1) u = 0) :
    u = 0 := by
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  refine eq_zero_of_lift_ae_eq_htC Γ u z hs₁ ?_
  refine ae_eq_htC_of_coeff Γ (exists_ideal_translations Γ) hD hfund n₀ hn₀ (X.lift Γ u)
    (X.stronglyMeasurable_lift Γ u).measurable (fun γ P => X.lift_smul Γ u (γ : Γ) P)
    (fun n => memLp_liftQ_restrict (X.isPOU_pou Γ) (X.measurableSet_box n)
      (ENNReal.natCast_ne_top _) (X.tsum_indicator_box_le_boxMult Γ n) u)
    (fun n => integrableOn_lift Γ n u) z s₁ h0 ?_
  intro ν hν hν0 n hn φ hφ hφ1
  rw [← X.coeffFunctional_apply Γ n (stripFn D ν φ) (measurable_stripFn hD ν hφ) 1
    (norm_stripFn_le D ν hφ1) u]
  exact h ν hν hν0 n hn φ hφ hφ1

/-- **(C10′), core form.**  Let `Ψ` be a twisted section fixed by the finite-index group `Γ`,
`D` a bounded measurable strict cell of the translations of `Γ`.  If all coefficient functionals
of `θ_Ψ` at the nonzero frequencies `ν ∈ Λ_Γ^⊥` vanish, then `θ_Ψ = 0`. -/
theorem theta_eq_zero_of_coeff (hG : Good 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) {D : Set (InfinitePlace F → ℂ)} (hD : MeasurableSet D)
    (hfund : ∀ x : InfinitePlace F → ℂ, ∃! γ : GammaN Γ, (fun w => x w + GammaN.shift γ w) ∈ D)
    {n₀ : ℕ} (hn₀ : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n₀)
    (h : ∀ ν ∈ dualLat Γ, ν ≠ 0 → ∀ n : ℕ, n₀ ≤ n → ∀ (φ : (InfinitePlace F → ℝ) → ℂ)
      (hφ : Measurable φ) (hφ1 : ∀ v, ‖φ v‖ ≤ 1),
      X.coeffFunctional Γ n (stripFn D ν φ) (measurable_stripFn hD ν hφ) 1
        (norm_stripFn_le D ν hφ1) (theta Γ Ψ) = 0) :
    theta Γ Ψ = 0 := by
  have hcell : Cell Γ D n₀ := Cell.of_hfund hD hfund hn₀
  have hE : ∀ s : ℂ, 2 < s.re → EisEigen Ψ s := fun s hs => GL.eisEigen_of_two_lt_re hG.ne_bot Ψ hs
  refine eq_zero_of_coeff_shape Γ hD hfund hn₀ (theta Γ Ψ) (zRes Γ Ψ D (n₀ + 1))
    (s₁ := 2 / 3) (by norm_num) ?_ h
  intro n hn φ hφ hφ1
  exact cf_theta hG hΓ hE (hcell.mono (Nat.le_succ n₀)) (Nat.succ_le_succ (Nat.zero_le n₀))
    (hcell.mono hn) hφ hφ1

/-! ### Independence of `Γ` -/

/-! ### Linearity bookkeeping -/

/-! ### A single big cell -/

end

end ArtinKP.C9
end

section
-- module Solutions.Artin.KP.T_Coef
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-T, file 4: the `ν`-th coefficient of `E_Φ` over a cell, for `Re s > 2`

* `freq ν = (−2σ_w ν)_w`: `conj (RF.eChar (freq ν) x) = B.chiInf ν x`, so that
  `X.coeffFunctional Γ n (RF.stripFn D (freq ν) φ) …` is the `ν`-th coefficient against `conj φ`.
* `HasCoefT Ψ ν' a₀ D κ` (twisted section, any coefficient series `a₀`): for `Re s > 2` and all
  `v`, `∫_D E_Ψ(x, v) conj e_∞(ν'x) dx = vol(D)·κ·W_s(ν'; v)·a₀(s)`;
  `HasCoef hG hz6 Φ ν D κ` is the case `Ψ = Φ.twist`, `a₀ = 𝔞_Φ(ν, ·)`.
  - `hasCoef_transLat`: a strict cell of `Λ_M` (`M ≥ 0` valid) has it with `κ = kap 𝔪 M` (WP-B);
  - **`hasCoef_latN`**: so has every bounded strict cell of the translation lattice of any `Γ`
    fixing `Φ.twist`, provided `conj e_∞(ν·)` is `Λ_Γ`-periodic (`T.mean_eq`).
* `Afun Γ Ψ n ψ s = ∫_{box n} conj ψ · lift (resPart Γ Ψ s) + ∫_{box n} conj ψ · h_s`: holomorphic
  on `E.slit`, `= ∫_{box n} conj ψ · E_Ψ` for `Re s > 2`, ray limit `∫ conj ψ · θ`.
* `Wc D n φ ν s = N.cf D n φ (WX s ν)`: holomorphic on `Re s > 1`; `exists_Wc_ne_zero`.
* **`Afun_eq_of_hasCoefT`**: `Afun … (stripFn D (freq ν') φ) s = κ·a₀(s)·Wc D n φ ν' s`, `Re s > 2`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.T

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

/-! ### The frequency of `ν` in WP-RF's parametrization -/

theorem conj_eChar_freq (ν : F) (x : InfinitePlace F → ℂ) :
    conj (eChar (freq ν) x) = chiInf ν x := by
  have h1 : chiInf ν x = Complex.exp (2 * Real.pi * Complex.I *
      ((∑ w : InfinitePlace F, 2 * (w.embedding ν * x w).re : ℝ) : ℂ)) := by
    rw [chiInf_eq_prod]
    simp only [archChar_eq_re, neg_neg]
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum]
  have h2 : pair (freq ν) x = -∑ w : InfinitePlace F, 2 * (w.embedding ν * x w).re := by
    unfold pair freq
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    have e : -2 * w.embedding ν * x w = ((-2 : ℝ) : ℂ) * (w.embedding ν * x w) := by
      push_cast; ring
    rw [e, Complex.re_ofReal_mul]
    ring
  rw [h1, eChar, h2, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

/-! ### Cells that compute the coefficient -/

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (Φ : GSection ι P 𝔪)
  (ν : SInt 𝔪)

theorem validDepth_mono {ν' : F} {M M' : ℤ} (h : ValidDepth hG Φ ν' M) (hMM : M ≤ M') :
    ValidDepth hG Φ ν' M' :=
  ⟨fun b hb => h.unip b (hb.mono hMM), fun x hx => h.char x (hx.mono hMM)⟩

theorem exists_validDepth_nonneg (ν' : F) : ∃ M : ℤ, 0 ≤ M ∧ ValidDepth hG Φ ν' M := by
  obtain ⟨M, hM⟩ := exists_validDepth hG Φ ν'
  exact ⟨max M 0, le_max_right _ _, validDepth_mono hG Φ hM (le_max_left _ _)⟩

/-! ### The coefficient function of the continuation -/

/-! ### The archimedean factor -/

/-! ### The coefficient of the series over an admissible cell -/

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.T_Theta
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-T, file 6: genuine sections — `aCont`, `tau`, the instance `E.Theta`, coefficients of `θ`

For `ν ∈ R ∖ 0` and a genuine section `Φ` (`Ψ = Φ.twist hG hz6`, `a₀ = (B.kubota hG hz6).aSer Φ ν`):

* `aCont hG hz6 Φ ν = contSlit a₀` — holomorphic on `E.slit` (`differentiableOn_aCont`), equal to
  the series on `Re s > 2` (`aCont_eq`), unique (`aCont_unique`);
* `tau hG hz6 Φ ν = resSlit a₀ = lim_{t↓0} (s_t − 4/3)·aCont(s_t)` (`tendsto_tau`);
* **`theta hG hz6 : E.Theta (B.kubota hG hz6) (4/3)`** with `toResFun = E.resFunSlit`;
* **`coeff_theta`** (item 3): the Fourier coefficients of `C5.theta Γ (Φ.twist)` for the cells of
  any `Γ`; `coeff_cont`: the same for the continuation on `E.slit`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.T

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (Φ : GSection ι P 𝔪)
  (ν : SInt 𝔪)

variable {ν}

/-! ### The archimedean factor as an integral over `v` -/


/-! ### Fourier coefficients of `θ` for the cells of `Γ` -/

/-- `freq ν` in WP-RF's dual lattice gives the periodicity hypothesis. -/
lemma chiInf_of_mem_dualLat {Γ : Subgroup (SL(2, 𝓞 F))} {ν' : F} (h : freq ν' ∈ dualLat Γ)
    (β : 𝓞 F) (hβ : β ∈ lamN Γ) : chiInf ν' (emb (β : F)) = 1 := by
  obtain ⟨m, hm⟩ := h (ofLam ⟨β, hβ⟩)
  rw [shift_ofLam] at hm
  rw [← conj_eChar_freq, eChar]
  have e : (emb (β : F) : InfinitePlace F → ℂ) = embO β := rfl
  rw [e, hm]
  have : Complex.exp (2 * Real.pi * Complex.I * ((m : ℝ) : ℂ)) = 1 := by
    have := Complex.exp_int_mul_two_pi_mul_I m
    rw [← this]; congr 1; push_cast; ring
  rw [this, map_one]

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.C9_Tau
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-C9, part 4: (C10′) and (C9) in the vocabulary of WP-T (`T.tau`, `T.theta`)

WP-T's `T.coeff_theta` computes the coefficient functional of `θ_{Φ.twist}` at the frequency
`T.freq ν`, `ν ∈ R ∖ 0` (`R = SInt 𝔪`), as `kap · τ_Φ(ν) · Wc`.  The core lemma
`C9.theta_eq_zero_of_coeff` needs the vanishing at **every** nonzero frequency of WP-RF's dual
lattice `RF.dualLat Γ`.  The bridge is the one named hypothesis of this file:

* `DualCover 𝔪 Γ`: every nonzero `ν' ∈ RF.dualLat Γ` is `T.freq ν` for some `ν ∈ R`.
  (True when `Λ_Γ ⊇ emb(𝔪^N)` — `TransLevel 𝔪 Γ` — and the different of `F` is supported in the
  primes of `𝔪`: trace duality.  Proved in `C9_Dual.lean` / stated in `C9_Stubs.lean`, see
  WP-C9.md.)

Results:

* `stabGroup Ψ` (the full stabilizer of `Ψ` in `SL₂(𝓞)`), finite index, `TransLevel` for twists.
* **`theta_eq_zero_of_tau`** — (C10′) in WP-T's form: `τ_Φ(ν) = 0` for all `ν ∈ R ∖ 0` implies
  `θ_{Φ.twist} = 0`.
* **`exists_tau_sumBig_ne_zero`**, **`exists_tau_bigCell_ne_zero`** — the hypothesis of package
  G (MATH3 §1.2 (G1)): some `τ_{Φ^Σ}(ν₁) ≠ 0`, and some single class `η` with
  `τ_{Φ^big_η}(ν) ≠ 0`.
* `exists_kir_ne_zero_of_theoremE`: given Theorem E in any form `τ_Φ(ν) = c(ν)·𝒦_Φ(ν)`, the
  Kirillov function is not identically zero.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C9

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

/-! ### The full stabilizer -/

/-! ### The bridge between the two parametrizations of the frequencies -/

lemma freq_zero : T.freq (0 : F) = 0 := by
  funext w
  simp [T.freq]

/-! ### (C10′) in WP-T's form -/

section tau

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-- **(C10′), WP-T's form.**  If `τ_Φ(ν) = 0` for every `ν ∈ R ∖ 0`, then `θ_{Φ.twist} = 0`
(for every finite-index `Γ` fixing the twist whose dual lattice is covered by `R`). -/
theorem theta_eq_zero_of_forall_tau_eq_zero_oai (Φ : GSection ι P 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    (hΓ : Inv Γ (Φ.twist hG hz6)) (hdual : DualCover 𝔪 Γ)
    (h : ∀ ν : SInt 𝔪, ν ≠ 0 → T.tau hG hz6 Φ ν = 0) :
    C5.theta Γ (Φ.twist hG hz6) = 0 := by
  obtain ⟨D, hD, hbdd, hfund⟩ := exists_fundamental_translations Γ (exists_ideal_translations Γ)
  obtain ⟨R, hR⟩ := hbdd.exists_norm_le
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge R
  have hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ (n₀ : ℝ) := fun x hx w =>
    (norm_le_pi_norm x w).trans ((hR x hx).trans hn₀)
  refine theta_eq_zero_of_coeff hG Γ hΓ hD hfund hb ?_
  intro ν' hν' hν'0 n hn φ hφ hφ1
  obtain ⟨ν, rfl⟩ := hdual ν' hν' hν'0
  have hν : ν ≠ 0 := by
    rintro rfl
    exact hν'0 freq_zero
  obtain ⟨M, hM, hV⟩ := T.exists_validDepth_nonneg hG Φ ((ν : SInt 𝔪) : F)
  have hbn : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ (n : ℝ) := fun x hx w =>
    (hb x hx w).trans (by exact_mod_cast hn)
  rw [T.coeffFunctional_theta_twist_eq hG hz6 Φ hν hM hV Γ hΓ hD hfund hbn (T.chiInf_of_mem_dualLat hν') hφ hφ1,
    h ν hν, mul_zero, zero_mul]

end tau

/-! ### The hypothesis of package G -/

end

end ArtinKP.C9
end

theorem solution.{u_1} : type_of% @ArtinKP.C9.theta_eq_zero_of_forall_tau_eq_zero_oai.{u_1} := @ArtinKP.C9.theta_eq_zero_of_forall_tau_eq_zero_oai.{u_1}
