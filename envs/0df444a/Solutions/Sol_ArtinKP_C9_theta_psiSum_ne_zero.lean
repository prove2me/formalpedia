-- Prove2me | solution 1 for ArtinKP.C9.theta_psiSum_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:04:29.955372+00:00
-- url     : https://prove2.me/submissions/3a816a6c-81a1-4e13-b756-60daf3eb6a78

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
import Theorems.Thm_ArtinKP_BZ_exists_mean_eis_sumBig_eq_pole_four_thirds
import Theorems.Thm_ArtinKP_GL_eisEigen_of_two_lt_re
import Theorems.Thm_ArtinKP_N_integral_box_theta_eq_of_tendsto_ray
import Theorems.Thm_ArtinKP_X_X_isPOU_pou
import Theorems.Thm_ArtinKP_X_X_tsum_indicator_box_le_boxMult

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

namespace H3

lemma rowDen_nonneg (c d : ℂ) (P : H3) : 0 ≤ rowDen c d P :=
  add_nonneg (Complex.normSq_nonneg _) (mul_nonneg (Complex.normSq_nonneg _) (sq_nonneg _))

end H3

open H3

lemma smul_def (g : SL(2, ℂ)) (P : H3) : g • P = mob g P := rfl

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

lemma sigma_apply (γ : SL(2, F)) (w : InfinitePlace F) (i j : Fin 2) :
    (sigma F γ w) i j = w.embedding (γ i j) := rfl

variable {F}

namespace X

lemma ht_pos (P : X F) : 0 < ht P := Finset.prod_pos fun w _ => P.v_pos w

lemma pairDen_pos {c d : F} (h : c ≠ 0 ∨ d ≠ 0) (P : X F) : 0 < pairDen c d P :=
  Finset.prod_pos fun w _ => H3.rowDen_pos (by simpa using h) (P w)

lemma pairDen_nonneg (c d : F) (P : X F) : 0 ≤ pairDen c d P :=
  Finset.prod_nonneg fun w _ => H3.rowDen_nonneg _ _ _

lemma pairHt_pos {c d : F} (h : c ≠ 0 ∨ d ≠ 0) (P : X F) : 0 < pairHt c d P :=
  div_pos (ht_pos P) (pairDen_pos h P)

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
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap _root_.ArtinKP.X.chart1_symm_fst _root_.ArtinKP.X.chart1_symm_snd _root_.ArtinKP.X.chart1_v _root_.ArtinKP.X.chart1_x _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
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

/-- `ht (γ • P) = ht P` for `γ ∈ Γ_∞` (units have norm one). -/
theorem ht_smul_of_upper [IsTotallyComplex F] {γ : SL(2, 𝓞 F)} (h : γ 1 0 = 0) (P : X F) :
    X.ht (γ • P) = X.ht P := by
  have h1 : X.ht (γ • P) = X.pairHt ((intSL F γ) 1 0) ((intSL F γ) 1 1) P := X.ht_smul _ P
  rw [h1, intSL_apply, intSL_apply, h, map_zero]
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two, h, mul_zero, sub_zero] at hdet
  have hunit : IsUnit (γ 1 1) := IsUnit.of_mul_eq_one (γ 0 0) (by rw [mul_comm]; exact hdet)
  have hN : |Algebra.norm ℚ (algebraMap (𝓞 F) F (γ 1 1))| = 1 := by
    have := (NumberField.isUnit_iff_norm (K := F)).mp hunit
    simpa [RingOfIntegers.coe_norm] using this
  have hden : ∀ w : InfinitePlace F,
      H3.rowDen (w.embedding 0) (w.embedding (algebraMap (𝓞 F) F (γ 1 1))) (P w) =
        (w (algebraMap (𝓞 F) F (γ 1 1))) ^ w.mult := by
    intro w
    rw [IsTotallyComplex.mult_eq]
    simp [H3.rowDen, Complex.normSq_eq_norm_sq, InfinitePlace.norm_embedding_eq]
  unfold X.pairHt X.pairDen
  simp_rw [hden]
  rw [InfinitePlace.prod_eq_abs_norm, hN]
  simp

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Units
attribute [-instance] _root_.ArtinKP.B1.PairClass.instNonempty _root_.ArtinKP.B1.instDiscreteTopologySubtypeE₂MemSubmoduleIntPairLattice _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instDiscreteTopologySubtypeMixedSpaceMemSubmoduleIntLattice _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
/-! # WP-X, file 10: Dirichlet's unit theorem and the cusp section

The unit lattice is cocompact in the trace-zero hyperplane of the logarithmic space, hence:
there is `C ≥ 1` such that for every `v ∈ (ℝ_{>0})^r` there is a unit `ε` with all the numbers
`|ε_w|² v_w` within the ratio `C` of each other (`exists_unit_balanced`).  For `X` this says that
every point is `diag(ε, ε⁻¹)`-equivalent to one with balanced heights; in particular the
norm-one slice `{∏ v_w = 1}` modulo units is covered by the compact cube `[C⁻¹, C]^r`
(`exists_unit_smul_balanced`, `balanced_bounds`).  Only place where the unit rank enters.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

open scoped Classical in
/-- The unit lattice is cocompact: every vector of the logarithmic space is within a fixed
distance of the image of a unit. -/
lemma exists_unit_logEmbedding_close :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ y : logSpace F, ∃ ε : (𝓞 F)ˣ,
      ‖y - logEmbedding F (Additive.ofMul ε)‖ ≤ C₀ := by
  classical
  let b := (basisUnitLattice F).ofZLatticeBasis ℝ (unitLattice F)
  refine ⟨∑ i, ‖b i‖, Finset.sum_nonneg fun i _ => norm_nonneg _, fun y => ?_⟩
  have hfl : ((ZSpan.floor b y : Submodule.span ℤ (Set.range b)) : logSpace F) ∈ unitLattice F := by
    have h : ((ZSpan.floor b y : Submodule.span ℤ (Set.range b)) : logSpace F) ∈
        Submodule.span ℤ (Set.range b) := (ZSpan.floor b y).2
    exact ((basisUnitLattice F).ofZLatticeBasis_span ℝ).le h
  obtain ⟨x, -, hx⟩ := hfl
  refine ⟨Additive.toMul x, ?_⟩
  have h1 : logEmbedding F (Additive.ofMul (Additive.toMul x)) = (ZSpan.floor b y : logSpace F) := hx
  rw [h1, ← ZSpan.fract_apply]
  exact ZSpan.norm_fract_le b y

/-- **Dirichlet's unit theorem, balanced form** (totally complex field): for every positive `v`
there is a unit `ε` such that the numbers `|ε_w|² v_w` are within ratio `C` of each other. -/
theorem exists_unit_balanced [IsTotallyComplex F] :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ v : InfinitePlace F → ℝ, (∀ w, 0 < v w) → ∃ ε : (𝓞 F)ˣ,
      ∀ w w' : InfinitePlace F,
        (w (ε : F)) ^ 2 * v w ≤ C * ((w' (ε : F)) ^ 2 * v w') := by
  classical
  obtain ⟨C₀, hC₀, hclose⟩ := exists_unit_logEmbedding_close (F := F)
  set r : ℝ := (Fintype.card (InfinitePlace F) : ℝ) with hr
  have hr1 : 1 ≤ r := by
    rw [hr]; exact_mod_cast Fintype.card_pos
  set C₁ : ℝ := r * C₀ with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  refine ⟨Real.exp (2 * C₁), by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by positivity), ?_⟩
  intro v hv
  set m : ℝ := (∑ w, Real.log (v w)) / r with hm
  obtain ⟨ε, hε⟩ := hclose (fun w => m - Real.log (v w.1))
  have hεpos : ∀ w : InfinitePlace F, 0 < w (ε : F) := fun w =>
    InfinitePlace.pos_iff.mpr (by simp)
  set c : InfinitePlace F → ℝ := fun w => 2 * Real.log (w (ε : F)) + Real.log (v w) - m with hc
  have hc1 : ∀ w : {w : InfinitePlace F // w ≠ w₀}, |c w.1| ≤ C₀ := by
    intro w
    have h1 := (norm_le_pi_norm _ w).trans hε
    rw [Pi.sub_apply, logEmbedding_component, IsTotallyComplex.mult_eq, Real.norm_eq_abs] at h1
    have h2 : -c w.1 = m - Real.log (v w.1) - ((2 : ℕ) : ℝ) * Real.log (w.1 (ε : F)) := by
      rw [hc]; push_cast; ring
    rw [← abs_neg, h2]
    exact h1
  have hsum : ∑ w, c w = 0 := by
    have h0 := sum_mult_mul_log ε
    simp_rw [IsTotallyComplex.mult_eq] at h0
    simp only [hc, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    have h2 : ∑ w : InfinitePlace F, 2 * Real.log (w (ε : F)) = 0 := by exact_mod_cast h0
    rw [h2, hm, ← hr]
    field_simp
    ring
  have hc0 : |c w₀| ≤ C₁ := by
    rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at hsum
    have h1 : c w₀ = -∑ w : {w : InfinitePlace F // w ≠ w₀}, c w.1 := by linarith
    rw [h1, abs_neg]
    calc |∑ w : {w : InfinitePlace F // w ≠ w₀}, c w.1|
        ≤ ∑ w : {w : InfinitePlace F // w ≠ w₀}, |c w.1| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _w : {w : InfinitePlace F // w ≠ w₀}, C₀ := Finset.sum_le_sum fun w _ => hc1 w
      _ = (Fintype.card {w : InfinitePlace F // w ≠ w₀} : ℝ) * C₀ := by simp
      _ ≤ r * C₀ := by
          gcongr
          rw [hr]
          exact_mod_cast Fintype.card_subtype_le _
  have hcall : ∀ w, |c w| ≤ C₁ := by
    intro w
    by_cases hw : w = w₀
    · rw [hw]; exact hc0
    · exact (hc1 ⟨w, hw⟩).trans (by rw [hC₁]; nlinarith)
  have hexp : ∀ w, (w (ε : F)) ^ 2 * v w = Real.exp (c w) * Real.exp m := by
    intro w
    rw [← Real.exp_add, hc]
    have : 2 * Real.log (w (ε : F)) + Real.log (v w) - m + m =
        Real.log ((w (ε : F)) ^ 2 * v w) := by
      rw [Real.log_mul (pow_pos (hεpos w) 2).ne' (hv w).ne', Real.log_pow]
      push_cast; ring
    rw [this, Real.exp_log (mul_pos (pow_pos (hεpos w) 2) (hv w))]
  refine ⟨ε, fun w w' => ?_⟩
  have h1 := abs_le.mp (hcall w)
  have h2 := abs_le.mp (hcall w')
  rw [hexp w, hexp w']
  calc Real.exp (c w) * Real.exp m ≤ Real.exp (2 * C₁ + c w') * Real.exp m :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos m).le
    _ = Real.exp (2 * C₁) * (Real.exp (c w') * Real.exp m) := by rw [Real.exp_add]; ring

/-- A balanced positive vector with product `h` has all coordinates comparable to `h^{1/r}`:
`v_w^r ≤ C^r ∏ v` and `∏ v ≤ C^r v_w^r`. -/
lemma balanced_bounds {ι : Type*} [Fintype ι] {C : ℝ} (hC : 0 ≤ C) {v : ι → ℝ}
    (hv : ∀ i, 0 < v i) (hbal : ∀ i j, v i ≤ C * v j) (i : ι) :
    v i ^ Fintype.card ι ≤ C ^ Fintype.card ι * ∏ j, v j ∧
      ∏ j, v j ≤ C ^ Fintype.card ι * v i ^ Fintype.card ι := by
  constructor
  · calc v i ^ Fintype.card ι = ∏ _j : ι, v i := by simp
      _ ≤ ∏ j, C * v j := Finset.prod_le_prod (fun _ _ => (hv i).le) fun j _ => hbal i j
      _ = C ^ Fintype.card ι * ∏ j, v j := by simp [Finset.prod_mul_distrib]
  · calc ∏ j, v j ≤ ∏ _j : ι, C * v i :=
        Finset.prod_le_prod (fun j _ => (hv j).le) fun j _ => hbal j i
      _ = C ^ Fintype.card ι * v i ^ Fintype.card ι := by simp [mul_pow]

lemma unitDiag_coe (ε : (𝓞 F)ˣ) :
    (unitDiag ε : Matrix (Fin 2) (Fin 2) (𝓞 F)) = !![(ε : 𝓞 F), 0; 0, ((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F)] :=
  rfl

lemma unitDiag_smul_v (ε : (𝓞 F)ˣ) (P : X F) (w : InfinitePlace F) :
    (unitDiag ε • P).v w = (w (ε : F)) ^ 2 * P.v w := by
  have h := (smul_of_upper (γ := unitDiag ε) (by simp [unitDiag_coe]) P w).2
  rw [h, Complex.normSq_eq_norm_sq, InfinitePlace.norm_embedding_eq]
  simp [unitDiag_coe]

/-- **The cusp section is compact modulo units**: every point of `X` has a translate by a diagonal
unit matrix (an element of `Γ_∞` for `Γ = SL(2,𝓞_F)`) whose heights are balanced. -/
theorem exists_unit_smul_balanced [IsTotallyComplex F] :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : X F, ∃ ε : (𝓞 F)ˣ, ∀ w w' : InfinitePlace F,
      (unitDiag ε • P).v w ≤ C * (unitDiag ε • P).v w' := by
  obtain ⟨C, hC, h⟩ := exists_unit_balanced (F := F)
  refine ⟨C, hC, fun P => ?_⟩
  obtain ⟨ε, hε⟩ := h P.v P.v_pos
  exact ⟨ε, fun w w' => by rw [unitDiag_smul_v, unitDiag_smul_v]; exact hε w w'⟩

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.B1_Lattice
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.B.coe_latREquiv _root_.ArtinKP.B.embR_apply
/-! # WP-B1, file 1: the lattice `𝓞_F² ⊂ ℂ^r × ℂ^r` and the Minkowski bound for the top height

`F` totally complex, `ι = InfinitePlace F`.  `emb : F →+ (ι → ℂ)` is the diagonal embedding,
`latE` the `ℝ`-basis of `ι → ℂ` given by an integral basis, `pairLattice` the `ℤ`-span of the
product basis of `(ι → ℂ) × (ι → ℂ)`; it is exactly `{(emb c, emb d) | c d ∈ 𝓞_F}` (`mem_pairLattice`).

**Lemma M** (`exists_integer_pair_pairHt_ge`): there is `c₀ > 0` such that for every `P ∈ X` some
nonzero pair `(c,d) ∈ 𝓞_F²` has `I_{(c,d)}(P) ≥ c₀`.  Proof: Minkowski's convex body theorem for the
body `{|c_w| ≤ λ/√v_w, |c_w x_w + d_w| ≤ λ√v_w}`, whose volume `(π²λ⁴)^r` does not depend on `P`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.B1

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

variable [IsTotallyComplex F]

theorem mem_pairLattice {z : E₂ F} :
    z ∈ pairLattice F ↔ ∃ c d : 𝓞 F, z = (emb (c : F), emb (d : F)) := by
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      rcases i with i | i
      · exact ⟨RingOfIntegers.basis F i, 0, by simp [pairBasis, latE_apply]⟩
      · exact ⟨0, RingOfIntegers.basis F i, by simp [pairBasis, latE_apply]⟩
    | zero => exact ⟨0, 0, Prod.ext (by simp) (by simp)⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, d, rfl⟩ := hx
      obtain ⟨c', d', rfl⟩ := hy
      exact ⟨c + c', d + d', by simp⟩
    | smul n x _ hx =>
      obtain ⟨c, d, rfl⟩ := hx
      have h : ∀ a : 𝓞 F, ((n • a : 𝓞 F) : F) = n • (a : F) := fun a => by simp [zsmul_eq_mul]
      exact ⟨n • c, n • d, by rw [h, h, map_zsmul, map_zsmul]; rfl⟩
  · rintro ⟨c, d, rfl⟩
    have h1 : (emb (c : F), (0 : InfinitePlace F → ℂ)) ∈ pairLattice F := by
      rw [emb_int_eq_sum, show ((∑ i, (RingOfIntegers.basis F).repr c i • latE i,
          (0 : InfinitePlace F → ℂ)) : E₂ F) =
          ∑ i, (RingOfIntegers.basis F).repr c i • pairBasis (Sum.inl i) by
        simp [pairBasis, Prod.ext_iff, Prod.fst_sum, Prod.snd_sum]]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    have h2 : ((0 : InfinitePlace F → ℂ), emb (d : F)) ∈ pairLattice F := by
      rw [emb_int_eq_sum, show (((0 : InfinitePlace F → ℂ),
          ∑ i, (RingOfIntegers.basis F).repr d i • latE i) : E₂ F) =
          ∑ i, (RingOfIntegers.basis F).repr d i • pairBasis (Sum.inr i) by
        simp [pairBasis, Prod.ext_iff, Prod.fst_sum, Prod.snd_sum]]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    have := Submodule.add_mem _ h1 h2
    simpa using this

instance instCountableSubtypeE₂MemSubmoduleIntPairLattice : Countable (pairLattice F) := by
  haveI _iCO := ArtinKP.X.instCountableRingOfIntegers (F := F)
  have : Function.Surjective (fun p : 𝓞 F × 𝓞 F =>
      (⟨(emb (p.1 : F), emb (p.2 : F)), mem_pairLattice.mpr ⟨p.1, p.2, rfl⟩⟩ : pairLattice F)) := by
    rintro ⟨z, hz⟩
    obtain ⟨c, d, rfl⟩ := mem_pairLattice.mp hz
    exact ⟨(c, d), rfl⟩
  exact this.countable

lemma finrank_pairLattice :
    Module.finrank ℤ (pairLattice F) = 4 * Fintype.card (InfinitePlace F) := by
  have b := (pairBasis (F := F)).restrictScalars ℤ
  have h := Module.finrank_eq_card_basis b
  unfold pairLattice
  rw [h, Fintype.card_sum, ← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank,
    IsTotallyComplex.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero]
  ring

/-! ### The Minkowski body -/

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.X_Disjoint
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

variable {F : Type*} [Field F] [NumberField F]

namespace X

lemma sNorm_pos (S : Finset (FinitePlace F)) {c d : F} (h : c ≠ 0 ∨ d ≠ 0) : 0 < sNorm S c d :=
  Finset.prod_pos fun v _ => by
    rcases h with h | h
    · exact lt_max_of_lt_left (FinitePlace.pos_iff.mpr h)
    · exact lt_max_of_lt_right (FinitePlace.pos_iff.mpr h)

lemma sHt_pos (S : Finset (FinitePlace F)) {c d : F} (h : c ≠ 0 ∨ d ≠ 0) (P : X F) :
    0 < sHt S c d P := div_pos (pairHt_pos h P) (sNorm_pos S h)

end X

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.B1_Conv
attribute [-instance] _root_.ArtinKP.B1.PairClass.instNonempty _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instDiscreteTopologySubtypeMixedSpaceMemSubmoduleIntLattice _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.B.coe_latREquiv _root_.ArtinKP.B.embR_apply _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap _root_.ArtinKP.X.chart1_symm_fst _root_.ArtinKP.X.chart1_symm_snd _root_.ArtinKP.X.chart1_v _root_.ArtinKP.X.chart1_x _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
/-! # WP-B1, file 2: convergence of the Eisenstein majorant over `𝓞_F`-pairs modulo units

For a family of nonzero pairs `(c,d) ∈ 𝓞_F²`, pairwise inequivalent under scaling by units,
`∑ I_{(c,d)}(P)^σ < ∞` for `σ > 2` (`summable_pairHt_rpow`).  Proof: by Dirichlet's unit theorem
every class has a representative whose local denominators are balanced; for it
`I(P) ≤ C(P) ‖(c,d)‖^{-2r}`, and the lattice sum `∑ ‖z‖^{-2rσ}` over `𝓞_F² ⊂ ℝ^{4r}` converges.

Local uniformity is obtained from the comparison `I_{(c,d)}(P) ≤ cmp P P₀ · I_{(c,d)}(P₀)`, valid for
all pairs, with `cmp · P₀` continuous (`pairHt_le_cmp`, `continuous_cmp`,
`exists_summable_majorant`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.B1

open ArtinKP.X

noncomputable section

lemma kap_pos (Q : H3) : 0 < kap Q := by
  have := Q.v_pos
  unfold kap; positivity

lemma norm_sq_le_kap (c d : ℂ) (Q : H3) :
    ‖c‖ ^ 2 ≤ kap Q * H3.rowDen c d Q ∧ ‖d‖ ^ 2 ≤ kap Q * H3.rowDen c d Q := by
  have hv := Q.v_pos
  have hD : H3.rowDen c d Q = ‖c * Q.x + d‖ ^ 2 + ‖c‖ ^ 2 * Q.v ^ 2 := by
    unfold H3.rowDen; rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  set A := ‖c * Q.x + d‖ with hA
  set D := H3.rowDen c d Q with hDdef
  have hA0 : 0 ≤ A := norm_nonneg _
  have hD0 : 0 ≤ D := H3.rowDen_nonneg _ _ _
  set t := D / Q.v ^ 2 with ht
  have ht0 : 0 ≤ t := by positivity
  have hct : ‖c‖ ^ 2 ≤ t := by
    rw [ht, le_div_iff₀ (by positivity)]; nlinarith [sq_nonneg A]
  have hk : kap Q * D = 2 * D + t + 2 * ‖Q.x‖ ^ 2 * t := by
    rw [ht]; unfold kap; field_simp; ring
  have hd : ‖d‖ ≤ A + ‖c‖ * ‖Q.x‖ := by
    have : d = (c * Q.x + d) - c * Q.x := by ring
    calc ‖d‖ = ‖(c * Q.x + d) - c * Q.x‖ := by rw [← this]
      _ ≤ ‖c * Q.x + d‖ + ‖c * Q.x‖ := norm_sub_le _ _
      _ = A + ‖c‖ * ‖Q.x‖ := by rw [norm_mul]
  have hx0 := norm_nonneg Q.x
  have hc0 := norm_nonneg c
  have hd0 := norm_nonneg d
  refine ⟨by rw [hk]; nlinarith [sq_nonneg ‖Q.x‖, mul_nonneg (sq_nonneg ‖Q.x‖) ht0], ?_⟩
  rw [hk]
  have h1 : ‖d‖ ^ 2 ≤ (A + ‖c‖ * ‖Q.x‖) ^ 2 := pow_le_pow_left₀ hd0 hd 2
  have h2 : (A + ‖c‖ * ‖Q.x‖) ^ 2 ≤ 2 * A ^ 2 + 2 * (‖c‖ ^ 2 * ‖Q.x‖ ^ 2) := by
    nlinarith [sq_nonneg (A - ‖c‖ * ‖Q.x‖)]
  have h3 : ‖c‖ ^ 2 * ‖Q.x‖ ^ 2 ≤ t * ‖Q.x‖ ^ 2 := mul_le_mul_of_nonneg_right hct (sq_nonneg _)
  have h4 : A ^ 2 ≤ D := by rw [hD]; nlinarith [mul_nonneg (sq_nonneg ‖c‖) (sq_nonneg Q.v)]
  nlinarith

lemma rowDen_smul (t c d : ℂ) (Q : H3) :
    H3.rowDen (t * c) (t * d) Q = Complex.normSq t * H3.rowDen c d Q := by
  unfold H3.rowDen
  rw [mul_assoc, ← mul_add, map_mul, map_mul]; ring

/-- Comparison of one local denominator at two points. -/
lemma rowDen_le_rowDen (c d : ℂ) (Q Q₀ : H3) :
    H3.rowDen c d Q₀ ≤ (2 * ‖Q₀.x‖ ^ 2 + Q₀.v ^ 2 + 2) * kap Q * H3.rowDen c d Q := by
  obtain ⟨h1, h2⟩ := norm_sq_le_kap c d Q
  have hD : H3.rowDen c d Q₀ = ‖c * Q₀.x + d‖ ^ 2 + ‖c‖ ^ 2 * Q₀.v ^ 2 := by
    unfold H3.rowDen; rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have h3 : ‖c * Q₀.x + d‖ ^ 2 ≤ 2 * (‖c‖ ^ 2 * ‖Q₀.x‖ ^ 2) + 2 * ‖d‖ ^ 2 := by
    have : ‖c * Q₀.x + d‖ ≤ ‖c‖ * ‖Q₀.x‖ + ‖d‖ := by
      calc _ ≤ ‖c * Q₀.x‖ + ‖d‖ := norm_add_le _ _
        _ = _ := by rw [norm_mul]
    have h := pow_le_pow_left₀ (norm_nonneg _) this 2
    nlinarith [sq_nonneg (‖c‖ * ‖Q₀.x‖ - ‖d‖)]
  set M := kap Q * H3.rowDen c d Q
  rw [hD]
  have e : (2 * ‖Q₀.x‖ ^ 2 + Q₀.v ^ 2 + 2) * kap Q * H3.rowDen c d Q =
      2 * ‖Q₀.x‖ ^ 2 * M + Q₀.v ^ 2 * M + 2 * M := by ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖Q₀.x‖),
    mul_le_mul_of_nonneg_right h1 (sq_nonneg Q₀.v)]

variable {F : Type*} [Field F] [NumberField F]

/-- **Comparison on compacts**: `I_{(c,d)}(P) ≤ cmp P P₀ · I_{(c,d)}(P₀)` for every nonzero pair. -/
theorem pairHt_le_cmp {c d : F} (h : c ≠ 0 ∨ d ≠ 0) (P P₀ : X F) :
    X.pairHt c d P ≤ cmp P P₀ * X.pairHt c d P₀ := by
  rw [X.pairHt_eq_prod, X.pairHt_eq_prod, cmp, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun w _ => ?_) fun w _ => ?_
  · exact div_nonneg (P.v_pos w).le (H3.rowDen_nonneg _ _ _)
  · have hv := P.v_pos w
    have hv0 := P₀.v_pos w
    have hD := H3.rowDen_pos (c := w.embedding c) (d := w.embedding d) (by simpa using h) (P w)
    have hD0 := H3.rowDen_pos (c := w.embedding c) (d := w.embedding d) (by simpa using h) (P₀ w)
    have key := rowDen_le_rowDen (w.embedding c) (w.embedding d) (P w) (P₀ w)
    change H3.rowDen _ _ (P₀ w) ≤ (2 * ‖P₀.x w‖ ^ 2 + P₀.v w ^ 2 + 2) * kap (P w) * _ at key
    rw [div_le_iff₀ hD]
    have e : P.v w / P₀.v w * ((2 * ‖P₀.x w‖ ^ 2 + P₀.v w ^ 2 + 2) * kap (P w)) *
        (P₀.v w / H3.rowDen (w.embedding c) (w.embedding d) (P₀ w)) *
        H3.rowDen (w.embedding c) (w.embedding d) (P w) =
        P.v w * (((2 * ‖P₀.x w‖ ^ 2 + P₀.v w ^ 2 + 2) * kap (P w) *
          H3.rowDen (w.embedding c) (w.embedding d) (P w)) /
          H3.rowDen (w.embedding c) (w.embedding d) (P₀ w)) := by
      field_simp
    rw [e]
    refine le_mul_of_one_le_right hv.le ?_
    rw [one_le_div hD0]
    exact key

lemma continuous_kap : Continuous kap := by
  unfold kap
  refine continuous_const.add (Continuous.div ?_ (H3.continuous_v.pow 2) fun Q => ?_)
  · exact continuous_const.add (continuous_const.mul (H3.continuous_x.norm.pow 2))
  · exact pow_ne_zero 2 Q.v_pos.ne'

lemma continuous_cmp (P₀ : X F) : Continuous fun P : X F => cmp P P₀ := by
  unfold cmp
  refine continuous_finsetProd _ fun w _ => ?_
  refine Continuous.mul (Continuous.div_const ?_ _) (continuous_const.mul ?_)
  · exact H3.continuous_v.comp (continuous_apply w)
  · exact continuous_kap.comp (continuous_apply w)

/-- On a compact set the pair heights are dominated by a multiple of those at a base point. -/
theorem exists_cmp_bound (P₀ : X F) {K : Set (X F)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ P ∈ K, ∀ c d : F, (c ≠ 0 ∨ d ≠ 0) →
      X.pairHt c d P ≤ C * X.pairHt c d P₀ := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (continuous_cmp P₀).continuousOn
  refine ⟨max C 1, by positivity, fun P hP c d h => ?_⟩
  refine (pairHt_le_cmp h P P₀).trans (mul_le_mul_of_nonneg_right ?_ (X.pairHt_pos h P₀).le)
  exact ((le_abs_self _).trans (hC P hP)).trans (le_max_left _ _)

lemma kap_le_kapX (P : X F) (w : InfinitePlace F) : kap (P w) ≤ kapX P :=
  Finset.single_le_sum (f := fun w => kap (P w)) (fun w _ => (kap_pos (P w)).le) (Finset.mem_univ w)

variable [IsTotallyComplex F]

lemma pairHt_unit_smul (ε : (𝓞 F)ˣ) (c d : F) (P : X F) :
    X.pairHt ((ε : F) * c) ((ε : F) * d) P = X.pairHt c d P := by
  rw [X.pairHt_smul_pair, X.prod_normSq_embedding, NumberField.Units.norm]
  simp

/-- **Balanced representatives.** There is `C ≥ 1` such that every nonzero pair of integers has a
unit multiple `z = ε·(c,d)` with `‖z‖^{2r} · I_{(c,d)}(P) ≤ (C · kapX P)^r · ht P`. -/
theorem exists_unit_rep : ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : X F) (c d : 𝓞 F), (c ≠ 0 ∨ d ≠ 0) →
    ∃ ε : (𝓞 F)ˣ, ‖((emb (((ε : 𝓞 F) * c : 𝓞 F) : F), emb (((ε : 𝓞 F) * d : 𝓞 F) : F)) : E₂ F)‖ ^
        (2 * Fintype.card (InfinitePlace F)) * X.pairHt (c : F) (d : F) P ≤
      (C * kapX P) ^ Fintype.card (InfinitePlace F) * X.ht P := by
  classical
  obtain ⟨C, hC1, hC⟩ := exists_unit_balanced (F := F)
  refine ⟨C, hC1, fun P c d hne => ?_⟩
  have hne' : (c : F) ≠ 0 ∨ (d : F) ≠ 0 :=
    hne.imp (fun h => by simpa using h) (fun h => by simpa using h)
  set D : InfinitePlace F → ℝ :=
    fun w => H3.rowDen (w.embedding (c : F)) (w.embedding (d : F)) (P w) with hDdef
  have hDpos : ∀ w, 0 < D w := fun w => H3.rowDen_pos (by simpa using hne') (P w)
  obtain ⟨ε, hε⟩ := hC D hDpos
  refine ⟨ε, ?_⟩
  set D' : InfinitePlace F → ℝ := fun w => (w (ε : F)) ^ 2 * D w with hD'def
  have hεpos : ∀ w : InfinitePlace F, 0 < w (ε : F) := fun w =>
    w.pos_iff.mpr (by simp)
  have hD'pos : ∀ w, 0 < D' w := fun w => mul_pos (pow_pos (hεpos w) 2) (hDpos w)
  have hD'eq : ∀ w, D' w = H3.rowDen (w.embedding ((ε : F) * c)) (w.embedding ((ε : F) * d)) (P w) := by
    intro w
    rw [map_mul, map_mul, rowDen_smul, Complex.normSq_eq_norm_sq, InfinitePlace.norm_embedding_eq]
  have hprod : ∏ w, D' w = X.pairDen (c : F) (d : F) P := by
    have h1 : ∏ w, D' w = X.pairDen ((ε : F) * c) ((ε : F) * d) P :=
      Finset.prod_congr rfl fun w _ => hD'eq w
    have h2 := pairHt_unit_smul ε (c : F) (d : F) P
    unfold X.pairHt at h2
    have hp1 := X.pairDen_pos (c := (ε : F) * c) (d := (ε : F) * d)
      (hne'.imp (fun h => mul_ne_zero (by simp) h) (fun h => mul_ne_zero (by simp) h)) P
    have hp2 := X.pairDen_pos hne' P
    have hh := X.ht_pos P
    rw [h1]
    rw [div_eq_div_iff hp1.ne' hp2.ne'] at h2
    exact (mul_left_cancel₀ hh.ne' h2).symm
  obtain ⟨wm, -, hwm⟩ := Finset.exists_max_image Finset.univ D' ⟨Classical.arbitrary _, Finset.mem_univ _⟩
  have hbb := (balanced_bounds (by linarith : (0 : ℝ) ≤ C) hD'pos (fun i j => hε i j) wm).1
  set z : E₂ F := (emb (((ε : 𝓞 F) * c : 𝓞 F) : F), emb (((ε : 𝓞 F) * d : 𝓞 F) : F)) with hz
  have hK0 : 0 ≤ kapX P := Finset.sum_nonneg fun w _ => (kap_pos (P w)).le
  have hloc : ∀ w : InfinitePlace F, ‖w.embedding ((ε : F) * c)‖ ^ 2 ≤ kapX P * D' wm ∧
      ‖w.embedding ((ε : F) * d)‖ ^ 2 ≤ kapX P * D' wm := by
    intro w
    obtain ⟨h1, h2⟩ := norm_sq_le_kap (w.embedding ((ε : F) * c)) (w.embedding ((ε : F) * d)) (P w)
    rw [← hD'eq] at h1 h2
    have h3 : kap (P w) * D' w ≤ kapX P * D' wm :=
      mul_le_mul (kap_le_kapX P w) (hwm w (Finset.mem_univ _)) (hD'pos w).le hK0
    exact ⟨h1.trans h3, h2.trans h3⟩
  have hB0 : 0 ≤ kapX P * D' wm := mul_nonneg hK0 (hD'pos wm).le
  have hznorm : ‖z‖ ≤ √(kapX P * D' wm) := by
    rw [hz, Prod.norm_def, max_le_iff, pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _),
      pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    constructor
    · intro w
      refine Real.le_sqrt_of_sq_le ?_
      simpa using (hloc w).1
    · intro w
      refine Real.le_sqrt_of_sq_le ?_
      simpa using (hloc w).2
  have hz2 : ‖z‖ ^ 2 ≤ kapX P * D' wm := by
    calc ‖z‖ ^ 2 ≤ √(kapX P * D' wm) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hznorm 2
      _ = _ := Real.sq_sqrt hB0
  have hz2r : ‖z‖ ^ (2 * Fintype.card (InfinitePlace F)) ≤
      (C * kapX P) ^ Fintype.card (InfinitePlace F) * X.pairDen (c : F) (d : F) P := by
    rw [pow_mul]
    calc (‖z‖ ^ 2) ^ Fintype.card (InfinitePlace F)
        ≤ (kapX P * D' wm) ^ Fintype.card (InfinitePlace F) :=
          pow_le_pow_left₀ (by positivity) hz2 _
      _ = kapX P ^ Fintype.card (InfinitePlace F) * D' wm ^ Fintype.card (InfinitePlace F) :=
          mul_pow _ _ _
      _ ≤ kapX P ^ Fintype.card (InfinitePlace F) *
          (C ^ Fintype.card (InfinitePlace F) * ∏ j, D' j) :=
          mul_le_mul_of_nonneg_left hbb (pow_nonneg hK0 _)
      _ = _ := by rw [hprod, mul_pow]; ring
  have hp2 := X.pairDen_pos hne' P
  unfold X.pairHt
  rw [← mul_div_assoc, div_le_iff₀ hp2]
  calc _ ≤ (C * kapX P) ^ Fintype.card (InfinitePlace F) * X.pairDen (c : F) (d : F) P * X.ht P :=
        mul_le_mul_of_nonneg_right hz2r (X.ht_pos P).le
    _ = _ := by ring

/-- **(B1) Convergence over `𝓞_F`-pairs modulo units**, `σ > 2`. -/
theorem summable_pairHt_rpow {ι' : Type*} (f : ι' → 𝓞 F × 𝓞 F) (hne : ∀ i, (f i).1 ≠ 0 ∨ (f i).2 ≠ 0)
    (hinj : ∀ i j, (∃ ε : (𝓞 F)ˣ, f j = ((ε : 𝓞 F) * (f i).1, (ε : 𝓞 F) * (f i).2)) → i = j)
    (P : X F) {σ : ℝ} (hσ : 2 < σ) :
    Summable fun i => X.pairHt ((f i).1 : F) ((f i).2 : F) P ^ σ := by
  classical
  obtain ⟨C, hC1, hC⟩ := exists_unit_rep (F := F)
  choose ε hε using fun i => hC P (f i).1 (f i).2 (hne i)
  set r := Fintype.card (InfinitePlace F) with hr
  have hr1 : 1 ≤ r := Fintype.card_pos
  let g : ι' → pairLattice F := fun i =>
    ⟨(emb (((ε i : 𝓞 F) * (f i).1 : 𝓞 F) : F), emb (((ε i : 𝓞 F) * (f i).2 : 𝓞 F) : F)),
      mem_pairLattice.mpr ⟨_, _, rfl⟩⟩
  have hcoe : ∀ {a b : 𝓞 F}, emb (a : F) = emb (b : F) → a = b := by
    intro a b h
    have := emb_eq_zero (by rw [map_sub, h, sub_self] : emb ((a : F) - (b : F)) = 0)
    exact RingOfIntegers.ext (sub_eq_zero.mp this)
  have hg : Function.Injective g := by
    intro i j hij
    have h := congrArg Subtype.val hij
    have h1 : (ε i : 𝓞 F) * (f i).1 = (ε j : 𝓞 F) * (f j).1 := hcoe (congrArg Prod.fst h)
    have h2 : (ε i : 𝓞 F) * (f i).2 = (ε j : 𝓞 F) * (f j).2 := hcoe (congrArg Prod.snd h)
    refine hinj i j ⟨(ε j)⁻¹ * ε i, Prod.ext ?_ ?_⟩
    · simp only [Units.val_mul, mul_assoc, h1]; simp
    · simp only [Units.val_mul, mul_assoc, h2]; simp
  have hgpos : ∀ i, 0 < ‖g i‖ := by
    intro i
    rw [norm_pos_iff]
    intro h0
    have h := congrArg Subtype.val h0
    have e1 : emb ((((ε i : 𝓞 F) * (f i).1 : 𝓞 F)) : F) = 0 := congrArg Prod.fst h
    have e2 : emb ((((ε i : 𝓞 F) * (f i).2 : 𝓞 F)) : F) = 0 := congrArg Prod.snd h
    have h1 : (ε i : 𝓞 F) * (f i).1 = 0 := hcoe (e1.trans (by simp))
    have h2 : (ε i : 𝓞 F) * (f i).2 = 0 := hcoe (e2.trans (by simp))
    rcases hne i with h' | h'
    · exact h' (by simpa using h1)
    · exact h' (by simpa using h2)
  set M : ℝ := (C * kapX P) ^ r * X.ht P with hM
  have hM0 : 0 ≤ M := by
    have : 0 ≤ kapX P := Finset.sum_nonneg fun w _ => (kap_pos (P w)).le
    have := X.ht_pos P
    positivity
  have hsum := ZLattice.summable_norm_rpow (pairLattice F) (-(2 * (r : ℝ) * σ)) (by
    rw [finrank_pairLattice, neg_lt_neg_iff]
    push_cast
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr1
    nlinarith)
  refine Summable.of_nonneg_of_le (fun i => Real.rpow_nonneg (X.pairHt_pos (c := ((f i).1 : F))
    (d := ((f i).2 : F)) ((hne i).imp (fun h => by simpa using h) (fun h => by simpa using h)) P).le _)
    (fun i => ?_) ((hsum.comp_injective hg).mul_left (M ^ σ))
  have hI0 := (X.pairHt_pos (c := ((f i).1 : F)) (d := ((f i).2 : F))
    ((hne i).imp (fun h => by simpa using h) (fun h => by simpa using h)) P).le
  have hpow : ‖g i‖ ^ (2 * r) = ‖g i‖ ^ (2 * (r : ℝ)) := by
    rw [← Real.rpow_natCast]; push_cast; rfl
  have hb : X.pairHt ((f i).1 : F) ((f i).2 : F) P ≤ M * ‖g i‖ ^ (-(2 * (r : ℝ))) := by
    rw [Real.rpow_neg (hgpos i).le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos (hgpos i) _),
      ← hpow, mul_comm]
    exact hε i
  calc X.pairHt ((f i).1 : F) ((f i).2 : F) P ^ σ
      ≤ (M * ‖g i‖ ^ (-(2 * (r : ℝ)))) ^ σ := Real.rpow_le_rpow hI0 hb (by linarith)
    _ = M ^ σ * ‖g i‖ ^ (-(2 * (r : ℝ) * σ)) := by
        rw [Real.mul_rpow hM0 (Real.rpow_nonneg (hgpos i).le _), ← Real.rpow_mul (hgpos i).le]
        congr 2; ring

/-- **(B1) Locally uniform convergence**: on a compact set `K ⊂ X` and for `σ` in a compact
interval `[σ₁, σ₂] ⊂ (2, ∞)` the series `∑ I_{(c,d)}(P)^σ` has a summable majorant. -/
theorem exists_summable_majorant {ι' : Type*} (f : ι' → 𝓞 F × 𝓞 F)
    (hne : ∀ i, (f i).1 ≠ 0 ∨ (f i).2 ≠ 0)
    (hinj : ∀ i j, (∃ ε : (𝓞 F)ˣ, f j = ((ε : 𝓞 F) * (f i).1, (ε : 𝓞 F) * (f i).2)) → i = j)
    {K : Set (X F)} (hK : IsCompact K) {σ₁ σ₂ : ℝ} (hσ₁ : 2 < σ₁) (hσ : σ₁ ≤ σ₂) :
    ∃ u : ι' → ℝ, Summable u ∧ ∀ P ∈ K, ∀ σ ∈ Set.Icc σ₁ σ₂, ∀ i,
      X.pairHt ((f i).1 : F) ((f i).2 : F) P ^ σ ≤ u i := by
  classical
  let P₀ : X F := X.mk (fun _ => 0) (fun _ => 1) (fun _ => one_pos)
  obtain ⟨C, hC0, hC⟩ := exists_cmp_bound P₀ hK
  have hne' : ∀ i, ((f i).1 : F) ≠ 0 ∨ ((f i).2 : F) ≠ 0 := fun i =>
    (hne i).imp (fun h => by simpa using h) (fun h => by simpa using h)
  refine ⟨fun i => C ^ σ₁ * X.pairHt ((f i).1 : F) ((f i).2 : F) P₀ ^ σ₁ +
      C ^ σ₂ * X.pairHt ((f i).1 : F) ((f i).2 : F) P₀ ^ σ₂,
    ((summable_pairHt_rpow f hne hinj P₀ hσ₁).mul_left _).add
      ((summable_pairHt_rpow f hne hinj P₀ (hσ₁.trans_le hσ)).mul_left _), ?_⟩
  intro P hP σ hσm i
  have h0 := (X.pairHt_pos (hne' i) P).le
  have h1 := (X.pairHt_pos (hne' i) P₀).le
  have hle := hC P hP _ _ (hne' i)
  set U := C * X.pairHt ((f i).1 : F) ((f i).2 : F) P₀ with hU
  have hU0 : 0 ≤ U := by positivity
  have hstep : X.pairHt ((f i).1 : F) ((f i).2 : F) P ^ σ ≤ U ^ σ :=
    Real.rpow_le_rpow h0 hle (by linarith [hσm.1])
  have e1 : C ^ σ₁ * X.pairHt ((f i).1 : F) ((f i).2 : F) P₀ ^ σ₁ = U ^ σ₁ := by
    rw [hU, Real.mul_rpow hC0.le h1]
  have e2 : C ^ σ₂ * X.pairHt ((f i).1 : F) ((f i).2 : F) P₀ ^ σ₂ = U ^ σ₂ := by
    rw [hU, Real.mul_rpow hC0.le h1]
  change X.pairHt _ _ P ^ σ ≤ C ^ σ₁ * X.pairHt _ _ P₀ ^ σ₁ + C ^ σ₂ * X.pairHt _ _ P₀ ^ σ₂
  rw [e1, e2]
  refine hstep.trans ?_
  rcases le_total U 1 with hU1 | hU1
  · exact (Real.rpow_le_rpow_of_exponent_ge' hU0 hU1 (by linarith) hσm.1).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hU0 _))
  · exact (Real.rpow_le_rpow_of_exponent_le hU1 hσm.2).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hU0 _))

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.B1_Pairs
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap _root_.ArtinKP.RO.rowPair_c _root_.ArtinKP.RO.rowPair_d _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
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

namespace SPair

lemma ne_zero (p : SPair S) : p.c ≠ 0 ∨ p.d ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨a, b, -, -, hab⟩ := p.prim
  rw [h.1, h.2] at hab
  simp at hab

end SPair

namespace PairClass

variable [IsTotallyComplex F]

lemma ht_eq_out (p : PairClass S) (P : X F) : p.ht P = X.sHt S p.out.c p.out.d P := by
  conv_lhs => rw [← Quotient.out_eq p]
  rfl

lemma ht_pos (p : PairClass S) (P : X F) : 0 < p.ht P := by
  rw [ht_eq_out]; exact X.sHt_pos S p.out.ne_zero P

lemma ht_inf (P : X F) : (inf S).ht P = X.ht P := by
  change X.sHt S 0 1 P = _
  unfold X.sHt X.sNorm
  rw [X.pairHt_zero_one]
  simp

/-- **Equivariance**: `ht_{pγ}(P) = ht_p(γP)` for `γ ∈ SL₂(𝓞_F)`. -/
theorem ht_act (p : PairClass S) (γ : SL(2, 𝓞 F)) (P : X F) : (p.act γ).ht P = p.ht (γ • P) := by
  induction p using Quotient.inductionOn with
  | _ q => exact sHt_actF (q.c, q.d) γ P

end PairClass

/-! ### (B1) for families of `S`-integer pairs -/

variable [IsTotallyComplex F]

/-- Rescaling a family of pairwise `U_S`-inequivalent pairs of `S`-integers into `𝓞_F²`. -/
theorem exists_rescaled_family (S : Finset (FinitePlace F)) {ι' : Type*} (f : ι' → F × F)
    (hint : ∀ i, IsSInt S (f i).1 ∧ IsSInt S (f i).2) (hne : ∀ i, (f i).1 ≠ 0 ∨ (f i).2 ≠ 0)
    (hinj : ∀ i j, (∃ u : F, IsSUnit S u ∧ f j = (u * (f i).1, u * (f i).2)) → i = j) :
    ∃ D : ℝ, 1 ≤ D ∧ ∃ f' : ι' → 𝓞 F × 𝓞 F, (∀ i, (f' i).1 ≠ 0 ∨ (f' i).2 ≠ 0) ∧
      (∀ i j, (∃ ε : (𝓞 F)ˣ, f' j = ((ε : 𝓞 F) * (f' i).1, (ε : 𝓞 F) * (f' i).2)) → i = j) ∧
      ∀ i (P : X F), X.sHt S (f i).1 (f i).2 P ≤ D * X.pairHt ((f' i).1 : F) ((f' i).2 : F) P := by
  classical
  obtain ⟨δ, hδ, hres⟩ := exists_unit_rescale S
  choose u hu0 huS hex hδle using fun i => hres (f i).1 (f i).2 (hne i) (hint i).1 (hint i).2
  choose c' d' hc' hd' using hex
  refine ⟨max 1 δ⁻¹, le_max_left _ _, fun i => (c' i, d' i), ?_, ?_, ?_⟩
  · intro i
    refine (hne i).imp (fun h h0 => ?_) (fun h h0 => ?_)
    · have h0' : c' i = 0 := h0
      have := hc' i; rw [h0'] at this
      exact mul_ne_zero (hu0 i) h (by simpa using this.symm)
    · have h0' : d' i = 0 := h0
      have := hd' i; rw [h0'] at this
      exact mul_ne_zero (hu0 i) h (by simpa using this.symm)
  · rintro i j ⟨ε, hε⟩
    have e1 : u j * (f j).1 = (ε : 𝓞 F) * (u i * (f i).1) := by
      rw [← hc' i, ← hc' j]; exact_mod_cast congrArg (fun z : 𝓞 F × 𝓞 F => (z.1 : F)) hε
    have e2 : u j * (f j).2 = (ε : 𝓞 F) * (u i * (f i).2) := by
      rw [← hd' i, ← hd' j]; exact_mod_cast congrArg (fun z : 𝓞 F × 𝓞 F => (z.2 : F)) hε
    refine hinj i j ⟨(u j)⁻¹ * ((ε : 𝓞 F) * u i),
      (IsSUnit.inv ⟨hu0 j, huS j⟩).mul ((isSUnit_unit ε).mul ⟨hu0 i, huS i⟩), Prod.ext ?_ ?_⟩
    · change (f j).1 = (u j)⁻¹ * ((ε : 𝓞 F) * u i) * (f i).1
      rw [mul_assoc, mul_assoc, ← e1, inv_mul_cancel_left₀ (hu0 j)]
    · change (f j).2 = (u j)⁻¹ * ((ε : 𝓞 F) * u i) * (f i).2
      rw [mul_assoc, mul_assoc, ← e2, inv_mul_cancel_left₀ (hu0 j)]
  · intro i P
    have hne' : u i * (f i).1 ≠ 0 ∨ u i * (f i).2 ≠ 0 :=
      (hne i).imp (mul_ne_zero (hu0 i)) (mul_ne_zero (hu0 i))
    have hp := X.pairHt_pos hne' P
    rw [← X.sHt_unit_smul S (hu0 i) (huS i)]
    change X.pairHt _ _ P / _ ≤ max 1 δ⁻¹ * X.pairHt ((c' i : 𝓞 F) : F) ((d' i : 𝓞 F) : F) P
    rw [hc' i, hd' i, div_le_iff₀ (X.sNorm_pos S hne')]
    have h1 : 1 ≤ max 1 δ⁻¹ * X.sNorm S (u i * (f i).1) (u i * (f i).2) := by
      calc (1 : ℝ) = δ⁻¹ * δ := (inv_mul_cancel₀ hδ.ne').symm
        _ ≤ max 1 δ⁻¹ * X.sNorm S (u i * (f i).1) (u i * (f i).2) :=
          mul_le_mul (le_max_right _ _) (hδle i) hδ.le (by positivity)
    nlinarith

/-- **(B1) Convergence**, `σ > 2`: pairs of `S`-integers modulo `S`-units, `S`-normalized heights. -/
theorem summable_sHt_rpow (S : Finset (FinitePlace F)) {ι' : Type*} (f : ι' → F × F)
    (hint : ∀ i, IsSInt S (f i).1 ∧ IsSInt S (f i).2) (hne : ∀ i, (f i).1 ≠ 0 ∨ (f i).2 ≠ 0)
    (hinj : ∀ i j, (∃ u : F, IsSUnit S u ∧ f j = (u * (f i).1, u * (f i).2)) → i = j)
    (P : X F) {σ : ℝ} (hσ : 2 < σ) :
    Summable fun i => X.sHt S (f i).1 (f i).2 P ^ σ := by
  obtain ⟨D, hD, f', hne', hinj', hle⟩ := exists_rescaled_family S f hint hne hinj
  refine Summable.of_nonneg_of_le (fun i => Real.rpow_nonneg (X.sHt_pos S (hne i) P).le _)
    (fun i => ?_) ((summable_pairHt_rpow f' hne' hinj' P hσ).mul_left (D ^ σ))
  have hp : 0 ≤ X.pairHt ((f' i).1 : F) ((f' i).2 : F) P :=
    div_nonneg (X.ht_pos P).le (X.pairDen_nonneg _ _ _)
  rw [← Real.mul_rpow (by linarith) hp]
  exact Real.rpow_le_rpow (X.sHt_pos S (hne i) P).le (hle i P) (by linarith)

/-- **(B1) Locally uniform convergence**: a summable majorant on `K × [σ₁, σ₂]`, `K ⊂ X` compact,
`2 < σ₁`. -/
theorem exists_summable_majorant_sHt (S : Finset (FinitePlace F)) {ι' : Type*} (f : ι' → F × F)
    (hint : ∀ i, IsSInt S (f i).1 ∧ IsSInt S (f i).2) (hne : ∀ i, (f i).1 ≠ 0 ∨ (f i).2 ≠ 0)
    (hinj : ∀ i j, (∃ u : F, IsSUnit S u ∧ f j = (u * (f i).1, u * (f i).2)) → i = j)
    {K : Set (X F)} (hK : IsCompact K) {σ₁ σ₂ : ℝ} (hσ₁ : 2 < σ₁) (hσ : σ₁ ≤ σ₂) :
    ∃ u : ι' → ℝ, Summable u ∧ ∀ P ∈ K, ∀ σ ∈ Set.Icc σ₁ σ₂, ∀ i,
      X.sHt S (f i).1 (f i).2 P ^ σ ≤ u i := by
  obtain ⟨D, hD, f', hne', hinj', hle⟩ := exists_rescaled_family S f hint hne hinj
  obtain ⟨u, hu, hub⟩ := exists_summable_majorant f' hne' hinj' hK hσ₁ hσ
  refine ⟨fun i => D ^ σ₂ * u i, hu.mul_left _, fun P hP σ hσm i => ?_⟩
  have hp : 0 ≤ X.pairHt ((f' i).1 : F) ((f' i).2 : F) P :=
    div_nonneg (X.ht_pos P).le (X.pairDen_nonneg _ _ _)
  calc X.sHt S (f i).1 (f i).2 P ^ σ
      ≤ (D * X.pairHt ((f' i).1 : F) ((f' i).2 : F) P) ^ σ :=
        Real.rpow_le_rpow (X.sHt_pos S (hne i) P).le (hle i P) (by linarith [hσm.1])
    _ = D ^ σ * X.pairHt ((f' i).1 : F) ((f' i).2 : F) P ^ σ := Real.mul_rpow (by linarith) hp
    _ ≤ D ^ σ₂ * u i := mul_le_mul (Real.rpow_le_rpow_of_exponent_le hD hσm.2) (hub P hP σ hσm i)
        (Real.rpow_nonneg hp _) (Real.rpow_nonneg (by linarith) _)

namespace PairClass

lemma out_family_inj (p q : PairClass S)
    (h : ∃ u : F, IsSUnit S u ∧ (q.out.c, q.out.d) = (u * p.out.c, u * p.out.d)) : p = q := by
  obtain ⟨u, hu, he⟩ := h
  rw [← Quotient.out_eq p, ← Quotient.out_eq q]
  exact Quotient.sound ⟨u, hu, congrArg Prod.fst he, congrArg Prod.snd he⟩

/-- **(B1)** `∑_{p ∈ 𝒫} ht_p(P)^σ < ∞` for `σ > 2`. -/
theorem summable_ht_rpow (S : Finset (FinitePlace F)) (P : X F) {σ : ℝ} (hσ : 2 < σ) :
    Summable fun p : PairClass S => p.ht P ^ σ := by
  have := summable_sHt_rpow S (fun p : PairClass S => (p.out.c, p.out.d))
    (fun p => ⟨p.out.hc, p.out.hd⟩) (fun p => p.out.ne_zero) out_family_inj P hσ
  simpa only [← ht_eq_out] using this

/-- **(B1), locally uniform.** -/
theorem exists_summable_majorant (S : Finset (FinitePlace F)) {K : Set (X F)} (hK : IsCompact K)
    {σ₁ σ₂ : ℝ} (hσ₁ : 2 < σ₁) (hσ : σ₁ ≤ σ₂) :
    ∃ u : PairClass S → ℝ, Summable u ∧ ∀ P ∈ K, ∀ σ ∈ Set.Icc σ₁ σ₂, ∀ p : PairClass S,
      p.ht P ^ σ ≤ u p := by
  have := exists_summable_majorant_sHt S (fun p : PairClass S => (p.out.c, p.out.d))
    (fun p => ⟨p.out.hc, p.out.hd⟩) (fun p => p.out.ne_zero) out_family_inj hK hσ₁ hσ
  simpa only [← ht_eq_out] using this

end PairClass

/-! ### Lemma M for pair classes -/

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.B1_Cusp
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.B.coe_latREquiv _root_.ArtinKP.B.embR_apply _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap _root_.ArtinKP.X.chart1_symm_snd _root_.ArtinKP.X.chart1_v _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
/-! # WP-B1, file 5: the series without the cusp at infinity — invariance and Harnack in `x`

`Tinf S σ P = ∑_{p ≠ ∞} ht_p(P)^σ` (all pair classes except that of `(0,1)`).  It is invariant under
upper triangular elements of `SL₂(𝓞_F)` (`Tinf_smul_of_upper`): translations `nInt β` and diagonal
units.  Harnack inequality in the horizontal variable (`Tinf_harnack`): moving `x_w` by at most `v_w`
changes every pair height by a factor `≤ 3^r`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.B1

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-! ### Continuity -/

lemma continuous_rowDen (c d : ℂ) : Continuous (H3.rowDen c d) := by
  unfold H3.rowDen
  exact (Complex.continuous_normSq.comp ((continuous_const.mul H3.continuous_x).add
    continuous_const)).add (continuous_const.mul (H3.continuous_v.pow 2))

lemma continuous_pairHt {c d : F} (h : c ≠ 0 ∨ d ≠ 0) : Continuous fun P : X F => X.pairHt c d P := by
  unfold X.pairHt
  exact X.continuous_ht.div (continuous_finsetProd _ fun w _ =>
    (continuous_rowDen _ _).comp (continuous_apply w)) (fun P => (X.pairDen_pos h P).ne')

lemma continuous_mk (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) :
    Continuous fun x : InfinitePlace F → ℂ => X.mk x v hv := by
  refine continuous_pi fun w => ?_
  change Continuous fun x : InfinitePlace F → ℂ => (⟨(x w, v w), hv w⟩ : {p : ℂ × ℝ // 0 < p.2})
  exact Continuous.subtype_mk ((continuous_apply w).prodMk continuous_const) _

/-! ### Translations -/

lemma nInt_smul_mk (β : 𝓞 F) (x : InfinitePlace F → ℂ) (v : InfinitePlace F → ℝ)
    (hv : ∀ w, 0 < v w) : nInt β • X.mk x v hv = X.mk (x + emb (β : F)) v hv := by
  refine X.ext' (funext fun w => ?_) (funext fun w => ?_)
  · rw [(smul_of_upper (γ := nInt β) (by simp [nInt_coe]) (X.mk x v hv) w).1]
    simp [nInt_coe]
  · rw [(smul_of_upper (γ := nInt β) (by simp [nInt_coe]) (X.mk x v hv) w).2]
    simp [nInt_coe]

variable {S : Finset (FinitePlace F)}

variable [IsTotallyComplex F]

lemma summable_Tinf (S : Finset (FinitePlace F)) {σ : ℝ} (hσ : 2 < σ) (P : X F) :
    Summable fun p : {p : PairClass S // p ≠ PairClass.inf S} => p.1.ht P ^ σ :=
  (PairClass.summable_ht_rpow S P hσ).subtype _

lemma Tinf_nonneg (S : Finset (FinitePlace F)) (σ : ℝ) (P : X F) : 0 ≤ Tinf S σ P :=
  tsum_nonneg fun p => Real.rpow_nonneg (p.1.ht_pos P).le _

/-- `Tinf` is invariant under upper triangular elements of `SL₂(𝓞_F)`. -/
theorem Tinf_smul_of_upper {γ : SL(2, 𝓞 F)} (h : γ 1 0 = 0) (σ : ℝ) (P : X F) :
    Tinf S σ (γ • P) = Tinf S σ P := by
  unfold Tinf
  rw [← (upperEquiv (S := S) h).tsum_eq fun p => p.1.ht P ^ σ]
  refine tsum_congr fun p => ?_
  change _ = (p.1.act γ).ht P ^ σ
  rw [PairClass.ht_act]

/-! ### Harnack in the horizontal variable -/

omit [IsTotallyComplex F] in
lemma rowDen_le_three (c d : ℂ) (Q Q' : H3) (hv : Q'.v = Q.v) (hx : ‖Q'.x - Q.x‖ ≤ Q.v) :
    H3.rowDen c d Q' ≤ 3 * H3.rowDen c d Q := by
  unfold H3.rowDen
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hv]
  have h1 : ‖c * Q'.x + d‖ ≤ ‖c * Q.x + d‖ + ‖c‖ * Q.v := by
    have e : c * Q'.x + d = (c * Q.x + d) + c * (Q'.x - Q.x) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖c * Q.x + d‖ - ‖c‖ * Q.v), norm_nonneg c, Q.v_pos,
    mul_nonneg (sq_nonneg ‖c‖) (sq_nonneg Q.v), sq_nonneg ‖c * Q.x + d‖]

omit [IsTotallyComplex F] in
lemma pairHt_harnack {c d : F} (hne : c ≠ 0 ∨ d ≠ 0) (x x' : InfinitePlace F → ℂ)
    (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) (hx : ∀ w, ‖x' w - x w‖ ≤ v w) :
    X.pairHt c d (X.mk x v hv) ≤
      3 ^ Fintype.card (InfinitePlace F) * X.pairHt c d (X.mk x' v hv) := by
  rw [X.pairHt_eq_prod, X.pairHt_eq_prod, ← Finset.card_univ, ← Finset.prod_const,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun w _ => div_nonneg (hv w).le (H3.rowDen_nonneg _ _ _)) fun w _ => ?_
  have hD := H3.rowDen_pos (c := w.embedding c) (d := w.embedding d) (by simpa using hne)
    (X.mk x v hv w)
  have hD' := H3.rowDen_pos (c := w.embedding c) (d := w.embedding d) (by simpa using hne)
    (X.mk x' v hv w)
  have key := rowDen_le_three (w.embedding c) (w.embedding d) (X.mk x v hv w) (X.mk x' v hv w) rfl
    (hx w)
  change v w / _ ≤ 3 * (v w / _)
  rw [← mul_div_assoc, div_le_div_iff₀ hD hD']
  nlinarith [hv w]

lemma PairClass.ht_harnack (p : PairClass S) (x x' : InfinitePlace F → ℂ)
    (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) (hx : ∀ w, ‖x' w - x w‖ ≤ v w) :
    p.ht (X.mk x v hv) ≤ 3 ^ Fintype.card (InfinitePlace F) * p.ht (X.mk x' v hv) := by
  rw [PairClass.ht_eq_out, PairClass.ht_eq_out]
  unfold X.sHt
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (pairHt_harnack p.out.ne_zero x x' v hv hx)
    (X.sNorm_pos S p.out.ne_zero).le

/-- **Harnack inequality for `Tinf` in `x`.** -/
theorem Tinf_harnack (S : Finset (FinitePlace F)) {σ : ℝ} (hσ : 2 < σ) (x x' : InfinitePlace F → ℂ)
    (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) (hx : ∀ w, ‖x' w - x w‖ ≤ v w) :
    Tinf S σ (X.mk x v hv) ≤
      ((3 : ℝ) ^ Fintype.card (InfinitePlace F)) ^ σ * Tinf S σ (X.mk x' v hv) := by
  unfold Tinf
  rw [← tsum_mul_left]
  refine (summable_Tinf S hσ _).tsum_le_tsum (fun p => ?_) ((summable_Tinf S hσ _).mul_left _)
  rw [← Real.mul_rpow (by positivity) (p.1.ht_pos _).le]
  exact Real.rpow_le_rpow (p.1.ht_pos _).le (p.1.ht_harnack x x' v hv hx) (by linarith)

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.B1_Const
attribute [-instance] _root_.ArtinKP.N.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instSigmaFiniteE1Mu1 _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.B.coe_latREquiv _root_.ArtinKP.B.embR_apply _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.X.chart1_symm_fst _root_.ArtinKP.X.chart1_symm_snd _root_.ArtinKP.X.chart1_v _root_.ArtinKP.X.chart1_x
/-! # WP-B1, file 6: the constant term of `Tinf` (Lemma K) by unfolding and scaling

`constTerm S σ v = ∫_{ℂ^r/𝓞} ∑_{p ≠ ∞} ht_p(x, v)^σ dx` (integral over the fundamental cell `fundD`).
Unfolding over the free action of the translations `n(β)`, `β ∈ 𝓞_F`, on the classes `≠ ∞`
(`orbEquiv`) turns it into a sum of integrals over all of `ℂ^r`, each of which scales exactly like
`ht(v)^{2-σ}` (`lintegral_sHt_scale`).  Hence `constTerm S σ v = ht(v)^{2-σ} · constTerm S σ 1`
(`constTerm_scale`), and `constTerm S σ 1 < ∞` by the locally uniform convergence (`constTerm_one_lt_top`).
No zeta function and no strong approximation are needed.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.B1

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

theorem instCountableField : Countable F := by
  haveI _iCO := ArtinKP.X.instCountableRingOfIntegers (F := F)
  have : Function.Surjective (fun p : 𝓞 F × 𝓞 F => ((p.1 : F) / (p.2 : F))) := by
    intro z
    obtain ⟨x, y, -, h⟩ := IsFractionRing.div_surjective (A := 𝓞 F) z
    exact ⟨(x, y), h⟩
  exact this.countable

instance instCountableSPair {S : Finset (FinitePlace F)} : Countable (SPair S) := by
  haveI _iCF := ArtinKP.B1.instCountableField (F := F)
  have : Function.Injective (fun q : SPair S => (q.c, q.d)) := by
    intro q q' h
    exact SPair.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  exact this.countable

instance instCountablePairClass {S : Finset (FinitePlace F)} : Countable (PairClass S) :=
  Quotient.countable

variable [IsTotallyComplex F]

/-! ### The lattice `𝓞_F ⊂ ℂ^r` -/

lemma isFund : IsAddFundamentalDomain (latSub F) (fundD F) volume :=
  ZSpan.isAddFundamentalDomain' (latE (F := F)) volume

lemma fundD_bounded : Bornology.IsBounded (fundD F) := ZSpan.fundamentalDomain_isBounded _

lemma measurableSet_fundD : MeasurableSet (fundD F) := ZSpan.fundamentalDomain_measurableSet _

/-- Unfolding over the lattice, indexed by `𝓞_F`. -/
lemma lintegral_eq_tsum_int (f : (InfinitePlace F → ℂ) → ℝ≥0∞) :
    ∫⁻ x, f x = ∑' β : 𝓞 F, ∫⁻ x in fundD F, f (x + emb (β : F)) := by
  rw [isFund.lintegral_eq_tsum' f, ← (latEquiv (F := F)).tsum_eq, ← (Equiv.neg (𝓞 F)).tsum_eq]
  refine tsum_congr fun β => ?_
  refine lintegral_congr fun x => ?_
  congr 1
  change -(emb (((-β : 𝓞 F)) : F)) + x = x + emb (β : F)
  simp [add_comm]

/-! ### Scaling -/

/-- Componentwise real scaling of `ℂ^r` multiplies Lebesgue measure by `∏ v_w²`. -/
lemma lintegral_comp_scale (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w)
    {g : (InfinitePlace F → ℂ) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x = ENNReal.ofReal (∏ w, v w ^ 2) *
      ∫⁻ y : InfinitePlace F → ℂ, g (fun w => (v w : ℂ) * y w) := by
  set A : (InfinitePlace F → ℂ) → (InfinitePlace F → ℂ) := fun y w => (v w : ℂ) * y w with hA
  have hAm : Measurable A := measurable_pi_iff.mpr fun w =>
    measurable_const.mul (measurable_pi_apply w)
  have hvol : (volume : Measure (InfinitePlace F → ℂ)) =
      ENNReal.ofReal (∏ w, v w ^ 2) • Measure.map A volume := by
    rw [volume_pi]
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.smul_apply, Measure.map_apply hAm (MeasurableSet.univ_pi hs)]
    have hpre : A ⁻¹' (Set.pi univ s) = Set.pi univ fun w => ((v w) • · : ℂ → ℂ) ⁻¹' s w := by
      ext y; simp [hA, Complex.real_smul]
    rw [hpre, ← volume_pi, volume_pi_pi, smul_eq_mul,
      ENNReal.ofReal_prod_of_nonneg (fun w _ => sq_nonneg _), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [Measure.addHaar_preimage_smul volume (hv w).ne', Complex.finrank_real_complex, ← mul_assoc,
      ← ENNReal.ofReal_mul (sq_nonneg _), abs_of_pos (inv_pos.mpr (pow_pos (hv w) 2)),
      mul_inv_cancel₀ (pow_ne_zero 2 (hv w).ne'), ENNReal.ofReal_one, one_mul]
  conv_lhs => rw [hvol]
  rw [lintegral_smul_measure, lintegral_map hg hAm, smul_eq_mul]

variable {S : Finset (FinitePlace F)}

lemma measurable_sHt_rpow {c d : F} (hne : c ≠ 0 ∨ d ≠ 0) (σ : ℝ) (v : InfinitePlace F → ℝ)
    (hv : ∀ w, 0 < v w) :
    Measurable fun x : InfinitePlace F → ℂ => ENNReal.ofReal (X.sHt S c d (X.mk x v hv) ^ σ) := by
  refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
  refine Continuous.rpow_const ?_ fun x => Or.inl (X.sHt_pos S hne _).ne'
  unfold X.sHt
  exact ((continuous_pairHt hne).comp (continuous_mk v hv)).div_const _

/-- **Exact scaling** of the full horizontal integral of one term: `∫_{ℂ^r} ht_{(c,d)}(x,v)^σ dx =
ht(v)^{2-σ} ∫_{ℂ^r} ht_{(c,d)}(y,1)^σ dy` for `c ≠ 0`. -/
theorem lintegral_sHt_scale {c d : F} (hc : c ≠ 0) (σ : ℝ) (v : InfinitePlace F → ℝ)
    (hv : ∀ w, 0 < v w) :
    ∫⁻ x, ENNReal.ofReal (X.sHt S c d (X.mk x v hv) ^ σ) =
      ENNReal.ofReal ((∏ w, v w) ^ (2 - σ)) * ∫⁻ y, ENNReal.ofReal (X.sHt S c d (mk1 y) ^ σ) := by
  set H : ℝ := ∏ w, v w with hH
  have hHpos : 0 < H := Finset.prod_pos fun w _ => hv w
  set t : InfinitePlace F → ℂ := fun w => ((v w : ℂ) - 1) * w.embedding d / w.embedding c with ht
  have hne : c ≠ 0 ∨ d ≠ 0 := Or.inl hc
  have hpt : ∀ y : InfinitePlace F → ℂ,
      X.sHt S c d (X.mk ((fun w => (v w : ℂ) * y w) + t) v hv) = H⁻¹ * X.sHt S c d (mk1 y) := by
    intro y
    unfold X.sHt
    rw [← mul_div_assoc]
    congr 1
    rw [X.pairHt_eq_prod, X.pairHt_eq_prod, hH, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    have hcw : w.embedding c ≠ 0 := (map_ne_zero _).mpr hc
    have hvw := hv w
    change v w / H3.rowDen _ _ (H3.mk _ (v w) _) = (v w)⁻¹ * (1 / H3.rowDen _ _ (H3.mk _ 1 _))
    unfold H3.rowDen
    change v w / (Complex.normSq (w.embedding c * ((v w : ℂ) * y w + t w) + w.embedding d) +
      Complex.normSq (w.embedding c) * v w ^ 2) = (v w)⁻¹ * (1 / (Complex.normSq
        (w.embedding c * y w + w.embedding d) + Complex.normSq (w.embedding c) * 1 ^ 2))
    have e : w.embedding c * ((v w : ℂ) * y w + t w) + w.embedding d =
        (v w : ℂ) * (w.embedding c * y w + w.embedding d) := by
      rw [ht]; field_simp; ring
    rw [e, map_mul, Complex.normSq_ofReal]
    have hD : 0 < Complex.normSq (w.embedding c * y w + w.embedding d) +
        Complex.normSq (w.embedding c) * 1 ^ 2 := by
      have := Complex.normSq_pos.mpr hcw
      have := Complex.normSq_nonneg (w.embedding c * y w + w.embedding d)
      nlinarith
    field_simp
  have hg := measurable_sHt_rpow (S := S) hne σ v hv
  calc ∫⁻ x, ENNReal.ofReal (X.sHt S c d (X.mk x v hv) ^ σ)
      = ∫⁻ x, ENNReal.ofReal (X.sHt S c d (X.mk (x + t) v hv) ^ σ) :=
        (lintegral_add_right_eq_self (fun x => ENNReal.ofReal (X.sHt S c d (X.mk x v hv) ^ σ)) t).symm
    _ = ENNReal.ofReal (∏ w, v w ^ 2) * ∫⁻ y : InfinitePlace F → ℂ, ENNReal.ofReal
          (X.sHt S c d (X.mk ((fun w => (v w : ℂ) * y w) + t) v hv) ^ σ) :=
        lintegral_comp_scale v hv (hg.comp (measurable_id.add_const t))
    _ = ENNReal.ofReal (H ^ 2) * ∫⁻ y, ENNReal.ofReal (H ^ (-σ)) *
          ENNReal.ofReal (X.sHt S c d (mk1 y) ^ σ) := by
        rw [Finset.prod_pow]
        congr 1
        refine lintegral_congr fun y => ?_
        rw [hpt y, Real.mul_rpow (inv_pos.mpr hHpos).le (X.sHt_pos S hne _).le,
          ENNReal.ofReal_mul (Real.rpow_nonneg (inv_pos.mpr hHpos).le _), Real.inv_rpow hHpos.le,
          Real.rpow_neg hHpos.le]
    _ = _ := by
        rw [lintegral_const_mul _ (measurable_sHt_rpow hne σ _ _), ← mul_assoc,
          ← ENNReal.ofReal_mul (sq_nonneg H)]
        congr 2
        rw [← Real.rpow_two, ← Real.rpow_add hHpos]
        congr 1

/-! ### Orbits of the translations on the classes `≠ ∞` -/

lemma orbEquiv_apply (ω : Quotient (transSetoid S)) (β : 𝓞 F) :
    (orbEquiv S (ω, β)).1 = ω.out.1.act (nInt β) := rfl

/-! ### The constant term -/

lemma measurable_ht_rpow (p : PairClass S) (σ : ℝ) (v : InfinitePlace F → ℝ)
    (hv : ∀ w, 0 < v w) :
    Measurable fun x : InfinitePlace F → ℂ => ENNReal.ofReal (p.ht (X.mk x v hv) ^ σ) := by
  simp only [PairClass.ht_eq_out]
  exact measurable_sHt_rpow p.out.ne_zero σ v hv

/-- Unfolding: the constant term is a sum over translation orbits of full horizontal integrals. -/
theorem constTerm_eq_orbits (S : Finset (FinitePlace F)) (σ : ℝ) (v : InfinitePlace F → ℝ)
    (hv : ∀ w, 0 < v w) :
    constTerm S σ v hv = ∑' ω : Quotient (transSetoid S),
      ∫⁻ x, ENNReal.ofReal (ω.out.1.ht (X.mk x v hv) ^ σ) := by
  unfold constTerm
  have hm : ∀ p : {p : PairClass S // p ≠ PairClass.inf S},
      AEMeasurable (fun x : InfinitePlace F → ℂ => ENNReal.ofReal (p.1.ht (X.mk x v hv) ^ σ))
        (volume.restrict (fundD F)) := fun p => (measurable_ht_rpow p.1 σ v hv).aemeasurable
  rw [lintegral_tsum hm]
  have h1 := (orbEquiv S).tsum_eq (fun p : {p : PairClass S // p ≠ PairClass.inf S} =>
    ∫⁻ x in fundD F, ENNReal.ofReal (p.1.ht (X.mk x v hv) ^ σ))
  rw [← h1, ENNReal.tsum_prod']
  refine tsum_congr fun ω => ?_
  rw [lintegral_eq_tsum_int]
  refine tsum_congr fun β => ?_
  refine lintegral_congr fun x => ?_
  rw [orbEquiv_apply, PairClass.ht_act, nInt_smul_mk]

/-- **Lemma K, scaling form**: `constTerm(v) = ht(v)^{2-σ} · constTerm(1)`. -/
theorem constTerm_scale (S : Finset (FinitePlace F)) (σ : ℝ) (v : InfinitePlace F → ℝ)
    (hv : ∀ w, 0 < v w) :
    constTerm S σ v hv = ENNReal.ofReal ((∏ w, v w) ^ (2 - σ)) *
      constTerm S σ (fun _ => 1) (fun _ => one_pos) := by
  rw [constTerm_eq_orbits, constTerm_eq_orbits, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun ω => ?_
  simp only [PairClass.ht_eq_out]
  have hc : ω.out.1.out.c ≠ 0 := SPair.c_ne_zero (by rw [Quotient.out_eq]; exact ω.out.2)
  exact lintegral_sHt_scale hc σ v hv

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.B1_Bound
attribute [-instance] _root_.ArtinKP.N.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instSigmaFiniteE1Mu1 _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
/-! # WP-B1, file 7: the majorant bound away from the top cusp (item 2)

`Tinf_le`: for `σ > 2` there is `K` with
`∑_{p ≠ ∞} ht_p(Q)^σ ≤ K · (ht(Q)^{2-σ} + ht(Q)^{-σ})` for **all** `Q ∈ X`.

Proof (MATH2 §1.3, with the average taken in `x` only): Harnack in `x` over the polydisc of radii
`v_w`, covering of the polydisc by translates of the fundamental cell (a volume count), the
constant term `constTerm v = ht(v)^{2-σ} constTerm 1 < ∞`, and Dirichlet's unit theorem to make
`v` balanced.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.B1

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {S : Finset (FinitePlace F)}

lemma ofReal_Tinf (S : Finset (FinitePlace F)) {σ : ℝ} (hσ : 2 < σ) (P : X F) :
    ENNReal.ofReal (Tinf S σ P) =
      ∑' p : {p : PairClass S // p ≠ PairClass.inf S}, ENNReal.ofReal (p.1.ht P ^ σ) :=
  ENNReal.ofReal_tsum_of_nonneg (fun p => Real.rpow_nonneg (p.1.ht_pos P).le _) (summable_Tinf S hσ P)

/-- The constant term at `v = 1` is finite. -/
theorem constTerm_one_lt_top (S : Finset (FinitePlace F)) {σ : ℝ} (hσ : 2 < σ) :
    constTerm S σ (fun _ => 1) (fun _ => one_pos) < ⊤ := by
  have hK : IsCompact ((fun x : InfinitePlace F → ℂ => mk1 x) '' closure (fundD F)) :=
    (fundD_bounded (F := F)).isCompact_closure.image (continuous_mk _ _)
  obtain ⟨u, hu, hub⟩ := PairClass.exists_summable_majorant S hK hσ (le_refl σ)
  have hbound : ∀ x ∈ fundD F, (∑' p : {p : PairClass S // p ≠ PairClass.inf S},
      ENNReal.ofReal (p.1.ht (mk1 x) ^ σ)) ≤ ENNReal.ofReal (∑' p : PairClass S, |u p|) := by
    intro x hx
    rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => abs_nonneg _) hu.abs]
    refine le_trans (ENNReal.tsum_le_tsum fun p => ?_)
      (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
        (fun p : PairClass S => ENNReal.ofReal |u p|))
    exact ENNReal.ofReal_le_ofReal ((hub _ ⟨x, subset_closure hx, rfl⟩ σ ⟨le_rfl, le_rfl⟩ p.1).trans
      (le_abs_self _))
  unfold constTerm
  refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_fundD hbound) ?_
  rw [setLIntegral_const]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (fundD_bounded (F := F)).measure_lt_top

omit [IsTotallyComplex F] in
lemma measurableSet_polydisc (x : InfinitePlace F → ℂ) (r : InfinitePlace F → ℝ) :
    MeasurableSet (polydisc x r) :=
  MeasurableSet.univ_pi fun _ => Metric.isClosed_closedBall.measurableSet

omit [IsTotallyComplex F] in
lemma volume_polydisc (x : InfinitePlace F → ℂ) (r : InfinitePlace F → ℝ) (hr : ∀ w, 0 ≤ r w) :
    volume (polydisc x r) = ENNReal.ofReal (∏ w, r w ^ 2 * Real.pi) := by
  unfold polydisc
  rw [volume_pi_pi, ENNReal.ofReal_prod_of_nonneg fun w _ => by have := Real.pi_pos; positivity]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Complex.volume_closedBall, ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (hr w)]
  congr 1
  rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]

lemma exists_fundD_diam : ∃ ρ : ℝ, 0 < ρ ∧ ∀ y ∈ fundD F, ∀ y' ∈ fundD F,
    ∀ w : InfinitePlace F, ‖y w - y' w‖ ≤ ρ := by
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp (fundD_bounded (F := F))
  refine ⟨max C 1, by positivity, fun y hy y' hy' w => ?_⟩
  have h1 : ‖(y - y') w‖ ≤ ‖y - y'‖ := norm_le_pi_norm (y - y') w
  have h2 := hC hy hy'
  rw [dist_eq_norm] at h2
  exact (h1.trans h2).trans (le_max_left _ _)

lemma volume_fundD_ne_zero : volume (fundD F) ≠ 0 := ZSpan.measure_fundamentalDomain_ne_zero _

lemma volume_fundD_ne_top : volume (fundD F) ≠ ⊤ := (fundD_bounded (F := F)).measure_lt_top.ne

/-- Lattice points in a polydisc: a volume count. -/
lemma count_le {ρ : ℝ} (hρ : ∀ y ∈ fundD F, ∀ y' ∈ fundD F, ∀ w : InfinitePlace F, ‖y w - y' w‖ ≤ ρ)
    (x : InfinitePlace F → ℂ) (v : InfinitePlace F → ℝ) {y' : InfinitePlace F → ℂ}
    (hy' : y' ∈ fundD F) :
    (∑' β : 𝓞 F, (polydisc x v).indicator (fun _ => (1 : ℝ≥0∞)) (y' + emb (β : F))) ≤
      volume (polydisc x fun w => v w + ρ) / volume (fundD F) := by
  haveI _iCO := ArtinKP.X.instCountableRingOfIntegers (F := F)
  rw [ENNReal.le_div_iff_mul_le (Or.inl volume_fundD_ne_zero) (Or.inl volume_fundD_ne_top)]
  have hm : MeasurableSet (polydisc x fun w => v w + ρ) := measurableSet_polydisc _ _
  calc (∑' β : 𝓞 F, (polydisc x v).indicator (fun _ => (1 : ℝ≥0∞)) (y' + emb (β : F))) *
        volume (fundD F)
      = ∫⁻ _ in fundD F, ∑' β : 𝓞 F,
          (polydisc x v).indicator (fun _ => (1 : ℝ≥0∞)) (y' + emb (β : F)) := by
        rw [setLIntegral_const]
    _ ≤ ∫⁻ y in fundD F, ∑' β : 𝓞 F,
          (polydisc x fun w => v w + ρ).indicator (fun _ => (1 : ℝ≥0∞)) (y + emb (β : F)) := by
        refine setLIntegral_mono' measurableSet_fundD fun y hy => ENNReal.tsum_le_tsum fun β => ?_
        by_cases hmem : y' + emb (β : F) ∈ polydisc x v
        · have hmem' : y + emb (β : F) ∈ polydisc x fun w => v w + ρ := by
            intro w _
            have h1 := hmem w (mem_univ w)
            rw [Metric.mem_closedBall, dist_eq_norm] at h1 ⊢
            have h2 := hρ y hy y' hy' w
            calc ‖(y + emb (β : F)) w - x w‖
                = ‖((y' + emb (β : F)) w - x w) + (y w - y' w)‖ := by
                  congr 1; simp only [Pi.add_apply]; ring
              _ ≤ ‖(y' + emb (β : F)) w - x w‖ + ‖y w - y' w‖ := norm_add_le _ _
              _ ≤ v w + ρ := add_le_add h1 h2
          rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem']
        · rw [Set.indicator_of_notMem hmem]; exact bot_le
    _ = volume (polydisc x fun w => v w + ρ) := by
        rw [← lintegral_indicator_one hm, lintegral_eq_tsum_int, lintegral_tsum]
        · rfl
        · intro β
          exact (((measurable_const (a := (1 : ℝ≥0∞))).indicator hm).comp
            (measurable_id.add_const _)).aemeasurable

lemma Tinf_mk_add_emb (σ : ℝ) (β : 𝓞 F) (y : InfinitePlace F → ℂ) (v : InfinitePlace F → ℝ)
    (hv : ∀ w, 0 < v w) :
    Tinf S σ (X.mk (y + emb (β : F)) v hv) = Tinf S σ (X.mk y v hv) := by
  rw [← nInt_smul_mk, Tinf_smul_of_upper (nInt_upper β)]

/-- **Box mean-value inequality** (average over the horizontal polydisc of radii `v_w`). -/
theorem average_le {ρ : ℝ}
    (hρ : ∀ y ∈ fundD F, ∀ y' ∈ fundD F, ∀ w : InfinitePlace F, ‖y w - y' w‖ ≤ ρ)
    {σ : ℝ} (hσ : 2 < σ) (x : InfinitePlace F → ℂ) (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) :
    ENNReal.ofReal (Tinf S σ (X.mk x v hv)) * volume (polydisc x v) ≤
      ENNReal.ofReal (((3 : ℝ) ^ Fintype.card (InfinitePlace F)) ^ σ) *
        (volume (polydisc x fun w => v w + ρ) / volume (fundD F) * constTerm S σ v hv) := by
  haveI _iCO := ArtinKP.X.instCountableRingOfIntegers (F := F)
  set τ : (InfinitePlace F → ℂ) → ℝ≥0∞ := fun y =>
    ∑' p : {p : PairClass S // p ≠ PairClass.inf S}, ENNReal.ofReal (p.1.ht (X.mk y v hv) ^ σ)
    with hτdef
  have hτ : ∀ y, τ y = ENNReal.ofReal (Tinf S σ (X.mk y v hv)) := fun y =>
    (ofReal_Tinf S hσ _).symm
  have hτm : Measurable τ := Measurable.ennreal_tsum fun p => measurable_ht_rpow p.1 σ v hv
  have hper : ∀ (y : InfinitePlace F → ℂ) (β : 𝓞 F), τ (y + emb (β : F)) = τ y := fun y β => by
    rw [hτ, hτ, Tinf_mk_add_emb]
  have hB := measurableSet_polydisc x v
  set N := volume (polydisc x fun w => v w + ρ) / volume (fundD F) with hN
  have h3 : (0 : ℝ) ≤ ((3 : ℝ) ^ Fintype.card (InfinitePlace F)) ^ σ := by positivity
  have hstep2 : ∫⁻ x' in polydisc x v, τ x' ≤ N * constTerm S σ v hv := by
    calc ∫⁻ x' in polydisc x v, τ x'
        = ∫⁻ x', (polydisc x v).indicator τ x' := (lintegral_indicator hB _).symm
      _ = ∑' β : 𝓞 F, ∫⁻ y in fundD F, (polydisc x v).indicator τ (y + emb (β : F)) :=
          lintegral_eq_tsum_int _
      _ = ∑' β : 𝓞 F, ∫⁻ y in fundD F,
            (polydisc x v).indicator (fun _ => (1 : ℝ≥0∞)) (y + emb (β : F)) * τ y := by
          refine tsum_congr fun β => lintegral_congr fun y => ?_
          by_cases hmem : y + emb (β : F) ∈ polydisc x v
          · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, hper, one_mul]
          · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, zero_mul]
      _ = ∫⁻ y in fundD F, ∑' β : 𝓞 F,
            (polydisc x v).indicator (fun _ => (1 : ℝ≥0∞)) (y + emb (β : F)) * τ y := by
          rw [lintegral_tsum]
          intro β
          exact ((((measurable_const (a := (1 : ℝ≥0∞))).indicator hB).comp
            (measurable_id.add_const _)).mul hτm).aemeasurable
      _ ≤ ∫⁻ y in fundD F, N * τ y := by
          refine setLIntegral_mono' measurableSet_fundD fun y hy => ?_
          rw [ENNReal.tsum_mul_right]
          exact mul_le_mul_left (count_le hρ x v hy) _
      _ = N * constTerm S σ v hv := by
          rw [lintegral_const_mul _ hτm]; rfl
  calc ENNReal.ofReal (Tinf S σ (X.mk x v hv)) * volume (polydisc x v)
      = ∫⁻ _ in polydisc x v, ENNReal.ofReal (Tinf S σ (X.mk x v hv)) := by
        rw [setLIntegral_const]
    _ ≤ ∫⁻ x' in polydisc x v,
          ENNReal.ofReal (((3 : ℝ) ^ Fintype.card (InfinitePlace F)) ^ σ) * τ x' := by
        refine setLIntegral_mono' hB fun x' hx' => ?_
        rw [hτ, ← ENNReal.ofReal_mul h3]
        refine ENNReal.ofReal_le_ofReal (Tinf_harnack S hσ x x' v hv fun w => ?_)
        have := hx' w (mem_univ w)
        rwa [Metric.mem_closedBall, dist_eq_norm] at this
    _ = ENNReal.ofReal (((3 : ℝ) ^ Fintype.card (InfinitePlace F)) ^ σ) *
          ∫⁻ x' in polydisc x v, τ x' := lintegral_const_mul _ hτm
    _ ≤ _ := mul_le_mul_right hstep2 _

omit [NumberField F] [IsTotallyComplex F] in
/-- Volume ratio of the enlarged polydisc, for balanced radii. -/
lemma prod_ratio_le {ι : Type*} [Fintype ι] [Nonempty ι] {C ρ : ℝ} (hC : 1 ≤ C) (hρ : 0 ≤ ρ)
    {v : ι → ℝ} (hv : ∀ i, 0 < v i) (hbal : ∀ i j, v i ≤ C * v j) :
    ∏ i, ((v i + ρ) ^ 2 * Real.pi) ≤
      (1 + ρ) ^ (2 * Fintype.card ι) * C ^ (2 * Fintype.card ι) * (1 + ((∏ i, v i) ^ 2)⁻¹) *
        ∏ i, (v i ^ 2 * Real.pi) := by
  classical
  obtain ⟨i₀, -, hmin⟩ := Finset.exists_min_image Finset.univ v ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  set m := v i₀ with hm
  have hm0 : 0 < m := hv i₀
  set r := Fintype.card ι with hr
  set H := ∏ i, v i with hH
  have hH0 : 0 < H := Finset.prod_pos fun i _ => hv i
  have hpi := Real.pi_pos
  set L := ((m + ρ) / m) ^ 2 with hL
  have h1 : ∏ i, ((v i + ρ) ^ 2 * Real.pi) ≤ L ^ r * ∏ i, (v i ^ 2 * Real.pi) := by
    rw [hr, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun i _ => by positivity) fun i _ => ?_
    have hvi := hv i
    have hmi : m ≤ v i := hmin i (Finset.mem_univ i)
    have h2 : (v i + ρ) / v i ≤ (m + ρ) / m := by
      rw [div_le_div_iff₀ hvi hm0]; nlinarith
    have h3 : ((v i + ρ) / v i) ^ 2 ≤ L := pow_le_pow_left₀ (by positivity) h2 2
    have e : (v i + ρ) ^ 2 * Real.pi = ((v i + ρ) / v i) ^ 2 * (v i ^ 2 * Real.pi) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right h3 (by positivity)
  have hHle : H ≤ (C * m) ^ r := by
    rw [hH, hr, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun i _ => (hv i).le) fun i _ => hbal i i₀
  have h2 : L ^ r ≤ (1 + ρ) ^ (2 * r) * C ^ (2 * r) * (1 + (H ^ 2)⁻¹) := by
    have hC2 : (1 : ℝ) ≤ C ^ (2 * r) := one_le_pow₀ hC
    have hHinv : 0 ≤ (H ^ 2)⁻¹ := by positivity
    have h1ρ : (1 : ℝ) ≤ (1 + ρ) ^ (2 * r) := one_le_pow₀ (by linarith)
    rw [hL, ← pow_mul]
    rcases le_or_gt 1 m with hm1 | hm1
    · have : (m + ρ) / m ≤ 1 + ρ := by rw [div_le_iff₀ hm0]; nlinarith
      calc ((m + ρ) / m) ^ (2 * r) ≤ (1 + ρ) ^ (2 * r) := pow_le_pow_left₀ (by positivity) this _
        _ = (1 + ρ) ^ (2 * r) * 1 * 1 := by ring
        _ ≤ _ := by gcongr; linarith
    · rw [div_pow]
      have ha : (m + ρ) ^ (2 * r) ≤ (1 + ρ) ^ (2 * r) :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      have hb : (m ^ (2 * r))⁻¹ ≤ C ^ (2 * r) * (H ^ 2)⁻¹ := by
        have hH2 : H ^ 2 ≤ C ^ (2 * r) * m ^ (2 * r) := by
          calc H ^ 2 ≤ ((C * m) ^ r) ^ 2 := pow_le_pow_left₀ hH0.le hHle 2
            _ = _ := by ring
        rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
      calc (m + ρ) ^ (2 * r) / m ^ (2 * r) = (m + ρ) ^ (2 * r) * (m ^ (2 * r))⁻¹ := div_eq_mul_inv _ _
        _ ≤ (1 + ρ) ^ (2 * r) * (C ^ (2 * r) * (H ^ 2)⁻¹) :=
          mul_le_mul ha hb (by positivity) (by positivity)
        _ ≤ _ := by
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith
  exact h1.trans (mul_le_mul_of_nonneg_right h2 (Finset.prod_nonneg fun i _ => by positivity))

/-- **Item 2 (majorant bound away from the cusp at infinity).** For `σ > 2` there is `K` such that
for all `Q ∈ X`: `∑_{p ≠ ∞} ht_p(Q)^σ ≤ K (ht(Q)^{2-σ} + ht(Q)^{-σ})`. -/
theorem Tinf_le (S : Finset (FinitePlace F)) {σ : ℝ} (hσ : 2 < σ) :
    ∃ K : ℝ, 0 < K ∧ ∀ Q : X F, Tinf S σ Q ≤ K * (X.ht Q ^ (2 - σ) + X.ht Q ^ (-σ)) := by
  obtain ⟨ρ, hρ0, hρ⟩ := exists_fundD_diam (F := F)
  obtain ⟨C, hC1, hbal⟩ := exists_unit_smul_balanced (F := F)
  set r := Fintype.card (InfinitePlace F) with hr
  obtain ⟨D', hD'def⟩ : ∃ D' : ℝ, D' = (volume (fundD F)).toReal := ⟨_, rfl⟩
  have hD' : 0 < D' := hD'def ▸ ENNReal.toReal_pos volume_fundD_ne_zero volume_fundD_ne_top
  have hDe : volume (fundD F) = ENNReal.ofReal D' := by
    rw [hD'def, ENNReal.ofReal_toReal volume_fundD_ne_top]
  obtain ⟨K1, hK1def⟩ : ∃ K1 : ℝ, K1 = (constTerm S σ (fun _ => 1) (fun _ => one_pos)).toReal :=
    ⟨_, rfl⟩
  have hK1 : 0 ≤ K1 := hK1def ▸ ENNReal.toReal_nonneg
  have hKe : constTerm S σ (fun _ => 1) (fun _ => one_pos) = ENNReal.ofReal K1 := by
    rw [hK1def, ENNReal.ofReal_toReal (constTerm_one_lt_top S hσ).ne]
  have hb : (0 : ℝ) ≤ ((3 : ℝ) ^ r) ^ σ := by positivity
  refine ⟨((3 : ℝ) ^ r) ^ σ * K1 / D' * ((1 + ρ) ^ (2 * r) * C ^ (2 * r)) + 1, by positivity,
    fun Q => ?_⟩
  obtain ⟨ε, hε⟩ := hbal Q
  have hT : Tinf S σ (unitDiag ε • Q) = Tinf S σ Q :=
    Tinf_smul_of_upper (by simp [unitDiag_coe]) σ Q
  have hht : X.ht (unitDiag ε • Q) = X.ht Q := ht_smul_of_upper (by simp [unitDiag_coe]) Q
  rw [← hT, ← hht]
  obtain ⟨Q', hQ'⟩ : ∃ Q' : X F, Q' = unitDiag ε • Q := ⟨_, rfl⟩
  rw [← hQ'] at hε ⊢
  have hv := Q'.v_pos
  have hQmk : Q' = X.mk Q'.x Q'.v hv := X.ext' rfl rfl
  set H := X.ht Q' with hH
  have hHpos : 0 < H := X.ht_pos Q'
  have hHprod : ∏ w, Q'.v w = H := rfl
  have havg := average_le (S := S) hρ hσ Q'.x Q'.v hv
  rw [← hQmk, constTerm_scale, hHprod, volume_polydisc _ _ (fun w => (hv w).le),
    volume_polydisc _ _ (fun w => by have := hv w; positivity), hDe, hKe] at havg
  set a := ∏ w, Q'.v w ^ 2 * Real.pi with ha
  set c := ∏ w, (Q'.v w + ρ) ^ 2 * Real.pi with hc
  have hpi := Real.pi_pos
  have ha0 : 0 < a := Finset.prod_pos fun w _ => by have := hv w; positivity
  have hc0 : 0 ≤ c := Finset.prod_nonneg fun w _ => by have := hv w; positivity
  have hT0 := Tinf_nonneg S σ Q'
  have he0 : 0 ≤ H ^ (2 - σ) := Real.rpow_nonneg hHpos.le _
  have e1 : ENNReal.ofReal (Tinf S σ Q') * ENNReal.ofReal a = ENNReal.ofReal (Tinf S σ Q' * a) :=
    (ENNReal.ofReal_mul hT0).symm
  have e2 : ENNReal.ofReal (((3 : ℝ) ^ r) ^ σ) * (ENNReal.ofReal c / ENNReal.ofReal D' *
      (ENNReal.ofReal (H ^ (2 - σ)) * ENNReal.ofReal K1)) =
      ENNReal.ofReal (((3 : ℝ) ^ r) ^ σ * (c / D' * (H ^ (2 - σ) * K1))) := by
    rw [ENNReal.ofReal_mul hb, ENNReal.ofReal_mul (div_nonneg hc0 hD'.le),
      ENNReal.ofReal_div_of_pos hD', ENNReal.ofReal_mul he0]
  rw [e1, e2] at havg
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp havg
  have hratio := prod_ratio_le hC1 hρ0.le hv hε
  rw [hHprod] at hratio
  change c ≤ (1 + ρ) ^ (2 * r) * C ^ (2 * r) * (1 + (H ^ 2)⁻¹) * a at hratio
  have hrp : H ^ (-σ) = H ^ (2 - σ) * (H ^ 2)⁻¹ := by
    rw [← Real.rpow_two, ← Real.rpow_neg hHpos.le, ← Real.rpow_add hHpos]
    congr 1; ring
  set M := (1 + ρ) ^ (2 * r) * C ^ (2 * r) with hM
  have hM0 : 0 ≤ M := by positivity
  -- `T a ≤ b (c / D') e K1 ≤ b (M (1 + H⁻²) a / D') e K1`
  have hmain : Tinf S σ Q' * a ≤
      (((3 : ℝ) ^ r) ^ σ * K1 / D' * M * (H ^ (2 - σ) + H ^ (-σ))) * a := by
    refine hreal.trans ?_
    rw [hrp]
    have h5 : c / D' ≤ M * (1 + (H ^ 2)⁻¹) * a / D' := div_le_div_of_nonneg_right hratio hD'.le
    calc ((3 : ℝ) ^ r) ^ σ * (c / D' * (H ^ (2 - σ) * K1))
        ≤ ((3 : ℝ) ^ r) ^ σ * (M * (1 + (H ^ 2)⁻¹) * a / D' * (H ^ (2 - σ) * K1)) := by
          gcongr
      _ = _ := by field_simp
  have hfin := le_of_mul_le_mul_right hmain ha0
  refine hfin.trans ?_
  have hsum0 : 0 ≤ H ^ (2 - σ) + H ^ (-σ) :=
    add_nonneg he0 (Real.rpow_nonneg hHpos.le _)
  nlinarith

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
-- module Solutions.Artin.KP.S_Basic
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-S, part 1: `S_f`-adic smallness, norms, the pairing `⟨·,·⟩` on `F`, rows of `SL₂(R)`

* `Small 𝔪 N x`: `v(x) ≤ exp(-N)` at every `v ∣ 𝔪` (`N : ℤ`; `N < 0` means "bounded").
* `absS 𝔪 x = |x|_{S_f}`, `normS 𝔪 c d = ‖(c,d)‖ = ∏_{v ∣ 𝔪} max(|c|_v, |d|_v)`.
* `brk ι P 𝔪 x y = ⟨x, y⟩ = ι (x, y)_S` for `x, y ≠ 0`, and `1` if `x = 0` or `y = 0`.
  With WP-A's orientation `⟨c, d⟩ = (d/c)(c/d)⁻¹` on coprime elements of `R` (`brk_reciprocity`).
* `sig`: Kubota's `σ_S` evaluated on a pair and a matrix, through `ι`.
* `Row 𝔪`: primitive pairs of `R = SInt 𝔪`; right action of `SL₂(R)`; scaling by `Rˣ`;
  `kappaRow` and its transformation laws (`kappaRow_act` is Lemma A5 on rows).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S

open ArtinKP.A

variable {F : Type*} [Field F] [NumberField F]

/-! ### Smallness at the places of `S_f` -/

/-! ### Absolute values at `S_f` -/

section abs

variable {𝔪 : Ideal (𝓞 F)}

open NumberField.HeightOneSpectrum

theorem normS_zero_left (d : F) : normS 𝔪 0 d = absS 𝔪 d := by
  simp only [normS, absS, map_zero]
  exact Finset.prod_congr rfl fun w _ => max_eq_right ((adicAbv F w).nonneg d)

end abs

/-! ### The pairing `⟨x, y⟩ = ι (x, y)_S` on `F` -/

/-! ### Kubota's `σ_S` on a pair and a matrix -/

/-! ### Primitive rows -/

/-! ### The Kubota symbol on rows -/

/-! ### The matrices `w` and `n(t)` -/

end ArtinKP.S
end
end

section
-- module Solutions.Artin.KP.B_Def
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-B0, part 1: the Eisenstein series of a twisted section

`eis Ψ s Q = ∑_{p ∈ Row 𝔪 / U_S} Ψ_s(p) · I_p(Q)^s` for a twisted section `Ψ : TSection ι 𝔪`,
`s : ℂ`, `Q : X F`.

* Indexing type: `RowClass 𝔪 = MulAction.orbitRel.Quotient (SInt 𝔪)ˣ (Row 𝔪)`; the summand is
  evaluated at `Quotient.out` and shown independent of the representative (`term_smul`,
  `term_out_mk`) by the product formula for `S`-units (`Ninf_mul_absS`).
* `sPl 𝔪 : Finset (FinitePlace F)` is the set `S_f` in the form B1 uses; `X.sNorm (sPl 𝔪) = normS 𝔪`,
  `IsSInt (sPl 𝔪) = membership in SInt 𝔪`, `IsSUnit (sPl 𝔪) = units of SInt 𝔪`.
* `RowClass.ht q Q = ht_q(Q) = I_q(Q)/‖q‖`; `eis_eq_tsum_ht : eis Ψ s Q = ∑ Ψ̃_s(q) ht_q(Q)^s`.
* Convergence for `Re s > 2` from `B1.summable_sHt_rpow` / `B1.exists_summable_majorant_sHt`.
* Automorphy: `eis Ψ s (γ • Q) = eis (translate γ⁻¹ Ψ) s Q` for `γ ∈ SL₂(R)` (note the inverse).
-/

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

open scoped MatrixGroups
open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### The places of `S_f` as finite places; `S`-integers and `S`-units -/

lemma mk_apply_eq (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    FinitePlace.mk v x = NumberField.HeightOneSpectrum.adicAbv F v x := by
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding]

lemma prod_sPl (f : FinitePlace F → ℝ) :
    ∏ v ∈ sPl 𝔪, f v = ∏ v ∈ CubicPkg.sFin 𝔪, f (FinitePlace.mk v) := by
  classical
  unfold sPl
  exact Finset.prod_image fun v _ v' _ h => FinitePlace.mk_eq_iff.mp h

/-- `∏_{v ∈ S_f} max(|c|_v, |d|_v)`: B1's `X.sNorm` is WP-S's `normS`. -/
theorem sNorm_sPl (c d : F) : X.sNorm (sPl 𝔪) c d = normS 𝔪 c d := by
  unfold X.sNorm normS
  rw [prod_sPl]
  simp only [mk_apply_eq]

theorem prod_sPl_eq_absS (x : F) : ∏ v ∈ sPl 𝔪, v x = absS 𝔪 x := by
  unfold absS
  rw [prod_sPl]
  simp only [mk_apply_eq]

lemma coe_sFin (h𝔪 : 𝔪 ≠ ⊥) :
    ((CubicPkg.sFin 𝔪 : Finset (HeightOneSpectrum (𝓞 F))) : Set (HeightOneSpectrum (𝓞 F)))
      = placesOf 𝔪 := by
  ext v
  simp [CubicPkg.mem_sFin h𝔪 v, placesOf]

/-- B1's `IsSInt (sPl 𝔪)` is membership in `R = SInt 𝔪`. -/
theorem isSInt_iff (h𝔪 : 𝔪 ≠ ⊥) (a : F) :
    IsSInt (sPl 𝔪) a ↔ a ∈ (placesOf 𝔪).integer F := by
  have h := isSInt_image_iff (CubicPkg.sFin 𝔪) a
  rw [coe_sFin h𝔪] at h
  exact h

theorem isSInt_coe (h𝔪 : 𝔪 ≠ ⊥) (a : SInt 𝔪) : IsSInt (sPl 𝔪) (a : F) :=
  (isSInt_iff h𝔪 _).mpr a.2

/-- Units of `R` are `S`-units in B1's sense. -/
theorem isSUnit_coe (h𝔪 : 𝔪 ≠ ⊥) (ε : (SInt 𝔪)ˣ) : IsSUnit (sPl 𝔪) ((ε : SInt 𝔪) : F) := by
  have h3 : ((ε : SInt 𝔪) : F) * (((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = 1 := by
    rw [← MulMemClass.coe_mul, ε.mul_inv]
    rfl
  refine ⟨left_ne_zero_of_mul_eq_one h3, fun v hv => ?_⟩
  have h1 := isSInt_coe h𝔪 (ε : SInt 𝔪) v hv
  have h2 := isSInt_coe h𝔪 ((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) v hv
  have h4 : v ((ε : SInt 𝔪) : F) * v (((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = 1 := by
    rw [← map_mul, h3, map_one]
  have h5 : 0 ≤ v ((ε : SInt 𝔪) : F) := apply_nonneg v _
  nlinarith

/-- `S`-units in B1's sense are units of `R`. -/
theorem exists_unit_of_isSUnit (h𝔪 : 𝔪 ≠ ⊥) {u : F} (hu : IsSUnit (sPl 𝔪) u) :
    ∃ ε : (SInt 𝔪)ˣ, ((ε : SInt 𝔪) : F) = u :=
  ⟨⟨⟨u, (isSInt_iff h𝔪 u).mp hu.isSInt⟩, ⟨u⁻¹, (isSInt_iff h𝔪 _).mp hu.inv.isSInt⟩,
    Subtype.ext (mul_inv_cancel₀ hu.1), Subtype.ext (inv_mul_cancel₀ hu.1)⟩, rfl⟩

/-! ### The product formula for `S`-units -/

theorem Ninf_pos {x : F} (hx : x ≠ 0) : 0 < Ninf x :=
  Finset.prod_pos fun _ _ => Complex.normSq_pos.mpr ((map_ne_zero _).mpr hx)

/-- Product formula for an `S`-unit in B1's sense, any finite set `T` of finite places. -/
theorem Ninf_mul_prod_of_isSUnit [IsTotallyComplex F] (T : Finset (FinitePlace F)) {u : F}
    (hu : IsSUnit T u) : Ninf u * ∏ v ∈ T, v u = 1 := by
  have h2 : ∏ᶠ v : FinitePlace F, v u = ∏ v ∈ T, v u := by
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra hvT
    exact hv (hu.2 v hvT)
  rw [← h2, X.finprod_finitePlace hu.1]
  exact mul_inv_cancel₀ (Ninf_pos hu.1).ne'

/-- **Product formula for `S`-units**: `N_∞(ε) · |ε|_{S_f} = 1` for `ε ∈ (SInt 𝔪)ˣ`
(WP-S open issue 7). -/
theorem Ninf_mul_absS [IsTotallyComplex F] (h𝔪 : 𝔪 ≠ ⊥) (ε : (SInt 𝔪)ˣ) :
    Ninf ((ε : SInt 𝔪) : F) * absS 𝔪 ((ε : SInt 𝔪) : F) = 1 := by
  rw [← prod_sPl_eq_absS]
  exact Ninf_mul_prod_of_isSUnit _ (isSUnit_coe h𝔪 ε)

/-- `I_{εp} = N_∞(ε)⁻¹ I_p = |ε|_{S_f} I_p` for `ε ∈ U_S`. -/
theorem pairHt_unit_smul [IsTotallyComplex F] (h𝔪 : 𝔪 ≠ ⊥) (ε : (SInt 𝔪)ˣ) (c d : F) (Q : X F) :
    X.pairHt (((ε : SInt 𝔪) : F) * c) (((ε : SInt 𝔪) : F) * d) Q
      = absS 𝔪 ((ε : SInt 𝔪) : F) * X.pairHt c d Q := by
  have h := Ninf_mul_absS h𝔪 ε
  have hN : Ninf ((ε : SInt 𝔪) : F) ≠ 0 := left_ne_zero_of_mul_eq_one h
  rw [X.pairHt_smul_pair]
  change X.pairHt c d Q / Ninf ((ε : SInt 𝔪) : F) = _
  rw [div_eq_iff hN, mul_comm (absS 𝔪 _), mul_assoc, mul_comm (absS 𝔪 _), h, mul_one]

/-! ### Rows modulo `S`-units -/

namespace RowClass

theorem exists_out_eq_smul (p : Row 𝔪) : ∃ ε : (SInt 𝔪)ˣ, (mk p).out = ε • p := by
  have h : MulAction.orbitRel (SInt 𝔪)ˣ (Row 𝔪) (mk p).out p := Quotient.exact' (mk_out (mk p))
  obtain ⟨ε, hε⟩ := MulAction.orbitRel_apply.mp h
  exact ⟨ε, hε.symm⟩

/-- A `U_S`-invariant function of rows may be evaluated at any representative. -/
theorem apply_out_mk {α : Type*} (f : Row 𝔪 → α) (hf : ∀ (ε : (SInt 𝔪)ˣ) (p : Row 𝔪), f (ε • p) = f p)
    (p : Row 𝔪) : f (mk p).out = f p := by
  obtain ⟨ε, hε⟩ := exists_out_eq_smul p
  rw [hε, hf]

end RowClass

/-- The `S`-normalized height of a row: `I_p(Q) / ‖p‖`. -/
theorem sHt_row (p : Row 𝔪) (Q : X F) :
    X.sHt (sPl 𝔪) (p.c : F) (p.d : F) Q = X.pairHt (p.c : F) (p.d : F) Q / p.norm := by
  unfold X.sHt Row.norm
  rw [sNorm_sPl]

/-! ### Convergence of the height series over row classes (from WP-B1) -/

lemma rowClass_family_inj (h𝔪 : 𝔪 ≠ ⊥) (i j : RowClass 𝔪)
    (h : ∃ u : F, IsSUnit (sPl 𝔪) u ∧
      ((j.out.c : F), (j.out.d : F)) = (u * (i.out.c : F), u * (i.out.d : F))) : i = j := by
  obtain ⟨u, hu, he⟩ := h
  obtain ⟨ε, rfl⟩ := exists_unit_of_isSUnit h𝔪 hu
  have hj : j.out = ε • i.out := by
    refine Row.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · rw [Row.smul_c]; exact congrArg Prod.fst he
    · rw [Row.smul_d]; exact congrArg Prod.snd he
  rw [← RowClass.mk_out i, ← RowClass.mk_out j, hj, RowClass.mk_smul]

/-- **(B1)** `∑_q ht_q(Q)^σ < ∞` for `σ > 2`, over row classes. -/
theorem RowClass.summable_ht_rpow [IsTotallyComplex F] (h𝔪 : 𝔪 ≠ ⊥) (Q : X F) {σ : ℝ}
    (hσ : 2 < σ) : Summable fun q : RowClass 𝔪 => q.ht Q ^ σ :=
  summable_sHt_rpow (sPl 𝔪) (fun q : RowClass 𝔪 => ((q.out.c : F), (q.out.d : F)))
    (fun _ => ⟨isSInt_coe h𝔪 _, isSInt_coe h𝔪 _⟩) (fun q => q.out.ne_zero)
    (rowClass_family_inj h𝔪) Q hσ

/-- **(B1), locally uniform**: a summable majorant on `K × [σ₁, σ₂]`. -/
theorem RowClass.exists_summable_majorant [IsTotallyComplex F] (h𝔪 : 𝔪 ≠ ⊥) {K : Set (X F)}
    (hK : IsCompact K) {σ₁ σ₂ : ℝ} (hσ₁ : 2 < σ₁) (hσ : σ₁ ≤ σ₂) :
    ∃ u : RowClass 𝔪 → ℝ, Summable u ∧ ∀ Q ∈ K, ∀ σ ∈ Set.Icc σ₁ σ₂, ∀ q : RowClass 𝔪,
      q.ht Q ^ σ ≤ u q :=
  exists_summable_majorant_sHt (sPl 𝔪) (fun q : RowClass 𝔪 => ((q.out.c : F), (q.out.d : F)))
    (fun _ => ⟨isSInt_coe h𝔪 _, isSInt_coe h𝔪 _⟩) (fun q => q.out.ne_zero)
    (rowClass_family_inj h𝔪) hK hσ₁ hσ

/-! ### The summand and the series -/

theorem _root_.ArtinKP.S.TSection.isHom {ι : F →+* ℂ} (Ψ : TSection ι 𝔪) (s : ℂ) : IsHom (Ψ s) s :=
  fun ε p => Ψ.hom s ε p

theorem IsHom.act {ψ : Row 𝔪 → ℂ} {s : ℂ} (hψ : IsHom ψ s) (γ : SL(2, SInt 𝔪)) :
    IsHom (fun p => ψ (p.act γ)) s := fun ε p => by
  change ψ ((ε • p).act γ) = _
  rw [Row.smul_act, hψ]

lemma unit_coe_ne_zero (ε : (SInt 𝔪)ˣ) : ((ε : SInt 𝔪) : F) ≠ 0 := by
  have h3 : ((ε : SInt 𝔪) : F) * (((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = 1 := by
    rw [← MulMemClass.coe_mul, ε.mul_inv]
    rfl
  exact left_ne_zero_of_mul_eq_one h3

/-- **The summand is invariant under `p ↦ εp`**, `ε ∈ U_S` (product formula). -/
theorem term_smul [IsTotallyComplex F] (h𝔪 : 𝔪 ≠ ⊥) {ψ : Row 𝔪 → ℂ} {s : ℂ} (hψ : IsHom ψ s)
    (ε : (SInt 𝔪)ˣ) (p : Row 𝔪) (Q : X F) : term ψ s Q (ε • p) = term ψ s Q p := by
  have ha : 0 < absS 𝔪 ((ε : SInt 𝔪) : F) := absS_pos (unit_coe_ne_zero ε)
  have hI : 0 ≤ X.pairHt (p.c : F) (p.d : F) Q := (X.pairHt_pos p.ne_zero Q).le
  have e : X.pairHt ((ε • p).c : F) ((ε • p).d : F) Q
      = absS 𝔪 ((ε : SInt 𝔪) : F) * X.pairHt (p.c : F) (p.d : F) Q := by
    rw [← pairHt_unit_smul h𝔪 ε, Row.smul_c, Row.smul_d]
    rfl
  have ha' : ((absS 𝔪 ((ε : SInt 𝔪) : F) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have h1 : ((absS 𝔪 ((ε : SInt 𝔪) : F) : ℝ) : ℂ) ^ (-s) *
      ((absS 𝔪 ((ε : SInt 𝔪) : F) : ℝ) : ℂ) ^ s = 1 := by
    rw [← Complex.cpow_add _ _ ha', neg_add_cancel, Complex.cpow_zero]
  unfold term
  rw [hψ, e, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg ha.le hI]
  linear_combination (ψ p * ((X.pairHt (p.c : F) (p.d : F) Q : ℝ) : ℂ) ^ s) * h1

theorem term_out_mk [IsTotallyComplex F] (h𝔪 : 𝔪 ≠ ⊥) {ψ : Row 𝔪 → ℂ} {s : ℂ} (hψ : IsHom ψ s)
    (Q : X F) (p : Row 𝔪) : term ψ s Q (RowClass.mk p).out = term ψ s Q p :=
  RowClass.apply_out_mk (term ψ s Q) (fun ε p => term_smul h𝔪 hψ ε p Q) p

theorem eis_def {ι : F →+* ℂ} (Ψ : TSection ι 𝔪) (s : ℂ) (Q : X F) :
    eis Ψ s Q = ∑' q : RowClass 𝔪, term (Ψ s) s Q q.out := rfl

/-! ### Height form (MATH2 §0.2) -/

section height

variable {ι : F →+* ℂ}

/-- `Ψ_s(p) I_p(Q)^s = Ψ̃_s(p) · ht_p(Q)^s`. -/
theorem term_eq_tilde (Ψ : TSection ι 𝔪) (s : ℂ) (Q : X F) (p : Row 𝔪) :
    term (Ψ s) s Q p
      = Ψ.tilde s p * ((X.sHt (sPl 𝔪) (p.c : F) (p.d : F) Q : ℝ) : ℂ) ^ s := by
  have hn := p.norm_pos
  have hh := X.sHt_pos (sPl 𝔪) p.ne_zero Q
  have e : X.pairHt (p.c : F) (p.d : F) Q
      = X.sHt (sPl 𝔪) (p.c : F) (p.d : F) Q * p.norm := by
    rw [sHt_row, div_mul_cancel₀ _ hn.ne']
  unfold term TSection.tilde
  rw [e, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hh.le hn.le]
  ring

/-- `Ψ̃` is `U_S`-invariant. -/
theorem tilde_smul (Ψ : TSection ι 𝔪) (s : ℂ) (ε : (SInt 𝔪)ˣ) (p : Row 𝔪) :
    Ψ.tilde s (ε • p) = Ψ.tilde s p := by
  have ha : 0 < absS 𝔪 ((ε : SInt 𝔪) : F) := absS_pos (unit_coe_ne_zero ε)
  have ha' : ((absS 𝔪 ((ε : SInt 𝔪) : F) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have h1 : ((absS 𝔪 ((ε : SInt 𝔪) : F) : ℝ) : ℂ) ^ (-s) *
      ((absS 𝔪 ((ε : SInt 𝔪) : F) : ℝ) : ℂ) ^ s = 1 := by
    rw [← Complex.cpow_add _ _ ha', neg_add_cancel, Complex.cpow_zero]
  have e : (ε • p).norm = absS 𝔪 ((ε : SInt 𝔪) : F) * p.norm := by
    unfold Row.norm
    rw [← normS_mul_left, Row.smul_c, Row.smul_d]
    rfl
  unfold TSection.tilde
  rw [Ψ.hom, e, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg ha.le p.norm_pos.le]
  linear_combination (Ψ s p * ((p.norm : ℝ) : ℂ) ^ s) * h1

theorem tildeC_mk (Ψ : TSection ι 𝔪) (s : ℂ) (p : Row 𝔪) :
    tildeC Ψ s (RowClass.mk p) = Ψ.tilde s p :=
  RowClass.apply_out_mk (Ψ.tilde s) (tilde_smul Ψ s) p

theorem term_out_eq (Ψ : TSection ι 𝔪) (s : ℂ) (Q : X F) (q : RowClass 𝔪) :
    term (Ψ s) s Q q.out = tildeC Ψ s q * ((q.ht Q : ℝ) : ℂ) ^ s :=
  term_eq_tilde Ψ s Q q.out

/-- **Orbit form** (MATH2 §0.2): `E_Ψ(Q, s) = ∑_q Ψ̃_s(q) · ht_q(Q)^s`. -/
theorem eis_eq_tsum_ht (Ψ : TSection ι 𝔪) (s : ℂ) (Q : X F) :
    eis Ψ s Q = ∑' q : RowClass 𝔪, tildeC Ψ s q * ((q.ht Q : ℝ) : ℂ) ^ s := by
  rw [eis_def]
  exact tsum_congr fun q => term_out_eq Ψ s Q q

/-! ### Bounds and convergence -/

/-- `|Ψ_s(q) I_q(Q)^s| ≤ B · ht_q(Q)^{Re s}`, `B` uniform on `‖s‖ ≤ M` (and in `Q`, `q`). -/
theorem exists_norm_term_le (Ψ : TSection ι 𝔪) (M : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, ‖s‖ ≤ M → ∀ (Q : X F) (q : RowClass 𝔪),
      ‖term (Ψ s) s Q q.out‖ ≤ B * q.ht Q ^ s.re := by
  obtain ⟨B, hB⟩ := Ψ.bound M
  refine ⟨max B 0, le_max_right _ _, fun s hs Q q => ?_⟩
  have hI := X.pairHt_pos q.out.ne_zero Q
  have hn := q.out.norm_pos
  have h1 := hB s hs q.out
  have e : q.ht Q ^ s.re
      = q.out.norm ^ (-s.re) * X.pairHt (q.out.c : F) (q.out.d : F) Q ^ s.re := by
    unfold RowClass.ht
    rw [sHt_row, Real.div_rpow hI.le hn.le, Real.rpow_neg hn.le]
    ring
  unfold term
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hI, e, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right (h1.trans ?_) (Real.rpow_nonneg hI.le _)
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hn.le _)

variable [IsTotallyComplex F]

/-- **Absolute convergence** for `Re s > 2`. -/
theorem summable_norm_term (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) {s : ℂ} (hs : 2 < s.re) (Q : X F) :
    Summable fun q : RowClass 𝔪 => ‖term (Ψ s) s Q q.out‖ := by
  obtain ⟨B, -, hB⟩ := exists_norm_term_le Ψ ‖s‖
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => hB s le_rfl Q q)
    ((RowClass.summable_ht_rpow h𝔪 Q hs).mul_left B)

theorem summable_term (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) {s : ℂ} (hs : 2 < s.re) (Q : X F) :
    Summable fun q : RowClass 𝔪 => term (Ψ s) s Q q.out :=
  (summable_norm_term h𝔪 Ψ hs Q).of_norm

/-- **Locally uniform absolute convergence**: a summable majorant of the summands for
`Q ∈ K` (compact), `σ₁ ≤ Re s`, `‖s‖ ≤ M`, `σ₁ > 2`. -/
theorem exists_summable_majorant_term (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) {K : Set (X F)}
    (hK : IsCompact K) {σ₁ : ℝ} (hσ₁ : 2 < σ₁) (M : ℝ) :
    ∃ u : RowClass 𝔪 → ℝ, Summable u ∧ ∀ Q ∈ K, ∀ s : ℂ, σ₁ ≤ s.re → ‖s‖ ≤ M →
      ∀ q : RowClass 𝔪, ‖term (Ψ s) s Q q.out‖ ≤ u q := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_term_le Ψ M
  obtain ⟨u, hu, hub⟩ := RowClass.exists_summable_majorant h𝔪 hK hσ₁ (le_max_left σ₁ M)
  refine ⟨fun q => B * u q, hu.mul_left B, fun Q hQ s hs1 hs2 q => ?_⟩
  refine (hB s hs2 Q q).trans (mul_le_mul_of_nonneg_left ?_ hB0)
  exact hub Q hQ s.re ⟨hs1, ((Complex.re_le_norm s).trans hs2).trans (le_max_right _ _)⟩ q

end height

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.B_Def2
attribute [-instance] _root_.ArtinKP.B1.instCountablePairClass _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap _root_.ArtinKP.RO.rowClassEquiv_mk _root_.ArtinKP.RO.rowPair_c _root_.ArtinKP.RO.rowPair_d _root_.ArtinKP.S.GSection.twist_apply _root_.ArtinKP.X.chart1_symm_fst _root_.ArtinKP.X.chart1_symm_snd _root_.ArtinKP.X.chart1_v _root_.ArtinKP.X.chart1_x _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
/-!
# WP-B0, part 2: regularity, automorphy, the term at `(0, 1)`

* `continuousOn_eis`: joint continuity of `(s, Q) ↦ E_Ψ(Q, s)` on `{Re s > 2} × X`;
  `continuous_eis`, `measurable_eis` (in `Q`); `differentiableOn_eis` (holomorphy in `s`).
* `eis_smul`: `E_Ψ(γ • Q) = E_{γ⁻¹·Ψ}(Q)` for `γ ∈ SL₂(R)` (the action on `X` through `toF 𝔪`),
  equivalently `eis_translate`: `E_{γ·Ψ}(Q) = E_Ψ(γ⁻¹ • Q)`.
* `TSection.stab Ψ`, `eis_smul_of_mem_stab`; `exists_level_eis`, `exists_level_eis_invariant`.
* `eis_eq_add`: `E_Ψ = Ψ_s(0,1) ht^s + ∑_{q ≠ ∞} Ψ̃_s(q) ht_q^s`.
-/

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

open scoped MatrixGroups
open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {ι : F →+* ℂ}

/-! ### Local compactness of `X` -/

theorem locallyCompactSpace_H3 : LocallyCompactSpace H3 :=
  (isOpen_lt (continuous_const : Continuous fun _ : ℂ × ℝ => (0 : ℝ))
    continuous_snd).locallyCompactSpace

theorem locallyCompactSpace_X : LocallyCompactSpace (X F) := by
  have := locallyCompactSpace_H3
  infer_instance

/-! ### Regularity of the summands -/

theorem continuous_term (Ψ : TSection ι 𝔪) (p : Row 𝔪) :
    Continuous fun z : ℂ × X F => term (Ψ z.1) z.1 z.2 p := by
  unfold term
  refine ((Ψ.holo p).continuous.comp continuous_fst).mul ?_
  refine Continuous.cpow (Complex.continuous_ofReal.comp
    ((continuous_pairHt p.ne_zero).comp continuous_snd)) continuous_fst fun z => ?_
  exact Complex.ofReal_mem_slitPlane.mpr (X.pairHt_pos p.ne_zero z.2)

section analytic

variable [IsTotallyComplex F]

/-- **Joint continuity** of `(s, Q) ↦ E_Ψ(Q, s)` on `{Re s > 2} × X`. -/
theorem continuousOn_eis (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) :
    ContinuousOn (fun z : ℂ × X F => eis Ψ z.1 z.2) {z | 2 < z.1.re} := by
  have := locallyCompactSpace_X (F := F)
  intro z hz
  have hz' : 2 < z.1.re := hz
  refine ContinuousAt.continuousWithinAt ?_
  set δ : ℝ := (z.1.re - 2) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds z.2
  obtain ⟨u, hu, hub⟩ := exists_summable_majorant_term h𝔪 Ψ hK
    (σ₁ := z.1.re - δ) (by rw [hδ]; linarith) (‖z.1‖ + δ)
  have hT : Metric.closedBall z.1 δ ×ˢ K ∈ nhds z := by
    have : z = (z.1, z.2) := rfl
    rw [this]
    exact prod_mem_nhds (Metric.closedBall_mem_nhds _ hδ0) hKn
  have hcont : ContinuousOn (fun z : ℂ × X F => ∑' q : RowClass 𝔪, term (Ψ z.1) z.1 z.2 q.out)
      (Metric.closedBall z.1 δ ×ˢ K) := by
    refine continuousOn_tsum (fun q => (continuous_term Ψ q.out).continuousOn) hu ?_
    rintro q ⟨s, Q⟩ ⟨hs, hQ⟩
    have hs' : ‖s - z.1‖ ≤ δ := by simpa [dist_eq_norm] using hs
    refine hub Q hQ s ?_ ?_ q
    · have h1 : |(s - z.1).re| ≤ ‖s - z.1‖ := Complex.abs_re_le_norm _
      have h2 := (abs_le.mp (h1.trans hs')).1
      rw [Complex.sub_re] at h2
      linarith
    · calc ‖s‖ = ‖z.1 + (s - z.1)‖ := by rw [add_sub_cancel]
        _ ≤ ‖z.1‖ + ‖s - z.1‖ := norm_add_le _ _
        _ ≤ ‖z.1‖ + δ := by linarith
  exact hcont.continuousAt hT

/-- Continuity in `Q` for `Re s > 2`. -/
theorem continuous_eis (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) {s : ℂ} (hs : 2 < s.re) :
    Continuous fun Q : X F => eis Ψ s Q :=
  (continuousOn_eis h𝔪 Ψ).comp_continuous (f := fun Q : X F => ((s, Q) : ℂ × X F))
    (by fun_prop) fun _ => hs

theorem measurable_eis (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) {s : ℂ} (hs : 2 < s.re) :
    Measurable fun Q : X F => eis Ψ s Q :=
  (continuous_eis h𝔪 Ψ hs).measurable

end analytic

/-! ### Automorphy by reindexing -/

/-- `I_p(γ • Q) = I_{pγ}(Q)` for `γ ∈ SL₂(R)`, acting on `X` through `toF 𝔪 γ ∈ SL₂(F)`. -/
theorem pairHt_toF_smul (p : Row 𝔪) (γ : SL(2, SInt 𝔪)) (Q : X F) :
    X.pairHt (p.c : F) (p.d : F) (toF 𝔪 γ • Q)
      = X.pairHt ((p.act γ).c : F) ((p.act γ).d : F) Q := by
  rw [X.pairHt_smul, Row.act_c, Row.act_d]
  rfl

theorem term_toF_smul (ψ : Row 𝔪 → ℂ) (s : ℂ) (γ : SL(2, SInt 𝔪)) (Q : X F) (p : Row 𝔪) :
    term ψ s (toF 𝔪 γ • Q) p = term (fun p' => ψ (p'.act γ⁻¹)) s Q (p.act γ) := by
  unfold term
  rw [pairHt_toF_smul]
  simp only [← Row.act_mul, mul_inv_cancel, Row.act_one]

section auto

variable [IsTotallyComplex F]

/-- **Automorphy by reindexing `p ↦ pγ`**, raw form:
`∑_p ψ(p) I_p(γQ)^s = ∑_p ψ(pγ⁻¹) I_p(Q)^s`.  No convergence hypothesis. -/
theorem eisRaw_smul (h𝔪 : 𝔪 ≠ ⊥) {ψ : Row 𝔪 → ℂ} {s : ℂ} (hψ : IsHom ψ s)
    (γ : SL(2, SInt 𝔪)) (Q : X F) :
    eisRaw ψ s (toF 𝔪 γ • Q) = eisRaw (fun p => ψ (p.act γ⁻¹)) s Q := by
  unfold eisRaw
  rw [← (RowClass.actEquiv γ).tsum_eq
    (fun q : RowClass 𝔪 => term (fun p => ψ (p.act γ⁻¹)) s Q q.out)]
  refine tsum_congr fun q => ?_
  have e : RowClass.actEquiv γ q = RowClass.mk (q.out.act γ) := by
    rw [RowClass.actEquiv_apply, ← RowClass.act_mk, RowClass.mk_out]
  rw [e, term_out_mk h𝔪 (hψ.act γ⁻¹), term_toF_smul]

/-- A scalar relation `ψ(pγ⁻¹) = χ ψ(p)` gives `E(γQ) = χ E(Q)`. -/
theorem eisRaw_smul_of_scalar (h𝔪 : 𝔪 ≠ ⊥) {ψ : Row 𝔪 → ℂ} {s : ℂ} (hψ : IsHom ψ s)
    (γ : SL(2, SInt 𝔪)) (χ : ℂ) (h : ∀ p, ψ (p.act γ⁻¹) = χ * ψ p) (Q : X F) :
    eisRaw ψ s (toF 𝔪 γ • Q) = χ * eisRaw ψ s Q := by
  rw [eisRaw_smul h𝔪 hψ]
  unfold eisRaw
  rw [← tsum_mul_left]
  refine tsum_congr fun q => ?_
  unfold term
  change ψ (q.out.act γ⁻¹) * _ = _
  rw [h, mul_assoc]

end auto

theorem _root_.ArtinKP.S.TSection.mem_stab {Ψ : TSection ι 𝔪} {γ : SL(2, SInt 𝔪)} :
    γ ∈ Ψ.stab ↔ ∀ (s : ℂ) (p : Row 𝔪), Ψ s (p.act γ) = Ψ s p := Iff.rfl

section auto2

variable [IsTotallyComplex F]

/-- **Invariance**: `E_Ψ(γ • Q) = E_Ψ(Q)` for `γ` in the stabilizer of `Ψ`. -/
theorem eis_smul_of_mem_stab (h𝔪 : 𝔪 ≠ ⊥) {Ψ : TSection ι 𝔪} {γ : SL(2, SInt 𝔪)}
    (hγ : γ ∈ Ψ.stab) (s : ℂ) (Q : X F) : eis Ψ s (toF 𝔪 γ • Q) = eis Ψ s Q := by
  have h := eisRaw_smul_of_scalar h𝔪 (Ψ.isHom s) γ 1
    (fun p => by rw [one_mul]; exact Ψ.stab.inv_mem hγ s p) Q
  rw [one_mul] at h
  exact h

end auto2

/-- The action of `SL₂(𝓞_F)` on `X` (WP-X, WP-B1) is the action of its image in `SL₂(R)`. -/
theorem toF_map_int (γ₀ : SL(2, 𝓞 F)) :
    toF 𝔪 (Matrix.SpecialLinearGroup.map (algebraMap (𝓞 F) (SInt 𝔪)) γ₀) = intSL F γ₀ := by
  ext i j
  rfl

theorem toF_map_int_smul (γ₀ : SL(2, 𝓞 F)) (Q : X F) :
    toF 𝔪 (Matrix.SpecialLinearGroup.map (algebraMap (𝓞 F) (SInt 𝔪)) γ₀) • Q = γ₀ • Q := by
  rw [toF_map_int, intSL_smul]

/-! ### The term at the class of `(0, 1)` -/

theorem Row.norm_inf : (Row.inf 𝔪).norm = 1 := by
  unfold Row.norm
  rw [Row.inf_c, Row.inf_d]
  change normS 𝔪 (0 : F) (1 : F) = 1
  rw [normS_zero_left, absS_one]

theorem tildeC_inf (Ψ : TSection ι 𝔪) (s : ℂ) : tildeC Ψ s (RowClass.inf 𝔪) = Ψ s (Row.inf 𝔪) := by
  rw [RowClass.inf, tildeC_mk, TSection.tilde, Row.norm_inf, Complex.ofReal_one, Complex.one_cpow,
    mul_one]

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.K_Jacquet
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-K, file 2: the Jacquet integral at a complex place

Additive character: `archChar z = exp(2πi (z + z̄)) = exp(2πi · 2 Re z)` (the trace form `e(Tr z)`
of `ℂ/ℝ`; the goal's `sAddChar` is `exp(−2πi Tr_{F/ℚ}(·))` on fractional parts, whose factor at a
complex place `w` is `archChar (−σ_w ·)`; the Jacquet integral is even in `ν`, so the sign is
immaterial).

`jacquet s ν v = ∫_ℂ (v / (|x|² + v²))^s · archChar(−ν x) dx`. For `Re s > 1`, `v > 0`:

* `jacquet_zero`: `jacquet s 0 v = π/(s−1) · v^{2−s}`;
* `jacquet_eq`: for `ν ≠ 0`,
  `jacquet s ν v = (2π/Γ(s)) · (2π|ν|)^{s−1} · v · K_{s−1}(4π|ν|v)`
  `= (2π^s/Γ(s)) · (2|ν|)^{s−1} · v · K_{s−1}(4π|ν|v)` (`jacquet_eq'`).

The proof is OpenAI's (`OAI.CubicEisenstein.sourceFourierKernel_bessel`, openai/math family 003,
`Eisenstein/HyperbolicSpace.lean`, Apache 2.0; in our port `Definitions.Def_OAIHecke78B005`),
**copied** and restated for `besselK` (importing the bundle would drag B000–B004, ~45k lines).
-/

namespace ArtinKP.K

open MeasureTheory Set Filter
open scoped FourierTransform RealInnerProductSpace

noncomputable section

theorem archChar_zero : archChar 0 = 1 := by simp [archChar]

/-! ## Radial integrals on `ℂ` (copied from OpenAI) -/

lemma integral_radial_sq (f : ℝ → ℂ) :
    (∫ z : ℂ, f (‖z‖ ^ 2)) = (Real.pi : ℂ) * ∫ t : ℝ in Set.Ioi 0, f t := by
  have hball : (volume : Measure ℂ).real (Metric.ball 0 1) = Real.pi := by
    simp [Measure.real, Complex.volume_ball]
  have hpolar := integral_fun_norm_addHaar (volume : Measure ℂ) (fun r : ℝ => f (r^2))
  have hsub := integral_comp_rpow_Ioi (E := ℂ) f (p := 2) (by norm_num)
  norm_num [Real.rpow_two, Real.rpow_one] at hsub
  simp only [Complex.finrank_real_complex, hball, Nat.reduceSub, pow_one,
    nsmul_eq_mul, Complex.real_smul, ] at hpolar hsub
  rw [hpolar]
  rw [← hsub]
  rw [show (fun x : ℝ => (2:ℂ)*x*f (x^2)) =
      (fun x : ℝ => (2:ℂ)*(x*f (x^2))) by funext x; ring, integral_const_mul]
  ring

lemma add_one_image_Ioi : (fun x : ℝ => x+1) '' Set.Ioi 0 = Set.Ioi 1 := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    simp only [Set.mem_Ioi] at *
    linarith
  · intro hy
    refine ⟨y-1, ?_, by ring⟩
    simp only [Set.mem_Ioi] at *
    linarith

lemma integral_add_one_Ioi (f : ℝ → ℂ) :
    (∫ x : ℝ in Set.Ioi 0, f (x+1)) = ∫ x : ℝ in Set.Ioi 1, f x := by
  have h := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi
    (fun x (hx : x ∈ Set.Ioi (0:ℝ)) => (hasDerivAt_id x |>.add_const 1).hasDerivWithinAt)
    (fun x hx y hy hxy => by dsimp at hxy; linarith : InjOn (fun x : ℝ => x+1) (Set.Ioi 0)) f
  simp only [id_eq] at h
  rw [add_one_image_Ioi] at h
  simpa only [abs_one, one_smul] using h.symm

theorem integral_hyperbolicKernel (s : ℂ) (hs : 1 < s.re) :
    (∫ z : ℂ, hyperbolicKernel s z) = (Real.pi : ℂ) / (s-1) := by
  unfold hyperbolicKernel
  rw [integral_radial_sq (fun t : ℝ => ((1+t : ℝ) : ℂ)^(-s))]
  simp_rw [add_comm (1:ℝ)]
  rw [integral_add_one_Ioi (fun t : ℝ => (t : ℂ)^(-s))]
  rw [integral_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs) (by norm_num : (0:ℝ)<1)]
  simp only [Complex.ofReal_one, Complex.one_cpow]
  have hn : (-s+1)⁻¹ = -(s-1)⁻¹ := by
    rw [show -s+1=-(s-1) by ring, inv_neg]
  simp only [div_eq_mul_inv, hn]
  ring

lemma sourceFourierKernel_zero (s : ℂ) (hs : 1 < s.re) :
    sourceFourierKernel s 0 = (Real.pi : ℂ)/(s-1) := by
  simpa only [sourceFourierKernel, neg_zero, zero_mul, archChar_zero, mul_one]
    using integral_hyperbolicKernel s hs

/-! ## The Bessel form (ours, for `besselK`) -/

lemma traceIntegral_scale (v : ℝ) (hv : 0 < v) (s freq : ℂ) :
    (∫ z : ℂ,hyperbolicKernel s (z/(v:ℂ))*archChar (-freq*z))=
      (v:ℂ)^2*sourceFourierKernel s (freq*v) := by
  have heq (z : ℂ) : hyperbolicKernel s (z/(v:ℂ))*archChar (-freq*z)=
      (fun w : ℂ => hyperbolicKernel s w*archChar (-(freq*v)*w)) (v⁻¹ • z) := by
    simp only [Complex.real_smul,Complex.ofReal_inv]
    congr 2
    · ring
    · field_simp [Complex.ofReal_ne_zero.mpr hv.ne']
  simp_rw [heq]
  have h := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure ℂ)
    (fun w : ℂ => hyperbolicKernel s w*archChar (-(freq*v)*w)) hv.le
  simpa only [Complex.finrank_real_complex,Complex.real_smul,Complex.ofReal_pow,sourceFourierKernel] using h

/-! ## The Jacquet integral -/

lemma height_cpow (s : ℂ) {v : ℝ} (hv : 0 < v) (x : ℂ) :
    ((v / (‖x‖ ^ 2 + v ^ 2) : ℝ) : ℂ) ^ s = (v : ℂ) ^ (-s) * hyperbolicKernel s (x / (v : ℂ)) := by
  unfold hyperbolicKernel
  have h1 : (v / (‖x‖ ^ 2 + v ^ 2) : ℝ) = v⁻¹ * (1 + ‖x / (v : ℂ)‖ ^ 2)⁻¹ := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hv.le]
    field_simp
    ring
  have hpos : (0 : ℝ) < 1 + ‖x / (v : ℂ)‖ ^ 2 := by positivity
  rw [h1, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (inv_nonneg.2 hv.le)
    (inv_nonneg.2 hpos.le), Complex.ofReal_inv, Complex.ofReal_inv,
    Complex.inv_cpow_ofReal_nonneg hv.le, Complex.inv_cpow_ofReal_nonneg hpos.le,
    Complex.cpow_neg, Complex.cpow_neg]

theorem jacquet_eq_sourceFourierKernel (s ν : ℂ) {v : ℝ} (hv : 0 < v) :
    jacquet s ν v = (v : ℂ) ^ (2 - s) * sourceFourierKernel s (ν * v) := by
  unfold jacquet
  simp_rw [height_cpow s hv, mul_assoc]
  rw [integral_const_mul, traceIntegral_scale v hv s ν, ← mul_assoc]
  congr 1
  rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hv.ne')]
  congr 1
  push_cast; ring

/-- The constant term: `∫_ℂ (v/(|x|²+v²))^s dx = π/(s−1) · v^{2−s}`. -/
theorem jacquet_zero (s : ℂ) (hs : 1 < s.re) {v : ℝ} (hv : 0 < v) :
    jacquet s 0 v = (Real.pi : ℂ) / (s - 1) * (v : ℂ) ^ (2 - s) := by
  rw [jacquet_eq_sourceFourierKernel s 0 hv, zero_mul, sourceFourierKernel_zero s hs, mul_comm]

/-! ## Holomorphy in `s` -/

end

end ArtinKP.K
end

section
-- module Solutions.Artin.KP.S_BigCell
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.G1.scal_apply _root_.ArtinKP.S2.cubicSymbol_sym
/-!
# WP-S, part 6: big-cell and small-cell sections

For `η ∈ Fˣ`, a deep level `N ≥ 1`, and a lattice coset `L = {u : Small M (u - t₀)}`:

* `InClass 𝔪 N η c`: `c ∈ η · U_S · (Fˣ)³ · U_N` (`U_N` = units `N`-close to `1`); this is the
  rational form of MATH2's cube-saturated class `η U_S U_𝔫 (F_{S_f}ˣ)³`.
* `bigCell`: `Φ^{big}_s(c, d) = ⟨η, c⟩ |c|_{S_f}^{-s} 1[c ∈ class η] 1[d/c ∈ L]`.
  The unitary factor `⟨η, c⟩` equals MATH2's `⟨η₀, ε⟩` for `c = η₀ ε t³ u` and needs no choice.
* `smallCell = w · bigCell`: `⟨c, d⟩ ⟨η, d⟩ |d|^{-s} 1[d ∈ class η] 1[-c/d ∈ L]`.
* `nT_bigCell`, `twist_smallCell`: the translates by `n(t)` and `w`.
* `sum_bigCell_apply`: the sum over pairwise disjoint classes (MATH2 §3.1, `Φ^Σ`).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S

open ArtinKP.A

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### Classes -/

/-! ### The support of a big-cell section and its stability -/

theorem bigCell_apply (ι : F →+* ℂ) (P : CubicPkg F) (hG : Good 𝔪) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : P.IsDeepLevel 𝔪 N) (η : F) (hη : η ≠ 0) (M : ℤ) (t₀ : F) (s : ℂ) (c d : F) :
    bigCell ι P hG hN1 hN η hη M t₀ s c d = bigFun ι P 𝔪 N η M t₀ s c d := rfl

/-! ### Small-cell sections -/

/-! ### Finite sums: the sum over classes and additive projections -/

namespace GSection

variable {ι : F →+* ℂ} {P : CubicPkg F}

theorem sum_apply {α : Type*} (T : Finset α) (f : α → GSection ι P 𝔪) (s : ℂ) (c d : F) :
    (∑ i ∈ T, f i) s c d = ∑ i ∈ T, f i s c d := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply, ih]

end GSection

end ArtinKP.S
end
end

section
-- module Solutions.Artin.KP.B_FourArch
attribute [-instance] _root_.ArtinKP.B1.instCountablePairClass _root_.ArtinKP.X.instSigmaFiniteE1Mu1 _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.B.coe_latREquiv _root_.ArtinKP.B.embR_apply _root_.ArtinKP.FB.v_gmap
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

theorem kerA_pos {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w) (x : InfinitePlace F → ℂ) :
    0 < kerA v x :=
  Finset.prod_pos fun w _ => div_pos (hv w) (by positivity [hv w])

theorem continuous_kerA {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w) :
    Continuous (kerA v) := by
  refine continuous_finsetProd _ fun w _ => ?_
  refine Continuous.div continuous_const (by fun_prop) fun x => ?_
  have := hv w
  positivity

/-- `I_{(c,d)}(x, v) = N_∞(c)⁻¹ ∏_w v_w / (|x_w + d/c|² + v_w²)` for `c ≠ 0`. -/
theorem pairHt_mk {c : F} (hc : c ≠ 0) (d : F) (x : InfinitePlace F → ℂ)
    (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) :
    X.pairHt c d (X.mk x v hv) = (Ninf c)⁻¹ * kerA v (x + emb (d / c)) := by
  rw [X.pairHt_eq_prod, Ninf, kerA, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hcw : w.embedding c ≠ 0 := (map_ne_zero _).mpr hc
  have hn : Complex.normSq (w.embedding c) ≠ 0 := Complex.normSq_pos.mpr hcw |>.ne'
  change v w / (Complex.normSq (w.embedding c * x w + w.embedding d)
    + Complex.normSq (w.embedding c) * v w ^ 2) = _
  have h1 : Complex.normSq (w.embedding c * x w + w.embedding d)
      = Complex.normSq (w.embedding c) * ‖x w + w.embedding (d / c)‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_mul]
    congr 1
    rw [map_div₀]
    field_simp
  rw [h1, Pi.add_apply, emb_apply, ← mul_add, ← div_div, div_eq_inv_mul, ← div_eq_inv_mul,
    div_eq_inv_mul, ← mul_div_assoc, div_eq_inv_mul]
  field_simp

theorem cpow_prod_nonneg {α : Type*} (t : Finset α) (f : α → ℝ) (hf : ∀ i, 0 ≤ f i) (s : ℂ) :
    (((∏ i ∈ t, f i : ℝ)) : ℂ) ^ s = ∏ i ∈ t, ((f i : ℝ) : ℂ) ^ s := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf a) (Finset.prod_nonneg fun i _ => hf i), ih]

theorem norm_chiInf (ν : F) (x : InfinitePlace F → ℂ) : ‖chiInf ν x‖ = 1 := by
  rw [chiInf, RCLike.norm_conj, norm_eInf]

theorem chiInf_add (ν : F) (x y : InfinitePlace F → ℂ) :
    chiInf ν (x + y) = chiInf ν x * chiInf ν y := by
  rw [chiInf, mul_add, eInf_add, map_mul]
  rfl

theorem chiInf_zero (x : InfinitePlace F → ℂ) : chiInf (0 : F) x = 1 := by
  simp [chiInf, eInf, archChar]

theorem chiInf_eq_prod (ν : F) (x : InfinitePlace F → ℂ) :
    chiInf ν x = ∏ w, archChar (-(-(w.embedding ν)) * x w) := by
  rw [chiInf, eInf, map_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← archChar_neg, Pi.mul_apply, emb_apply]
  congr 1
  ring

/-- `∫ (kerA v)^s · conj e_∞(ν ·) = W_s(ν; v)`. -/
theorem integral_kerA (s : ℂ) (ν : F) (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) :
    ∫ x : InfinitePlace F → ℂ, ((kerA v x : ℝ) : ℂ) ^ s * chiInf ν x = Winf s ν v := by
  let g : InfinitePlace F → ℂ → ℂ := fun w y =>
    ((v w / (‖y‖ ^ 2 + v w ^ 2) : ℝ) : ℂ) ^ s * archChar (-(-(w.embedding ν)) * y)
  have h : ∀ x : InfinitePlace F → ℂ, ((kerA v x : ℝ) : ℂ) ^ s * chiInf ν x
      = ∏ w, g w (x w) := by
    intro x
    rw [Finset.prod_mul_distrib, ← chiInf_eq_prod, kerA,
      cpow_prod_nonneg _ _ (fun w => by have := hv w; positivity)]
  rw [integral_congr_ae (Filter.Eventually.of_forall h), volume_pi]
  exact integral_fintype_prod_eq_prod g

/-! ### Shifted kernels -/

theorem measurable_hKer (A : ℂ) (N : ℝ) (e : InfinitePlace F → ℂ) (s : ℂ)
    {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w) : Measurable (hKer A N e s v) := by
  have h1 : Measurable fun x : InfinitePlace F → ℂ => N⁻¹ * kerA v (x + e) :=
    measurable_const.mul
      ((continuous_kerA hv).comp (continuous_id.add continuous_const)).measurable
  exact measurable_const.mul ((Complex.measurable_ofReal.comp h1).pow_const s)

theorem hKer_eq {A : ℂ} {N : ℝ} (hN : 0 < N) (e : InfinitePlace F → ℂ) (s : ℂ)
    {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w) (x : InfinitePlace F → ℂ) :
    hKer A N e s v x = A * ((N⁻¹ : ℝ) : ℂ) ^ s * ((kerA v (x + e) : ℝ) : ℂ) ^ s := by
  rw [hKer, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (inv_pos.mpr hN).le (kerA_pos hv _).le, mul_assoc]

/-- The integral of a shifted kernel against `conj e_∞(ν ·)`. -/
theorem integral_hKer (A : ℂ) {N : ℝ} (hN : 0 < N) (e : InfinitePlace F → ℂ) (s : ℂ) (ν : F)
    {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w) :
    ∫ x : InfinitePlace F → ℂ, hKer A N e s v x * chiInf ν x
      = A * ((N⁻¹ : ℝ) : ℂ) ^ s * conj (chiInf ν e) * Winf s ν v := by
  have hunit : chiInf ν e * conj (chiInf ν e) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_chiInf]
    simp
  have h : ∀ x : InfinitePlace F → ℂ, hKer A N e s v x * chiInf ν x
      = (A * ((N⁻¹ : ℝ) : ℂ) ^ s * conj (chiInf ν e))
        * (fun y : InfinitePlace F → ℂ => ((kerA v y : ℝ) : ℂ) ^ s * chiInf ν y) (x + e) := by
    intro x
    simp only
    rw [hKer_eq hN e s hv, chiInf_add]
    linear_combination (-(A * ((N⁻¹ : ℝ) : ℂ) ^ s * ((kerA v (x + e) : ℝ) : ℂ) ^ s
      * chiInf ν x)) * hunit
  rw [integral_congr_ae (Filter.Eventually.of_forall h), integral_const_mul,
    integral_add_right_eq_self (fun y : InfinitePlace F → ℂ =>
      ((kerA v y : ℝ) : ℂ) ^ s * chiInf ν y) e, integral_kerA s ν v hv]

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.B_FourIndex
attribute [-instance] _root_.ArtinKP.N.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-B, part 4: the index set of the unfolded sum

* `exists_sInt_sub_small`: strong approximation `F = R + 𝔩_M` (from `B7.hasWit_all`).
* `latR 𝔪 M = R ∩ 𝔩_M`, `transLat 𝔪 M = emb (R ∩ 𝔩_M) ⊂ ℂ^r` (the translation lattice `Λ_M`).
* `sec`: for `c ≠ 0` a section of `R → R/cR × F/𝔩_M`, `d ↦ (d mod c, d/c mod 𝔩_M)`.
* `thetaEquiv`: `((Σ a, R/c_a R) × F/𝔩_M) × Λ_M ≃ (R∖0)/Rˣ × R`,
  `(((a, α), u), b) ↦ (a, sec(α, u) + c_a b)` — MATH2's `R/cΛ ≅ R/cR × F_{S_f}/cΛ̂`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### Strong approximation -/

/-! ### The translation lattice -/

instance instCountableSInt : Countable (SInt 𝔪) :=
  haveI _iCF := ArtinKP.B1.instCountableField (F := F)
  (Subtype.val_injective : Function.Injective fun b : SInt 𝔪 => (b : F)).countable

instance instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupTransLat (M : ℤ) : Countable (transLat 𝔪 M) := (latREquiv 𝔪 M).symm.injective.countable

/-! ### The section -/

/-! ### The index equivalence -/

/-! ### Rows with `c ≠ 0` modulo units -/

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.B_FourUnfold
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.B1.instCountablePairClass _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-B, part 1: unfolding an integral over a fundamental cell (abstract measure theory)

For a countable subgroup `L` of `E` with fundamental domain `D`, a countable family `h i : E → ℂ`
with `∑ᵢ ∫ ‖h i‖ < ∞` and a bounded `L`-periodic `χ`:

`∫_D (∑_{(i,b) ∈ I × L} h i (b + x)) χ(x) dx = ∑ᵢ ∫_E h i · χ`.

No pointwise convergence is assumed (it holds almost everywhere by Tonelli).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory ENNReal

noncomputable section

namespace ArtinKP.B

variable {E : Type*} [AddCommGroup E] [MeasurableSpace E] {μ : Measure E}
  (L : AddSubgroup E) [Countable L] [MeasurableVAdd L E] [VAddInvariantMeasure L E μ]
  {I : Type*} [Countable I] {D : Set E}

/-- Tonelli for the unfolded family. -/
theorem lintegral_unfold (hD : IsAddFundamentalDomain L D μ) (h : I → E → ℂ) :
    ∑' p : I × L, ∫⁻ x in D, ‖h p.1 ((p.2 : E) + x)‖ₑ ∂μ = ∑' i, ∫⁻ x, ‖h i x‖ₑ ∂μ := by
  rw [ENNReal.tsum_prod (f := fun (i : I) (b : L) => ∫⁻ x in D, ‖h i ((b : E) + x)‖ₑ ∂μ)]
  refine tsum_congr fun i => ?_
  rw [hD.lintegral_eq_tsum' fun x => ‖h i x‖ₑ, ← (Equiv.neg L).tsum_eq]
  refine tsum_congr fun b => ?_
  simp only [Equiv.neg_apply, neg_neg]
  rfl

variable (hD : IsAddFundamentalDomain L D μ) (h : I → E → ℂ) (hm : ∀ i, Measurable (h i))
  (hfin : ∑' i, ∫⁻ x, ‖h i x‖ₑ ∂μ ≠ ⊤) (χ : E → ℂ) (hχm : Measurable χ)
  (hχ1 : ∀ x, ‖χ x‖ ≤ 1)

include hD hfin hχ1 in
theorem tsum_lintegral_unfold_ne_top :
    ∑' p : I × L, ∫⁻ x in D, ‖h p.1 ((p.2 : E) + x) * χ x‖ₑ ∂μ ≠ ⊤ := by
  have h0 : ∑' p : I × L, ∫⁻ x in D, ‖h p.1 ((p.2 : E) + x)‖ₑ ∂μ ≠ ⊤ := by
    rwa [lintegral_unfold L hD h]
  refine ne_top_of_le_ne_top h0 ?_
  refine ENNReal.tsum_le_tsum fun p => lintegral_mono fun x => ?_
  rw [enorm_mul]
  calc ‖h p.1 ((p.2 : E) + x)‖ₑ * ‖χ x‖ₑ ≤ ‖h p.1 ((p.2 : E) + x)‖ₑ * 1 := by
        gcongr
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_one.mpr (hχ1 x)
    _ = _ := mul_one _

variable [MeasurableAdd E]

include hm hχm in
theorem measurable_unfold_term (p : I × L) :
    Measurable fun x => h p.1 ((p.2 : E) + x) * χ x :=
  ((hm p.1).comp (measurable_const_add _)).mul hχm

include hD hfin hχ1 hm hχm in
/-- The unfolded sum is integrable over the cell (finiteness of the `L¹` norm). -/
theorem lintegral_tsum_unfold_ne_top :
    ∫⁻ x in D, ‖(∑' p : I × L, h p.1 ((p.2 : E) + x)) * χ x‖ₑ ∂μ ≠ ⊤ := by
  refine ne_top_of_le_ne_top (tsum_lintegral_unfold_ne_top L hD h hfin χ hχ1) ?_
  rw [← lintegral_tsum fun p => (measurable_unfold_term L h hm χ hχm p).enorm.aemeasurable]
  refine lintegral_mono fun x => ?_
  rw [← tsum_mul_right]
  exact enorm_tsum_le_tsum_enorm

include hD hfin hχ1 hm hχm in
/-- **Unfolding.** -/
theorem integral_unfold (hχp : ∀ (b : L) (x : E), χ ((b : E) + x) = χ x) :
    Summable (fun i => ‖∫ x, h i x * χ x ∂μ‖) ∧
    ∫ x in D, (∑' p : I × L, h p.1 ((p.2 : E) + x)) * χ x ∂μ = ∑' i, ∫ x, h i x * χ x ∂μ := by
  have hT := tsum_lintegral_unfold_ne_top L hD h hfin χ hχ1
  -- each `h i χ` is integrable
  have hint : ∀ i, Integrable (fun x => h i x * χ x) μ := by
    intro i
    refine ⟨((hm i).mul hχm).aestronglyMeasurable, ?_⟩
    have hi : ∫⁻ x, ‖h i x‖ₑ ∂μ ≠ ⊤ := ne_top_of_le_ne_top hfin (ENNReal.le_tsum i)
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hi.lt_top
    rw [enorm_mul]
    calc ‖h i x‖ₑ * ‖χ x‖ₑ ≤ ‖h i x‖ₑ * 1 := by
          gcongr
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_one.mpr (hχ1 x)
      _ = _ := mul_one _
  -- the sum over `b` of the cell integrals
  have hcell : ∀ i, ∫ x, h i x * χ x ∂μ = ∑' b : L, ∫ x in D, h i ((b : E) + x) * χ x ∂μ := by
    intro i
    rw [hD.integral_eq_tsum' _ (hint i), ← (Equiv.neg L).tsum_eq]
    refine tsum_congr fun b => ?_
    simp only [Equiv.neg_apply, neg_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change h i ((b : E) + x) * χ ((b : E) + x) = _
    rw [hχp]
  -- summability of the double family
  have hsum : Summable fun p : I × L => ∫ x in D, h p.1 ((p.2 : E) + x) * χ x ∂μ := by
    refine Summable.of_norm_bounded (ENNReal.summable_toReal hT) fun p => ?_
    have hle := enorm_integral_le_lintegral_enorm (μ := μ.restrict D)
      (fun x => h p.1 ((p.2 : E) + x) * χ x)
    have hp : ∫⁻ x in D, ‖h p.1 ((p.2 : E) + x) * χ x‖ₑ ∂μ ≠ ⊤ :=
      ne_top_of_le_ne_top hT (ENNReal.le_tsum p)
    rw [← toReal_enorm]
    exact ENNReal.toReal_mono hp hle
  have hmain : ∫ x in D, (∑' p : I × L, h p.1 ((p.2 : E) + x)) * χ x ∂μ
      = ∑' i, ∫ x, h i x * χ x ∂μ := by
    have h1 : ∀ x, (∑' p : I × L, h p.1 ((p.2 : E) + x)) * χ x
        = ∑' p : I × L, h p.1 ((p.2 : E) + x) * χ x := fun x => tsum_mul_right.symm
    simp only [h1]
    rw [integral_tsum (fun p => (measurable_unfold_term L h hm χ hχm p).aestronglyMeasurable) hT,
      hsum.tsum_prod]
    exact tsum_congr fun i => (hcell i).symm
  refine ⟨?_, hmain⟩
  have h2 : Summable fun i => ‖∑' b : L, ∫ x in D, h i ((b : E) + x) * χ x ∂μ‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun i => norm_tsum_le_tsum_norm (hsum.norm.prod_factor i)) hsum.norm.prod
  have h3 : (fun i => ‖∫ x, h i x * χ x ∂μ‖)
      = fun i => ‖∑' b : L, ∫ x in D, h i ((b : E) + x) * χ x ∂μ‖ := funext fun i => by
    rw [hcell i]
  rw [h3]
  exact h2

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.B_FourThm
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-B, part 8: the Fourier expansion at `∞` — statements

For a genuine section `Φ`, `Re s > 2`, `ν ∈ R`, a depth `M` valid for `(Φ, ν)`
(`ValidDepth hG Φ ν M`), and any fundamental cell `D` of finite volume of the translation
lattice `Λ_M = transLat 𝔪 M = emb (R ∩ 𝔩_M) ⊂ ℂ^r`:

* `fourier_coeff` (all `ν`), `fourier_coeff_ne_zero` (`ν ≠ 0`), `const_term` (`ν = 0`).

Normalizations: `chiInf ν x = conj e_∞(νx)`, `e_∞(x) = ∏_w archChar (-x_w)` (so
`e_∞ = exp(-2πi Tr)` on `F`); `dx` is Lebesgue measure on `ℂ^r = (ℝ²)^r`;
`Winf s ν v = ∏_w jacquet s (-σ_w ν) v_w`; `vol 𝔪 M = ∏_{v ∣ 𝔪} q_v^{-M}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate Pointwise
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E ArtinKP.K

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

instance instCountableIdxI (M : ℤ) : Countable (IdxI 𝔪 M) := by
  haveI _iCF := ArtinKP.B1.instCountableField (F := F)
  have : Countable (Associates (SInt 𝔪)) := Associates.mk_surjective.countable
  have : ∀ c : SInt 𝔪, Countable (SInt 𝔪 ⧸ Ideal.span {c}) := fun c =>
    Ideal.Quotient.mk_surjective.countable
  have : Countable (F ⧸ lat 𝔪 M) := QuotientAddGroup.mk_surjective.countable
  infer_instance

theorem continuous_mk_x (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) :
    Continuous fun x : InfinitePlace F → ℂ => X.mk x v hv := by
  refine continuous_pi fun w => ?_
  exact Continuous.subtype_mk ((continuous_apply w).prodMk continuous_const) _

/-! ### Characters on the cell -/

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.BZ_Main
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instSigmaFiniteE1Mu1 _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-BZ, part 5: the constant term of `E(Φ^Σ)` — what C9 uses

`Φ^Σ = sumBig ι hG hN1 hN M T`, `T` a complete system of pairwise disjoint classes, `D` any
fundamental cell of `Λ_M = transLat 𝔪 M`, `Re s > 2`, `ht = ∏_w v_w`.

* `vol_pos`, `volume_cell_ne_top`, `volume_cell_toReal`: `vol(D) = covol(𝓞_F)/vol(𝔩_M)`, finite.
* `sumBig_zero_left`: `Φ^Σ_s(0, d) = 0`, so the constant term has **no** `ht^s` term.
* **`const_term_sumBig`**:
  `∫_D E(Φ^Σ)(x, v) dx = (π/(s-1))^r · ζ^S(3s-3)/ζ^S(3s-2) · ht^{2-s}`.
* **`mean_const_term_sumBig`**: the mean over the cell,
  `vol(D)⁻¹ ∫_D E(Φ^Σ) = C · (π/(s-1))^r · ζ^S(3s-3)/ζ^S(3s-2) · ht^{2-s}` with
  `C = vol(𝔩_M)/covol(𝓞_F) = vol 𝔪 M / (volume (B1.fundD F)).toReal > 0` (`constC_pos`).
* **`exists_mean_const_term_pole`**: with the function `G` of `Z.exists_zetaRatio` (holomorphic on
  `Re s > 1`, `G(4/3) = ρ_S/(3ζ^S(2)) ≠ 0`), the coefficient is
  `C · (π/(s-1))^r · G(s)/(s - 4/3)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.BZ

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E ArtinKP.K ArtinKP.B7 ArtinKP.B

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

theorem vol_pos (𝔪 : Ideal (𝓞 F)) (M : ℤ) : 0 < vol 𝔪 M :=
  Finset.prod_pos fun v _ => zpow_pos (by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm v
    exact_mod_cast (by omega : 0 < Ideal.absNorm v.asIdeal)) _

/-- `Φ^Σ` vanishes on the rows `(0, d)`. -/
theorem sumBig_zero_left (hG : Good 𝔪) {N : ℕ} (hN1 : 1 ≤ N) (hN : P.IsDeepLevel 𝔪 N) (M : ℤ)
    (T : Finset {η : F // η ≠ 0}) (s : ℂ) (d : F) : sumBig ι hG hN1 hN M T s 0 d = 0 := by
  rw [sumBig, GSection.sum_apply]
  refine Finset.sum_eq_zero fun η _ => ?_
  rw [bigCell_apply]
  exact bigFun_of_not_supp (fun h => InClass.ne_zero hG hN1 η.2 h.1 rfl) s

variable [IsTotallyComplex F]

theorem constC_pos (𝔪 : Ideal (𝓞 F)) (M : ℤ) : 0 < constC 𝔪 M :=
  div_pos (vol_pos 𝔪 M) (ENNReal.toReal_pos (ZSpan.measure_fundamentalDomain_ne_zero _)
    (fundD_bounded (F := F)).measure_lt_top.ne)

end ArtinKP.BZ
end
end

section
-- module Solutions.Artin.KP.RO_Bridge
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

end

end ArtinKP.RO
end

section
-- module Solutions.Artin.KP.B_RO
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-B0, part 3: compatibility with WP-RO's bridge `Row 𝔪 / U_S ≃ B1.PairClass (SOf 𝔪)`

`B.sPl 𝔪` and `RO.SOf 𝔪` are the same finset, `B.RowClass 𝔪` is the source of `RO.rowClassEquiv`,
and the bridge preserves heights and the class of `(0, 1)`.  Hence B1's statements about
`PairClass (SOf 𝔪)` (`Tinf_le`, `G_le`, `PairClass.exists_top`, …) transfer to `RowClass 𝔪`.
(Leaf file: nothing in `B_Def`, `B_Def2` depends on WP-RO.)
-/

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

open scoped MatrixGroups
open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

theorem rowClassEquiv_mk (h𝔪 : 𝔪 ≠ ⊥) (p : Row 𝔪) :
    RO.rowClassEquiv h𝔪 (RowClass.mk p) = RO.rowClass h𝔪 p := rfl

variable [IsTotallyComplex F]

/-- WP-RO's bridge preserves heights. -/
theorem ht_rowClassEquiv (h𝔪 : 𝔪 ≠ ⊥) (q : RowClass 𝔪) (Q : X F) :
    (RO.rowClassEquiv h𝔪 q).ht Q = q.ht Q := by
  conv_lhs => rw [← RowClass.mk_out q]
  rfl

theorem rowClassEquiv_inf (h𝔪 : 𝔪 ≠ ⊥) :
    RO.rowClassEquiv h𝔪 (RowClass.inf 𝔪) = PairClass.inf (RO.SOf 𝔪) := by
  rw [RowClass.inf, rowClassEquiv_mk]
  refine congrArg _ (SPair.ext ?_ ?_)
  · change ((0 : SInt 𝔪) : F) = 0
    rfl
  · change ((1 : SInt 𝔪) : F) = 1
    rfl

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.X2_Chart
attribute [-instance] _root_.ArtinKP.B.instCountableIdxI _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.B1.instCountablePairClass _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
-- module Solutions.Artin.KP.X_L2
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
attribute [-instance] _root_.ArtinKP.B.instCountableIdxI _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.B.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupTransLat _root_.ArtinKP.B1.instCountablePairClass _root_.ArtinKP.B1.instCountableSubtypeE₂MemSubmoduleIntPairLattice _root_.ArtinKP.B1.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatSub _root_.ArtinKP.N.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
-- module Solutions.Artin.KP.C5_Holo
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
-- module Solutions.Artin.KP.X2_Prod
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
-- module Solutions.Artin.KP.C5_Series
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.S.GSection.twist_apply
/-! # WP-C5, file 4: the cut-off part `h_s`, the source `F_s` and `u_s = E_Ψ − h_s`

For a twisted section `Ψ : TSection ι 𝔪` (weights `B.tildeC Ψ s` on `B.RowClass 𝔪`):

* `hpart Ψ s Q = ∑_q Ψ̃_s(q) ρ(ht_q(Q)) ht_q(Q)^s`, `src Ψ s Q = ∑_q Ψ̃_s(q) φ_s(log ht_q(Q))`,
  `upart Ψ s = eis Ψ s − hpart Ψ s`.  All three are defined without hypotheses; `hpart` and `src`
  are locally single terms for every `s ∈ ℂ` (`hpart_eq_pe`, `src_eq_pe`: they are WP-C5's `pe`
  with the weights `wt h𝔪 Ψ s` on `B1.PairClass (SOf 𝔪)`).
* `Inv Γ Ψ`: `Ψ` is fixed by (the image in `SL₂(R)` of) `Γ ≤ SL₂(𝓞_F)`.
* `norm_upart_le`: `|u_s| ≤ B · G` (WP-B1's `G`), `Re s > 2`; `l2Rep_upart`.
* `lap_hpart : Δ h_s = λ(s) h_s + F_s`; with the named hypothesis `EisEigen Ψ s` (WP-RF, D1:
  `E_Ψ(·, s)` is smooth and `Δ E = λ(s) E`): `lap_upart : Δ u_s = λ(s) u_s + (−F_s)`.
* `src`: smooth, invariant, in the core (`src_mem_core`), bounded (`exists_norm_src_le`), entire in
  `s` pointwise (`differentiable_src`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C5

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {ι : F →+* ℂ}

/-! ### Definitions (no hypotheses) -/

lemma wt_rowClass (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) (s : ℂ) (r : Row 𝔪) :
    wt h𝔪 Ψ s (RO.rowClass h𝔪 r) = Ψ.tilde s r := by
  unfold wt
  have : (RO.rowClassEquiv h𝔪).symm (RO.rowClass h𝔪 r) = B.RowClass.mk r := by
    rw [Equiv.symm_apply_eq]
    rfl
  rw [this, tildeC_mk]

/-- `|Ψ̃_s| ≤ B` uniformly for `‖s‖ ≤ M`. -/
lemma exists_wt_bound (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) (M : ℝ) :
    ∃ Bd : ℝ, 0 ≤ Bd ∧ ∀ s : ℂ, ‖s‖ ≤ M → ∀ p : PairClass (RO.SOf 𝔪), ‖wt h𝔪 Ψ s p‖ ≤ Bd := by
  obtain ⟨B₀, hB₀⟩ := Ψ.bound M
  refine ⟨max B₀ 0, le_max_right _ _, fun s hs p => ?_⟩
  unfold wt tildeC TSection.tilde
  set r : Row 𝔪 := ((RO.rowClassEquiv h𝔪).symm p).out
  have hn : 0 < r.norm := r.norm_pos
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hn]
  have h1 := hB₀ s hs r
  have h2 : r.norm ^ (-s.re) * r.norm ^ s.re = 1 := by
    rw [← Real.rpow_add hn]; simp
  calc ‖Ψ s r‖ * r.norm ^ s.re ≤ B₀ * r.norm ^ (-s.re) * r.norm ^ s.re :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hn.le _)
    _ = B₀ := by rw [mul_assoc, h2, mul_one]
    _ ≤ max B₀ 0 := le_max_left _ _

lemma norm_act_intMat (r : Row 𝔪) (γ : SL(2, 𝓞 F)) : (r.act (RO.intMat 𝔪 γ)).norm = r.norm := by
  unfold Row.norm
  rw [← RO.sNorm_SOf, ← RO.sNorm_SOf]
  exact B1.sNorm_actF (S := RO.SOf 𝔪) ((r.c : F), (r.d : F)) γ

/-- The weights are `Γ`-invariant. -/
lemma wt_act (h𝔪 : 𝔪 ≠ ⊥) {Γ : Subgroup (SL(2, 𝓞 F))} {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ)
    {γ : SL(2, 𝓞 F)} (hγ : γ ∈ Γ) (s : ℂ) (p : PairClass (RO.SOf 𝔪)) :
    wt h𝔪 Ψ s (p.act γ) = wt h𝔪 Ψ s p := by
  obtain ⟨r, rfl⟩ := RO.rowClass_surjective h𝔪 p
  rw [← RO.rowClass_act_intMat, wt_rowClass, wt_rowClass]
  unfold TSection.tilde
  rw [TSection.mem_stab.mp (hΓ γ hγ) s r, norm_act_intMat]

variable [IsTotallyComplex F]

/-! ### The Eisenstein series on pair classes -/

lemma eis_eq_tsum_pair (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) (s : ℂ) (Q : X F) :
    eis Ψ s Q = ∑' p : PairClass (RO.SOf 𝔪), wt h𝔪 Ψ s p * ((p.ht Q : ℝ) : ℂ) ^ s := by
  rw [eis_eq_tsum_ht, ← (RO.rowClassEquiv h𝔪).tsum_eq]
  refine tsum_congr fun q => ?_
  rw [ht_rowClassEquiv]
  unfold wt
  rw [Equiv.symm_apply_apply]

lemma summable_pair (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) {s : ℂ} (hs : 2 < s.re) (Q : X F) :
    Summable fun p : PairClass (RO.SOf 𝔪) => wt h𝔪 Ψ s p * ((p.ht Q : ℝ) : ℂ) ^ s := by
  have h1 := summable_term h𝔪 Ψ hs Q
  rw [← (RO.rowClassEquiv h𝔪).summable_iff]
  refine h1.congr fun q => ?_
  change _ = wt h𝔪 Ψ s (RO.rowClassEquiv h𝔪 q) * (((RO.rowClassEquiv h𝔪 q).ht Q : ℝ) : ℂ) ^ s
  rw [term_out_eq, ht_rowClassEquiv]
  unfold wt
  rw [Equiv.symm_apply_apply]

/-! ### Invariance, regularity -/

lemma smul_eq_toF (γ : SL(2, 𝓞 F)) (Q : X F) : γ • Q = toF 𝔪 (RO.intMat 𝔪 γ) • Q :=
  (toF_map_int_smul (𝔪 := 𝔪) γ Q).symm

lemma isInv_eis (h𝔪 : 𝔪 ≠ ⊥) {Γ : Subgroup (SL(2, 𝓞 F))} {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ)
    (s : ℂ) : X.IsInv Γ fun Q : X F => eis Ψ s Q := fun γ Q => by
  change eis Ψ s ((γ : SL(2, 𝓞 F)) • Q) = eis Ψ s Q
  rw [smul_eq_toF (𝔪 := 𝔪), eis_smul_of_mem_stab h𝔪 (hΓ γ γ.2)]

/-! ### The source -/

end

end ArtinKP.C5
end

section
-- module Solutions.Artin.KP.N_Orbit
attribute [-instance] _root_.ArtinKP.B.instCountableIdxI _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.B.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupTransLat _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.B.coe_latREquiv _root_.ArtinKP.B.embR_apply _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
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

lemma lamEquiv_coe (Γ : Subgroup (SL(2, 𝓞 F))) (β : lamN Γ) :
    ((lamEquiv Γ β : latN Γ) : InfinitePlace F → ℂ) = emb ((β : 𝓞 F) : F) := rfl

/-! ### Orbits of `Λ_Γ` on the classes `≠ ∞` -/

variable {S : Finset (FinitePlace F)}

lemma orbN_apply (Γ : Subgroup (SL(2, 𝓞 F))) (ω : Quotient (setN Γ S)) (β : lamN Γ) :
    (orbN Γ S (ω, β)).1 = ω.out.1.act (nInt (β : 𝓞 F)) := rfl

/-! ### The terms as shifted kernels -/

lemma out_c_ne (p : {p : PairClass S // p ≠ PairClass.inf S}) : p.1.out.c ≠ 0 :=
  SPair.c_ne_zero (by rw [Quotient.out_eq]; exact p.2)

lemma nrm_pos (p : {p : PairClass S // p ≠ PairClass.inf S}) :
    0 < Ninf p.1.out.c * X.sNorm S p.1.out.c p.1.out.d :=
  mul_pos (Ninf_pos (out_c_ne p)) (X.sNorm_pos S (Or.inl (out_c_ne p)))

lemma term_eq_hN (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) (s : ℂ) {v : InfinitePlace F → ℝ}
    (hv : ∀ w, 0 < v w) (p : {p : PairClass (RO.SOf 𝔪) // p ≠ PairClass.inf (RO.SOf 𝔪)})
    (y : InfinitePlace F → ℂ) :
    wt h𝔪 Ψ s p.1 * ((p.1.ht (X.mk y v hv) : ℝ) : ℂ) ^ s = hN h𝔪 Ψ s v p y := by
  unfold hN hKer
  rw [PairClass.ht_eq_out, X.sHt, pairHt_mk (out_c_ne p)]
  congr 3
  rw [mul_inv]
  ring

variable {Γ : Subgroup (SL(2, 𝓞 F))}

lemma hN_orb (h𝔪 : 𝔪 ≠ ⊥) {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) (s : ℂ) {v : InfinitePlace F → ℝ}
    (hv : ∀ w, 0 < v w) (ω : Quotient (setN Γ (RO.SOf 𝔪))) (β : lamN Γ)
    (x : InfinitePlace F → ℂ) :
    hN h𝔪 Ψ s v (orbN Γ (RO.SOf 𝔪) (ω, β)) x
      = hN h𝔪 Ψ s v ω.out (((lamEquiv Γ β : latN Γ) : InfinitePlace F → ℂ) + x) := by
  rw [← term_eq_hN h𝔪 Ψ s hv, ← term_eq_hN h𝔪 Ψ s hv, orbN_apply, wt_act h𝔪 hΓ β.2,
    PairClass.ht_act, nInt_smul_mk, lamEquiv_coe, add_comm x]

/-- Reindexing of a sum over the classes `≠ ∞` along the orbits of `Λ_Γ`. -/
lemma tsum_hN_orb {α : Type*} [AddCommMonoid α] [TopologicalSpace α] (h𝔪 : 𝔪 ≠ ⊥)
    {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) (s : ℂ) {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w)
    (g : ℂ → α) (x : InfinitePlace F → ℂ) :
    ∑' z : Quotient (setN Γ (RO.SOf 𝔪)) × latN Γ,
        g (hN h𝔪 Ψ s v z.1.out ((z.2 : InfinitePlace F → ℂ) + x))
      = ∑' p : {p : PairClass (RO.SOf 𝔪) // p ≠ PairClass.inf (RO.SOf 𝔪)},
        g (hN h𝔪 Ψ s v p x) := by
  rw [← (orbN Γ (RO.SOf 𝔪)).tsum_eq, ← ((Equiv.refl _).prodCongr (lamEquiv Γ)).tsum_eq]
  refine tsum_congr fun z => ?_
  obtain ⟨ω, β⟩ := z
  change g (hN h𝔪 Ψ s v ω.out (((lamEquiv Γ β : latN Γ) : InfinitePlace F → ℂ) + x)) = _
  rw [← hN_orb h𝔪 hΓ s hv]

/-! ### The tail -/

lemma wt_inf (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) (s : ℂ) :
    wt h𝔪 Ψ s (PairClass.inf (RO.SOf 𝔪)) = Ψ s (Row.inf 𝔪) := by
  unfold wt
  rw [← rowClassEquiv_inf h𝔪, Equiv.symm_apply_apply, tildeC_inf]

open Classical in
lemma tail_eq_tsum (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) {s : ℂ} (hs : 2 < s.re) (Q : X F) :
    tail Ψ s Q = ∑' p : {p : PairClass (RO.SOf 𝔪) // p ≠ PairClass.inf (RO.SOf 𝔪)},
      wt h𝔪 Ψ s p.1 * ((p.1.ht Q : ℝ) : ℂ) ^ s := by
  unfold tail
  rw [eis_eq_tsum_pair h𝔪, (summable_pair h𝔪 Ψ hs Q).tsum_eq_add_tsum_ite
    (PairClass.inf (RO.SOf 𝔪)), wt_inf, PairClass.ht_inf, add_sub_cancel_left]
  have h := tsum_subtype {p : PairClass (RO.SOf 𝔪) | p ≠ PairClass.inf (RO.SOf 𝔪)}
      (fun p => wt h𝔪 Ψ s p * ((p.ht Q : ℝ) : ℂ) ^ s)
  refine Eq.trans (tsum_congr fun p => ?_) h.symm
  by_cases hp : p = PairClass.inf (RO.SOf 𝔪)
  · rw [if_pos hp, indicator_of_notMem (by simpa using hp)]
  · rw [if_neg hp, indicator_of_mem (by simpa using hp)]

lemma tail_mk (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) {s : ℂ} (hs : 2 < s.re)
    {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w) (x : InfinitePlace F → ℂ) :
    tail Ψ s (X.mk x v hv)
      = ∑' p : {p : PairClass (RO.SOf 𝔪) // p ≠ PairClass.inf (RO.SOf 𝔪)}, hN h𝔪 Ψ s v p x := by
  rw [tail_eq_tsum h𝔪 Ψ hs]
  exact tsum_congr fun p => term_eq_hN h𝔪 Ψ s hv p x

/-! ### Finiteness of the unfolded `L¹` norm -/

lemma ht_mk (x : InfinitePlace F → ℂ) {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w) :
    X.ht (X.mk x v hv) = ∏ w, v w := by
  simp [X.ht]

lemma lintegral_hN_ne_top (h𝔪 : 𝔪 ≠ ⊥) {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) {s : ℂ}
    (hs : 2 < s.re) {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w)
    {D : Set (InfinitePlace F → ℂ)} (hD : IsAddFundamentalDomain (latN Γ) D volume)
    (hDfin : volume D ≠ ⊤) :
    ∑' ω : Quotient (setN Γ (RO.SOf 𝔪)), ∫⁻ x, ‖hN h𝔪 Ψ s v ω.out x‖ₑ ≠ ⊤ := by
  rw [← lintegral_unfold (latN Γ) hD fun (ω : Quotient (setN Γ (RO.SOf 𝔪))) => hN h𝔪 Ψ s v ω.out]
  obtain ⟨Bd, hBd0, hBd⟩ := exists_wt_bound h𝔪 Ψ ‖s‖
  obtain ⟨K, hK0, hK⟩ := Tinf_le (RO.SOf 𝔪) hs
  have hm : ∀ z : Quotient (setN Γ (RO.SOf 𝔪)) × latN Γ, Measurable fun x =>
      ‖hN h𝔪 Ψ s v z.1.out ((z.2 : InfinitePlace F → ℂ) + x)‖ₑ := fun z =>
    ((measurable_hKer _ _ _ s hv).comp (measurable_const_add _)).enorm
  rw [← lintegral_tsum fun z => (hm z).aemeasurable]
  set C : ℝ := Bd * (K * ((∏ w, v w) ^ (2 - s.re) + (∏ w, v w) ^ (-s.re))) with hC
  have hle : ∀ x : InfinitePlace F → ℂ,
      ∑' z : Quotient (setN Γ (RO.SOf 𝔪)) × latN Γ,
        ‖hN h𝔪 Ψ s v z.1.out ((z.2 : InfinitePlace F → ℂ) + x)‖ₑ ≤ ENNReal.ofReal C := by
    intro x
    rw [tsum_hN_orb h𝔪 hΓ s hv (fun z : ℂ => ‖z‖ₑ) x]
    have hsum : Summable fun p : {p : PairClass (RO.SOf 𝔪) // p ≠ PairClass.inf (RO.SOf 𝔪)} =>
        Bd * p.1.ht (X.mk x v hv) ^ s.re :=
      ((PairClass.summable_ht_rpow (RO.SOf 𝔪) (X.mk x v hv) hs).subtype _).mul_left Bd
    have h1 : ∀ p : {p : PairClass (RO.SOf 𝔪) // p ≠ PairClass.inf (RO.SOf 𝔪)},
        ‖hN h𝔪 Ψ s v p x‖ₑ ≤ ENNReal.ofReal (Bd * p.1.ht (X.mk x v hv) ^ s.re) := by
      intro p
      rw [← term_eq_hN h𝔪 Ψ s hv, ← ofReal_norm, norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos (p.1.ht_pos _)]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hBd s le_rfl p.1)
        (Real.rpow_nonneg (p.1.ht_pos _).le _))
    calc _ ≤ ∑' p : {p : PairClass (RO.SOf 𝔪) // p ≠ PairClass.inf (RO.SOf 𝔪)},
          ENNReal.ofReal (Bd * p.1.ht (X.mk x v hv) ^ s.re) := ENNReal.tsum_le_tsum h1
      _ = ENNReal.ofReal (∑' p : {p : PairClass (RO.SOf 𝔪) // p ≠ PairClass.inf (RO.SOf 𝔪)},
          Bd * p.1.ht (X.mk x v hv) ^ s.re) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun p => mul_nonneg hBd0
          (Real.rpow_nonneg (p.1.ht_pos _).le _)) hsum).symm
      _ ≤ ENNReal.ofReal C := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [tsum_mul_left, hC]
        refine mul_le_mul_of_nonneg_left ?_ hBd0
        have := hK (X.mk x v hv)
        rw [ht_mk] at this
        exact this
  refine ne_top_of_le_ne_top ?_ (lintegral_mono fun x => hle x)
  rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hDfin

/-! ### The integral over a cell -/

lemma measurable_mk {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w) :
    Measurable fun x : InfinitePlace F → ℂ => X.mk x v hv :=
  (continuous_mk v hv).measurable

/-- The tail is integrable over a cell of the translations. -/
theorem integrableOn_tail (h𝔪 : 𝔪 ≠ ⊥) {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) {s : ℂ}
    (hs : 2 < s.re) {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w)
    {D : Set (InfinitePlace F → ℂ)} (hD : IsAddFundamentalDomain (latN Γ) D volume)
    (hDfin : volume D ≠ ⊤) :
    IntegrableOn (fun x => tail Ψ s (X.mk x v hv)) D := by
  have hfin := lintegral_hN_ne_top h𝔪 hΓ hs hv hD hDfin
  have h1 := lintegral_tsum_unfold_ne_top (latN Γ) hD
    (fun (ω : Quotient (setN Γ (RO.SOf 𝔪))) => hN h𝔪 Ψ s v ω.out)
    (fun ω => measurable_hKer _ _ _ s hv) hfin (fun _ => 1) measurable_const (fun _ => by simp)
  have hmeas : Measurable fun x => tail Ψ s (X.mk x v hv) := by
    unfold tail
    exact ((measurable_eis h𝔪 Ψ hs).comp (measurable_mk hv)).sub (by
      simp only [ht_mk]
      exact measurable_const)
  refine ⟨hmeas.aestronglyMeasurable, lt_of_le_of_lt (le_of_eq ?_) h1.lt_top⟩
  refine lintegral_congr fun x => ?_
  beta_reduce
  rw [mul_one, tail_mk h𝔪 Ψ hs hv, ← tsum_hN_orb h𝔪 hΓ s hv (fun z : ℂ => z) x]

/-- **The `x`-integral of the tail scales exactly like `ht^{2−s}`** (Lemma K with the weights of
`Ψ` and complex `s`): there is a constant `C` such that for all `v`,
`∫_D tail Ψ s (x, v) dx = C · ∏_w v_w^{2−s}`. -/
theorem exists_integral_tail (h𝔪 : 𝔪 ≠ ⊥) {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) {s : ℂ}
    (hs : 2 < s.re) {D : Set (InfinitePlace F → ℂ)}
    (hD : IsAddFundamentalDomain (latN Γ) D volume) (hDfin : volume D ≠ ⊤) :
    ∃ C : ℂ, ∀ (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w),
      ∫ x in D, tail Ψ s (X.mk x v hv) = C * ∏ w, ((v w : ℝ) : ℂ) ^ (2 - s) := by
  refine ⟨(∑' ω : Quotient (setN Γ (RO.SOf 𝔪)), wt h𝔪 Ψ s ω.out.1
      * (((Ninf ω.out.1.out.c * X.sNorm (RO.SOf 𝔪) ω.out.1.out.c ω.out.1.out.d)⁻¹ : ℝ) : ℂ) ^ s)
      * ((Real.pi : ℂ) / (s - 1)) ^ Fintype.card (InfinitePlace F), fun v hv => ?_⟩
  have hfin := lintegral_hN_ne_top h𝔪 hΓ hs hv hD hDfin
  have h1 := (integral_unfold (latN Γ) hD
    (fun (ω : Quotient (setN Γ (RO.SOf 𝔪))) => hN h𝔪 Ψ s v ω.out)
    (fun ω => measurable_hKer _ _ _ s hv) hfin (fun _ => 1) measurable_const (fun _ => by simp)
    (fun _ _ => rfl)).2
  have h2 : ∀ x : InfinitePlace F → ℂ, tail Ψ s (X.mk x v hv)
      = (∑' z : Quotient (setN Γ (RO.SOf 𝔪)) × latN Γ,
          hN h𝔪 Ψ s v z.1.out ((z.2 : InfinitePlace F → ℂ) + x)) * 1 := fun x => by
    rw [mul_one, tail_mk h𝔪 Ψ hs hv, ← tsum_hN_orb h𝔪 hΓ s hv (fun z : ℂ => z) x]
  simp only [h2]
  rw [h1]
  have hW : Winf s (0 : F) v
      = ((Real.pi : ℂ) / (s - 1)) ^ Fintype.card (InfinitePlace F)
        * ∏ w, ((v w : ℝ) : ℂ) ^ (2 - s) := by
    unfold Winf
    simp only [map_zero, neg_zero]
    rw [Finset.prod_congr rfl fun w _ => jacquet_zero s (by linarith) (hv w),
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have h3 : ∀ ω : Quotient (setN Γ (RO.SOf 𝔪)), ∫ x, hN h𝔪 Ψ s v ω.out x * 1
      = wt h𝔪 Ψ s ω.out.1
        * (((Ninf ω.out.1.out.c * X.sNorm (RO.SOf 𝔪) ω.out.1.out.c ω.out.1.out.d)⁻¹ : ℝ) : ℂ) ^ s
        * Winf s (0 : F) v := fun ω => by
    have := integral_hKer (wt h𝔪 Ψ s ω.out.1) (nrm_pos ω.out)
      (emb (ω.out.1.out.d / ω.out.1.out.c)) s (0 : F) hv
    simp only [chiInf_zero, map_one, mul_one] at this ⊢
    exact this
  simp only [h3]
  rw [tsum_mul_right, hW]
  ring

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.RF_Strip
attribute [-instance] _root_.ArtinKP.B.instCountableIdxI _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.B1.instCountablePairClass _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma ofXV_toXV (P : X F) : ofXV (toXV P) = P := (chart F).apply_symm_apply P

lemma measurable_ofXV : Measurable (ofXV : XV F → X F) := by
  refine (chart F).continuous.measurable.comp (measurable_pi_lambda _ fun w => ?_)
  exact ((measurable_pi_apply w).comp measurable_fst).prodMk
    (Real.measurable_log.comp ((measurable_pi_apply w).comp measurable_snd))

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
-- module Solutions.Artin.KP.RF_Fourier
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
attribute [-instance] _root_.ArtinKP.B.instCountableIdxI _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.B.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupTransLat _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma Cell.vol_ne_top {D : Set (InfinitePlace F → ℂ)} {n₀ : ℕ} (h : Cell Γ D n₀) :
    volume D ≠ ⊤ := by
  have hsub : D ⊆ Metric.closedBall (0 : InfinitePlace F → ℂ) n₀ := fun x hx => by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)]
    exact h.bdd x hx
  exact ((measure_mono hsub).trans_lt measure_closedBall_lt_top).ne

lemma Cell.vol_ne_zero {D : Set (InfinitePlace F → ℂ)} {n₀ : ℕ} (h : Cell Γ D n₀) :
    volume D ≠ 0 :=
  h.fund.measure_ne_zero (NeZero.ne _)

/-! ### The constant-term functional -/

lemma eChar_zero (x : InfinitePlace F → ℂ) : eChar 0 x = 1 := by
  simp [eChar, pair]

lemma stripFn_zero (D : Set (InfinitePlace F → ℂ)) (φ : (InfinitePlace F → ℝ) → ℂ) (P : X F) :
    stripFn D 0 φ P = D.indicator (fun _ => (1 : ℂ)) P.x * φ P.v := by
  rw [stripFn, eChar_zero, one_mul]

theorem coeffFunctional_eq_cf {D : Set (InfinitePlace F → ℂ)} (hD : MeasurableSet D) (n : ℕ)
    {φ : (InfinitePlace F → ℝ) → ℂ} (hφ : Measurable φ) (hφ1 : ∀ v, ‖φ v‖ ≤ 1) (u : X.L2 Γ) :
    X.coeffFunctional Γ n (stripFn D 0 φ) (measurable_stripFn hD 0 hφ) 1
      (norm_stripFn_le D 0 hφ1) u = cf D n φ (X.lift Γ u) :=
  X.coeffFunctional_apply ..

section lin

variable {D : Set (InfinitePlace F → ℂ)} {n : ℕ} {φ : (InfinitePlace F → ℝ) → ℂ}

lemma cf_integrable (hD : MeasurableSet D) (hφ : Measurable φ) (hφ1 : ∀ v, ‖φ v‖ ≤ 1)
    {f : X F → ℂ} (hf : IntegrableOn f (X.box n) (X.vol F)) :
    IntegrableOn (fun P => conj (stripFn D 0 φ P) * f P) (X.box n) (X.vol F) := by
  refine Integrable.bdd_mul (c := 1) hf
    (Complex.continuous_conj.measurable.comp (measurable_stripFn hD 0 hφ)).aestronglyMeasurable ?_
  exact Eventually.of_forall fun P => by
    rw [RCLike.norm_conj]; exact norm_stripFn_le D 0 hφ1 P

lemma cf_sub (hD : MeasurableSet D) (hφ : Measurable φ) (hφ1 : ∀ v, ‖φ v‖ ≤ 1)
    {f g : X F → ℂ} (hf : IntegrableOn f (X.box n) (X.vol F))
    (hg : IntegrableOn g (X.box n) (X.vol F)) :
    cf D n φ (fun P => f P - g P) = cf D n φ f - cf D n φ g := by
  unfold cf
  rw [← integral_sub (cf_integrable hD hφ hφ1 hf) (cf_integrable hD hφ hφ1 hg)]
  exact integral_congr_ae (Eventually.of_forall fun P => by ring)

lemma cf_const_mul (c : ℂ) (f : X F → ℂ) :
    cf D n φ (fun P => c * f P) = c * cf D n φ f := by
  unfold cf
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun P => by ring)

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

/-- The `x`-integral of the tail is `vol(D) · mD · ht^{2−s}`, for every `v`. -/
theorem integral_tail_eq (h𝔪 : 𝔪 ≠ ⊥) {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) {s : ℂ}
    (hs : 2 < s.re) {D : Set (InfinitePlace F → ℂ)} {n₀ : ℕ} (hD : Cell Γ D n₀)
    (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) :
    ∫ x in D, tail Ψ s (X.mk x v hv)
      = (((volume D).toReal : ℝ) : ℂ) * (mD D Ψ s * ∏ w, ((v w : ℝ) : ℂ) ^ (2 - s)) := by
  obtain ⟨C, hC⟩ := exists_integral_tail h𝔪 hΓ hs hD.fund hD.vol_ne_top
  have hvol : (((volume D).toReal : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr ⟨hD.vol_ne_zero, hD.vol_ne_top⟩)
  have h1 : mD D Ψ s = (((volume D).toReal : ℝ) : ℂ)⁻¹ * C := by
    unfold mD
    rw [hC (fun _ => 1) (fun _ => one_pos)]
    simp
  rw [hC v hv, h1]
  field_simp

/-- **MATH2 §2.1(b): the constant term of `E_Ψ(·, s)` at `∞` is
`Ψ_s(0,1)·ht^s + m·ht^{2−s}`**, tested against `(n, φ)`; `Re s > 2`. -/
theorem cf_eis (h𝔪 : 𝔪 ≠ ⊥) {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) {s : ℂ} (hs : 2 < s.re)
    {D : Set (InfinitePlace F → ℂ)} {n : ℕ} (hD : Cell Γ D n)
    {φ : (InfinitePlace F → ℝ) → ℂ} (hφ : Measurable φ) (hφ1 : ∀ v, ‖φ v‖ ≤ 1) :
    cf D n φ (fun P => eis Ψ s P)
      = Ψ s (Row.inf 𝔪) * cf D n φ (htC s) + mD D Ψ s * cf D n φ (htC (2 - s)) := by
  have hE : IntegrableOn (fun P : X F => eis Ψ s P) (X.box n) (X.vol F) :=
    (continuous_eis h𝔪 Ψ hs).continuousOn.integrableOn_compact (isCompact_box n)
  have h1 := integrableOn_htC (F := F) s n
  have h2 := integrableOn_htC (F := F) (2 - s) n
  set R : X F → ℂ := fun P => (eis Ψ s P - Ψ s (Row.inf 𝔪) * htC s P)
    - mD D Ψ s * htC (2 - s) P with hR
  have hRm : Measurable R :=
    ((measurable_eis h𝔪 Ψ hs).sub ((continuous_htC s).measurable.const_mul _)).sub
      ((continuous_htC (2 - s)).measurable.const_mul _)
  have hh1 : IntegrableOn (fun P => Ψ s (Row.inf 𝔪) * htC s P) (X.box n) (X.vol F) :=
    h1.const_mul _
  have hh2 : IntegrableOn (fun P => mD D Ψ s * htC (2 - s) P) (X.box n) (X.vol F) :=
    h2.const_mul _
  have hEh : IntegrableOn (fun P => eis Ψ s P - Ψ s (Row.inf 𝔪) * htC s P) (X.box n)
      (X.vol F) := hE.sub hh1
  have hRint : IntegrableOn R (X.box n) (X.vol F) := hEh.sub hh2
  have hzero : cf D n φ R = 0 := by
    refine cf_eq_zero_of_fibers hD.meas hD.bdd hφ hφ1 hRm hRint fun v hv => ?_
    have hT := integrableOn_tail h𝔪 hΓ hs hv hD.fund hD.vol_ne_top
    have e : ∀ x : InfinitePlace F → ℂ, R (X.mk x v hv)
        = tail Ψ s (X.mk x v hv) - mD D Ψ s * ∏ w, ((v w : ℝ) : ℂ) ^ (2 - s) := fun x => by
      rw [← htC_mk (2 - s) x hv]
      rfl
    simp only [e]
    rw [integral_sub hT (integrableOn_const hD.vol_ne_top), integral_tail_eq h𝔪 hΓ hs hD v hv,
      setIntegral_const, Complex.real_smul, measureReal_def, sub_self]
  have hsplit : cf D n φ R = cf D n φ (fun P => eis Ψ s P)
      - Ψ s (Row.inf 𝔪) * cf D n φ (htC s) - mD D Ψ s * cf D n φ (htC (2 - s)) := by
    rw [hR, cf_sub hD.meas hφ hφ1 hEh hh2, cf_sub hD.meas hφ hφ1 hE hh1, cf_const_mul,
      cf_const_mul]
  rw [hsplit] at hzero
  linear_combination hzero

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.N_Cont
attribute [-instance] _root_.ArtinKP.B.instCountableIdxI _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap _root_.ArtinKP.S2.cubicSymbol_sym
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

lemma continuous_ray : Continuous ray := by unfold ray; fun_prop

lemma tendsto_ray : Tendsto ray (𝓝[>] 0) (𝓝 (4 / 3)) := by
  have h := continuous_ray.tendsto 0
  have h0 : ray 0 = 4 / 3 := by simp [ray]
  rw [h0] at h
  exact h.mono_left nhdsWithin_le_nhds

lemma tendsto_ray_mul_zero {g : ℂ → ℂ} (hg : ContinuousAt g (4 / 3)) :
    Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) * g (ray t)) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I))) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) := by fun_prop
    have h := hc.tendsto 0
    simp only [Complex.ofReal_zero, zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h2 := hg.tendsto.comp tendsto_ray
  simpa using h1.mul h2

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

/-- **MATH2 §2.1(d), transfer form.**  If `m'` continues `mD D Ψ` holomorphically to `E.slit`
and `(s_t − s₀)·m'(s_t) → z` along the ray, then the constant term of `θ_Ψ` at `∞` is
`z·ht^{2/3}`: `cf D n φ (θ_Ψ) = z · cf D n φ (ht^{2/3})` for every test pair `(n, φ)`. -/
theorem cf_theta_of_continuation (hG : Good 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) (hE : ∀ s : ℂ, 2 < s.re → EisEigen Ψ s)
    {D : Set (InfinitePlace F → ℂ)} {n : ℕ} (hD : Cell Γ D n)
    {φ : (InfinitePlace F → ℝ) → ℂ} (hφ : Measurable φ) (hφ1 : ∀ v, ‖φ v‖ ≤ 1) {m' : ℂ → ℂ}
    (hm' : DifferentiableOn ℂ m' E.slit) (hmeq : ∀ s : ℂ, 2 < s.re → m' s = mD D Ψ s) {z : ℂ}
    (hz : Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) * m' (ray t)) (𝓝[>] 0) (𝓝 z)) :
    cf D n φ (X.lift Γ (theta Γ Ψ)) = z * cf D n φ (htC (2 / 3)) := by
  have hP := differentiable_cf_htC hD.meas n hφ hφ1
  have hP2 : Differentiable ℂ fun s : ℂ => cf D n φ (htC (2 - s)) :=
    hP.comp ((differentiable_const (2 : ℂ)).sub differentiable_id)
  have hΨ : Differentiable ℂ fun s : ℂ => Ψ s (Row.inf 𝔪) := Ψ.holo _
  refine integral_box_theta_eq_of_tendsto_ray hG Γ hΓ hE n (stripFn D 0 φ) (measurable_stripFn hD.meas 0 hφ)
    1 (norm_stripFn_le D 0 hφ1)
    (a := fun s => Ψ s (Row.inf 𝔪) * cf D n φ (htC s) + m' s * cf D n φ (htC (2 - s)))
    ((hΨ.mul hP).differentiableOn.add (hm'.mul hP2.differentiableOn)) (fun s hs => ?_) ?_
  · rw [hmeq s hs]
    exact (cf_eis hG.ne_bot hΓ hs hD hφ hφ1).symm
  · have h1 := tendsto_ray_mul_zero (g := fun s => Ψ s (Row.inf 𝔪) * cf D n φ (htC s))
      (hΨ.mul hP).continuous.continuousAt
    have h2 := hz.mul ((hP2.continuous.tendsto (4 / 3)).comp tendsto_ray)
    have e : (2 : ℂ) - 4 / 3 = 2 / 3 := by norm_num
    rw [e] at h2
    have h3 := h1.add h2
    rw [zero_add] at h3
    refine h3.congr fun t => ?_
    simp only [Function.comp_apply]
    ring

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.N_Res
attribute [-instance] _root_.ArtinKP.B.instCountableIdxI _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

section

variable (hG : Good 𝔪) [Γ.FiniteIndex] {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ)
  (hE : ∀ s : ℂ, 2 < s.re → EisEigen Ψ s) {D : Set (InfinitePlace F → ℂ)} {n n' : ℕ}
  {φ φ' : (InfinitePlace F → ℝ) → ℂ}

/-! ### The continued coefficient and its residue -/

include hG hΓ hE in
/-- The residue can be read off any holomorphic continuation of `mD D Ψ` to `E.slit`. -/
theorem zRes_eq_of_continuation (hD : Cell Γ D n) (hn : 1 ≤ n) {m' : ℂ → ℂ}
    (hm' : DifferentiableOn ℂ m' E.slit) (hmeq : ∀ s : ℂ, 2 < s.re → m' s = mD D Ψ s) {z : ℂ}
    (hz : Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) * m' (ray t)) (𝓝[>] 0) (𝓝 z)) :
    zRes Γ Ψ D n = z := by
  have h := cf_theta_of_continuation hG Γ hΓ hE hD (measurable_phase (2 / 3))
    (norm_phase_le (2 / 3)) hm' hmeq hz
  unfold zRes
  rw [h, mul_div_assoc, div_self (cf_phase_ne_zero hD hn (2 / 3 : ℂ)), mul_one]

/-- Converse direction of Corollary N: `θ_Ψ = 0` forces `zRes = 0`. -/
theorem zRes_eq_zero_of_theta (hD : Cell Γ D n) (h : theta Γ Ψ = 0) : zRes Γ Ψ D n = 0 := by
  unfold zRes
  rw [← coeffFunctional_eq_cf hD.meas n (measurable_phase (2 / 3)) (norm_phase_le (2 / 3)), h,
    map_zero, zero_div]

end

/-! ### `‖θ‖² = −c₀⟪F, θ⟫` -/

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.T_Mean
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma IsReps.injective {κ : Type*} {rep : κ → E} (h : IsReps L L₁ rep) :
    Function.Injective rep := by
  intro k k' hkk
  obtain ⟨k₀, _, hu⟩ := h.uniq (rep k) (h.mem k)
  have h1 : k = k₀ := hu k (by simp)
  have h2 : k' = k₀ := hu k' (by rw [hkk]; simp)
  rw [h1, h2]

lemma IsReps.nonempty {κ : Type*} {rep : κ → E} (h : IsReps L L₁ rep) : Nonempty κ := by
  obtain ⟨k, _, _⟩ := h.uniq 0 L₁.zero_mem
  exact ⟨k⟩

section union

variable {κ : Type*} [Fintype κ] {rep : κ → E}

/-- The translates `rep k + D` are pairwise disjoint. -/
lemma disjoint_shiftSet (hrep : IsReps L L₁ rep) (h : PCell L₁ D) {k k' : κ} (hk : k ≠ k') :
    Disjoint (shiftSet (rep k) D) (shiftSet (rep k') D) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨g, _, hu⟩ := h.fund x
  have h1 := hu ⟨-rep k, L₁.neg_mem (hrep.mem k)⟩ (by
    change -rep k + x ∈ D
    rw [neg_add_eq_sub]; exact hx)
  have h2 := hu ⟨-rep k', L₁.neg_mem (hrep.mem k')⟩ (by
    change -rep k' + x ∈ D
    rw [neg_add_eq_sub]; exact hx')
  have h3 : -rep k = -rep k' := congrArg Subtype.val (h1.trans h2.symm)
  exact hk (hrep.injective (neg_injective h3))

variable {μ : Measure E}

theorem integral_unionSet (hrep : IsReps L L₁ rep) (h : PCell L₁ D) {f : E → ℂ}
    (hf : ∀ k, IntegrableOn f (shiftSet (rep k) D) μ) :
    ∫ x in unionSet rep D, f x ∂μ = ∑ k, ∫ x in shiftSet (rep k) D, f x ∂μ := by
  have e : unionSet rep D = ⋃ k ∈ (Finset.univ : Finset κ), shiftSet (rep k) D := by
    rw [unionSet_eq]; simp
  rw [e]
  exact integral_biUnion_finset _ (fun k _ => measurableSet_shiftSet _ h.meas)
    (fun k _ k' _ hkk => disjoint_shiftSet hrep h hkk) (fun k _ => hf k)

theorem measure_unionSet (hrep : IsReps L L₁ rep) (h : PCell L₁ D) :
    μ (unionSet rep D) = ∑ k, μ (shiftSet (rep k) D) := by
  have e : unionSet rep D = ⋃ k ∈ (Finset.univ : Finset κ), shiftSet (rep k) D := by
    rw [unionSet_eq]; simp
  rw [e]
  exact measure_biUnion_finset (fun k _ k' _ hkk => disjoint_shiftSet hrep h hkk)
    (fun k _ => measurableSet_shiftSet _ h.meas)

end union

section shift

variable {μ : Measure E} [μ.IsAddRightInvariant]

theorem measure_shiftSet (t : E) (D : Set E) (hD : MeasurableSet D) :
    μ (shiftSet t D) = μ D :=
  (measurePreserving_sub_right μ t).measure_preimage hD.nullMeasurableSet

theorem integral_shiftSet (t : E) {D : Set E} (hD : MeasurableSet D) (f : E → ℂ) :
    ∫ x in shiftSet t D, f x ∂μ = ∫ y in D, f (y + t) ∂μ := by
  have h := (measurePreserving_sub_right μ t).setIntegral_preimage_emb
    (MeasurableEquiv.subRight t).measurableEmbedding (fun y => f (y + t)) D
  rw [← h]
  refine setIntegral_congr_fun (measurableSet_shiftSet t hD) fun x _ => ?_
  simp

theorem integrableOn_shiftSet (t : E) {D : Set E} {f : E → ℂ}
    (hf : IntegrableOn (fun y => f (y + t)) D μ) : IntegrableOn f (shiftSet t D) μ := by
  have h := (measurePreserving_sub_right μ t).integrableOn_comp_preimage
    (MeasurableEquiv.subRight t).measurableEmbedding (f := fun y => f (y + t)) (s := D)
  have e : ((fun y => f (y + t)) ∘ fun x => x - t) = f := by
    funext x; simp
  rw [e] at h
  exact h.mpr hf

end shift

/-- **Mean values over cells of commensurable lattices.** -/
theorem mean_eq {μ : Measure E} [μ.IsAddRightInvariant] [μ.IsAddLeftInvariant] [Countable L]
    (hL₁ : L ≤ L₁) (hL₂ : L ≤ L₂)
    {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂] {rep₁ : κ₁ → E} {rep₂ : κ₂ → E}
    (hrep₁ : IsReps L L₁ rep₁) (hrep₂ : IsReps L L₂ rep₂) (h₁ : PCell L₁ D₁) (h₂ : PCell L₂ D₂)
    {f : E → ℂ} (hper : ∀ g ∈ L₁, ∀ x, f (x + g) = f x)
    (hint₁ : IntegrableOn f D₁ μ) (hint₂ : ∀ k, IntegrableOn f (shiftSet (rep₂ k) D₂) μ) {I : ℂ}
    (hI : ∀ k, ∫ x in shiftSet (rep₂ k) D₂, f x ∂μ = I) :
    ((μ.real D₂ : ℝ) : ℂ) * ∫ x in D₁, f x ∂μ = ((μ.real D₁ : ℝ) : ℂ) * I := by
  have hU₁ := (h₁.union hL₁ hrep₁).isAddFundamentalDomain μ
  have hU₂ := (h₂.union hL₂ hrep₂).isAddFundamentalDomain μ
  have hinv : ∀ (g : L) (x : E), f (g +ᵥ x) = f x := fun g x => by
    change f ((g : E) + x) = f x
    rw [add_comm]; exact hper _ (hL₁ g.2) x
  have hint₁' : ∀ k, IntegrableOn f (shiftSet (rep₁ k) D₁) μ := fun k =>
    integrableOn_shiftSet _ (by simpa only [hper _ (hrep₁.mem k)] using hint₁)
  have e1 : ∫ x in unionSet rep₁ D₁, f x ∂μ = (Fintype.card κ₁ : ℂ) * ∫ x in D₁, f x ∂μ := by
    rw [integral_unionSet hrep₁ h₁ hint₁']
    have : ∀ k, ∫ x in shiftSet (rep₁ k) D₁, f x ∂μ = ∫ x in D₁, f x ∂μ := fun k => by
      rw [integral_shiftSet _ h₁.meas]
      simp only [hper _ (hrep₁.mem k)]
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have e2 : ∫ x in unionSet rep₂ D₂, f x ∂μ = (Fintype.card κ₂ : ℂ) * I := by
    rw [integral_unionSet hrep₂ h₂ hint₂]
    simp only [hI, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have e3 : ∫ x in unionSet rep₁ D₁, f x ∂μ = ∫ x in unionSet rep₂ D₂, f x ∂μ :=
    hU₁.setIntegral_eq hU₂ hinv
  have m1 : μ (unionSet rep₁ D₁) = Fintype.card κ₁ * μ D₁ := by
    rw [measure_unionSet hrep₁ h₁]
    simp only [measure_shiftSet _ _ h₁.meas, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have m2 : μ (unionSet rep₂ D₂) = Fintype.card κ₂ * μ D₂ := by
    rw [measure_unionSet hrep₂ h₂]
    simp only [measure_shiftSet _ _ h₂.meas, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have m3 : (Fintype.card κ₁ : ℝ) * μ.real D₁ = (Fintype.card κ₂ : ℝ) * μ.real D₂ := by
    have := hU₁.measure_eq hU₂
    rw [m1, m2] at this
    have h' := congrArg ENNReal.toReal this
    simpa [measureReal_def, ENNReal.toReal_mul] using h'
  have hc : (Fintype.card κ₁ : ℂ) ≠ 0 := by
    have := hrep₁.nonempty
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have m3' : (Fintype.card κ₁ : ℂ) * ((μ.real D₁ : ℝ) : ℂ)
      = (Fintype.card κ₂ : ℂ) * ((μ.real D₂ : ℝ) : ℂ) := by exact_mod_cast m3
  have e4 : (Fintype.card κ₁ : ℂ) * ∫ x in D₁, f x ∂μ = (Fintype.card κ₂ : ℂ) * I := by
    rw [← e1, ← e2, e3]
  apply mul_left_cancel₀ hc
  linear_combination ((μ.real D₂ : ℝ) : ℂ) * e4 - I * m3'

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.T_Lat
attribute [-instance] _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-T, file 3: the lattices `Λ_Γ` (translations of `Γ`) and `Λ_M` (`B.transLat 𝔪 M`)

Both sit in `latO F = emb(𝓞_F)` (for `M ≥ 0`) and contain the image of a nonzero ideal, hence are
commensurable: `relIndex_inf_left/right`.

* `pcell_of_hfund`: WP-X2/WP-RF's `hfund` is a strict cell `T.PCell (N.latN Γ) D`;
  `exists_pcell_latN`.
* `exists_pcell_transLat`: a bounded strict cell of `Λ_M` (`M ≥ 0`), as a union of translates of a
  cell of `emb(𝓞_F)`;  `cellM 𝔪 M` (a chosen one, bounded by `cellN 𝔪 M`).
* `kap 𝔪 M = (vol(cellM 𝔪 M) · vol(𝔩_M))⁻¹` — the constant of all coefficient formulas
  (`= covol(𝓞_F)⁻¹` by WP-B's stub B-2; independent of the chosen cell: `volume_eq_cellM`).
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

/-! ### Ideal lattices -/

lemma latN_le_latO (Γ : Subgroup (SL(2, 𝓞 F))) : latN Γ ≤ latO F :=
  AddSubgroup.map_mono le_top

/-- Two lattices between `emb(ideal)` and `emb(𝓞)` are commensurable. -/
theorem relIndex_inf_left {A B : AddSubgroup (InfinitePlace F → ℂ)} {I J : Ideal (𝓞 F)}
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (hIA : idealLat I ≤ A) (hJB : idealLat J ≤ B)
    (hA : A ≤ latO F) : (A ⊓ B).relIndex A ≠ 0 := by
  have hIJ : I * J ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot]
    exact not_or.mpr ⟨hI, hJ⟩
  have h0 := relIndex_idealLat hIJ
  have h1 : idealLat (I * J) ≤ idealLat I :=
    AddSubgroup.map_mono (Submodule.toAddSubgroup_mono Ideal.mul_le_left)
  have h2 : idealLat (I * J) ≤ idealLat J :=
    AddSubgroup.map_mono (Submodule.toAddSubgroup_mono Ideal.mul_le_right)
  have hle : idealLat (I * J) ≤ A ⊓ B := le_inf (h1.trans hIA) (h2.trans hJB)
  intro h
  exact h0 (AddSubgroup.relIndex_eq_zero_of_le_right hA
    (AddSubgroup.relIndex_eq_zero_of_le_left hle h))

theorem relIndex_inf_right {A B : AddSubgroup (InfinitePlace F → ℂ)} {I J : Ideal (𝓞 F)}
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (hIA : idealLat I ≤ A) (hJB : idealLat J ≤ B)
    (hB : B ≤ latO F) : (A ⊓ B).relIndex B ≠ 0 := by
  rw [inf_comm]
  exact relIndex_inf_left hJ hI hJB hIA hB

/-! ### The two families of lattices -/

theorem exists_idealLat_le_latN (Γ : Subgroup (SL(2, 𝓞 F)))
    [Γ.FiniteIndex] : ∃ 𝔫 : Ideal (𝓞 F), 𝔫 ≠ ⊥ ∧ idealLat 𝔫 ≤ latN Γ := by
  obtain ⟨𝔫, h𝔫, h⟩ := exists_ideal_translations Γ
  refine ⟨𝔫, h𝔫, ?_⟩
  rintro x ⟨β, hβ, rfl⟩
  obtain ⟨γ, hγ⟩ := h β hβ
  refine ⟨β, ?_, rfl⟩
  change nInt β ∈ Γ
  rw [← hγ, nInt_eq_of_GammaN]
  exact (γ : Γ).2

/-! ### Cells -/

lemma volume_ne_top_of_bdd {D : Set (InfinitePlace F → ℂ)} {n : ℕ}
    (h : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) : volume D ≠ ⊤ := by
  have hsub : D ⊆ Metric.closedBall (0 : InfinitePlace F → ℂ) n := fun x hx => by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)]
    exact h x hx
  exact ((measure_mono hsub).trans_lt measure_closedBall_lt_top).ne

lemma integrableOn_of_bdd {D : Set (InfinitePlace F → ℂ)} {n : ℕ}
    (h : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) {f : (InfinitePlace F → ℂ) → ℂ} (hf : Continuous f) :
    IntegrableOn f D volume := by
  have hsub : D ⊆ Metric.closedBall (0 : InfinitePlace F → ℂ) n := fun x hx => by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)]
    exact h x hx
  exact (hf.continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set hsub

/-- A translate of a bounded set is bounded. -/
lemma exists_bdd_shiftSet {D : Set (InfinitePlace F → ℂ)} {n : ℕ}
    (h : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) (t : InfinitePlace F → ℂ) :
    ∃ n' : ℕ, ∀ x ∈ shiftSet t D, ∀ w, ‖x w‖ ≤ n' := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖t‖
  refine ⟨n + N, fun x hx w => ?_⟩
  have h1 := h _ hx w
  have h2 : ‖t w‖ ≤ N := (norm_le_pi_norm t w).trans hN
  have e : x w = (x - t) w + t w := by simp
  rw [e]
  push_cast
  exact (norm_add_le _ _).trans (add_le_add h1 h2)


theorem pcell_cellM (h𝔪 : 𝔪 ≠ ⊥) {M : ℤ} (hM : 0 ≤ M) : PCell (transLat 𝔪 M) (cellM 𝔪 M) := by
  unfold cellM
  rw [dif_pos ⟨h𝔪, hM⟩]
  exact (exists_pcell_transLat h𝔪 hM).choose_spec.choose_spec.1

theorem cellM_bdd (h𝔪 : 𝔪 ≠ ⊥) {M : ℤ} (hM : 0 ≤ M) :
    ∀ x ∈ cellM 𝔪 M, ∀ w, ‖x w‖ ≤ cellN 𝔪 M := by
  unfold cellM cellN
  rw [dif_pos ⟨h𝔪, hM⟩, dif_pos ⟨h𝔪, hM⟩]
  exact (exists_pcell_transLat h𝔪 hM).choose_spec.choose_spec.2

lemma volume_toReal_pos {L : AddSubgroup (InfinitePlace F → ℂ)} [Countable L]
    {D : Set (InfinitePlace F → ℂ)} (h : PCell L D) {n : ℕ} (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) :
    0 < (volume D).toReal :=
  ENNReal.toReal_pos ((h.isAddFundamentalDomain volume).measure_ne_zero (NeZero.ne _))
    (volume_ne_top_of_bdd hb)

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.C9_Nonvanish
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.G1.scal_apply
/-!
# WP-C9, part 1: `θ_{Φ^Σ} ≠ 0` (MATH2 §3)

`Φ^Σ = B.sumBig ι hG hN1 hN M T` (`T` a complete disjoint system of classes, `M ≥ 0`),
`Ψ^Σ = twist Φ^Σ`.

* `mD_eq_of_mean`: reconciliation of the two normalizations.  WP-N's coefficient `mD D Ψ s` is a
  mean over a cell `D` of `Λ_Γ = N.latN Γ`; WP-BZ computes means over cells of
  `Λ_M = B.transLat 𝔪 M`.  The two lattices are commensurable (`T.relIndex_inf_left/right`) and
  the means agree (`T.mean_eq`).
* `mD_sumBig`: `mD D Ψ^Σ s = C·(π/(s-1))^r·G(s)/(s-4/3)` for `Re s > 2`, `G` as in
  `BZ.exists_mean_const_term_pole`.
* **`zRes_sumBig`**: `zRes Γ Ψ^Σ D n = C·(3π)^r·G(4/3)`, and **`zRes_sumBig_ne_zero`**.
* **`theta_sumBig_ne_zero`**: `θ_{Ψ^Σ} ≠ 0`, for every finite-index `Γ` fixing `Ψ^Σ`.
* **`exists_theta_bigCell_ne_zero`**: some single big-cell section has `θ ≠ 0`.
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

/-- A bounded strict cell is a cell in WP-N's sense. -/
theorem cell_of_pcell {Γ : Subgroup (SL(2, 𝓞 F))} {D : Set (InfinitePlace F → ℂ)} {n : ℕ}
    (hD : T.PCell (latN Γ) D) (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) : Cell Γ D n :=
  ⟨hD.meas, hD.isAddFundamentalDomain volume, hb⟩

/-- `E_Ψ(x + g, v) = E_Ψ(x, v)` for `g ∈ Λ_Γ`. -/
theorem eis_add_latN (h𝔪 : 𝔪 ≠ ⊥) {Γ : Subgroup (SL(2, 𝓞 F))} {Ψ : TSection ι 𝔪}
    (hΓ : Inv Γ Ψ) (s : ℂ) {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w)
    {g : InfinitePlace F → ℂ} (hg : g ∈ latN Γ) (x : InfinitePlace F → ℂ) :
    eis Ψ s (X.mk (x + g) v hv) = eis Ψ s (X.mk x v hv) := by
  obtain ⟨β, hβ, rfl⟩ := hg
  have h := isInv_eis h𝔪 hΓ s ⟨nInt β, hβ⟩ (X.mk x v hv)
  change eis Ψ s (nInt β • X.mk x v hv) = _ at h
  rwa [nInt_smul_mk] at h

/-- **Reconciliation of the normalizations of WP-N and WP-BZ.**  If `Ψ_s(0,1) = 0` and the mean
of `E_Ψ(·, 1)` over every cell of `Λ_M` is `c`, then `mD D Ψ s = c` for every bounded strict
cell `D` of `Λ_Γ`. -/
theorem mD_eq_of_mean (h𝔪 : 𝔪 ≠ ⊥) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) {M : ℤ} (hM : 0 ≤ M) {s : ℂ} (hs : 2 < s.re)
    (h0 : Ψ s (Row.inf 𝔪) = 0) {D : Set (InfinitePlace F → ℂ)} {n : ℕ}
    (hD : T.PCell (latN Γ) D) (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) {c : ℂ}
    (hc : ∀ D₂ : Set (InfinitePlace F → ℂ), IsAddFundamentalDomain (transLat 𝔪 M) D₂ volume →
      (((volume D₂).toReal : ℝ) : ℂ)⁻¹
        * ∫ x in D₂, eis Ψ s (X.mk x (fun _ => 1) (fun _ => one_pos)) = c) :
    mD D Ψ s = c := by
  set f : (InfinitePlace F → ℂ) → ℂ :=
    fun x => eis Ψ s (X.mk x (fun _ => 1) (fun _ => one_pos)) with hf
  have hfc : Continuous f :=
    (continuous_eis h𝔪 Ψ hs).comp (continuous_mk_x _ _)
  have htail : ∀ x, tail Ψ s (X.mk x (fun _ => 1) (fun _ => one_pos)) = f x := fun x => by
    rw [tail, h0, zero_mul, sub_zero]
  obtain ⟨I, hI, hIle⟩ := T.exists_idealLat_le_latN Γ
  obtain ⟨J, hJ, hJle⟩ := T.exists_idealLat_le_transLat (𝔪 := 𝔪) h𝔪 M
  have r1 := T.relIndex_inf_left hI hJ hIle hJle (T.latN_le_latO Γ)
  have r2 := T.relIndex_inf_right hI hJ hIle hJle (T.transLat_le_latO (𝔪 := 𝔪) hM)
  obtain ⟨κ₁, _, rep₁, hrep₁⟩ := T.exists_reps r1
  obtain ⟨κ₂, _, rep₂, hrep₂⟩ := T.exists_reps r2
  have hD₂ := T.pcell_cellM (𝔪 := 𝔪) h𝔪 hM
  have hb₂ := T.cellM_bdd (𝔪 := 𝔪) h𝔪 hM
  have hpos₂ : 0 < (volume (T.cellM 𝔪 M)).toReal := T.volume_toReal_pos hD₂ hb₂
  have hpos₁ : 0 < (volume D).toReal := T.volume_toReal_pos hD hb
  have hshift : ∀ k, ∫ x in T.shiftSet (rep₂ k) (T.cellM 𝔪 M), f x
      = (((volume (T.cellM 𝔪 M)).toReal : ℝ) : ℂ) * c := fun k => by
    have h1 := hc _ ((hD₂.shift (rep₂ k)).isAddFundamentalDomain volume)
    rw [T.measure_shiftSet _ _ hD₂.meas] at h1
    rw [← h1, ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hpos₂.ne'), one_mul]
  have key := T.mean_eq (μ := (volume : Measure (InfinitePlace F → ℂ)))
    (inf_le_left : latN Γ ⊓ transLat 𝔪 M ≤ latN Γ) inf_le_right hrep₁ hrep₂ hD hD₂ (f := f)
    (fun g hg x => eis_add_latN h𝔪 hΓ s _ hg x)
    (T.integrableOn_of_bdd hb hfc)
    (fun k => by
      obtain ⟨n', hn'⟩ := T.exists_bdd_shiftSet hb₂ (rep₂ k)
      exact T.integrableOn_of_bdd hn' hfc)
    hshift
  rw [measureReal_def, measureReal_def] at key
  unfold mD
  simp only [htail]
  have h2 : (((volume (T.cellM 𝔪 M)).toReal : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hpos₂.ne'
  have h1 : (((volume D).toReal : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos₁.ne'
  have key' : ∫ x in D, f x = (((volume D).toReal : ℝ) : ℂ) * c := by
    apply mul_left_cancel₀ h2
    rw [key]; ring
  rw [key', ← mul_assoc, inv_mul_cancel₀ h1, one_mul]

/-! ### The class-sum section -/

section sumBig

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  {N : ℕ} (hN1 : 1 ≤ N) (hN : P.IsDeepLevel 𝔪 N) (M : ℤ) (Tc : Finset {η : F // η ≠ 0})

theorem psiSum_inf (s : ℂ) : psiSum hG hz6 hN1 hN M Tc ι s (Row.inf 𝔪) = 0 := by
  unfold psiSum
  rw [GSection.twist_apply]
  have h : (((Row.inf 𝔪).c : SInt 𝔪) : F) = 0 := by
    change (((0 : SInt 𝔪) : SInt 𝔪) : F) = 0
    rfl
  rw [h, BZ.sumBig_zero_left, mul_zero]

lemma slit_sub_one_ne {s : ℂ} (hs : s ∈ E.slit) : s - 1 ≠ 0 := by
  intro h
  have : s.re = 1 := by
    have := congrArg Complex.re h
    simp at this; linarith
  exact absurd hs.1 (by rw [this]; exact lt_irrefl _)

lemma slit_sub_ne {s : ℂ} (hs : s ∈ E.slit) : s - 4 / 3 ≠ 0 := by
  intro h
  have hs' : s = 4 / 3 := sub_eq_zero.mp h
  have h1 : s.im = 0 := by rw [hs']; simp
  have h2 := hs.2 h1
  rw [hs'] at h2
  norm_num at h2

theorem differentiableOn_mModel (M : ℤ) {G : ℂ → ℂ}
    (hGd : DifferentiableOn ℂ G {s : ℂ | 1 < s.re}) :
    DifferentiableOn ℂ (mModel 𝔪 M G) E.slit := by
  unfold mModel
  have hG' : DifferentiableOn ℂ G E.slit := hGd.mono fun s hs => hs.1
  refine ((DifferentiableOn.const_mul ?_ _).mul ?_)
  · exact ((differentiableOn_const _).div (differentiableOn_id.sub (differentiableOn_const _))
      fun s hs => slit_sub_one_ne hs).pow _
  · exact hG'.div (differentiableOn_id.sub (differentiableOn_const _)) fun s hs => slit_sub_ne hs

/-- The ray residue of the model: `C·(3π)^r·G(4/3)`. -/
theorem tendsto_ray_mModel (M : ℤ) {G : ℂ → ℂ}
    (hGd : DifferentiableOn ℂ G {s : ℂ | 1 < s.re}) :
    Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) * mModel 𝔪 M G (ray t)) (𝓝[>] 0)
      (𝓝 (((BZ.constC 𝔪 M : ℝ) : ℂ) * (3 * (Real.pi : ℂ)) ^ Fintype.card (InfinitePlace F)
        * G (4 / 3))) := by
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : (4 / 3 : ℂ) ∈ {s : ℂ | 1 < s.re} := by
    change (1 : ℝ) < (4 / 3 : ℂ).re
    norm_num
  have hGc : ContinuousAt G (4 / 3) := (hGd.differentiableAt (hopen.mem_nhds hmem)).continuousAt
  have hg : ContinuousAt (fun s : ℂ => ((BZ.constC 𝔪 M : ℝ) : ℂ)
      * ((Real.pi : ℂ) / (s - 1)) ^ Fintype.card (InfinitePlace F) * G s) (4 / 3) := by
    refine (ContinuousAt.mul continuousAt_const ?_).mul hGc
    refine ContinuousAt.pow (continuousAt_const.div (continuousAt_id.sub continuousAt_const) ?_) _
    norm_num
  have hlim := (hg.tendsto.comp tendsto_ray)
  have hval : ((BZ.constC 𝔪 M : ℝ) : ℂ)
      * ((Real.pi : ℂ) / ((4 / 3 : ℂ) - 1)) ^ Fintype.card (InfinitePlace F) * G (4 / 3)
      = ((BZ.constC 𝔪 M : ℝ) : ℂ) * (3 * (Real.pi : ℂ)) ^ Fintype.card (InfinitePlace F)
        * G (4 / 3) := by
    congr 2
    congr 1
    have : ((4 / 3 : ℂ) - 1) = 1 / 3 := by norm_num
    rw [this]; field_simp
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : (t : ℂ) * (1 + Complex.I) ≠ 0 := by
    refine mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt ht)) ?_
    intro h
    have := congrArg Complex.re h
    simp at this
  have hr : ray t - 4 / 3 = (t : ℂ) * (1 + Complex.I) := by
    unfold ray; ring
  have halg : ∀ a b c : ℂ, c ≠ 0 → a * b = c * (a * (b / c)) := by
    intro a b c hc; field_simp
  simp only [Function.comp_apply, mModel]
  rw [hr]
  exact halg _ _ _ ht0

variable (hdisj : ∀ η ∈ Tc, ∀ η' ∈ Tc, η ≠ η' → ∀ c : F, InClass 𝔪 N η.1 c → ¬ InClass 𝔪 N η'.1 c)
  (hcov : ∀ c : F, c ≠ 0 → ∃ η ∈ Tc, InClass 𝔪 N η.1 c)

/-- The function `G` of `BZ.exists_mean_const_term_pole` (holomorphic on `Re s > 1`,
`G(4/3) = ρ_S/(3ζ^S(2)) ≠ 0`), with the formula for `mD` on cells of `Λ_Γ`. -/
theorem exists_mD_sumBig (ι : F →+* ℂ) (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F}
    (hz6 : IsPrimitiveRoot z6 6) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | 1 < s.re} ∧
      G (4 / 3) = (sZetaResidue 𝔪 : ℂ) / (3 * C3P.zetaS 𝔪 2) ∧ G (4 / 3) ≠ 0 ∧
      ∀ {N : ℕ} (hN1 : 1 ≤ N) (hN : P.IsDeepLevel 𝔪 N) (M : ℤ) (Tc : Finset {η : F // η ≠ 0}),
        (∀ η ∈ Tc, ∀ η' ∈ Tc, η ≠ η' → ∀ c : F, InClass 𝔪 N η.1 c → ¬ InClass 𝔪 N η'.1 c) →
        (∀ c : F, c ≠ 0 → ∃ η ∈ Tc, InClass 𝔪 N η.1 c) → 0 ≤ M →
        ∀ (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex], Inv Γ (psiSum hG hz6 hN1 hN M Tc ι) →
        ∀ {D : Set (InfinitePlace F → ℂ)} {n : ℕ}, T.PCell (latN Γ) D →
          (∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) → ∀ {s : ℂ}, 2 < s.re →
            mD D (psiSum hG hz6 hN1 hN M Tc ι) s = mModel 𝔪 M G s := by
  obtain ⟨G, hGd, hG1, hG0, hmean⟩ := BZ.exists_mean_eis_sumBig_eq_pole_four_thirds ι P hG hz6
  refine ⟨G, hGd, hG1, hG0, fun hN1 hN M Tc hdisj hcov hM Γ _ hΓ D n hD hb s hs => ?_⟩
  refine mD_eq_of_mean hG.ne_bot Γ hΓ hM hs (psiSum_inf hG hz6 hN1 hN M Tc s) hD hb
    fun D₂ hD₂ => ?_
  have h := hmean hN1 hN M Tc hdisj hcov hD₂ hs (fun _ => 1) (fun _ => one_pos)
  unfold psiSum
  rw [h]
  simp [mModel]

include hdisj hcov in
/-- **(C9), residue form**: `zRes(Ψ^Σ) ≠ 0`, for every finite-index `Γ` fixing `Ψ^Σ`, every
bounded strict cell `D` of `Λ_Γ` and every box index `n ≥ 1` bounding `D`. -/
theorem zRes_sumBig_ne_zero (hM : 0 ≤ M) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    (hΓ : Inv Γ (psiSum hG hz6 hN1 hN M Tc ι)) {D : Set (InfinitePlace F → ℂ)} {n : ℕ}
    (hD : T.PCell (latN Γ) D) (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) (hn : 1 ≤ n) :
    zRes Γ (psiSum hG hz6 hN1 hN M Tc ι) D n ≠ 0 := by
  obtain ⟨G, hGd, -, hG0, hm⟩ := exists_mD_sumBig ι P hG hz6
  have hz := zRes_eq_of_continuation hG hΓ
    (fun s hs => GL.eisEigen_of_two_lt_re hG.ne_bot _ hs) (cell_of_pcell hD hb) hn
    (differentiableOn_mModel M hGd)
    (fun s hs => (hm hN1 hN M Tc hdisj hcov hM Γ hΓ hD hb hs).symm)
    (tendsto_ray_mModel M hGd)
  rw [hz]
  refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ ?_)) hG0
  · exact Complex.ofReal_ne_zero.mpr (BZ.constC_pos 𝔪 M).ne'
  · exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)

include hdisj hcov in
/-- **(C9): `θ_{Φ^Σ} ≠ 0`**, for every finite-index `Γ` fixing the twist of `Φ^Σ`. -/
theorem theta_psiSum_ne_zero_oai (hM : 0 ≤ M) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    (hΓ : Inv Γ (psiSum hG hz6 hN1 hN M Tc ι)) :
    theta Γ (psiSum hG hz6 hN1 hN M Tc ι) ≠ 0 := by
  obtain ⟨D, n, hD, hb⟩ := T.exists_pcell_latN Γ
  have hb' : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ ((n + 1 : ℕ) : ℝ) := fun x hx w =>
    (hb x hx w).trans (by push_cast; linarith)
  intro h
  exact zRes_sumBig_ne_zero hG hz6 hN1 hN M Tc hdisj hcov hM Γ hΓ hD hb' (Nat.succ_le_succ
    (Nat.zero_le n)) (zRes_eq_zero_of_theta (cell_of_pcell hD hb') h)

end sumBig

end

end ArtinKP.C9
end

theorem solution.{u_1} : type_of% @ArtinKP.C9.theta_psiSum_ne_zero_oai.{u_1} := @ArtinKP.C9.theta_psiSum_ne_zero_oai.{u_1}
