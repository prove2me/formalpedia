-- Prove2me | solution 1 for ArtinKP.N2.mD_eq_of_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:13:39.59468+00:00
-- url     : https://prove2.me/submissions/688cb0fb-0724-4680-aedc-69e9bb02023c

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
import Theorems.Thm_ArtinKP_B_continuous_eis
import Theorems.Thm_ArtinKP_B1_Tinf_le

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
attribute [-instance] _root_.ArtinKP.B1.PairClass.instNonempty _root_.ArtinKP.B1.instDiscreteTopologySubtypeE₂MemSubmoduleIntPairLattice _root_.ArtinKP.X.instDiscreteTopologySubtypeMixedSpaceMemSubmoduleIntLattice _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

variable {F : Type*} [Field F] [NumberField F]

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

end PairClass

/-! ### Lemma M for pair classes -/

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.B1_Cusp
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.B.coe_latREquiv _root_.ArtinKP.B.embR_apply _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
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

/-! ### Harnack in the horizontal variable -/

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.B1_Const
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-! ### The lattice `𝓞_F ⊂ ℂ^r` -/

/-! ### Scaling -/

/-! ### Orbits of the translations on the classes `≠ ∞` -/

/-! ### The constant term -/

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

end height

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.B_Def2
attribute [-instance] _root_.ArtinKP.B1.instCountablePairClass _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-! ### Regularity of the summands -/

section analytic

variable [IsTotallyComplex F]

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
-- module Solutions.Artin.KP.B_FourArch
attribute [-instance] _root_.ArtinKP.B1.instCountablePairClass _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-! ### The `S_f`-character -/

/-! ### The archimedean kernel -/

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

/-! ### Shifted kernels -/

theorem measurable_hKer (A : ℂ) (N : ℝ) (e : InfinitePlace F → ℂ) (s : ℂ)
    {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w) : Measurable (hKer A N e s v) := by
  have h1 : Measurable fun x : InfinitePlace F → ℂ => N⁻¹ * kerA v (x + e) :=
    measurable_const.mul
      ((continuous_kerA hv).comp (continuous_id.add continuous_const)).measurable
  exact measurable_const.mul ((Complex.measurable_ofReal.comp h1).pow_const s)

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.B_FourUnfold
attribute [-instance] _root_.ArtinKP.B1.instCountablePairClass _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.RO_Bridge
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
-- module Solutions.Artin.KP.C5_Series
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

end

end ArtinKP.N
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
-- module Solutions.Artin.KP.N_Shape
attribute [-instance] _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-! ### Fubini: a function with vanishing `x`-integrals over `D` is killed by `cf` -/

/-! ### The shape -/

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.N2_Lattice
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
/-! # WP-N2, file 1: independence of `mD` and `zRes` from the auxiliary choices `(Γ, D, n)`

* `avg_eq_of_le` (abstract): for additive subgroups `Λ₂ ≤ Λ₁` of a measurable group, a strict
  fundamental set `D₁` of `Λ₁` and an (a.e.) fundamental domain `D₂` of `Λ₂` of finite measure, the
  mean of a `Λ₁`-periodic function over `D₂` is its mean over `D₁`.  (The union of the translates
  of `D₁` by coset representatives is a strict fundamental set of `Λ₂`; finiteness of the index is
  a consequence of `μ D₂ < ∞`.)
* `exists_strict_cell`: every finite-index `Γ` has a bounded measurable *strict* fundamental set of
  its translation lattice.
* **`mD_congr`**: `mD D Ψ s` (`Re s > 2`) does not depend on the group fixing `Ψ` nor on the cell.
* **`zRes_congr`**: `zRes Γ Ψ D n` does not depend on `(Γ, D, n)` (`n ≥ 1`); so `z_Ψ` is intrinsic
  (WP-N open item 4; the intrinsic value `zPsi` is in `N2_Cor`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N2

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

/-! ### Fundamental domains of a subgroup and of a subgroup of it -/

section abstract

variable {E : Type*} [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd E] {μ : Measure E}
  [μ.IsAddLeftInvariant]

lemma existsUnique_unionDom {Λ₁ Λ₂ : AddSubgroup E} (hle : Λ₂ ≤ Λ₁) {D₁ : Set E}
    (h₁ : ∀ x, ∃! g : Λ₁, (g : E) + x ∈ D₁) (x : E) :
    ∃! g : Λ₂, (g : E) + x ∈ unionDom Λ₁ Λ₂ D₁ := by
  obtain ⟨g₁, hg₁, huniq⟩ := h₁ x
  obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add (Λ₂.addSubgroupOf Λ₁) (-g₁)
  have hmem : ((h : Λ₁) : E) ∈ Λ₂ := AddSubgroup.mem_addSubgroupOf.mp h.2
  refine ⟨⟨((h : Λ₁) : E), hmem⟩, ?_, ?_⟩
  · refine mem_iUnion.mpr ⟨QuotientAddGroup.mk (-g₁), ?_⟩
    change -(((QuotientAddGroup.mk (-g₁) : Λ₁ ⧸ Λ₂.addSubgroupOf Λ₁).out : Λ₁) : E)
      + (((h : Λ₁) : E) + x) ∈ D₁
    rw [hh]
    have : -((-g₁ + (h : Λ₁) : Λ₁) : E) + (((h : Λ₁) : E) + x) = (g₁ : E) + x := by
      push_cast; abel
    rw [this]; exact hg₁
  · intro g' hg'
    obtain ⟨q', hq'⟩ := mem_iUnion.mp hg'
    change -((q'.out : Λ₁) : E) + ((g' : E) + x) ∈ D₁ at hq'
    set g'₁ : Λ₁ := ⟨(g' : E), hle g'.2⟩ with hg'₁
    have he : -(q'.out : Λ₁) + g'₁ = g₁ := huniq _ (by
      have : ((-(q'.out : Λ₁) + g'₁ : Λ₁) : E) + x = -((q'.out : Λ₁) : E) + ((g' : E) + x) := by
        push_cast; rw [hg'₁]; abel
      change ((-(q'.out : Λ₁) + g'₁ : Λ₁) : E) + x ∈ D₁
      rw [this]; exact hq')
    have hout : (q'.out : Λ₁) = -g₁ + g'₁ := by
      rw [← he]; abel
    have hmem' : g'₁ ∈ Λ₂.addSubgroupOf Λ₁ := AddSubgroup.mem_addSubgroupOf.mpr g'.2
    have hq : q' = QuotientAddGroup.mk (-g₁) := by
      rw [← QuotientAddGroup.out_eq' q', hout]
      exact QuotientAddGroup.mk_add_of_mem _ hmem'
    have h3 : g'₁ = (h : Λ₁) := by
      have h4 : (q'.out : Λ₁) = -g₁ + (h : Λ₁) := by rw [hq]; exact hh
      have := hout.symm.trans h4
      exact add_left_cancel this
    exact Subtype.ext (congrArg (fun z : Λ₁ => (z : E)) h3)

/-- **Means over fundamental domains of a group and of a subgroup agree.** -/
theorem avg_eq_of_le {Λ₁ Λ₂ : AddSubgroup E} [Countable Λ₁] (hle : Λ₂ ≤ Λ₁) {D₁ D₂ : Set E}
    (hD₁ : MeasurableSet D₁) (h₁ : ∀ x, ∃! g : Λ₁, (g : E) + x ∈ D₁)
    (h₂ : IsAddFundamentalDomain Λ₂ D₂ μ) (hfin : μ D₂ ≠ ⊤) (h0 : μ D₁ ≠ 0)
    {f : E → ℂ} (hf : ∀ (g : Λ₁) (x : E), f ((g : E) + x) = f x) (hint : IntegrableOn f D₁ μ) :
    (((μ D₂).toReal : ℝ) : ℂ)⁻¹ * ∫ x in D₂, f x ∂μ
      = (((μ D₁).toReal : ℝ) : ℂ)⁻¹ * ∫ x in D₁, f x ∂μ := by
  classical
  have : Countable Λ₂ := (AddSubgroup.inclusion_injective hle).countable
  have : Countable (Λ₁ ⧸ Λ₂.addSubgroupOf Λ₁) := QuotientAddGroup.mk_surjective.countable
  set s : Λ₁ ⧸ Λ₂.addSubgroupOf Λ₁ → Set E := fun q => (fun x => -((q.out : Λ₁) : E) + x) ⁻¹' D₁
    with hs
  have hsm : ∀ q, MeasurableSet (s q) := fun q => (measurable_const_add _) hD₁
  have hdisj : Pairwise (Function.onFun Disjoint s) := by
    intro q q' hne
    refine Set.disjoint_left.mpr fun x hx hx' => hne ?_
    have e1 : ((-(q.out : Λ₁) : Λ₁) : E) + x ∈ D₁ := by push_cast; exact hx
    have e2 : ((-(q'.out : Λ₁) : Λ₁) : E) + x ∈ D₁ := by push_cast; exact hx'
    have := (h₁ x).unique e1 e2
    have h3 : (q.out : Λ₁) = q'.out := neg_injective this
    rw [← QuotientAddGroup.out_eq' q, h3, QuotientAddGroup.out_eq']
  have hU : IsAddFundamentalDomain Λ₂ (unionDom Λ₁ Λ₂ D₁) μ :=
    IsAddFundamentalDomain.mk' (MeasurableSet.iUnion hsm).nullMeasurableSet
      (existsUnique_unionDom hle h₁)
  have hpiece : ∀ q, μ (s q) = μ D₁ := fun q => measure_preimage_add μ _ D₁
  have hμ : μ D₂ = ∑' _ : Λ₁ ⧸ Λ₂.addSubgroupOf Λ₁, μ D₁ := by
    rw [h₂.measure_eq hU]
    change μ (⋃ q, s q) = _
    rw [measure_iUnion hdisj hsm]
    exact tsum_congr hpiece
  have : Finite (Λ₁ ⧸ Λ₂.addSubgroupOf Λ₁) := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    rw [ENNReal.tsum_const_eq_top_of_ne_zero h0] at hμ
    exact hfin hμ
  have : Fintype (Λ₁ ⧸ Λ₂.addSubgroupOf Λ₁) := Fintype.ofFinite _
  set k : ℕ := Fintype.card (Λ₁ ⧸ Λ₂.addSubgroupOf Λ₁) with hk
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hμ' : μ D₂ = k * μ D₁ := by
    rw [hμ, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hf' : ∀ (g : Λ₂) (x : E), f (g +ᵥ x) = f x := fun g x => hf ⟨(g : E), hle g.2⟩ x
  have hints : ∀ q, IntegrableOn f (s q) μ := fun q => by
    have h1 := ((measurePreserving_add_left μ (-((q.out : Λ₁) : E))).integrableOn_comp_preimage
      (MeasurableEquiv.addLeft _).measurableEmbedding (f := f) (s := D₁)).mpr hint
    refine h1.congr_fun (fun x _ => ?_) (hsm q)
    exact hf (-(q.out : Λ₁)) x
  have hintq : ∀ q, ∫ x in s q, f x ∂μ = ∫ x in D₁, f x ∂μ := fun q => by
    have h1 := (measurePreserving_add_left μ (-((q.out : Λ₁) : E))).setIntegral_preimage_emb
      (MeasurableEquiv.addLeft _).measurableEmbedding f D₁
    rw [← h1]
    refine setIntegral_congr_fun (hsm q) fun x _ => ?_
    exact (hf (-(q.out : Λ₁)) x).symm
  have hI : ∫ x in D₂, f x ∂μ = k * ∫ x in D₁, f x ∂μ := by
    rw [h₂.setIntegral_eq hU hf']
    change ∫ x in ⋃ q, s q, f x ∂μ = _
    rw [integral_iUnion_fintype hsm hdisj hints, Finset.sum_congr rfl fun q _ => hintq q,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hD₁top : μ D₁ ≠ ⊤ := fun h => by
    rw [h, ENNReal.mul_top (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)] at hμ'
    exact hfin hμ'
  have hv : (((μ D₁).toReal : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr ⟨h0, hD₁top⟩)
  rw [hI, hμ', ENNReal.toReal_mul, ENNReal.toReal_natCast]
  push_cast
  field_simp

end abstract

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ}

/-! ### Strict cells -/

/-- The `hfund` form of WP-X2 in terms of the lattice `latN Γ`. -/
lemma strict_of_hfund {Γ : Subgroup (SL(2, 𝓞 F))} {D : Set (InfinitePlace F → ℂ)}
    (hfund : ∀ x : InfinitePlace F → ℂ, ∃! γ : GammaN Γ, (fun w => x w + GammaN.shift γ w) ∈ D)
    (x : InfinitePlace F → ℂ) : ∃! g : latN Γ, (g : InfinitePlace F → ℂ) + x ∈ D := by
  obtain ⟨γ, hγ, huniq⟩ := hfund x
  have key : ∀ γ' : GammaN Γ, (fun w => x w + GammaN.shift γ' w)
      = (GammaN.shift γ' : InfinitePlace F → ℂ) + x := fun γ' => by
    funext w; simp [add_comm]
  refine ⟨⟨GammaN.shift γ, shift_mem_latN γ⟩, ?_, fun g hg => ?_⟩
  · change (GammaN.shift γ : InfinitePlace F → ℂ) + x ∈ D
    rw [← key]; exact hγ
  · obtain ⟨β, hβ, hgβ⟩ := g.2
    have h1 : (fun w => x w + GammaN.shift (ofLam ⟨β, hβ⟩) w) ∈ D := by
      rw [key, shift_ofLam, hgβ]; exact hg
    have h2 := huniq _ h1
    refine Subtype.ext ?_
    change (g : InfinitePlace F → ℂ) = GammaN.shift γ
    rw [← h2, shift_ofLam, hgβ]

lemma latN_mono {Γ' Γ : Subgroup (SL(2, 𝓞 F))} (h : Γ' ≤ Γ) : latN Γ' ≤ latN Γ :=
  AddSubgroup.map_mono fun _ hβ => h hβ

/-! ### Periodicity of the tail -/

lemma mk_add_latN {Γ : Subgroup (SL(2, 𝓞 F))} (g : latN Γ) (x : InfinitePlace F → ℂ)
    {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w) :
    ∃ γ : Γ, X.mk ((g : InfinitePlace F → ℂ) + x) v hv = γ • X.mk x v hv ∧
      ((γ : SL(2, 𝓞 F)) 1 0 = 0) := by
  obtain ⟨β, hβ, hgβ⟩ := g.2
  refine ⟨((ofLam ⟨β, hβ⟩ : GammaN Γ) : Γ), ?_, (ofLam ⟨β, hβ⟩ : GammaN Γ).2.1⟩
  have h1 := GammaN.smul_eq (ofLam ⟨β, hβ⟩ : GammaN Γ) (X.mk x v hv)
  change ((ofLam ⟨β, hβ⟩ : GammaN Γ) : Γ) • X.mk x v hv = _ at h1
  rw [h1, shift_ofLam]
  refine X.ext' ?_ rfl
  change (g : InfinitePlace F → ℂ) + x = fun w => x w + embO β w
  rw [← hgβ]
  funext w
  simp [add_comm]

lemma tail_periodic (h𝔪 : 𝔪 ≠ ⊥) {Γ : Subgroup (SL(2, 𝓞 F))} {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ)
    (s : ℂ) {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w) (g : latN Γ)
    (x : InfinitePlace F → ℂ) :
    tail Ψ s (X.mk ((g : InfinitePlace F → ℂ) + x) v hv) = tail Ψ s (X.mk x v hv) := by
  obtain ⟨γ, hγ, hup⟩ := mk_add_latN g x hv
  have h1 : eis Ψ s (γ • X.mk x v hv) = eis Ψ s (X.mk x v hv) := isInv_eis h𝔪 hΓ s γ _
  have h2 : X.ht (γ • X.mk x v hv) = X.ht (X.mk x v hv) := ht_smul_of_upper hup _
  unfold tail
  rw [hγ, h1, h2]

/-! ### Independence of `mD` -/

/-- Comparison with a strict cell of a larger group. -/
theorem mD_eq_of_le_oai (h𝔪 : 𝔪 ≠ ⊥) {Γ Γ' : Subgroup (SL(2, 𝓞 F))} [Γ.FiniteIndex]
    {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) (hle : Γ' ≤ Γ) {s : ℂ} (hs : 2 < s.re)
    {D D' : Set (InfinitePlace F → ℂ)} {n n' : ℕ} (hD : MeasurableSet D)
    (hfund : ∀ x : InfinitePlace F → ℂ, ∃! γ : GammaN Γ, (fun w => x w + GammaN.shift γ w) ∈ D)
    (hcell : Cell Γ D n) (hD' : Cell Γ' D' n') : mD D' Ψ s = mD D Ψ s := by
  unfold mD
  exact avg_eq_of_le (latN_mono hle) hD (strict_of_hfund hfund) hD'.fund hD'.vol_ne_top
    hcell.vol_ne_zero (fun g x => tail_periodic h𝔪 hΓ s _ g x)
    (integrableOn_tail h𝔪 hΓ hs _ hcell.fund hcell.vol_ne_top)

/-! ### Independence of `zRes` -/

end

end ArtinKP.N2
end

theorem solution.{u_1} : type_of% @ArtinKP.N2.mD_eq_of_le_oai.{u_1} := @ArtinKP.N2.mD_eq_of_le_oai.{u_1}
