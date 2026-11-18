-- Prove2me | solution 1 for ArtinKP.C5.l2Rep_src
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:42:21.559878+00:00
-- url     : https://prove2.me/submissions/c5094d43-774c-4099-8cd3-7c1b25d63079

import Mathlib
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
import Definitions.Def_ArtinKPB015
import Theorems.Thm_ArtinKP_X_X_l2Rep_of_mem_core
import Theorems.Thm_ArtinKP_X_X_summable_comp_smul_of_hasCompactSupport

section
-- module Solutions.Artin.KP.X_H3
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulGinfX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatComplexH3 _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulGinfX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatComplexH3 _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatXVol _root_.ArtinKP.X.instSigmaFiniteH3Vol _root_.ArtinKP.X.instSigmaFiniteXVol
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

lemma coe_eq (P : H3) : P.coe = (P.x, P.v) := rfl

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
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol
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
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
attribute [-simp] _root_.ArtinKP.X.chart1_symm_fst _root_.ArtinKP.X.chart1_symm_snd _root_.ArtinKP.X.chart1_v _root_.ArtinKP.X.chart1_x _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
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
attribute [-instance] _root_.ArtinKP.B1.instDiscreteTopologySubtypeE₂MemSubmoduleIntPairLattice _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instDiscreteTopologySubtypeMixedSpaceMemSubmoduleIntLattice _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
attribute [-simp] _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
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

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.B1_Lattice
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
attribute [-simp] _root_.ArtinKP.B.coe_latREquiv _root_.ArtinKP.B.embR_apply _root_.ArtinKP.X.chart1_symm_fst _root_.ArtinKP.X.chart1_symm_snd _root_.ArtinKP.X.chart1_v _root_.ArtinKP.X.chart1_x _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
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

theorem instIsAddHaarMeasureE₂Volume : (volume : Measure (E₂ F)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure volume volume

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

lemma mkSet_symm (P : X F) (lam : ℝ) : ∀ z ∈ mkSet P lam, -z ∈ mkSet P lam := by
  intro z hz w
  obtain ⟨h1, h2⟩ := hz w
  refine ⟨by simpa using h1, ?_⟩
  have : (-z).1 w * P.x w + (-z).2 w = -(z.1 w * P.x w + z.2 w) := by simp; ring
  rw [this, norm_neg]; exact h2

lemma mkSet_convex (P : X F) (lam : ℝ) : Convex ℝ (mkSet P lam) := by
  intro z hz z' hz' a b ha hb hab w
  obtain ⟨h1, h2⟩ := hz w
  obtain ⟨h1', h2'⟩ := hz' w
  constructor
  · calc ‖(a • z + b • z').1 w‖ = ‖a • z.1 w + b • z'.1 w‖ := rfl
      _ ≤ ‖a • z.1 w‖ + ‖b • z'.1 w‖ := norm_add_le _ _
      _ = a * ‖z.1 w‖ + b * ‖z'.1 w‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * (lam / √(P.v w)) + b * (lam / √(P.v w)) := by gcongr
      _ = lam / √(P.v w) := by rw [← add_mul, hab, one_mul]
  · have e : (a • z + b • z').1 w * P.x w + (a • z + b • z').2 w =
        a • (z.1 w * P.x w + z.2 w) + b • (z'.1 w * P.x w + z'.2 w) := by
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
        Pi.smul_apply, Complex.real_smul]
      ring
    calc _ = ‖a • (z.1 w * P.x w + z.2 w) + b • (z'.1 w * P.x w + z'.2 w)‖ := by rw [e]
      _ ≤ ‖a • (z.1 w * P.x w + z.2 w)‖ + ‖b • (z'.1 w * P.x w + z'.2 w)‖ := norm_add_le _ _
      _ = a * ‖z.1 w * P.x w + z.2 w‖ + b * ‖z'.1 w * P.x w + z'.2 w‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * (lam * √(P.v w)) + b * (lam * √(P.v w)) := by gcongr
      _ = lam * √(P.v w) := by rw [← add_mul, hab, one_mul]

/-- The shear `(c, d) ↦ (c, d + c x)` preserves Lebesgue measure. -/
lemma measurePreserving_shear (x : InfinitePlace F → ℂ) :
    MeasurePreserving (fun z : E₂ F => (z.1, z.2 + z.1 * x))
      (volume : Measure (E₂ F)) volume := by
  have := MeasurePreserving.skew_product (μa := (volume : Measure (InfinitePlace F → ℂ)))
    (μb := volume) (μc := (volume : Measure (InfinitePlace F → ℂ))) (μd := volume)
    (f := id) (MeasurePreserving.id _)
    (g := fun (c d : InfinitePlace F → ℂ) => d + c * x)
    (by
      have : Measurable fun p : (InfinitePlace F → ℂ) × (InfinitePlace F → ℂ) => p.2 + p.1 * x :=
        measurable_snd.add (measurable_fst.mul measurable_const)
      exact this)
    (Filter.Eventually.of_forall fun c => map_add_right_eq_self volume (c * x))
  exact this

lemma volume_mkSet (P : X F) {lam : ℝ} (hlam : 0 ≤ lam) :
    ENNReal.ofReal (lam ^ 4) ^ Fintype.card (InfinitePlace F) ≤ volume (mkSet P lam) := by
  set A : Set (InfinitePlace F → ℂ) :=
    Set.pi univ fun w => Metric.closedBall (0 : ℂ) (lam / √(P.v w)) with hA
  set B : Set (InfinitePlace F → ℂ) :=
    Set.pi univ fun w => Metric.closedBall (0 : ℂ) (lam * √(P.v w)) with hB
  have hAm : MeasurableSet A := MeasurableSet.univ_pi fun w => Metric.isClosed_closedBall.measurableSet
  have hBm : MeasurableSet B := MeasurableSet.univ_pi fun w => Metric.isClosed_closedBall.measurableSet
  have hset : mkSet P lam = (fun z : E₂ F => (z.1, z.2 + z.1 * P.x)) ⁻¹' (A ×ˢ B) := by
    ext z
    simp only [mkSet, mem_setOf_eq, mem_preimage, mem_prod, hA, hB, mem_pi, mem_univ,
      forall_true_left, mem_closedBall_zero_iff, Pi.add_apply, Pi.mul_apply, ← forall_and]
    refine forall_congr' fun w => ?_
    rw [add_comm (z.2 w)]
  rw [hset, (measurePreserving_shear P.x).measure_preimage (hAm.prod hBm).nullMeasurableSet]
  rw [Measure.volume_eq_prod, Measure.prod_prod, volume_pi, hA, hB, Measure.pi_pi, Measure.pi_pi,
    ← Finset.prod_mul_distrib, ← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_le_prod' fun w _ => ?_
  rw [Complex.volume_closedBall, Complex.volume_closedBall]
  have hv := P.v_pos w
  have hs : 0 < √(P.v w) := Real.sqrt_pos.mpr hv
  have e : lam ^ 4 = (lam / √(P.v w)) ^ 2 * (lam * √(P.v w)) ^ 2 := by field_simp
  rw [e, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_pow (by positivity)]
  have hpi : (1 : ℝ≥0∞) ≤ (NNReal.pi : ℝ≥0∞) :=
    ENNReal.one_le_coe_iff.mpr (by
      rw [← NNReal.coe_le_coe]; simpa using (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi))
  calc ENNReal.ofReal (lam / √(P.v w)) ^ 2 * ENNReal.ofReal (lam * √(P.v w)) ^ 2
      = (ENNReal.ofReal (lam / √(P.v w)) ^ 2 * 1) * (ENNReal.ofReal (lam * √(P.v w)) ^ 2 * 1) := by
        simp
    _ ≤ _ := by gcongr

/-- **Lemma M (Minkowski), integral form.** There is `c₀ > 0` such that for every `P ∈ X` there
is a nonzero pair `(c, d) ∈ 𝓞_F²` with `I_{(c,d)}(P) ≥ c₀`. -/
theorem exists_integer_pair_pairHt_ge :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ P : X F, ∃ c d : 𝓞 F, (c ≠ 0 ∨ d ≠ 0) ∧
      c₀ ≤ X.pairHt (c : F) (d : F) P := by
  haveI _iHE := ArtinKP.B1.instIsAddHaarMeasureE₂Volume (F := F)
  classical
  have hfund : IsAddFundamentalDomain (pairLattice F).toAddSubgroup
      (ZSpan.fundamentalDomain (pairBasis (F := F))) volume :=
    ZSpan.isAddFundamentalDomain' (pairBasis (F := F)) volume
  have hfin : volume (ZSpan.fundamentalDomain (pairBasis (F := F))) < ⊤ :=
    (ZSpan.fundamentalDomain_isBounded (pairBasis (F := F))).measure_lt_top

  obtain ⟨m, hm⟩ : ∃ m : ℝ≥0∞, m = volume (ZSpan.fundamentalDomain (pairBasis (F := F))) *
      2 ^ finrank ℝ (E₂ F) := ⟨_, rfl⟩
  have hmtop : m ≠ ⊤ := by
    rw [hm]; exact ENNReal.mul_ne_top hfin.ne (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = max 1 (m.toReal + 1) := ⟨_, rfl⟩
  have hlam1 : 1 ≤ lam := hlam ▸ le_max_left _ _
  have hlam2 : m.toReal + 1 ≤ lam := hlam ▸ le_max_right _ _
  refine ⟨(1 / (2 * lam ^ 2)) ^ Fintype.card (InfinitePlace F), by positivity, fun P => ?_⟩
  have hvol : m < volume (mkSet P lam) := by
    refine lt_of_lt_of_le ?_ (volume_mkSet P (by linarith))
    have h4 : m.toReal < lam ^ 4 := by
      have : lam ≤ lam ^ 4 := le_self_pow₀ hlam1 (by norm_num)
      linarith
    have h5 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (lam ^ 4) := by
      rw [ENNReal.one_le_ofReal]; exact one_le_pow₀ hlam1
    calc m < ENNReal.ofReal (lam ^ 4) := (ENNReal.lt_ofReal_iff_toReal_lt hmtop).mpr h4
      _ ≤ _ := le_self_pow₀ h5 Fintype.card_ne_zero
  haveI : Countable (pairLattice F).toAddSubgroup := inferInstanceAs (Countable (pairLattice F))
  obtain ⟨x, hx0, hxs⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure hfund
    (mkSet_symm P lam) (mkSet_convex P lam) (hm ▸ hvol)
  obtain ⟨c, d, hcd⟩ := mem_pairLattice.mp x.2
  have hne : c ≠ 0 ∨ d ≠ 0 := by
    by_contra h
    push Not at h
    apply hx0
    apply Subtype.ext
    rw [hcd, h.1, h.2]
    refine Prod.ext ?_ ?_ <;> simp
  refine ⟨c, d, hne, ?_⟩
  rw [X.pairHt_eq_prod, ← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_le_prod (fun _ _ => by positivity) fun w _ => ?_
  have hw := hxs w
  rw [hcd] at hw
  obtain ⟨h1, h2⟩ := hw
  simp only [emb_apply] at h1 h2
  have hv := P.v_pos w
  have hs2 : √(P.v w) ^ 2 = P.v w := Real.sq_sqrt hv.le
  have hs : 0 < √(P.v w) := Real.sqrt_pos.mpr hv
  have hD := H3.rowDen_pos (c := w.embedding (c : F)) (d := w.embedding (d : F))
    (hne.imp (fun h => by simpa using h) (fun h => by simpa using h)) (P w)
  have hle : H3.rowDen (w.embedding (c : F)) (w.embedding (d : F)) (P w) ≤ 2 * lam ^ 2 * P.v w := by
    unfold H3.rowDen
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    have a1 : ‖w.embedding (c : F) * P.x w + w.embedding (d : F)‖ ^ 2 ≤ (lam * √(P.v w)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h2 2
    have a2 : ‖w.embedding (c : F)‖ ^ 2 ≤ (lam / √(P.v w)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have a3 : (lam / √(P.v w)) ^ 2 * (P.v w) ^ 2 = lam ^ 2 * P.v w := by
      rw [div_pow, hs2]; field_simp
    have a4 : (lam * √(P.v w)) ^ 2 = lam ^ 2 * P.v w := by rw [mul_pow, hs2]
    have a5 : ‖w.embedding (c : F)‖ ^ 2 * (P.v w) ^ 2 ≤ (lam / √(P.v w)) ^ 2 * (P.v w) ^ 2 :=
      mul_le_mul_of_nonneg_right a2 (by positivity)
    change ‖w.embedding (c : F) * P.x w + w.embedding (d : F)‖ ^ 2 +
      ‖w.embedding (c : F)‖ ^ 2 * (P.v w) ^ 2 ≤ _
    linarith
  change 1 / (2 * lam ^ 2) ≤ P.v w / _
  rw [div_le_div_iff₀ (by positivity) hD]
  linarith

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.X_Disjoint
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol
attribute [-simp] _root_.ArtinKP.X.chart1_symm_snd _root_.ArtinKP.X.chart1_v _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
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

lemma finprod_le_prod_of_le_one {α : Type*} (f : α → ℝ) (hf : f.HasFiniteMulSupport)
    (hpos : ∀ a, 0 ≤ f a) (S : Finset α) (hS : ∀ a ∉ S, f a ≤ 1) :
    ∏ᶠ a, f a ≤ ∏ a ∈ S, f a := by
  classical
  have hsub : S ⊆ S ∪ hf.toFinset := Finset.subset_union_left
  rw [finprod_eq_prod_of_mulSupport_toFinset_subset f hf (Finset.subset_union_right (s₁ := S)),
    ← Finset.prod_sdiff hsub]
  have h1 : ∏ a ∈ (S ∪ hf.toFinset) \ S, f a ≤ 1 :=
    Finset.prod_le_one (fun a _ => hpos a) (fun a ha => hS a (Finset.mem_sdiff.mp ha).2)
  have h2 : 0 ≤ ∏ a ∈ S, f a := Finset.prod_nonneg fun a _ => hpos a
  nlinarith

lemma sNorm_pos (S : Finset (FinitePlace F)) {c d : F} (h : c ≠ 0 ∨ d ≠ 0) : 0 < sNorm S c d :=
  Finset.prod_pos fun v _ => by
    rcases h with h | h
    · exact lt_max_of_lt_left (FinitePlace.pos_iff.mpr h)
    · exact lt_max_of_lt_right (FinitePlace.pos_iff.mpr h)

lemma sHt_pos (S : Finset (FinitePlace F)) {c d : F} (h : c ≠ 0 ∨ d ≠ 0) (P : X F) :
    0 < sHt S c d P := div_pos (pairHt_pos h P) (sNorm_pos S h)

lemma finitePlace_sub_le (v : FinitePlace F) (x y : F) : v (x - y) ≤ max (v x) (v y) := by
  have h := FinitePlace.add_le v x (-y)
  have h2 : v (-y) = v y := v.1.map_neg y
  rwa [← sub_eq_add_neg, h2] at h

lemma finitePlace_det_le (v : FinitePlace F) (c d c' d' : F) :
    v (c * d' - c' * d) ≤ max (v c) (v d) * max (v c') (v d') := by
  refine (finitePlace_sub_le v _ _).trans (max_le ?_ ?_)
  · rw [map_mul]
    exact mul_le_mul (le_max_left _ _) (le_max_right _ _) (apply_nonneg v _)
      (le_max_of_le_left (apply_nonneg v _))
  · rw [map_mul, mul_comm]
    exact mul_le_mul (le_max_right _ _) (le_max_left _ _) (apply_nonneg v _)
      (le_max_of_le_left (apply_nonneg v _))

/-- **Product of two `S`-normalized heights is at most one** when `Δ = c d' - c' d` is a nonzero
`S`-integer (product formula). -/
theorem sHt_mul_sHt_le_one [IsTotallyComplex F] (S : Finset (FinitePlace F)) {c d c' d' : F}
    (hΔ : c * d' - c' * d ≠ 0) (hint : ∀ v : FinitePlace F, v ∉ S → v (c * d' - c' * d) ≤ 1)
    (P : X F) : sHt S c d P * sHt S c' d' P ≤ 1 := by
  have h1 : c ≠ 0 ∨ d ≠ 0 := by
    by_contra h; push Not at h; exact hΔ (by rw [h.1, h.2]; ring)
  have h2 : c' ≠ 0 ∨ d' ≠ 0 := by
    by_contra h; push Not at h; exact hΔ (by rw [h.1, h.2]; ring)
  have hN := sNorm_pos S h1
  have hN' := sNorm_pos S h2
  have hI := pairHt_mul_pairHt_le hΔ P
  rw [← finprod_finitePlace hΔ] at hI
  have hfin := finprod_le_prod_of_le_one (fun v : FinitePlace F => v (c * d' - c' * d))
    (FinitePlace.hasFiniteMulSupport hΔ) (fun v => apply_nonneg v _) S hint
  have hS : ∏ v ∈ S, v (c * d' - c' * d) ≤ sNorm S c d * sNorm S c' d' := by
    unfold sNorm
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun v _ => apply_nonneg v _)
      (fun v _ => finitePlace_det_le v c d c' d')
  unfold sHt
  rw [div_mul_div_comm, div_le_one (mul_pos hN hN')]
  exact hI.trans (hfin.trans hS)

/-- **Disjointness of cusp neighbourhoods.** If two pairs with `S`-integral entries both have
`S`-normalized height `> 1` at the same point, they are proportional. Hence at each point at most
one pair class contributes to a pseudo-Eisenstein series supported in `{ht^S > 1}`. -/
theorem proportional_of_one_lt_sHt [IsTotallyComplex F] (S : Finset (FinitePlace F))
    {c d c' d' : F}
    (hc : ∀ v : FinitePlace F, v ∉ S → v c ≤ 1) (hd : ∀ v : FinitePlace F, v ∉ S → v d ≤ 1)
    (hc' : ∀ v : FinitePlace F, v ∉ S → v c' ≤ 1) (hd' : ∀ v : FinitePlace F, v ∉ S → v d' ≤ 1)
    (h0 : c ≠ 0 ∨ d ≠ 0) (h0' : c' ≠ 0 ∨ d' ≠ 0)
    {P : X F} (h : 1 < sHt S c d P) (h' : 1 < sHt S c' d' P) : c * d' - c' * d = 0 := by
  by_contra hΔ
  have hint : ∀ v : FinitePlace F, v ∉ S → v (c * d' - c' * d) ≤ 1 := by
    intro v hv
    refine (finitePlace_det_le v c d c' d').trans ?_
    have a1 : max (v c) (v d) ≤ 1 := max_le (hc v hv) (hd v hv)
    have a2 : max (v c') (v d') ≤ 1 := max_le (hc' v hv) (hd' v hv)
    have a3 : 0 ≤ max (v c) (v d) := le_max_of_le_left (apply_nonneg v _)
    have a4 : 0 ≤ max (v c') (v d') := le_max_of_le_left (apply_nonneg v _)
    nlinarith
  have := sHt_mul_sHt_le_one S hΔ hint P
  have hp := sHt_pos S h0 P
  nlinarith

end X

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.B1_Conv
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instDiscreteTopologySubtypeMixedSpaceMemSubmoduleIntLattice _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
attribute [-simp] _root_.ArtinKP.B.coe_latREquiv _root_.ArtinKP.B.embR_apply _root_.ArtinKP.X.chart1_symm_fst _root_.ArtinKP.X.chart1_symm_snd _root_.ArtinKP.X.chart1_v _root_.ArtinKP.X.chart1_x _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
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
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
attribute [-simp] _root_.ArtinKP.RO.rowClassEquiv_mk _root_.ArtinKP.RO.rowPair_c _root_.ArtinKP.RO.rowPair_d _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
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

lemma ht_mk (q : SPair S) (P : X F) : ht (⟦q⟧ : PairClass S) P = X.sHt S q.c q.d P := rfl

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

/-- Two classes with height `> 1` at the same point are equal (H1). -/
theorem eq_of_one_lt_ht {p p' : PairClass S} {P : X F} (h : 1 < p.ht P) (h' : 1 < p'.ht P) :
    p = p' := by
  induction p using Quotient.inductionOn with
  | _ q =>
  induction p' using Quotient.inductionOn with
  | _ q' =>
    rw [ht_mk] at h h'
    have hΔ := X.proportional_of_one_lt_sHt S q.hc q.hd q'.hc q'.hd q.ne_zero q'.ne_zero h h'
    obtain ⟨a, b, ha, hb, hab⟩ := q.prim
    obtain ⟨a', b', ha', hb', hab'⟩ := q'.prim
    -- `u = a c' + b d'` satisfies `u (c, d) = (c', d')`, and `u' = a' c + b' d` is its inverse
    have e1 : q'.c = (a * q'.c + b * q'.d) * q.c := by linear_combination (-q'.c) * hab - b * hΔ
    have e2 : q'.d = (a * q'.c + b * q'.d) * q.d := by linear_combination (-q'.d) * hab + a * hΔ
    refine Quotient.sound ⟨a * q'.c + b * q'.d, ⟨?_, ?_⟩, e1, e2⟩
    · intro h0
      rw [h0, zero_mul] at e1 e2
      rcases q'.ne_zero with h | h
      · exact h e1
      · exact h e2
    · intro v hv
      have hu : IsSInt S (a * q'.c + b * q'.d) := (ha.mul q'.hc).add (hb.mul q'.hd)
      have hu' : IsSInt S (a' * q.c + b' * q.d) := (ha'.mul q.hc).add (hb'.mul q.hd)
      have hprod : (a * q'.c + b * q'.d) * (a' * q.c + b' * q.d) = 1 := by
        linear_combination (-a') * e1 - b' * e2 + hab'
      have h1 := hu v hv
      have h2 := hu' v hv
      have h3 : v (a * q'.c + b * q'.d) * v (a' * q.c + b' * q.d) = 1 := by
        rw [← map_mul, hprod, map_one]
      have h4 : 0 ≤ v (a * q'.c + b * q'.d) := apply_nonneg v _
      nlinarith

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

/-- The supremum of the heights at a point is attained. -/
theorem exists_max_ht (S : Finset (FinitePlace F)) (P : X F) :
    ∃ p₀ : PairClass S, ∀ p : PairClass S, p.ht P ≤ p₀.ht P := by
  have hsum := summable_ht_rpow S P (σ := 3) (by norm_num)
  have h0 := ht_pos (inf S) P
  have hfin : {p : PairClass S | (inf S).ht P ^ (3 : ℝ) ≤ p.ht P ^ (3 : ℝ)}.Finite := by
    have := hsum.tendsto_cofinite_zero.eventually
      (gt_mem_nhds (Real.rpow_pos_of_pos h0 (3 : ℝ)))
    rw [Filter.eventually_cofinite] at this
    refine this.subset fun p hp => ?_
    simpa using hp
  obtain ⟨p₀, hp₀, hmax⟩ := hfin.exists_maximalFor (fun p : PairClass S => p.ht P) _
    ⟨inf S, show (inf S).ht P ^ (3 : ℝ) ≤ (inf S).ht P ^ (3 : ℝ) from le_refl _⟩
  refine ⟨p₀, fun p => ?_⟩
  by_cases hp : (inf S).ht P ^ (3 : ℝ) ≤ p.ht P ^ (3 : ℝ)
  · by_contra hlt
    push Not at hlt
    exact absurd (hmax hp hlt.le) (not_le.mpr hlt)
  · push Not at hp
    have h1 : p.ht P ≤ (inf S).ht P := by
      by_contra hlt
      push Not at hlt
      exact absurd (Real.rpow_le_rpow h0.le hlt.le (by norm_num)) (not_le.mpr hp)
    have h2 : (inf S).ht P ≤ p₀.ht P := by
      by_contra hlt
      push Not at hlt
      exact absurd hp₀ (not_le.mpr (Real.rpow_lt_rpow (ht_pos p₀ P).le hlt (by norm_num)))
    exact h1.trans h2

end PairClass

/-! ### Lemma M for pair classes -/

/-- Scaling a pair by a nonzero `S`-integer does not increase the `S`-normalized height
(`N^{ext}(t) ≥ 1`). -/
lemma sHt_smul_le (S : Finset (FinitePlace F)) {t : F} (ht0 : t ≠ 0) (ht : IsSInt S t) {c d : F}
    (hne : c ≠ 0 ∨ d ≠ 0) (P : X F) : X.sHt S (t * c) (t * d) P ≤ X.sHt S c d P := by
  have hN : 0 < ∏ w : InfinitePlace F, Complex.normSq (w.embedding t) :=
    Finset.prod_pos fun w _ => Complex.normSq_pos.mpr ((map_ne_zero _).mpr ht0)
  have h1 := X.finprod_le_prod_of_le_one (fun v : FinitePlace F => v t)
    (FinitePlace.hasFiniteMulSupport ht0) (fun v => apply_nonneg v _) S ht
  rw [X.finprod_finitePlace ht0] at h1
  have hsn : X.sNorm S (t * c) (t * d) = (∏ v ∈ S, v t) * X.sNorm S c d := by
    unfold X.sNorm
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [map_mul, map_mul, mul_max_of_nonneg _ _ (apply_nonneg v t)]
  have hS0 : 0 < ∏ v ∈ S, v t := Finset.prod_pos fun v _ => FinitePlace.pos_iff.mpr ht0
  have h2 : 1 ≤ (∏ w : InfinitePlace F, Complex.normSq (w.embedding t)) * ∏ v ∈ S, v t := by
    calc (1 : ℝ) = (∏ w : InfinitePlace F, Complex.normSq (w.embedding t)) *
          (∏ w : InfinitePlace F, Complex.normSq (w.embedding t))⁻¹ := (mul_inv_cancel₀ hN.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 hN.le
  have hs := X.sNorm_pos S hne
  have hp := X.pairHt_pos hne P
  unfold X.sHt
  rw [X.pairHt_smul_pair, hsn, div_div, div_le_div_iff₀ (by positivity) hs]
  nlinarith [mul_pos hp hs]

/-- **Lemma M (Minkowski lower bound for the top height).** If `R` is Bezout, there is `c₀ > 0`
with `sup_p ht_p(P) ≥ c₀` for every `P ∈ X`. -/
theorem PairClass.exists_ht_ge (hB : SBezout S) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ P : X F, ∃ p : PairClass S, c₀ ≤ p.ht P := by
  obtain ⟨c₀, hc₀, hM⟩ := exists_integer_pair_pairHt_ge (F := F)
  refine ⟨c₀, hc₀, fun P => ?_⟩
  obtain ⟨c, d, hne, hle⟩ := hM P
  have hne' : (c : F) ≠ 0 ∨ (d : F) ≠ 0 :=
    hne.imp (fun h => by simpa using h) (fun h => by simpa using h)
  obtain ⟨t, ht, p, hc, hd⟩ := hB c d (isSInt_int c) (isSInt_int d) hne'
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hc hd
    rcases hne' with h | h
    · exact h hc
    · exact h hd
  refine ⟨⟦p⟧, ?_⟩
  have h1 : X.sHt S (c : F) (d : F) P ≤ X.sHt S p.c p.d P := by
    rw [hc, hd]; exact sHt_smul_le S ht0 ht p.ne_zero P
  have h2 : X.pairHt (c : F) (d : F) P ≤ X.sHt S (c : F) (d : F) P := by
    unfold X.sHt
    rw [le_div_iff₀ (X.sNorm_pos S hne')]
    have hs1 : X.sNorm S (c : F) (d : F) ≤ 1 :=
      Finset.prod_le_one (fun v _ => le_max_of_le_left (apply_nonneg v _))
        fun v _ => max_le (finitePlace_int_le_one v c) (finitePlace_int_le_one v d)
    exact mul_le_of_le_one_right (X.pairHt_pos hne' P).le hs1
  exact hle.trans (h2.trans h1)

/-- **Lemma M with the maximum**: the top class has height `≥ c₀`. -/
theorem PairClass.exists_top (hB : SBezout S) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ P : X F, ∃ p₀ : PairClass S,
      c₀ ≤ p₀.ht P ∧ ∀ p : PairClass S, p.ht P ≤ p₀.ht P := by
  obtain ⟨c₀, hc₀, hM⟩ := PairClass.exists_ht_ge hB
  refine ⟨c₀, hc₀, fun P => ?_⟩
  obtain ⟨p₀, hp₀⟩ := PairClass.exists_max_ht S P
  obtain ⟨p, hp⟩ := hM P
  exact ⟨p₀, hp.trans (hp₀ p), hp₀⟩

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.B1_Bridge
attribute [-simp] _root_.ArtinKP.RO.coe_sIntEquiv _root_.ArtinKP.RO.coe_sIntEquiv_symm _root_.ArtinKP.RO.rowPair_c _root_.ArtinKP.RO.rowPair_d
/-! # WP-B1, file 10: bridges to the ring `R = 𝓞_S`

* `SIntRing S : Subring F`, the ring `{a | IsSInt S a}`; `isSInt_image_iff`: for
  `S = S₀.image FinitePlace.mk` it is Mathlib's `S₀.integer F` (so `SInt 𝔪` when `↑S₀ = placesOf 𝔪`).
* `sBezout_of_isPrincipalIdealRing`: the hypothesis `SBezout S` of Lemma M holds when `R` is a PID.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open NumberField IsDedekindDomain

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.B1

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {S : Finset (FinitePlace F)}

/-- **`SBezout` holds when `R = 𝓞_S` is a principal ideal ring.** -/
theorem sBezout_of_isPrincipalIdealRing [IsPrincipalIdealRing (SIntRing S)] : SBezout S := by
  intro c d hc hd hne
  set c' : SIntRing S := ⟨c, hc⟩ with hc'
  set d' : SIntRing S := ⟨d, hd⟩ with hd'
  obtain ⟨t, ht⟩ := (IsPrincipalIdealRing.principal (Ideal.span {c', d'})).principal
  rw [Ideal.submodule_span_eq] at ht
  have hcm : c' ∈ Ideal.span {t} := ht ▸ Ideal.subset_span (by simp)
  have hdm : d' ∈ Ideal.span {t} := ht ▸ Ideal.subset_span (by simp)
  obtain ⟨c₁, hc₁⟩ := Ideal.mem_span_singleton'.mp hcm
  obtain ⟨d₁, hd₁⟩ := Ideal.mem_span_singleton'.mp hdm
  have htm : t ∈ Ideal.span {c', d'} := ht ▸ Ideal.mem_span_singleton_self t
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp htm
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc₁ hd₁
    rcases hne with h | h
    · exact h (congrArg Subtype.val hc₁.symm)
    · exact h (congrArg Subtype.val hd₁.symm)
  have h1 : a * c₁ + b * d₁ = 1 := by
    refine mul_left_cancel₀ ht0 ?_
    rw [mul_one]
    calc t * (a * c₁ + b * d₁) = a * (c₁ * t) + b * (d₁ * t) := by ring
      _ = t := by rw [hc₁, hd₁, hab]
  have h1F : (a : F) * (c₁ : F) + (b : F) * (d₁ : F) = 1 := by
    exact_mod_cast congrArg Subtype.val h1
  refine ⟨t, t.2, ⟨c₁, d₁, c₁.2, d₁.2, a, b, a.2, b.2, h1F⟩, ?_, ?_⟩
  · have := congrArg Subtype.val hc₁
    change (c₁ : F) * (t : F) = c at this
    rw [← this, mul_comm]
  · have := congrArg Subtype.val hd₁
    change (d₁ : F) * (t : F) = d at this
    rw [← this, mul_comm]

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.B1_Cusp
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
attribute [-simp] _root_.ArtinKP.B.coe_latREquiv _root_.ArtinKP.B.embR_apply _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
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

lemma PairClass.continuous_ht (p : PairClass S) : Continuous p.ht := by
  have : p.ht = fun P => X.pairHt p.out.c p.out.d P / X.sNorm S p.out.c p.out.d := by
    funext P; rw [PairClass.ht_eq_out]; rfl
  rw [this]
  exact (continuous_pairHt p.out.ne_zero).div_const _

/-! ### Harnack in the horizontal variable -/

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.B1_Const
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

variable [IsTotallyComplex F]

/-! ### The lattice `𝓞_F ⊂ ℂ^r` -/

lemma fundD_bounded : Bornology.IsBounded (fundD F) := ZSpan.fundamentalDomain_isBounded _

/-! ### Scaling -/

/-! ### Orbits of the translations on the classes `≠ ∞` -/

/-! ### The constant term -/

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.B1_G
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
/-! # WP-B1, file 8: all cusps; boundedness of `G` (Proposition B of MATH2 §1.3)

* `IsSMat S τ`: `τ ∈ SL₂(F)` with `S`-integral entries (`SL₂(R)`); `PairClass.actR` its right action
  on pair classes; heights change by at most the factor `cS S τ` / `cS S τ⁻¹`.
* `Tcusp S σ p₀ P = ∑_{p ≠ p₀} ht_p(P)^σ`; `Tcusp_le`: under `FiniteCusps S` there are `K`, `C` with
  `Tcusp S σ p₀ P ≤ K (h^{2-σ} + h^{-σ})` for some `h ≥ ht_{p₀}(P)/C`.
* `G S σ P = ∑_p 1[ht_p(P) < 3] ht_p(P)^σ` is `SL₂(𝓞_F)`-invariant and bounded on `X` (`G_le`), under
  `SBezout S` (Lemma M) and `FiniteCusps S` (finitely many `SL₂(𝓞_F)`-orbits of pair classes).
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.B1

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {S : Finset (FinitePlace F)}

/-! ### The action of `SL₂(R)` -/

lemma pairHt_actFF (q : F × F) (τ : SL(2, F)) (P : X F) :
    X.pairHt (actFF q τ).1 (actFF q τ).2 P = X.pairHt q.1 q.2 (τ • P) :=
  (X.pairHt_smul q.1 q.2 τ P).symm

lemma one_le_cS (τ : SL(2, F)) : 1 ≤ cS S τ := by
  unfold cS
  calc (1 : ℝ) = ∏ _v ∈ S, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) fun v _ => le_max_left _ _

lemma sNorm_actFF_le (q : F × F) (τ : SL(2, F)) :
    X.sNorm S (actFF q τ).1 (actFF q τ).2 ≤ cS S τ * X.sNorm S q.1 q.2 := by
  unfold X.sNorm cS
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun v _ => le_max_of_le_left (apply_nonneg v _)) fun v _ => ?_
  set m := max 1 (max (max (v (τ 0 0)) (v (τ 0 1))) (max (v (τ 1 0)) (v (τ 1 1)))) with hm
  have hm0 : 0 ≤ m := le_trans zero_le_one (le_max_left _ _)
  have hx0 : 0 ≤ max (v q.1) (v q.2) := le_max_of_le_left (apply_nonneg v _)
  have key : ∀ a b : F, v a ≤ m → v b ≤ m → v (q.1 * a + q.2 * b) ≤ m * max (v q.1) (v q.2) := by
    intro a b ha hb
    refine (FinitePlace.add_le v _ _).trans (max_le ?_ ?_)
    · rw [map_mul, mul_comm]
      exact mul_le_mul ha (le_max_left _ _) (apply_nonneg v _) hm0
    · rw [map_mul, mul_comm]
      exact mul_le_mul hb (le_max_right _ _) (apply_nonneg v _) hm0
  have h00 : v (τ 0 0) ≤ m := le_max_of_le_right (le_max_of_le_left (le_max_left _ _))
  have h01 : v (τ 0 1) ≤ m := le_max_of_le_right (le_max_of_le_left (le_max_right _ _))
  have h10 : v (τ 1 0) ≤ m := le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have h11 : v (τ 1 1) ≤ m := le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  exact max_le (key _ _ h00 h10) (key _ _ h01 h11)

namespace PairClass

variable [IsTotallyComplex F]

/-- `ht_{pτ}(P) ≤ c(τ⁻¹) · ht_p(τP)`. -/
theorem ht_actR_le (p : PairClass S) (τ : SL(2, F)) (hτ : IsSMat S τ) (P : X F) :
    (p.actR τ hτ).ht P ≤ cS S τ⁻¹ * p.ht (τ • P) := by
  induction p using Quotient.inductionOn with
  | _ q =>
    change X.sHt S (actFF (q.c, q.d) τ).1 (actFF (q.c, q.d) τ).2 P ≤ cS S τ⁻¹ * X.sHt S q.c q.d (τ • P)
    unfold X.sHt
    rw [pairHt_actFF]
    have hne' := (q.actR τ hτ).ne_zero
    change (actFF (q.c, q.d) τ).1 ≠ 0 ∨ (actFF (q.c, q.d) τ).2 ≠ 0 at hne'
    have hs1 := X.sNorm_pos S hne'
    have hs2 := X.sNorm_pos S q.ne_zero
    have hp := X.pairHt_pos q.ne_zero (τ • P)
    have h := sNorm_actFF_le (S := S) (actFF (q.c, q.d) τ) τ⁻¹
    rw [← actFF_mul, mul_inv_cancel, actFF_one] at h
    rw [← mul_div_assoc, div_le_div_iff₀ hs1 hs2]
    nlinarith [one_le_cS (S := S) τ⁻¹]

/-- `ht_p(τP) ≤ c(τ) · ht_{pτ}(P)`. -/
theorem ht_le_ht_actR (p : PairClass S) (τ : SL(2, F)) (hτ : IsSMat S τ) (P : X F) :
    p.ht (τ • P) ≤ cS S τ * (p.actR τ hτ).ht P := by
  induction p using Quotient.inductionOn with
  | _ q =>
    change X.sHt S q.c q.d (τ • P) ≤ cS S τ * X.sHt S (actFF (q.c, q.d) τ).1 (actFF (q.c, q.d) τ).2 P
    unfold X.sHt
    rw [pairHt_actFF]
    have hne' := (q.actR τ hτ).ne_zero
    change (actFF (q.c, q.d) τ).1 ≠ 0 ∨ (actFF (q.c, q.d) τ).2 ≠ 0 at hne'
    have hs1 := X.sNorm_pos S hne'
    have hs2 := X.sNorm_pos S q.ne_zero
    have hp := X.pairHt_pos q.ne_zero (τ • P)
    have h := sNorm_actFF_le (S := S) (q.c, q.d) τ
    rw [← mul_div_assoc, div_le_div_iff₀ hs2 hs1]
    nlinarith [one_le_cS (S := S) τ]

end PairClass

/-! ### The series without one cusp -/

/-! ### The function `G` -/

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.B1_L2
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
attribute [-simp] _root_.ArtinKP.X.chart1_symm_fst _root_.ArtinKP.X.chart1_symm_snd _root_.ArtinKP.X.chart1_v _root_.ArtinKP.X.chart1_x _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
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
-- module Solutions.Artin.KP.B_Def
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

/-! ### The product formula for `S`-units -/

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

/-! ### Convergence of the height series over row classes (from WP-B1) -/

/-! ### The summand and the series -/

lemma unit_coe_ne_zero (ε : (SInt 𝔪)ˣ) : ((ε : SInt 𝔪) : F) ≠ 0 := by
  have h3 : ((ε : SInt 𝔪) : F) * (((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = 1 := by
    rw [← MulMemClass.coe_mul, ε.mul_inv]
    rfl
  exact left_ne_zero_of_mul_eq_one h3

/-! ### Height form (MATH2 §0.2) -/

section height

variable {ι : F →+* ℂ}

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

/-! ### Bounds and convergence -/

end height

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.B_Def2
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

/-! ### Automorphy by reindexing -/

theorem _root_.ArtinKP.S.TSection.mem_stab {Ψ : TSection ι 𝔪} {γ : SL(2, SInt 𝔪)} :
    γ ∈ Ψ.stab ↔ ∀ (s : ℂ) (p : Row 𝔪), Ψ s (p.act γ) = Ψ s p := Iff.rfl

/-! ### The term at the class of `(0, 1)` -/

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.RO_Cusps
attribute [-simp] _root_.ArtinKP.RO.rowClassEquiv_mk _root_.ArtinKP.RO.rowPair_c _root_.ArtinKP.RO.rowPair_d
/-! # WP-RO, file 2: finitely many cusp orbits ((O) of MATH2 §0.1)

`S` is an arbitrary finite set of finite places of the number field `F`.

* `exists_SL2_of_span_eq`: in a Dedekind domain, two pairs generating the same nonzero ideal differ
  by a matrix of `SL₂` (entries in `𝔞𝔞⁻¹`, written without fractional ideals).
* `HasClass q g`: the primitive pair `q` has an `S`-unit multiple in `𝓞²` generating an ideal of
  class `g ∈ Cl(F)`; every `q` has a class (`exists_hasClass`, from `B1.exists_unit_rescale`), and two
  pairs with a common class are in one `SL₂(𝓞)`-orbit modulo `S`-units (`exists_act_of_hasClass`).
* `finiteCusps S : B1.FiniteCusps S`, unconditionally; `finite_orbits_SL2` the same as a finite set of
  classes.
-/

open scoped MatrixGroups
open NumberField IsDedekindDomain

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.RO

open ArtinKP.B1 ArtinKP.X

noncomputable section

/-! ### Pairs generating the same ideal -/

lemma span_singleton_mul_span_pair {A : Type*} [CommRing A] (x c d : A) :
    Ideal.span {x} * Ideal.span {c, d} = Ideal.span {x * c, x * d} := by
  refine le_antisymm (Ideal.mul_le.mpr fun r hr s hs => ?_) (Ideal.span_le.mpr ?_)
  · obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    obtain ⟨b, e, rfl⟩ := Ideal.mem_span_pair.mp hs
    exact Ideal.mem_span_pair.mpr ⟨a * b, a * e, by ring⟩
  · rintro z (rfl | rfl)
    · exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self x) (Ideal.subset_span (by simp))
    · exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self x) (Ideal.subset_span (by simp))

/-- **Two pairs generating the same ideal differ by `SL₂`.** -/
theorem exists_SL2_of_span_eq {A : Type*} [CommRing A] [IsDedekindDomain A] {c₁ d₁ c₂ d₂ : A}
    (hne : c₁ ≠ 0 ∨ d₁ ≠ 0) (h : Ideal.span {c₁, d₁} = Ideal.span {c₂, d₂}) :
    ∃ γ : SL(2, A), c₁ * γ 0 0 + d₁ * γ 1 0 = c₂ ∧ c₁ * γ 0 1 + d₁ * γ 1 1 = d₂ := by
  set J : Ideal A := Ideal.span {c₁, d₁} with hJ
  have hc₁ : c₁ ∈ J := Ideal.subset_span (by simp)
  have hd₁ : d₁ ∈ J := Ideal.subset_span (by simp)
  have hc₂ : c₂ ∈ J := h ▸ Ideal.subset_span (by simp)
  have hd₂ : d₂ ∈ J := h ▸ Ideal.subset_span (by simp)
  obtain ⟨x, hxJ, hx0⟩ : ∃ x ∈ J, x ≠ 0 := by
    rcases hne with h0 | h0
    · exact ⟨c₁, hc₁, h0⟩
    · exact ⟨d₁, hd₁, h0⟩
  obtain ⟨J', hJ'⟩ : J ∣ Ideal.span {x} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem J).mpr hxJ)
  have hdiv : ∀ j ∈ J, ∀ j' ∈ J', ∃ m : A, j * j' = x * m := by
    intro j hj j' hj'
    have hm : j * j' ∈ Ideal.span {x} := hJ' ▸ Ideal.mul_mem_mul hj hj'
    obtain ⟨m, hm⟩ := Ideal.mem_span_singleton'.mp hm
    exact ⟨m, by rw [← hm, mul_comm]⟩
  have hdec : ∀ c d : A, Ideal.span {c, d} = J → ∃ α ∈ J', ∃ β ∈ J', c * α + d * β = x := by
    intro c d hcd
    have hx : x ∈ Ideal.span {c, d} * J' := by
      rw [hcd, ← hJ']; exact Ideal.mem_span_singleton_self x
    rw [Ideal.span_insert, Ideal.sup_mul] at hx
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx
    obtain ⟨α, hα, rfl⟩ := Ideal.mem_span_singleton_mul.mp hy
    obtain ⟨β, hβ, rfl⟩ := Ideal.mem_span_singleton_mul.mp hz
    exact ⟨α, hα, β, hβ, hyz⟩
  obtain ⟨α₁, hα₁, β₁, hβ₁, hx₁⟩ := hdec c₁ d₁ rfl
  obtain ⟨α₂, hα₂, β₂, hβ₂, hx₂⟩ := hdec c₂ d₂ h.symm
  obtain ⟨m1, h1⟩ := hdiv d₁ hd₁ β₂ hβ₂
  obtain ⟨m2, h2⟩ := hdiv c₂ hc₂ α₁ hα₁
  obtain ⟨m3, h3⟩ := hdiv d₁ hd₁ α₂ hα₂
  obtain ⟨m4, h4⟩ := hdiv d₂ hd₂ α₁ hα₁
  obtain ⟨m5, h5⟩ := hdiv c₁ hc₁ β₂ hβ₂
  obtain ⟨m6, h6⟩ := hdiv c₂ hc₂ β₁ hβ₁
  obtain ⟨m7, h7⟩ := hdiv c₁ hc₁ α₂ hα₂
  obtain ⟨m8, h8⟩ := hdiv d₂ hd₂ β₁ hβ₁
  have hdet : (m1 + m2) * (m7 + m8) - (-m3 + m4) * (-m5 + m6) = 1 := by
    refine mul_left_cancel₀ (mul_ne_zero hx0 hx0) ?_
    calc x * x * ((m1 + m2) * (m7 + m8) - (-m3 + m4) * (-m5 + m6))
        = (x * m1 + x * m2) * (x * m7 + x * m8) - (-(x * m3) + x * m4) * (-(x * m5) + x * m6) := by
          ring
      _ = (d₁ * β₂ + c₂ * α₁) * (c₁ * α₂ + d₂ * β₁) - (-(d₁ * α₂) + d₂ * α₁) * (-(c₁ * β₂) + c₂ * β₁) := by
          rw [h1, h2, h3, h4, h5, h6, h7, h8]
      _ = (c₁ * α₁ + d₁ * β₁) * (c₂ * α₂ + d₂ * β₂) := by ring
      _ = x * x * 1 := by rw [hx₁, hx₂, mul_one]
  refine ⟨⟨!![m1 + m2, -m3 + m4; -m5 + m6, m7 + m8], by rw [Matrix.det_fin_two_of]; exact hdet⟩, ?_, ?_⟩
  · refine mul_left_cancel₀ hx0 ?_
    change x * (c₁ * (m1 + m2) + d₁ * (-m5 + m6)) = x * c₂
    calc x * (c₁ * (m1 + m2) + d₁ * (-m5 + m6))
        = c₁ * (x * m1 + x * m2) + d₁ * (-(x * m5) + x * m6) := by ring
      _ = c₁ * (d₁ * β₂ + c₂ * α₁) + d₁ * (-(c₁ * β₂) + c₂ * β₁) := by rw [h1, h2, h5, h6]
      _ = (c₁ * α₁ + d₁ * β₁) * c₂ := by ring
      _ = x * c₂ := by rw [hx₁]
  · refine mul_left_cancel₀ hx0 ?_
    change x * (c₁ * (-m3 + m4) + d₁ * (m7 + m8)) = x * d₂
    calc x * (c₁ * (-m3 + m4) + d₁ * (m7 + m8))
        = c₁ * (-(x * m3) + x * m4) + d₁ * (x * m7 + x * m8) := by ring
      _ = c₁ * (-(d₁ * α₂) + d₂ * α₁) + d₁ * (c₁ * α₂ + d₂ * β₁) := by rw [h3, h4, h7, h8]
      _ = (c₁ * α₁ + d₁ * β₁) * d₂ := by ring
      _ = x * d₂ := by rw [hx₁]

variable {F : Type*} [Field F] [NumberField F] {S : Finset (FinitePlace F)}

/-! ### Proportional primitive pairs -/

/-- Two primitive pairs which are proportional over `F` are equivalent modulo `S`-units. -/
lemma SPair.equiv_of_smul {p p' : SPair S} {t : F} (h1 : p'.c = t * p.c) (h2 : p'.d = t * p.d) :
    p ≈ p' := by
  obtain ⟨a, b, ha, hb, hab⟩ := p.prim
  obtain ⟨a', b', ha', hb', hab'⟩ := p'.prim
  have ht : t = a * p'.c + b * p'.d := by rw [h1, h2]; linear_combination (-t) * hab
  have hprod : t * (a' * p.c + b' * p.d) = 1 := by rw [← hab', h1, h2]; ring
  have hI : IsSInt S t := ht ▸ (ha.mul p'.hc).add (hb.mul p'.hd)
  have hI' : IsSInt S (a' * p.c + b' * p.d) := (ha'.mul p.hc).add (hb'.mul p.hd)
  refine ⟨t, ⟨left_ne_zero_of_mul_eq_one hprod, fun v hv => ?_⟩, h1, h2⟩
  have e1 := hI v hv
  have e2 := hI' v hv
  have e3 : v t * v (a' * p.c + b' * p.d) = 1 := by rw [← map_mul, hprod, map_one]
  have e4 : 0 ≤ v t := apply_nonneg v _
  nlinarith

/-- Every pair class is a translate of the cusp `∞` by a matrix of `SL₂(R)`. -/
lemma exists_actR_inf (q : SPair S) :
    ∃ (τ : SL(2, F)) (hτ : IsSMat S τ), (PairClass.inf S).actR τ hτ = ⟦q⟧ := by
  obtain ⟨a, b, ha, hb, hab⟩ := q.prim
  refine ⟨⟨!![b, -a; q.c, q.d], by rw [Matrix.det_fin_two_of]; linear_combination hab⟩, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j
    · exact hb
    · exact ha.neg
    · exact q.hc
    · exact q.hd
  · change (⟦(SPair.inf S).actR _ _⟧ : PairClass S) = ⟦q⟧
    congr 1
    ext <;> simp [SPair.actR, SPair.inf, actFF]

/-! ### The ideal class of a pair -/

lemma exists_hasClass (q : SPair S) : ∃ g : ClassGroup (𝓞 F), HasClass q g := by
  obtain ⟨_, _, hres⟩ := exists_unit_rescale S
  obtain ⟨u, hu0, huS, ⟨c, d, hc, hd⟩, -⟩ := hres q.c q.d q.ne_zero q.hc q.hd
  have hne : Ideal.span {c, d} ≠ (⊥ : Ideal (𝓞 F)) := by
    intro h0
    rw [Ideal.span_eq_bot] at h0
    have hc0 : c = 0 := h0 c (by simp)
    have hd0 : d = 0 := h0 d (by simp)
    rw [hc0] at hc
    rw [hd0] at hd
    rcases q.ne_zero with h | h
    · exact mul_ne_zero hu0 h (by simpa using hc.symm)
    · exact mul_ne_zero hu0 h (by simpa using hd.symm)
  exact ⟨_, u, c, d, ⟨Ideal.span {c, d}, mem_nonZeroDivisors_of_ne_zero hne⟩, ⟨hu0, huS⟩, hc, hd, rfl,
    rfl⟩

/-- **Two pairs with the same ideal class lie in one `SL₂(𝓞)`-orbit.** -/
theorem exists_act_of_hasClass {q q' : SPair S} {g : ClassGroup (𝓞 F)} (h : HasClass q g)
    (h' : HasClass q' g) : ∃ γ : SL(2, 𝓞 F), (⟦q'⟧ : PairClass S) = PairClass.act (⟦q⟧ : PairClass S) γ := by
  obtain ⟨u₁, c₁, d₁, I₁, hu₁, hc₁, hd₁, hI₁, hg₁⟩ := h
  obtain ⟨u₂, c₂, d₂, I₂, hu₂, hc₂, hd₂, hI₂, hg₂⟩ := h'
  obtain ⟨x, y, hx, hy, hxy⟩ := (ClassGroup.mk0_eq_mk0_iff (I := I₁) (J := I₂)).mp (hg₁.trans hg₂.symm)
  rw [hI₁, hI₂, span_singleton_mul_span_pair, span_singleton_mul_span_pair] at hxy
  have hne : x * c₁ ≠ 0 ∨ x * d₁ ≠ 0 := by
    have h0 : (c₁ : F) ≠ 0 ∨ (d₁ : F) ≠ 0 := by
      rw [hc₁, hd₁]
      exact q.ne_zero.imp (mul_ne_zero hu₁.1) (mul_ne_zero hu₁.1)
    refine h0.imp (fun h hz => h ?_) (fun h hz => h ?_)
    · rw [(mul_eq_zero.mp hz).resolve_left hx]; simp
    · rw [(mul_eq_zero.mp hz).resolve_left hx]; simp
  obtain ⟨γ, hγ1, hγ2⟩ := exists_SL2_of_span_eq hne hxy
  have hxF : (x : F) ≠ 0 := by simpa using hx
  have e1 : (x : F) * u₁ * (q.c * (γ 0 0 : 𝓞 F) + q.d * (γ 1 0 : 𝓞 F)) = y * u₂ * q'.c := by
    have := congrArg (fun z : 𝓞 F => (z : F)) hγ1
    simp only [map_mul, map_add, hc₁, hd₁, hc₂] at this
    linear_combination this
  have e2 : (x : F) * u₁ * (q.c * (γ 0 1 : 𝓞 F) + q.d * (γ 1 1 : 𝓞 F)) = y * u₂ * q'.d := by
    have := congrArg (fun z : 𝓞 F => (z : F)) hγ2
    simp only [map_mul, map_add, hc₁, hd₁, hd₂] at this
    linear_combination this
  have hxu : (x : F) * u₁ ≠ 0 := mul_ne_zero hxF hu₁.1
  refine ⟨γ, Quotient.sound (SPair.equiv_of_smul (t := (y : F) * u₂ / (x * u₁)) ?_ ?_)⟩
  · change q.c * (γ 0 0 : 𝓞 F) + q.d * (γ 1 0 : 𝓞 F) = _
    rw [div_mul_eq_mul_div, eq_div_iff hxu]
    linear_combination e1
  · change q.c * (γ 0 1 : 𝓞 F) + q.d * (γ 1 1 : 𝓞 F) = _
    rw [div_mul_eq_mul_div, eq_div_iff hxu]
    linear_combination e2

/-! ### Finiteness -/

open scoped Classical in
/-- **(O): finitely many `SL₂(𝓞)`-orbits of pair classes**, in the form of `B1.FiniteCusps`. -/
theorem finiteCusps (S : Finset (FinitePlace F)) : FiniteCusps S := by
  set rep : ClassGroup (𝓞 F) → SPair S := fun g =>
    if h : ∃ q : SPair S, HasClass q g then h.choose else SPair.inf S with hrep
  have hrepc : ∀ (q : SPair S) (g : ClassGroup (𝓞 F)), HasClass q g → HasClass (rep g) g := by
    intro q g hq
    have hex : ∃ q : SPair S, HasClass q g := ⟨q, hq⟩
    simp only [hrep, dif_pos hex]
    exact hex.choose_spec
  choose τ hτ hτe using fun g => exists_actR_inf (rep g)
  set e := Fintype.equivFin (ClassGroup (𝓞 F)) with he
  refine ⟨Fintype.card (ClassGroup (𝓞 F)), fun i => τ (e.symm i), fun i => hτ _, fun p => ?_⟩
  induction p using Quotient.inductionOn with
  | _ q =>
    obtain ⟨g, hg⟩ := exists_hasClass q
    obtain ⟨γ, hγ⟩ := exists_act_of_hasClass (hrepc q g hg) hg
    refine ⟨e g, γ, ?_⟩
    change _ = PairClass.act ((PairClass.inf S).actR (τ (e.symm (e g))) (hτ _)) γ
    rw [hτe, e.symm_apply_apply]
    exact hγ

end

end ArtinKP.RO
end

section
-- module Solutions.Artin.KP.RO_Ring
/-! # WP-RO, file 1: the ring of `S`-integers is a PID; `SBezout`

`SOf 𝔪 : Finset (FinitePlace F)` is the set of finite places dividing `𝔪`, in the form used by
WP-B1.  For `𝔪 ≠ ⊥`, `B1.IsSInt (SOf 𝔪)` is membership in `SInt 𝔪` (`isSInt_SOf_iff`), so
`B1.SIntRing (SOf 𝔪) ≃+* SInt 𝔪` (`sIntEquiv`).

* `isPrincipalIdealRing_SInt (hG : Good 𝔪) : IsPrincipalIdealRing (SInt 𝔪)`: every ideal of `SInt 𝔪`
  is extended from `𝓞 F` (clear denominators by an `S`-unit, `B1.exists_unit_rescale`), and extended
  ideals are principal (`Good.principal`).
* `isPrincipalIdealRing_SIntRing`, `sBezout (hG : Good 𝔪) : B1.SBezout (SOf 𝔪)`.
-/

open scoped MatrixGroups
open NumberField IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.RO

open ArtinKP.A ArtinKP.B1

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- **`R = SInt 𝔪` is a principal ideal ring** when `𝔪` is good. -/
theorem isPrincipalIdealRing_SInt (hG : Good 𝔪) : IsPrincipalIdealRing (SInt 𝔪) :=
  ⟨fun J => by
    rw [← map_comap_eq hG.ne_bot J]
    exact hG.principal _⟩

/-- The same for WP-B1's model of `R`. -/
theorem isPrincipalIdealRing_SIntRing (hG : Good 𝔪) : IsPrincipalIdealRing (SIntRing (SOf 𝔪)) :=
  haveI := isPrincipalIdealRing_SInt hG
  IsPrincipalIdealRing.of_surjective (sIntEquiv hG.ne_bot).toRingHom (sIntEquiv hG.ne_bot).surjective

/-- **`SBezout` holds for the places of a good modulus.** -/
theorem sBezout (hG : Good 𝔪) : SBezout (SOf 𝔪) :=
  haveI := isPrincipalIdealRing_SIntRing hG
  sBezout_of_isPrincipalIdealRing

end

end ArtinKP.RO
end

section
-- module Solutions.Artin.KP.RO_Bridge
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
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
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

variable [IsTotallyComplex F]

/-- WP-RO's bridge preserves heights. -/
theorem ht_rowClassEquiv (h𝔪 : 𝔪 ≠ ⊥) (q : RowClass 𝔪) (Q : X F) :
    (RO.rowClassEquiv h𝔪 q).ht Q = q.ht Q := by
  conv_lhs => rw [← RowClass.mk_out q]
  rfl

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.RC_Cusp
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
attribute [-simp] _root_.ArtinKP.B.coe_latREquiv _root_.ArtinKP.B.embR_apply _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
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

/-- Diagonal matrices of units `≡ 1 mod m` are in `conjSub τ`. -/
lemma unitDiag_mem_conjSub {τ : SL(2, F)} {m : 𝓞 F}
    (hm : ∀ i j k l : Fin 2,
      ∃ a : 𝓞 F, algebraMap (𝓞 F) F a = algebraMap (𝓞 F) F m * (τ i j * τ k l))
    (η : (𝓞 F)ˣ) (t : 𝓞 F) (hη : (η : 𝓞 F) = 1 + m * t) :
    unitDiag η ∈ conjSub τ := by
  have hdet := det_eq τ
  obtain ⟨xbc, hbc⟩ := hm 0 1 1 0
  obtain ⟨xbd, hbd⟩ := hm 0 1 1 1
  obtain ⟨xac, hac⟩ := hm 0 0 1 0
  set θ : 𝓞 F := ((η⁻¹ : (𝓞 F)ˣ) : 𝓞 F) with hθ
  have hηθ : algebraMap (𝓞 F) F (η : 𝓞 F) * algebraMap (𝓞 F) F θ = 1 := by
    rw [← map_mul, hθ, Units.mul_inv, map_one]
  have hη' : algebraMap (𝓞 F) F (η : 𝓞 F) =
      1 + algebraMap (𝓞 F) F m * algebraMap (𝓞 F) F t := by
    rw [hη, map_add, map_mul, map_one]
  have key : algebraMap (𝓞 F) F (η : 𝓞 F) - algebraMap (𝓞 F) F θ =
      algebraMap (𝓞 F) F m * algebraMap (𝓞 F) F t * (1 + algebraMap (𝓞 F) F θ) := by
    linear_combination (1 + algebraMap (𝓞 F) F θ) * hη' - hηθ
  obtain ⟨e00, e01, e10, e11⟩ := conj_entries τ (intSL F (unitDiag η))
    (by simp [intSL_apply, unitDiag_coe])
  have g00 : (intSL F (unitDiag η)) 0 0 = algebraMap (𝓞 F) F (η : 𝓞 F) := by
    simp [intSL_apply, unitDiag_coe]
  have g01 : (intSL F (unitDiag η)) 0 1 = 0 := by simp [intSL_apply, unitDiag_coe]
  have g11 : (intSL F (unitDiag η)) 1 1 = algebraMap (𝓞 F) F θ := by
    simp [intSL_apply, unitDiag_coe, hθ]
  refine mem_conjSub_of_entries fun i j => ?_
  fin_cases i <;> fin_cases j
  · refine ⟨(η : 𝓞 F) + t * (1 + θ) * xbc, ?_⟩
    change _ = (τ⁻¹ * intSL F (unitDiag η) * τ) 0 0
    rw [e00, g00, g01, g11, map_add, map_mul, map_mul, map_add, map_one, hbc]
    linear_combination (-(τ 0 1 * τ 1 0)) * key - algebraMap (𝓞 F) F (η : 𝓞 F) * hdet
  · refine ⟨t * (1 + θ) * xbd, ?_⟩
    change _ = (τ⁻¹ * intSL F (unitDiag η) * τ) 0 1
    rw [e01, g00, g01, g11, map_mul, map_mul, map_add, map_one, hbd]
    linear_combination (-(τ 0 1 * τ 1 1)) * key
  · refine ⟨-(t * (1 + θ) * xac), ?_⟩
    change _ = (τ⁻¹ * intSL F (unitDiag η) * τ) 1 0
    rw [e10, g00, g01, g11, map_neg, map_mul, map_mul, map_add, map_one, hac]
    linear_combination (τ 0 0 * τ 1 0) * key
  · refine ⟨θ - t * (1 + θ) * xbc, ?_⟩
    change _ = (τ⁻¹ * intSL F (unitDiag η) * τ) 1 1
    rw [e11, g00, g01, g11, map_sub, map_mul, map_mul, map_add, map_one, hbc]
    linear_combination (τ 0 1 * τ 1 0) * key - algebraMap (𝓞 F) F θ * hdet

/-- A power of every unit is `≡ 1 mod m`. -/
lemma exists_pow_unit_congr {m : 𝓞 F} (hm : m ≠ 0) :
    ∃ k : ℕ, k ≠ 0 ∧ ∀ ε : (𝓞 F)ˣ, ∃ t : 𝓞 F, ((ε ^ k : (𝓞 F)ˣ) : 𝓞 F) = 1 + m * t := by
  let I : Ideal (𝓞 F) := Ideal.span {m}
  have hI : I ≠ ⊥ := by
    simpa [I, Ideal.span_singleton_eq_bot] using hm
  have : Finite (𝓞 F ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  refine ⟨Nat.card (𝓞 F ⧸ I)ˣ, Nat.card_pos.ne', fun ε => ?_⟩
  have h1 : (Units.map (Ideal.Quotient.mk I).toMonoidHom ε) ^ Nat.card (𝓞 F ⧸ I)ˣ = 1 :=
    pow_card_eq_one'
  have h2 : Ideal.Quotient.mk I (((ε ^ Nat.card (𝓞 F ⧸ I)ˣ : (𝓞 F)ˣ) : 𝓞 F) - 1) = 0 := by
    have := congrArg Units.val h1
    rw [Units.val_pow_eq_pow_val, Units.val_one] at this
    rw [map_sub, map_one, sub_eq_zero, Units.val_pow_eq_pow_val, map_pow]
    exact this
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h2
  obtain ⟨t, ht⟩ := h2
  exact ⟨t, by linear_combination -ht⟩

variable [IsTotallyComplex F]

/-- **Reduction under the upper triangular part of a subgroup `K ≤ SL₂(𝓞_F)`** containing the
translations by `m𝓞_F` and the diagonal matrices of the `k`-th powers of units.  There are `C, ρ`
such that every `Q ∈ X` has a translate `γ' • Q`, `γ' ∈ K` upper triangular, of the same height,
with `|x_w| ≤ ρ` and `v` balanced with ratio `C`. -/
theorem exists_reduced_subgroup (K : Subgroup (SL(2, 𝓞 F))) {m : 𝓞 F} (hm0 : m ≠ 0)
    (hN : ∀ β : 𝓞 F, nInt (m * β) ∈ K) {k : ℕ} (hk0 : k ≠ 0)
    (hU : ∀ ε : (𝓞 F)ˣ, unitDiag (ε ^ k) ∈ K) : ∃ C ρ : ℝ, 1 ≤ C ∧ 0 < ρ ∧ ∀ Q : X F,
    ∃ γ' : SL(2, 𝓞 F), γ' ∈ K ∧ γ' 1 0 = 0 ∧ X.ht (γ' • Q) = X.ht Q ∧
      (∀ w, ‖(γ' • Q).x w‖ ≤ ρ) ∧ ∀ w w', (γ' • Q).v w ≤ C * (γ' • Q).v w' := by
  obtain ⟨C₀, hC₀, hbal⟩ := exists_unit_balanced (F := F)
  obtain ⟨R, hR⟩ := (fundD_bounded (F := F)).exists_norm_le
  have hC₀' : (0 : ℝ) ≤ C₀ := by linarith
  refine ⟨C₀ ^ k, (∑ w : InfinitePlace F, ‖w.embedding (m : F)‖) * |R| + 1, one_le_pow₀ hC₀,
    by positivity, fun Q => ?_⟩
  obtain ⟨ε, hε⟩ := hbal (fun w => Q.v w ^ ((k : ℝ)⁻¹))
    (fun w => Real.rpow_pos_of_pos (Q.v_pos w) _)
  obtain ⟨η, hηdef⟩ : ∃ η : (𝓞 F)ˣ, η = ε ^ k := ⟨_, rfl⟩
  have hηF : algebraMap (𝓞 F) F (η : 𝓞 F) = algebraMap (𝓞 F) F (ε : 𝓞 F) ^ k := by
    rw [hηdef, Units.val_pow_eq_pow_val, map_pow]
  obtain ⟨Q₁, hQ₁⟩ : ∃ Q₁ : X F, Q₁ = unitDiag η • Q := ⟨_, rfl⟩
  have hv1 : ∀ w, Q₁.v w = ((w (ε : F)) ^ 2 * Q.v w ^ ((k : ℝ)⁻¹)) ^ k := by
    intro w
    rw [hQ₁, unitDiag_smul_v, hηF, map_pow, mul_pow,
      Real.rpow_inv_natCast_pow (Q.v_pos w).le hk0]
    ring
  have hbal1 : ∀ w w', Q₁.v w ≤ C₀ ^ k * Q₁.v w' := by
    intro w w'
    rw [hv1, hv1, ← mul_pow]
    exact pow_le_pow_left₀
      (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Q.v_pos w).le _)) (hε w w') k
  have hht1 : X.ht Q₁ = X.ht Q := by
    rw [hQ₁]; exact ht_smul_of_upper (by simp [unitDiag_coe]) Q
  have hmw : ∀ w : InfinitePlace F, w.embedding (m : F) ≠ 0 := fun w => by
    simpa using hm0
  obtain ⟨g, hg, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain (latE (F := F))
    (fun w => Q₁.x w / w.embedding (m : F))
  obtain ⟨β, hβ⟩ := mem_latSub.mp g.2
  have hmem : (fun w => Q₁.x w / w.embedding (m : F)) + emb (β : F) ∈ fundD F := by
    have : (g : InfinitePlace F → ℂ) + (fun w => Q₁.x w / w.embedding (m : F)) ∈ fundD F := hg
    rwa [hβ, add_comm] at this
  have hQ₁mk : Q₁ = X.mk Q₁.x Q₁.v Q₁.v_pos := X.ext' rfl rfl
  have hQ₂ : nInt (m * β) • Q₁ = X.mk (Q₁.x + emb ((m * β : 𝓞 F) : F)) Q₁.v Q₁.v_pos := by
    conv_lhs => rw [hQ₁mk]
    exact nInt_smul_mk (m * β) _ _ _
  have hht2 : X.ht (nInt (m * β) • Q₁) = X.ht Q₁ := ht_smul_of_upper (nInt_upper (m * β)) Q₁
  refine ⟨nInt (m * β) * unitDiag η,
    K.mul_mem (hN β) (by rw [hηdef]; exact hU ε), ?_, ?_, ?_, ?_⟩
  · simp [nInt_coe, unitDiag_coe, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [mul_smul, ← hQ₁, hht2, hht1]
  · intro w
    rw [mul_smul, ← hQ₁, hQ₂]
    change ‖(Q₁.x + emb ((m * β : 𝓞 F) : F)) w‖ ≤ _
    have h1 : (Q₁.x + emb ((m * β : 𝓞 F) : F)) w =
        w.embedding (m : F) * ((fun w => Q₁.x w / w.embedding (m : F)) + emb (β : F)) w := by
      simp only [Pi.add_apply, emb_apply]
      have : ((m * β : 𝓞 F) : F) = (m : F) * (β : F) := by simp
      rw [this, map_mul]
      field_simp [hmw w]
    rw [h1, norm_mul]
    have h2 : ‖((fun w => Q₁.x w / w.embedding (m : F)) + emb (β : F)) w‖ ≤ |R| :=
      ((norm_le_pi_norm _ w).trans (hR _ hmem)).trans (le_abs_self R)
    have h3 : ‖w.embedding (m : F)‖ ≤ ∑ w : InfinitePlace F, ‖w.embedding (m : F)‖ :=
      Finset.single_le_sum (f := fun w : InfinitePlace F => ‖w.embedding (m : F)‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
    calc ‖w.embedding (m : F)‖ * ‖((fun w => Q₁.x w / w.embedding (m : F)) + emb (β : F)) w‖
        ≤ (∑ w : InfinitePlace F, ‖w.embedding (m : F)‖) * |R| :=
          mul_le_mul h3 h2 (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      _ ≤ _ := by linarith
  · intro w w'
    rw [mul_smul, ← hQ₁, hQ₂]
    exact hbal1 w w'

/-- **Reduction under the upper triangular part of `τ SL₂(𝓞_F) τ⁻¹`**: `exists_reduced_subgroup`
for `K = conjSub τ`. -/
theorem exists_reduced_conj (τ : SL(2, F)) : ∃ C ρ : ℝ, 1 ≤ C ∧ 0 < ρ ∧ ∀ Q : X F,
    ∃ γ' : SL(2, 𝓞 F), γ' ∈ conjSub τ ∧ γ' 1 0 = 0 ∧ X.ht (γ' • Q) = X.ht Q ∧
      (∀ w, ‖(γ' • Q).x w‖ ≤ ρ) ∧ ∀ w w', (γ' • Q).v w ≤ C * (γ' • Q).v w' := by
  obtain ⟨m, hm0, hm⟩ := exists_denominator τ
  obtain ⟨k, hk0, hk⟩ := exists_pow_unit_congr hm0
  refine exists_reduced_subgroup (conjSub τ) hm0 (nInt_mem_conjSub hm) hk0 fun ε => ?_
  obtain ⟨t, ht⟩ := hk ε
  exact unitDiag_mem_conjSub hm _ t ht

/-- **R1 (WP-B1 stub): reduction at a general cusp.**  For every `τ ∈ SL₂(F)` there are `C, ρ`
such that every `Q` with `c ≤ ht Q ≤ T` has a translate `g • Q` in the compact box, `g` upper
triangular in `τ SL₂(𝓞_F) τ⁻¹`. -/
theorem reduction_cusp (τ : SL(2, F)) : ∃ C ρ : ℝ, 1 ≤ C ∧ 0 < ρ ∧ ∀ c T : ℝ, 0 < c →
    ∀ Q : X F, c ≤ X.ht Q → X.ht Q ≤ T → ∃ γ : SL(2, 𝓞 F), ∃ g : SL(2, F), g 1 0 = 0 ∧
      τ * intSL F γ = g * τ ∧
      g • Q ∈ siegelBox F (min 1 (c / C ^ Fintype.card (InfinitePlace F)))
        (max 1 (C ^ Fintype.card (InfinitePlace F) * T)) ρ := by
  obtain ⟨C, ρ, hC, hρ, h⟩ := exists_reduced_conj τ
  set r := Fintype.card (InfinitePlace F) with hr
  have hr0 : r ≠ 0 := Fintype.card_ne_zero
  refine ⟨C, ρ, hC, hρ, fun c T hc Q hcQ hQT => ?_⟩
  obtain ⟨γ', hmem, hup, hht, hx, hbal⟩ := h Q
  obtain ⟨γ, hγ⟩ := mem_conjSub.mp hmem
  refine ⟨γ, intSL F γ', ?_, hγ, fun w => ?_⟩
  · rw [intSL_apply, hup, map_zero]
  · have hv := (γ' • Q).v_pos
    obtain ⟨hb1, hb2⟩ := balanced_bounds (by linarith : (0 : ℝ) ≤ C) hv hbal w
    have hprod : ∏ j, (γ' • Q).v j = X.ht Q := hht
    rw [hprod] at hb1 hb2
    have hCr : 0 < C ^ r := by positivity
    refine ⟨hx w, ?_, ?_⟩
    · change min 1 (c / C ^ r) ≤ (γ' • Q).v w
      rcases le_total 1 ((γ' • Q).v w) with h1 | h1
      · exact (min_le_left _ _).trans h1
      · refine (min_le_right _ _).trans ?_
        have h2 : (γ' • Q).v w ^ r ≤ (γ' • Q).v w := pow_le_of_le_one (hv w).le h1 hr0
        rw [div_le_iff₀ hCr]
        nlinarith
    · change (γ' • Q).v w ≤ max 1 (C ^ r * T)
      rcases le_total ((γ' • Q).v w) 1 with h1 | h1
      · exact h1.trans (le_max_left _ _)
      · refine le_trans ?_ (le_max_right _ _)
        have h2 : (γ' • Q).v w ≤ (γ' • Q).v w ^ r := le_self_pow₀ h1 hr0
        nlinarith

end

end ArtinKP.RC
end

section
-- module Solutions.Artin.KP.X2_Chart
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol
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

/-! ### One factor -/

/-! ### The product -/

variable (F : Type*) [Field F] [NumberField F]

variable {F}

lemma chart_v (y : Coord F) (w : InfinitePlace F) : (chart F y).v w = Real.exp (y w).2 := rfl

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.RC_Compact
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
/-! # WP-RC, file 2: compactness modulo `Γ` of bounded-height sets (MATH2 1.4(d)) and finite volume (V1)

* `spread Γ B = ⋃_{q ∈ SL₂(𝓞)/Γ} q.out⁻¹ • B`: passage from `SL₂(𝓞_F)` to a subgroup of finite index.
* `exists_compact_top_le`, `exists_compact_top_le_subgroup`: **MATH2 1.4(d)**,
  `{P : ht_p(P) ≤ T ∀ p} ⊆ Γ · K`, `K` compact.
* `exists_cover_finite_vol`: `X = SL₂(𝓞_F) · B` with `vol B < ∞` (finite union of translated Siegel sets).
* `lintegral_mul_pou_le_of_cover` (covering lemma), `quotVol_univ_le`.
* `quotVol_univ_lt_top`: **V1**, `μ(Γ\X) < ∞` for `Γ` of finite index.
* `lintegral_G_pow_lt_top`: `G ∈ L^k(Γ\X)` with no volume hypothesis.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Pointwise
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.RC

open ArtinKP.X ArtinKP.B1

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-! ### Subgroups of finite index -/

lemma exists_subgroup_smul_mem_spread (Γ : Subgroup (SL(2, 𝓞 F))) {B : Set (X F)} {P : X F}
    (h : ∃ γ : SL(2, 𝓞 F), γ • P ∈ B) : ∃ γ : Γ, γ • P ∈ spread Γ B := by
  obtain ⟨γ, hγ⟩ := h
  obtain ⟨q, hq⟩ : ∃ q : SL(2, 𝓞 F) ⧸ Γ, q = QuotientGroup.mk γ := ⟨_, rfl⟩
  have hmem : q.out⁻¹ * γ ∈ Γ := by
    have : (QuotientGroup.mk q.out : SL(2, 𝓞 F) ⧸ Γ) = QuotientGroup.mk γ := by
      rw [← hq]; exact q.out_eq'
    exact QuotientGroup.eq.mp this
  refine ⟨⟨q.out⁻¹ * γ, hmem⟩, Set.mem_iUnion.mpr ⟨q, γ • P, hγ, ?_⟩⟩
  change q.out⁻¹ • γ • P = (q.out⁻¹ * γ) • P
  rw [mul_smul]

lemma isCompact_spread (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex] {K : Set (X F)}
    (hK : IsCompact K) : IsCompact (spread Γ K) :=
  isCompact_iUnion fun q => hK.image (continuous_const_smul (q.out⁻¹ : SL(2, 𝓞 F)))

variable [IsTotallyComplex F] {S : Finset (FinitePlace F)}

/-! ### MATH2 1.4(d) -/

/-- **MATH2 1.4(d) for `SL₂(𝓞_F)`**: the set where all pair heights are `≤ T` is contained in
`SL₂(𝓞_F) · K` with `K` compact (`K = ⋃_i τ_i⁻¹ • box_i` over the cusp representatives). -/
theorem exists_compact_top_le (hB : SBezout S) (hO : FiniteCusps S) (T : ℝ) :
    ∃ K : Set (X F), IsCompact K ∧ ∀ P : X F, (∀ p : PairClass S, p.ht P ≤ T) →
      ∃ γ : SL(2, 𝓞 F), γ • P ∈ K := by
  obtain ⟨n, τ, hτ, hcov⟩ := hO
  obtain ⟨c₀, hc₀, htop⟩ := PairClass.exists_top hB
  choose C ρ hC hρ hred using fun i => reduction_cusp (τ i)
  have hcS : ∀ i, 0 < cS S (τ i)⁻¹ := fun i => lt_of_lt_of_le one_pos (one_le_cS _)
  have hc : ∀ i, 0 < c₀ / cS S (τ i)⁻¹ := fun i => div_pos hc₀ (hcS i)
  refine ⟨⋃ i, (fun P : X F => (τ i)⁻¹ • P) ''
      siegelBox F (min 1 (c₀ / cS S (τ i)⁻¹ / C i ^ Fintype.card (InfinitePlace F)))
        (max 1 (C i ^ Fintype.card (InfinitePlace F) * (cS S (τ i) * T))) (ρ i),
    isCompact_iUnion fun i => (isCompact_siegelBox
      (lt_min one_pos (div_pos (hc i) (pow_pos (lt_of_lt_of_le one_pos (hC i)) _)))).image
      (continuous_const_smul _), fun P hP => ?_⟩
  obtain ⟨p₀, hp₀, -⟩ := htop P
  obtain ⟨i, γ₀, hi⟩ := hcov p₀
  have h1 : p₀.ht P = ((PairClass.inf S).actR (τ i) (hτ i)).ht (γ₀ • P) := by
    rw [hi, PairClass.ht_act]
  have hle := PairClass.ht_actR_le (PairClass.inf S) (τ i) (hτ i) (γ₀ • P)
  have hge := PairClass.ht_le_ht_actR (PairClass.inf S) (τ i) (hτ i) (γ₀ • P)
  rw [PairClass.ht_inf] at hle hge
  rw [← h1] at hle hge
  have hQ1 : c₀ / cS S (τ i)⁻¹ ≤ X.ht (τ i • γ₀ • P) := by
    rw [div_le_iff₀ (hcS i)]
    linarith [mul_comm (cS S (τ i)⁻¹) (X.ht (τ i • γ₀ • P))]
  have hQ2 : X.ht (τ i • γ₀ • P) ≤ cS S (τ i) * T :=
    hge.trans (mul_le_mul_of_nonneg_left (hP p₀) (le_trans zero_le_one (one_le_cS _)))
  obtain ⟨γ, g, -, hg, hmem⟩ := hred i (c₀ / cS S (τ i)⁻¹) (cS S (τ i) * T) (hc i) _ hQ1 hQ2
  refine ⟨γ * γ₀, Set.mem_iUnion.mpr ⟨i, g • τ i • γ₀ • P, hmem, ?_⟩⟩
  have e : g • τ i • γ₀ • P = τ i • intSL F γ • γ₀ • P := by
    rw [← mul_smul g, ← hg, mul_smul]
  change (τ i)⁻¹ • g • τ i • γ₀ • P = (γ * γ₀) • P
  rw [e, inv_smul_smul, mul_smul]
  try rfl

/-- **MATH2 1.4(d)** for a subgroup `Γ` of finite index in `SL₂(𝓞_F)`. -/
theorem exists_compact_top_le_subgroup (hB : SBezout S) (hO : FiniteCusps S)
    (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex] (T : ℝ) :
    ∃ K : Set (X F), IsCompact K ∧ ∀ P : X F, (∀ p : PairClass S, p.ht P ≤ T) →
      ∃ γ : Γ, γ • P ∈ K := by
  obtain ⟨K, hK, h⟩ := exists_compact_top_le hB hO T
  exact ⟨spread Γ K, isCompact_spread Γ hK, fun P hP =>
    exists_subgroup_smul_mem_spread Γ (h P hP)⟩

/-! ### Finite volume -/

end

end ArtinKP.RC
end

section
-- module Solutions.Artin.KP.X2_Calc
/-! # WP-X2, file 2: calculus in the logarithmic chart

On `Coord F = InfinitePlace F → ℂ × ℝ` (coordinates `(x_w, t_w)`, `v_w = exp t_w`):

* `pd w k U` — partial derivative in the direction `bvec w k` (`k = 0, 1`: real and imaginary
  part of `x_w`; `k = 2`: `t_w`);
* `lapE U = ∑_w (-(e^{2t_w}(∂₀² + ∂₁²) + ∂₂²) U + 2 ∂₂ U)` — the Laplacian
  `∑_w (-v_w²(∂²_{x₁} + ∂²_{x₂} + ∂²_v) + v_w ∂_v)` in the chart;
* `gamE U W = ∑_w (e^{2t_w}(∂₀U ∂₀W + ∂₁U ∂₁W) + ∂₂U ∂₂W)` — the (bilinear) carré du champ
  `∑_w v_w² ∇_w U · ∇_w W`;
* `green_E`: `∫ ρ T ΔU = ∫ ρ Γ(T, U)` when one of `T`, `U` has compact support;
* Leibniz rules, compatibility with conjugation.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F]

/-- Decomposition of a vector of `E1` in the basis `e1`. -/
lemma e1_decomp (v : E1) : v = v.1.re • e1 0 + v.1.im • e1 1 + v.2 • e1 2 := by
  apply Prod.ext
  · apply Complex.ext <;> simp
  · simp

lemma clm_decomp (α : E1 →L[ℝ] ℂ) (v : E1) :
    α v = v.1.re * α (e1 0) + v.1.im * α (e1 1) + v.2 * α (e1 2) := by
  conv_lhs => rw [e1_decomp v]
  simp only [map_add, map_smul, Complex.real_smul]

/-! ### Regularity -/

/-! ### Algebraic rules -/

/-! ### The weights `ρ · a_k` -/

lemma Ls_apply (y : Coord F) : Ls y = ∑ w, (y w).2 := by
  simp [Ls]

/-! ### Green's identity on the chart -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Isom
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol
/-! # WP-X2, file 3: the group acts by isometries; the Laplacian commutes with it

* `Iso1 φ`: a smooth self-map of one factor (in the chart) whose derivative is conformal for the
  hyperbolic metric; translations and the inversion `Jmap` (the chart form of the Weyl element)
  are such, hence every element of `SL(2,ℂ)` acts by one (`mem_iso1`).
* `IsoHalf Φ`: a smooth self-map of `Coord F` preserving the carré du champ.
* `lapE_comp_of_iso`: a measure-preserving `IsoHalf` bijection with `IsoHalf` inverse commutes
  with the Laplacian.  The proof is weak: test against `C_c^∞`, use Green twice — no second
  derivative of the Möbius action is ever computed.
* On `X`: `X.Smooth`, `X.lap`, `X.gam`, and their invariance under `G∞ = SL(2,ℂ)^r`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

/-! ### One factor -/

lemma Iso1.trans (b : ℂ) : Iso1 (fun p : E1 => (p.1 + b, p.2)) where
  smooth := by fun_prop
  conf p α β := by
    have h0 : (fun p : E1 => (p.1 + b, p.2)) = fun p => p + (b, 0) := by
      funext p; apply Prod.ext <;> simp
    have : fderiv ℝ (fun p : E1 => (p.1 + b, p.2)) p = ContinuousLinearMap.id ℝ E1 := by
      rw [h0, fderiv_add_const]; exact fderiv_id'
    simp [this, acoef]

lemma rhoJ_pos (p : E1) : 0 < rhoJ p := by
  unfold rhoJ; positivity

lemma contDiff_rhoJ : ContDiff ℝ (⊤ : ℕ∞) rhoJ := by
  unfold rhoJ
  have h1 : ContDiff ℝ (⊤ : ℕ∞) fun p : E1 => p.1.re :=
    Complex.reCLM.contDiff.comp contDiff_fst
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun p : E1 => p.1.im :=
    Complex.imCLM.contDiff.comp contDiff_fst
  have h3 : ContDiff ℝ (⊤ : ℕ∞) fun p : E1 => Real.exp (2 * p.2) := by fun_prop
  exact ((h1.pow 2).add (h2.pow 2)).add h3

lemma contDiff_Jmap : ContDiff ℝ (⊤ : ℕ∞) Jmap := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) fun p : E1 => p.1.re :=
    Complex.reCLM.contDiff.comp contDiff_fst
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun p : E1 => p.1.im :=
    Complex.imCLM.contDiff.comp contDiff_fst
  have hi : ContDiff ℝ (⊤ : ℕ∞) fun p : E1 => (rhoJ p)⁻¹ :=
    contDiff_rhoJ.inv fun p => (rhoJ_pos p).ne'
  have hA : ContDiff ℝ (⊤ : ℕ∞) fun p : E1 => ((-p.1.re * (rhoJ p)⁻¹ : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (h1.neg.mul hi)
  have hB : ContDiff ℝ (⊤ : ℕ∞) fun p : E1 => ((p.1.im * (rhoJ p)⁻¹ : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (h2.mul hi)
  have hC : ContDiff ℝ (⊤ : ℕ∞) fun p : E1 => p.2 - Real.log (rhoJ p) :=
    contDiff_snd.sub (contDiff_rhoJ.log fun p => (rhoJ_pos p).ne')
  exact (hA.add (hB.mul contDiff_const)).prodMk hC

lemma fderiv_Jmap (p h : E1) :
    fderiv ℝ Jmap p h =
      (((-h.1.re * (rhoJ p)⁻¹ + p.1.re * sJ p h * ((rhoJ p)⁻¹) ^ 2 : ℝ) : ℂ) +
          ((h.1.im * (rhoJ p)⁻¹ - p.1.im * sJ p h * ((rhoJ p)⁻¹) ^ 2 : ℝ) : ℂ) * Complex.I,
        h.2 - sJ p h * (rhoJ p)⁻¹) := by
  have hne : rhoJ p ≠ 0 := (rhoJ_pos p).ne'
  have hre : HasFDerivAt (fun p : E1 => p.1.re)
      (Complex.reCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℝ)) p :=
    (Complex.reCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℝ)).hasFDerivAt
  have him : HasFDerivAt (fun p : E1 => p.1.im)
      (Complex.imCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℝ)) p :=
    (Complex.imCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℝ)).hasFDerivAt
  have hsnd : HasFDerivAt (fun p : E1 => p.2) (ContinuousLinearMap.snd ℝ ℂ ℝ) p :=
    (ContinuousLinearMap.snd ℝ ℂ ℝ).hasFDerivAt
  have hρ := ((hre.pow 2).add (him.pow 2)).add ((hsnd.const_mul 2).exp)
  have hρ' : HasFDerivAt rhoJ _ p := hρ
  have hI := (hasDerivAt_inv hne).comp_hasFDerivAt p hρ'
  have hA := (hre.neg).mul hI
  have hB := him.mul hI
  have hC := hsnd.sub (hρ'.log hne)
  have hx := (Complex.ofRealCLM.hasFDerivAt.comp p hA).add
    ((Complex.ofRealCLM.hasFDerivAt.comp p hB).mul_const Complex.I)
  have hJ : HasFDerivAt Jmap _ p := hx.prodMk hC
  rw [hJ.fderiv]
  apply Prod.ext
  · apply Complex.ext
    · simp [sJ]
      ring
    · simp [sJ]
      ring
  · simp [sJ]
    ring

lemma acoef_Jmap (k : Fin 3) (p : E1) :
    acoef k (Jmap p) = if k = 2 then 1 else Real.exp (2 * p.2) * ((rhoJ p)⁻¹) ^ 2 := by
  unfold acoef
  split_ifs
  · rfl
  · have : 2 * (Jmap p).2 = 2 * p.2 - 2 * Real.log (rhoJ p) := by
      simp [Jmap]; ring
    have h2 : Real.exp (2 * Real.log (rhoJ p)) = rhoJ p ^ 2 := by
      rw [two_mul, Real.exp_add, Real.exp_log (rhoJ_pos p)]; ring
    rw [this, Real.exp_sub, h2, div_eq_mul_inv, inv_pow]

lemma iso1_Jmap : Iso1 Jmap where
  smooth := contDiff_Jmap
  conf p α β := by
    have hα : ∀ (γ : E1 →L[ℝ] ℂ) (h : E1), γ (fderiv ℝ Jmap p h) =
        ((-h.1.re * (rhoJ p)⁻¹ + p.1.re * sJ p h * ((rhoJ p)⁻¹) ^ 2 : ℝ) : ℂ) * γ (e1 0) +
        ((h.1.im * (rhoJ p)⁻¹ - p.1.im * sJ p h * ((rhoJ p)⁻¹) ^ 2 : ℝ) : ℂ) * γ (e1 1) +
        ((h.2 - sJ p h * (rhoJ p)⁻¹ : ℝ) : ℂ) * γ (e1 2) := by
      intro γ h
      have hr : ∀ a b : ℝ, ((a : ℂ) + (b : ℂ) * Complex.I).re = a := fun a b => by simp
      have hi : ∀ a b : ℝ, ((a : ℂ) + (b : ℂ) * Complex.I).im = b := fun a b => by simp
      rw [clm_decomp γ, fderiv_Jmap]
      simp only [hr, hi]
    simp only [hα, Fin.sum_univ_three, acoef_Jmap]
    have hE : Real.exp (2 * p.2) = rhoJ p - p.1.re ^ 2 - p.1.im ^ 2 := by
      unfold rhoJ; ring
    have hne : (rhoJ p : ℂ) ≠ 0 := by exact_mod_cast (rhoJ_pos p).ne'
    simp only [acoef, sJ, e1_zero, e1_one, e1_two, hE]
    generalize α (1, 0) = a0
    generalize α (Complex.I, 0) = a1
    generalize α (0, 1) = a2
    generalize β (1, 0) = b0
    generalize β (Complex.I, 0) = b1
    generalize β (0, 1) = b2
    generalize rhoJ p = r at hne ⊢
    generalize p.1.re = x1
    generalize p.1.im = x2
    simp
    field_simp
    ring

/-! ### Every element of `SL(2,ℂ)` acts by an `Iso1` -/

lemma nMat_mem_iso1 (b : ℂ) : nMat b ∈ iso1Submonoid := by
  refine ⟨fun p => (p.1 + b, p.2), Iso1.trans b, fun p => ?_⟩
  have h := nMat_smul b (chart1 p)
  apply H3.ext
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

lemma wMat_mem_iso1 : wMat ∈ iso1Submonoid := by
  refine ⟨Jmap, iso1_Jmap, fun p => ?_⟩
  have h := wMat_smul (chart1 p)
  have hn : nsq (chart1 p).coe = rhoJ p := by
    simp only [nsq, rhoJ, H3.coe_eq, chart1_x, chart1_v, Complex.normSq_apply]
    rw [← Real.exp_nat_mul]
    push_cast
    ring_nf
  have hpos := rhoJ_pos p
  apply H3.ext
  · have h1 : (wMat • chart1 p).x = -conj (inv3 (chart1 p).coe).1 := by
      have := congrArg Prod.fst h; exact this
    rw [h1, inv3_fst, hn]
    change _ = (Jmap p).1
    apply Complex.ext
    · simp [Jmap, H3.coe_eq, Complex.div_re, Complex.normSq_apply]
      field_simp
    · simp [Jmap, H3.coe_eq, Complex.div_im, Complex.normSq_apply]
      field_simp
  · have h2 : (wMat • chart1 p).v = (inv3 (chart1 p).coe).2 := by
      have := congrArg Prod.snd h; exact this
    rw [h2, inv3_snd, hn]
    change _ = Real.exp (Jmap p).2
    simp only [Jmap, H3.coe_eq, chart1_v]
    rw [Real.exp_sub, Real.exp_log hpos]

lemma wMat_inv_eq : wMat⁻¹ = wMat * wMat * wMat := by
  apply Subtype.ext
  rw [wMat_inv_coe]
  simp only [Matrix.SpecialLinearGroup.coe_mul, wMat_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **Every element of `SL(2,ℂ)` acts in the chart by a conformal smooth map.** -/
theorem mem_iso1 (g : SL(2, ℂ)) : g ∈ iso1Submonoid := by
  have hn := nMat_mem_iso1
  have hw := wMat_mem_iso1
  have hwi : wMat⁻¹ ∈ iso1Submonoid := by
    rw [wMat_inv_eq]
    exact iso1Submonoid.mul_mem (iso1Submonoid.mul_mem hw hw) hw
  have key : ∀ g : SL(2, ℂ), g 1 0 ≠ 0 → g ∈ iso1Submonoid := by
    intro g hc
    rw [bruhat_of_ne hc]
    exact iso1Submonoid.mul_mem (iso1Submonoid.mul_mem (iso1Submonoid.mul_mem
      (iso1Submonoid.mul_mem (iso1Submonoid.mul_mem
      (iso1Submonoid.mul_mem (hn _) (hn _)) hwi) (hn _)) hw) (hn _)) (hn _)
  by_cases hc : g 1 0 = 0
  · have h1 : (g * wMat) 1 0 ≠ 0 := by
      have hd := det_eq g
      have : (g * wMat) 1 0 = g 1 1 := by
        rw [Matrix.SpecialLinearGroup.coe_mul, wMat_coe]
        simp [Matrix.mul_apply, Fin.sum_univ_two]
      rw [this]
      intro h
      rw [hc, h] at hd
      simp at hd
    have : g = (g * wMat) * wMat⁻¹ := by group
    rw [this]
    exact iso1Submonoid.mul_mem (key _ h1) hwi
  · exact key g hc

/-! ### Isometries of the chart -/

variable {F : Type*} [Field F] [NumberField F]

/-- A product of one-factor conformal maps is an isometry of the chart. -/
theorem isoHalf_pi {φ : InfinitePlace F → E1 → E1} (h : ∀ w, Iso1 (φ w)) :
    IsoHalf (fun (y : Coord F) w => φ w (y w)) where
  smooth := contDiff_pi.2 fun w => (h w).smooth.comp (contDiff_apply ℝ E1 w)
  gam_comp U W y hU hW := by
    show gamE (fun z => U (fun w => φ w (z w))) (fun z => W (fun w => φ w (z w))) y =
      gamE U W (fun w => φ w (y w))
    have hΦ : HasFDerivAt (fun (y : Coord F) w => φ w (y w)) (ContinuousLinearMap.pi fun w =>
        (fderiv ℝ (φ w) (y w)).comp (ContinuousLinearMap.proj w)) y :=
      hasFDerivAt_pi.2 fun w =>
        (((h w).smooth.differentiable (by simp) (y w)).hasFDerivAt).comp y
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : InfinitePlace F => E1) w).hasFDerivAt
    have key : ∀ (V : Coord F → ℂ), DifferentiableAt ℝ V (fun w => φ w (y w)) → ∀ w k,
        pd w k (fun z => V (fun w => φ w (z w))) y =
          ((fderiv ℝ V (fun w => φ w (y w))).comp
            (ContinuousLinearMap.single ℝ (fun _ : InfinitePlace F => E1) w))
            (fderiv ℝ (φ w) (y w) (e1 k)) := by
      intro V hV w k
      unfold pd
      have hcomp := (hV.hasFDerivAt.comp y hΦ).fderiv
      rw [show (fun z : Coord F => V (fun w => φ w (z w))) =
        V ∘ (fun (y : Coord F) w => φ w (y w)) from rfl, hcomp]
      simp only [ContinuousLinearMap.comp_apply]
      congr 1
      funext w'
      by_cases hw : w' = w
      · subst hw
        simp [bvec]
      · simp [bvec, Pi.single_apply, hw]
    unfold gamE
    refine Finset.sum_congr rfl fun w _ => ?_
    simp_rw [key U hU w, key W hW w]
    exact (h w).conf (y w) _ _

/-! ### The action of `G∞` in the chart -/

lemma chart_actE (g : Ginf F) (y : Coord F) : chart F (actE g y) = g • chart F y := by
  simp [actE]

theorem isoHalf_actE (g : Ginf F) : IsoHalf (actE g) := by
  choose φ hφ hg using fun w => mem_iso1 (g w)
  have : actE g = fun (y : Coord F) w => φ w (y w) := by
    funext y w
    change chart1.symm (g w • chart1 (y w)) = _
    rw [hg w, Homeomorph.symm_apply_apply]
  rw [this]
  exact isoHalf_pi hφ

/-! ### Calculus on `X` -/

lemma X.Smooth.comp_Ginf {u : X F → ℂ} (hu : X.Smooth u) (g : Ginf F) :
    X.Smooth fun P => u (g • P) := by
  unfold X.Smooth
  have : (fun y => u (g • chart F y)) = fun y => (fun z => u (chart F z)) (actE g y) := by
    funext y; simp only [chart_actE]
  rw [this]
  have hu' : ContDiff ℝ (⊤ : ℕ∞) fun y => u (chart F y) := hu
  exact hu'.comp (isoHalf_actE g).smooth

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Core
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup
/-! # WP-X2, file 4: Green's identity on `X` and averaging over `Γ`

* `X.green`: `∫_X φ Δu = ∫_X Γ(φ, u)` when `φ` or `u` has compact support;
* `X.avg Γ φ = ∑_{γ ∈ Γ} φ ∘ γ` for compactly supported `φ`: locally finite, smooth,
  `Δ (avg φ) = avg (Δ φ)`, `Γ(avg φ, u) = avg Γ(φ, u)` for `Γ`-invariant `u`;
* unfolding `∫ η · avg φ · g = ∫_X φ g` for invariant `g` (`integral_avg_mul`);
* **Green's identity on `Γ \ X`** for `w = avg φ` and any smooth invariant `u`
  (`X.qgreen`, `X.qgreen'`): `∫ η w Δu = ∫ η Γ(w, u) = ∫ η u Δw`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F]

/-! ### Measure-theoretic instances -/

/-! ### Calculus on `X`: basic rules -/

lemma X.Smooth.sum {ι : Type*} (s : Finset ι) {u : ι → X F → ℂ} (hu : ∀ i ∈ s, X.Smooth (u i)) :
    X.Smooth fun P => ∑ i ∈ s, u i P := ContDiff.sum fun i hi => (hu i hi).contDiff

lemma eventuallyEq_chart {β : Type*} {u w : X F → β} {P : X F} (h : u =ᶠ[𝓝 P] w) :
    (fun y => u (chart F y)) =ᶠ[𝓝 ((chart F).symm P)] fun y => w (chart F y) := by
  have ht : Tendsto (chart F) (𝓝 ((chart F).symm P)) (𝓝 P) := by
    have := (chart F).continuous.continuousAt (x := (chart F).symm P)
    rwa [ContinuousAt, Homeomorph.apply_symm_apply] at this
  exact ht.eventually h

/-! ### Invariance -/

variable {Γ : Subgroup (SL(2, 𝓞 F))}

/-! ### Local finiteness and averaging -/

/-- Near any point, only finitely many `γ ∈ Γ` move points into a given compact set. -/
theorem exists_finset_nhds (Γ : Subgroup (SL(2, 𝓞 F))) {K : Set (X F)} (hK : IsCompact K)
    (P₀ : X F) : ∃ R : Finset Γ, ∃ N ∈ 𝓝 P₀, ∀ P ∈ N, ∀ γ : Γ, γ • P ∈ K → γ ∈ R := by
  set C : Set (X F) := (chart F).symm ⁻¹' Metric.closedBall ((chart F).symm P₀) 1 with hC
  have hCc : IsCompact C := (chart F).symm.isCompact_preimage.2 (isCompact_closedBall _ _)
  have hCn : C ∈ 𝓝 P₀ :=
    (chart F).symm.continuous.continuousAt.preimage_mem_nhds
      (Metric.closedBall_mem_nhds _ one_pos)
  have hfin := finite_return_of_isCompact (hCc.union hK)
  have hfin' : {γ : Γ | ∃ P ∈ C ∪ K, γ • P ∈ C ∪ K}.Finite :=
    hfin.preimage (f := fun γ : Γ => (γ : SL(2, 𝓞 F))) Subtype.val_injective.injOn
  exact ⟨hfin'.toFinset, C, hCn, fun P hP γ hγ =>
    hfin'.mem_toFinset.mpr ⟨P, Or.inl hP, Or.inr hγ⟩⟩

lemma exists_finset_avg (Γ : Subgroup (SL(2, 𝓞 F))) {φ : X F → ℂ} (hc : HasCompactSupport φ)
    (P₀ : X F) : ∃ R : Finset Γ, ∃ N ∈ 𝓝 P₀, ∀ P ∈ N, ∀ γ : Γ, γ ∉ R → γ • P ∉ tsupport φ := by
  obtain ⟨R, N, hN, h⟩ := exists_finset_nhds Γ hc P₀
  exact ⟨R, N, hN, fun P hP γ hγ hmem => hγ (h P hP γ hmem)⟩

lemma X.avg_eventuallyEq (Γ : Subgroup (SL(2, 𝓞 F))) {φ : X F → ℂ} (hc : HasCompactSupport φ)
    (P₀ : X F) : ∃ R : Finset Γ, (∀ γ : Γ, γ ∉ R → γ • P₀ ∉ tsupport φ) ∧
      X.avg Γ φ =ᶠ[𝓝 P₀] fun P => ∑ γ ∈ R, φ (γ • P) := by
  obtain ⟨R, N, hN, h⟩ := exists_finset_avg Γ hc P₀
  refine ⟨R, h P₀ (mem_of_mem_nhds hN), ?_⟩
  filter_upwards [hN] with P hP
  exact tsum_eq_sum fun γ hγ => image_eq_zero_of_notMem_tsupport (h P hP γ hγ)

lemma X.Smooth.comp_gamma {φ : X F → ℂ} (hφ : X.Smooth φ) (γ : Γ) :
    X.Smooth fun P => φ (γ • P) := hφ.comp_Ginf (gin (γ : SL(2, 𝓞 F)))

lemma X.smooth_avg {φ : X F → ℂ} (hφ : X.Smooth φ) (hc : HasCompactSupport φ) :
    X.Smooth (X.avg Γ φ) := by
  unfold X.Smooth
  rw [contDiff_iff_contDiffAt]
  intro y
  obtain ⟨R, -, hR⟩ := X.avg_eventuallyEq Γ hc (chart F y)
  have h1 := eventuallyEq_chart hR
  rw [Homeomorph.symm_apply_apply] at h1
  have h2 : X.Smooth fun P => ∑ γ ∈ R, φ (γ • P) := X.Smooth.sum R fun γ _ => hφ.comp_gamma γ
  exact h2.contDiff.contDiffAt.congr_of_eventuallyEq h1

/-! ### Unfolding -/

/-! ### Green's identity on the quotient -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Weak
/-! # WP-X2, file 6: cut-offs; classical solutions are weak solutions in `H¹`

* `X.isClosed_saturation`: `Γ · K` is closed for compact `K`;
* `X.mem_core_of_support`: a smooth `Γ`-invariant function whose support lies in `Γ · K`,
  `K` compact, belongs to the core (it is `∑_γ φ ∘ γ` with `φ = ψ w / ∑_γ ψ ∘ γ`);
* `X.integrable_pou_mul`: `η · h` is integrable for `h` continuous, invariant, supported in
  `Γ · K`;
* `X.exists_weakSol`: **the height cut-off lemma** (MATH2 §1.6).  A smooth `Γ`-invariant `u`
  with `u ∈ L²(Γ\X)` and `Δu = λu + f` pointwise, `f ∈ L²(Γ\X)`, lies in `H¹(Γ\X)` and satisfies
  the weak equation `𝔇(u', u) − λ⟪u', u⟫ = ⟪u', f⟫` against all `u' ∈ H¹`, provided there are
  cut-offs `χ_n` (smooth, invariant, `0 ≤ χ_n ≤ 1`, compact support modulo `Γ`, `χ_n → 1`
  pointwise, `∑_w v_w²|∇_w χ_n|² ≤ ε_n → 0`).  Finite energy of `u` is a conclusion, not a
  hypothesis (IMS localisation formula).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F] {Γ : Subgroup (SL(2, 𝓞 F))}

/-! ### Saturations of compact sets -/

/-- `Γ · K` is closed for compact `K`. -/
theorem X.isClosed_saturation (Γ : Subgroup (SL(2, 𝓞 F))) {K : Set (X F)} (hK : IsCompact K) :
    IsClosed {P : X F | ∃ γ : Γ, γ • P ∈ K} := by
  have h : {P : X F | ∃ γ : Γ, γ • P ∈ K} = ⋃ γ : Γ, (fun P : X F => γ • P) ⁻¹' K := by
    ext P; simp
  rw [h]
  refine LocallyFinite.isClosed_iUnion ?_ fun γ => hK.isClosed.preimage (continuous_const_smul γ)
  intro P₀
  obtain ⟨R, N, hN, hR⟩ := exists_finset_nhds Γ hK P₀
  refine ⟨N, hN, R.finite_toSet.subset ?_⟩
  rintro γ ⟨P, hP, hPN⟩
  exact hR P hPN γ hP

lemma X.tsupport_subset_saturation {β : Type*} [Zero β] {h : X F → β} {K : Set (X F)}
    (hK : IsCompact K) (hsupp : ∀ P, h P ≠ 0 → ∃ γ : Γ, γ • P ∈ K) :
    tsupport h ⊆ {P : X F | ∃ γ : Γ, γ • P ∈ K} :=
  closure_minimal (fun P hP => hsupp P hP) (X.isClosed_saturation Γ hK)

/-! ### A bump function positive on a compact set -/

lemma exists_bump {K : Set (X F)} (hK : IsCompact K) :
    ∃ ψ : X F → ℝ, X.Smooth (fun P => (ψ P : ℂ)) ∧ HasCompactSupport ψ ∧ (∀ P, 0 ≤ ψ P) ∧
      ∀ P ∈ K, 0 < ψ P := by
  have hK' : IsCompact ((chart F).symm '' K) := hK.image (chart F).symm.continuous
  obtain ⟨R, hR⟩ := hK'.isBounded.subset_closedBall (0 : Coord F)
  let f : ContDiffBump (0 : Coord F) :=
    ⟨max R 0 + 1, max R 0 + 2, by positivity, by linarith⟩
  refine ⟨fun P => f ((chart F).symm P), ?_, ?_, fun P => f.nonneg, fun P hP => ?_⟩
  · unfold X.Smooth
    simp only [Homeomorph.symm_apply_apply]
    exact Complex.ofRealCLM.contDiff.comp f.contDiff
  · exact f.hasCompactSupport.comp_isClosedEmbedding (chart F).symm.isClosedEmbedding
  · have h1 : (chart F).symm P ∈ Metric.closedBall (0 : Coord F) R := hR ⟨P, hP, rfl⟩
    have h2 : (chart F).symm P ∈ Metric.closedBall (0 : Coord F) f.rIn :=
      Metric.closedBall_subset_closedBall (by
        change R ≤ max R 0 + 1
        linarith [le_max_left R 0]) h1
    show 0 < f ((chart F).symm P)
    rw [f.one_of_mem_closedBall h2]
    exact one_pos

/-- A smooth compactly supported `ψ` whose `Γ`-average does not vanish on `Γ · K`. -/
lemma exists_bump_avg (Γ : Subgroup (SL(2, 𝓞 F))) {K : Set (X F)} (hK : IsCompact K) :
    ∃ ψ : X F → ℂ, X.Smooth ψ ∧ HasCompactSupport ψ ∧
      ∀ P, (∃ γ : Γ, γ • P ∈ K) → X.avg Γ ψ P ≠ 0 := by
  obtain ⟨ψ, hψs, hψc, hψ0, hψK⟩ := exists_bump hK
  have hc : HasCompactSupport fun P => (ψ P : ℂ) := hψc.comp_left Complex.ofReal_zero
  refine ⟨fun P => (ψ P : ℂ), hψs, hc, ?_⟩
  rintro P ⟨γ₀, hγ₀⟩
  have hsum : Summable fun γ : Γ => ψ (γ • P) :=
    Complex.summable_ofReal.1 (X.summable_comp_smul_of_hasCompactSupport Γ hc P)
  have h1 : X.avg Γ (fun P => (ψ P : ℂ)) P = ((∑' γ : Γ, ψ (γ • P) : ℝ) : ℂ) := by
    unfold X.avg
    rw [Complex.ofReal_tsum]
  rw [h1]
  have h2 : 0 < ∑' γ : Γ, ψ (γ • P) :=
    lt_of_lt_of_le (hψK _ hγ₀) (hsum.le_tsum γ₀ fun γ _ => hψ0 _)
  exact_mod_cast h2.ne'

/-! ### Invariant functions supported in `Γ · K` are averages -/

lemma X.rep_hasCompactSupport {ψ : X F → ℂ} (hψc : HasCompactSupport ψ) (h : X F → ℂ) :
    HasCompactSupport (X.rep Γ ψ h) :=
  hψc.mono fun P hP => by
    intro h0
    apply hP
    simp [X.rep, show ψ P = 0 from h0]

lemma X.avg_rep {ψ h : X F → ℂ} (hinv : X.IsInv Γ h)
    (hne : ∀ P, h P ≠ 0 → X.avg Γ ψ P ≠ 0) : X.avg Γ (X.rep Γ ψ h) = h := by
  funext P
  have h1 : ∀ γ : Γ, X.rep Γ ψ h (γ • P) = ψ (γ • P) * (h P / X.avg Γ ψ P) := by
    intro γ
    unfold X.rep
    rw [hinv γ P, X.avg_inv Γ ψ γ P, mul_div_assoc]
  unfold X.avg
  simp_rw [h1]
  rw [tsum_mul_right]
  by_cases h0 : h P = 0
  · simp [h0]
  · have h2 : X.avg Γ ψ P ≠ 0 := hne P h0
    show X.avg Γ ψ P * (h P / X.avg Γ ψ P) = h P
    field_simp

lemma X.rep_contDiff {ψ h : X F → ℂ} (hψ : X.Smooth ψ) (hψc : HasCompactSupport ψ)
    {n : WithTop ℕ∞} (hn : n ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
    (hh : ContDiff ℝ n fun y => h (chart F y))
    (hne : ∀ P ∈ tsupport h, X.avg Γ ψ P ≠ 0) :
    ContDiff ℝ n fun y => X.rep Γ ψ h (chart F y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : chart F y ∈ tsupport h
  · have h1 : ContDiffAt ℝ n (fun y => ψ (chart F y) * h (chart F y)) y :=
      ((hψ.contDiff.of_le hn).mul hh).contDiffAt
    have h2 : ContDiffAt ℝ n (fun y => X.avg Γ ψ (chart F y)) y :=
      ((X.smooth_avg (Γ := Γ) hψ hψc).contDiff.of_le hn).contDiffAt
    exact (h1.mul (h2.inv (hne _ hy))).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun z => by simp [X.rep, div_eq_mul_inv])
  · have h0 : h =ᶠ[𝓝 (chart F y)] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.1 hy
    have h1 : X.rep Γ ψ h =ᶠ[𝓝 (chart F y)] fun _ => 0 := by
      filter_upwards [h0] with P hP
      simp [X.rep, hP]
    have h2 := eventuallyEq_chart h1
    rw [Homeomorph.symm_apply_apply] at h2
    exact contDiffAt_const.congr_of_eventuallyEq h2

/-- **Characterisation of the core**: a smooth `Γ`-invariant function with support in `Γ · K`,
`K` compact, is in the core. -/
theorem X.mem_core_of_support {w : X F → ℂ} (hw : X.Smooth w) (hinv : X.IsInv Γ w)
    {K : Set (X F)} (hK : IsCompact K) (hsupp : ∀ P, w P ≠ 0 → ∃ γ : Γ, γ • P ∈ K) :
    w ∈ X.core Γ := by
  obtain ⟨ψ, hψ, hψc, hψK⟩ := exists_bump_avg Γ hK
  refine ⟨X.rep Γ ψ w, ?_, X.rep_hasCompactSupport hψc w, ?_⟩
  · exact X.rep_contDiff hψ hψc le_rfl hw
      fun P hP => hψK P (X.tsupport_subset_saturation hK hsupp hP)
  · exact (X.avg_rep hinv fun P hP => hψK P (hsupp P hP)).symm

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Eigen
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup
/-! # WP-X2, file 8: functions of the height

For `G : ℝ → ℂ` smooth, the function `P ↦ G (log (ht P))` on `X` is smooth and
`Δ (G ∘ log ht) = r · (-G'' + 2 G') ∘ log ht`, `∑_w v_w² |∇_w (G ∘ log ht)|² = r · |G'|² ∘ log ht`
(`r` = number of infinite places; in the variable `h = ht` this is `r(-(h∂_h)² + 2h∂_h)`).
The same holds for every pair height `pairHt c d`, `(c, d) ≠ 0`, by invariance under `SL(2,F)`.
In particular `ht^s` and `pairHt c d ^ s` are eigenfunctions with eigenvalue `r · s(2 - s)`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F]

/-- `log ht` is `∑_w t_w` in the chart. -/
lemma log_ht_chart (y : Coord F) : Real.log (X.ht (chart F y)) = Ls y := by
  unfold X.ht
  rw [Real.log_prod fun w _ => (X.v_pos _ w).ne', Ls_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [chart_v, Real.log_exp]

lemma contDiff_comp_Ls {G : ℝ → ℂ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    ContDiff ℝ (⊤ : ℕ∞) fun y : Coord F => G (Ls y) := hG.comp (Ls (F := F)).contDiff

/-! ### Functions of the height on `X` -/

/-- A smooth function of `log ht` is smooth on `X`. -/
theorem X.smooth_comp_log_ht {G : ℝ → ℂ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    X.Smooth fun P : X F => G (Real.log (X.ht P)) := by
  unfold X.Smooth
  simp_rw [log_ht_chart]
  exact contDiff_comp_Ls hG

/-! ### Invariance: pair heights -/

/-- A matrix of `SL(2,F)` with prescribed nonzero bottom row. -/
lemma exists_bottom_row {c d : F} (h : c ≠ 0 ∨ d ≠ 0) :
    ∃ γ : SL(2, F), γ 1 0 = c ∧ γ 1 1 = d := by
  by_cases hc : c = 0
  · have hd : d ≠ 0 := by simpa [hc] using h
    refine ⟨⟨!![d⁻¹, 0; 0, d], by simp [Matrix.det_fin_two, hd]⟩, ?_, ?_⟩
    · simp [hc]
    · simp
  · refine ⟨⟨!![0, -c⁻¹; c, d], by simp [Matrix.det_fin_two, hc]⟩, ?_, ?_⟩ <;> simp

/-- A smooth function of the logarithm of a pair height is smooth. -/
theorem X.smooth_comp_log_pairHt {G : ℝ → ℂ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) {c d : F}
    (h : c ≠ 0 ∨ d ≠ 0) : X.Smooth fun P : X F => G (Real.log (X.pairHt c d P)) := by
  obtain ⟨γ, rfl, rfl⟩ := exists_bottom_row h
  simp_rw [← X.ht_smul]
  exact (X.smooth_comp_log_ht hG).comp_Ginf (sigma F γ)

/-! ### Eigenfunctions -/

lemma contDiff_cexp_mul (s : ℂ) : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => Complex.exp (s * (t : ℂ)) :=
  Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.RC_Cutoff
attribute [-simp] _root_.ArtinKP.RO.rowClassEquiv_mk
/-! # WP-RC, file 3: the height cut-offs `χ_n` of MATH2 §1.6

`chi S n P = 1 − ∑_{p ∈ PairClass S} ϑ(log ht_p(P) / (n+1))`, `ϑ = 0` on `(−∞,1]`, `ϑ = 1` on `[2,∞)`.
Near every point at most one fixed term is nonzero (`exists_single`: local finiteness from the
summable majorant, uniqueness from (H1)), so `χ_n` is smooth, `0 ≤ χ_n ≤ 1`, and
`∑_w v_w²|∇_w χ_n|² = r ϑ'(…)²/(n+1)² ≤ r C²/(n+1)²` by `X.grad2_comp_log_pairHt` ((H2) in exact form).
`χ_n` is `SL₂(𝓞_F)`-invariant, `χ_n → 1` pointwise (eventually `= 1`), and `χ_n ≠ 0` forces all
heights `≤ e^{2(n+1)}`, a set that is compact modulo `Γ` (MATH2 1.4(d)).

* `exists_cutoffs`: the sequence, in exactly the form of the hypotheses of `X.exists_weakSol`.
* `exists_weakSol`: `X.exists_weakSol` with the cut-off hypotheses discharged.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Module Filter

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.RC

open ArtinKP.X ArtinKP.B1

noncomputable section

/-! ### The profile `ϑ` -/

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {S : Finset (FinitePlace F)}

/-! ### Local finiteness -/

/-- Near every point all but finitely many classes have height `< 1`. -/
lemma exists_nhds_finset (S : Finset (FinitePlace F)) (P₀ : X F) :
    ∃ A : Finset (PairClass S), ∀ᶠ P in 𝓝 P₀, ∀ p ∉ A, p.ht P < 1 := by
  classical
  set K : Set (X F) := chart F '' Metric.closedBall ((chart F).symm P₀) 1 with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).image (chart F).continuous
  have hKn : K ∈ 𝓝 P₀ := by
    have := (chart F).isOpenMap.image_mem_nhds
      (Metric.closedBall_mem_nhds ((chart F).symm P₀) one_pos)
    rwa [Homeomorph.apply_symm_apply] at this
  obtain ⟨u, hu, hle⟩ := PairClass.exists_summable_majorant S hKc
    (σ₁ := 3) (σ₂ := 3) (by norm_num) le_rfl
  have hfin : {p : PairClass S | ¬ u p < 1}.Finite :=
    hu.tendsto_cofinite_zero.eventually (gt_mem_nhds one_pos)
  refine ⟨hfin.toFinset, ?_⟩
  filter_upwards [hKn] with P hP p hp
  have hup : u p < 1 := by
    by_contra h
    exact hp (hfin.mem_toFinset.mpr h)
  by_contra h
  have h1 : (1 : ℝ) ≤ p.ht P ^ (3 : ℝ) := Real.one_le_rpow (not_lt.mp h) (by norm_num)
  linarith [hle P hP 3 ⟨le_rfl, le_rfl⟩ p]

/-! ### The cut-offs -/

/-! ### Smoothness and the gradient bound -/

/-! ### The cut-off sequence for `X.exists_weakSol` -/

end

end ArtinKP.RC
end

section
-- module Solutions.Artin.KP.C5_PE
attribute [-simp] _root_.ArtinKP.RO.rowClassEquiv_mk _root_.ArtinKP.RO.rowPair_c _root_.ArtinKP.RO.rowPair_d
/-! # WP-C5, file 1: pseudo-Eisenstein series with a profile vanishing below height 2

For weights `a : PairClass S → ℂ` and a profile `g : ℝ → ℂ` (a function of `τ = log ht`),
`pe S a g P = ∑_p a(p) · g(log ht_p(P))`.  If `g` vanishes for `τ < log 2` (`VanishLow g`) the sum
is **locally a single term**, uniformly in `a` and `g` (`pe_eventually`; (H1) of MATH2 §0.1):
no convergence question arises.  Hence, for smooth `g`:

* `smooth_pe`, `lap_pe : Δ (pe a g) = pe a (Lg g)`, `Lg g = r(−g'' + 2g')`;
* `pe_smul`: invariance under `γ` when `a(pγ) = a(p)`;
* `norm_pe_le`, linearity in `a` and in `g`;
* if moreover `g` vanishes for `τ > log 3` (`VanishHigh g`), the support of `pe a g` lies in
  `Γ · K`, `K` compact (`exists_compact_pe`), so `pe a g ∈ X.core Γ` (`pe_mem_core`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ArtinKP.C5

open ArtinKP.X ArtinKP.B1

noncomputable section

/-! ### Profiles -/

lemma VanishLow.deriv {g : ℝ → ℂ} (hg : VanishLow g) : VanishLow (deriv g) := by
  intro τ hτ
  have h : g =ᶠ[𝓝 τ] fun _ => (0 : ℂ) := by
    filter_upwards [Iio_mem_nhds hτ] with t ht using hg t ht
  rw [h.deriv_eq]
  simp

lemma VanishHigh.deriv {g : ℝ → ℂ} (hg : VanishHigh g) : VanishHigh (deriv g) := by
  intro τ hτ
  have h : g =ᶠ[𝓝 τ] fun _ => (0 : ℂ) := by
    filter_upwards [Ioi_mem_nhds hτ] with t ht using hg t ht
  rw [h.deriv_eq]
  simp

lemma contDiff_shift {g : ℝ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (ℓ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (shift g ℓ) :=
  hg.comp (contDiff_id.sub contDiff_const)

variable {F : Type*} [Field F] [NumberField F]

variable [IsTotallyComplex F] {S : Finset (FinitePlace F)}

/-! ### Locally a single term -/

/-- **(H1), local form**: near every point there is one class outside of which all heights are
`< 3/2`. -/
lemma exists_single (S : Finset (FinitePlace F)) (P₀ : X F) :
    ∃ p₁ : PairClass S, ∀ᶠ P in 𝓝 P₀, ∀ p : PairClass S, p ≠ p₁ → p.ht P < 3 / 2 := by
  by_cases h : ∃ p₁ : PairClass S, 1 < p₁.ht P₀
  · obtain ⟨p₁, hp₁⟩ := h
    refine ⟨p₁, ?_⟩
    filter_upwards [p₁.continuous_ht.continuousAt.eventually (lt_mem_nhds hp₁)] with P hP p hp
    by_contra h2
    exact hp (PairClass.eq_of_one_lt_ht (by linarith) hP)
  · push Not at h
    obtain ⟨A, hA⟩ := RC.exists_nhds_finset S P₀
    refine ⟨PairClass.inf S, ?_⟩
    have hev : ∀ᶠ P in 𝓝 P₀, ∀ p ∈ A, p.ht P < 3 / 2 :=
      (Filter.eventually_all_finset A).mpr fun p _ =>
        p.continuous_ht.continuousAt.eventually
          (gt_mem_nhds (lt_of_le_of_lt (h p) (by norm_num)))
    filter_upwards [hA, hev] with P h1 h2 p _
    by_cases hp : p ∈ A
    · exact h2 p hp
    · exact lt_trans (h1 p hp) (by norm_num)

lemma log_ht_lt {p : PairClass S} {P : X F} (h : p.ht P < 3 / 2) :
    Real.log (p.ht P) < Real.log 2 :=
  Real.log_lt_log (p.ht_pos P) (by linarith)

lemma pe_term_eq_zero {a : PairClass S → ℂ} {g : ℝ → ℂ} (hg : VanishLow g) {P : X F}
    {p : PairClass S} (h : p.ht P < 3 / 2) : a p * g (Real.log (p.ht P)) = 0 := by
  rw [hg _ (log_ht_lt h), mul_zero]

lemma pe_eq_single {a : PairClass S → ℂ} {g : ℝ → ℂ} (hg : VanishLow g) {P : X F}
    {p₁ : PairClass S} (h : ∀ p : PairClass S, p ≠ p₁ → p.ht P < 3 / 2) :
    pe S a g P = a p₁ * g (Real.log (p₁.ht P)) := by
  unfold pe
  exact tsum_eq_single p₁ fun p hp => pe_term_eq_zero hg (h p hp)

/-- **Locally a single term**, uniformly in the weights and the profile. -/
lemma pe_eventually (S : Finset (FinitePlace F)) (P₀ : X F) :
    ∃ p₁ : PairClass S, ∀ᶠ P in 𝓝 P₀, ∀ (a : PairClass S → ℂ) (g : ℝ → ℂ), VanishLow g →
      pe S a g P = a p₁ * g (Real.log (p₁.ht P)) := by
  obtain ⟨p₁, h⟩ := exists_single S P₀
  exact ⟨p₁, h.mono fun P hP a g hg => pe_eq_single hg hP⟩

/-! ### Algebra -/

/-- Invariance under `γ ∈ SL₂(𝓞_F)` fixing the weights. -/
lemma pe_smul {a : PairClass S → ℂ} (g : ℝ → ℂ) {γ : SL(2, 𝓞 F)}
    (ha : ∀ p : PairClass S, a (p.act γ) = a p) (P : X F) : pe S a g (γ • P) = pe S a g P := by
  unfold pe
  have e := (PairClass.actEquiv (S := S) γ).tsum_eq
    fun p : PairClass S => a p * g (Real.log (p.ht P))
  rw [← e]
  refine tsum_congr fun p => ?_
  change _ = a (p.act γ) * g (Real.log ((p.act γ).ht P))
  rw [PairClass.ht_act, ha]

/-! ### Smoothness and the Laplacian -/

lemma term_eq_shift (g : ℝ → ℂ) (p : PairClass S) (P : X F) :
    g (Real.log (p.ht P)) =
      shift g (Real.log (X.sNorm S p.out.c p.out.d)) (Real.log (X.pairHt p.out.c p.out.d P)) := by
  unfold shift
  rw [PairClass.ht_eq_out]
  unfold X.sHt
  rw [Real.log_div (X.pairHt_pos p.out.ne_zero P).ne' (X.sNorm_pos S p.out.ne_zero).ne']

lemma pe_eventuallyEq (S : Finset (FinitePlace F)) (a : PairClass S → ℂ) {g : ℝ → ℂ}
    (hg : VanishLow g) (P₀ : X F) :
    ∃ p₁ : PairClass S, (∀ (a' : PairClass S → ℂ) (g' : ℝ → ℂ), VanishLow g' →
        pe S a' g' P₀ = a' p₁ * g' (Real.log (p₁.ht P₀))) ∧
      pe S a g =ᶠ[𝓝 P₀] fun P => a p₁ *
        shift g (Real.log (X.sNorm S p₁.out.c p₁.out.d)) (Real.log (X.pairHt p₁.out.c p₁.out.d P)) := by
  obtain ⟨p₁, h⟩ := pe_eventually S P₀
  refine ⟨p₁, h.self_of_nhds, h.mono fun P hP => ?_⟩
  rw [hP a g hg, term_eq_shift g p₁ P]

/-- `pe a g` is smooth for a smooth profile vanishing below height 2. -/
theorem smooth_pe (a : PairClass S → ℂ) {g : ℝ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hv : VanishLow g) : X.Smooth (pe S a g) := by
  unfold X.Smooth
  rw [contDiff_iff_contDiffAt]
  intro y
  obtain ⟨p₁, -, h⟩ := pe_eventuallyEq S a hv (chart F y)
  have h' := eventuallyEq_chart h
  rw [Homeomorph.symm_apply_apply] at h'
  have hs : X.Smooth fun P : X F => a p₁ *
      shift g (Real.log (X.sNorm S p₁.out.c p₁.out.d)) (Real.log (X.pairHt p₁.out.c p₁.out.d P)) :=
    (X.smooth_comp_log_pairHt (contDiff_shift hg _) p₁.out.ne_zero).const_mul (a p₁)
  exact hs.contDiffAt.congr_of_eventuallyEq h'

/-! ### Support -/

lemma exists_of_pe_ne_zero {a : PairClass S → ℂ} {g : ℝ → ℂ} {P : X F} (h : pe S a g P ≠ 0) :
    ∃ p : PairClass S, g (Real.log (p.ht P)) ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  unfold pe
  simp [hn]

/-- Where `pe a g ≠ 0` (profile supported in heights `[2, 3]`) all heights are `≤ 3`. -/
lemma ht_le_three_of_pe_ne_zero {a : PairClass S → ℂ} {g : ℝ → ℂ} (hl : VanishLow g)
    (hh : VanishHigh g) {P : X F} (h : pe S a g P ≠ 0) (p' : PairClass S) : p'.ht P ≤ 3 := by
  obtain ⟨p, hp⟩ := exists_of_pe_ne_zero h
  have h2 : Real.log 2 ≤ Real.log (p.ht P) := by
    by_contra hc
    exact hp (hl _ (not_le.mp hc))
  have h3 : Real.log (p.ht P) ≤ Real.log 3 := by
    by_contra hc
    exact hp (hh _ (not_le.mp hc))
  have h2' : (2 : ℝ) ≤ p.ht P := (Real.log_le_log_iff (by norm_num) (p.ht_pos P)).mp h2
  have h3' : p.ht P ≤ 3 := (Real.log_le_log_iff (p.ht_pos P) (by norm_num)).mp h3
  by_cases hpp : p' = p
  · rw [hpp]; exact h3'
  · by_contra hc
    exact hpp (PairClass.eq_of_one_lt_ht (by linarith) (by linarith))

/-- **Compact support modulo `Γ`**: one compact set for all weights and all profiles supported in
heights `[2, 3]`. -/
theorem exists_compact_pe (hB : SBezout S) (hO : FiniteCusps S) (Γ : Subgroup (SL(2, 𝓞 F)))
    [Γ.FiniteIndex] :
    ∃ K : Set (X F), IsCompact K ∧ ∀ (a : PairClass S → ℂ) (g : ℝ → ℂ), VanishLow g →
      VanishHigh g → ∀ P : X F, pe S a g P ≠ 0 → ∃ γ : Γ, γ • P ∈ K := by
  obtain ⟨K, hK, h⟩ := RC.exists_compact_top_le_subgroup hB hO Γ 3
  exact ⟨K, hK, fun a g hl hh P hP => h P (ht_le_three_of_pe_ne_zero hl hh hP)⟩

/-- `pe a g` is in the core of `Γ\X` when the weights are `Γ`-invariant and the profile is smooth
and supported in heights `[2, 3]`. -/
theorem pe_mem_core (hB : SBezout S) (hO : FiniteCusps S) {Γ : Subgroup (SL(2, 𝓞 F))}
    [Γ.FiniteIndex] {a : PairClass S → ℂ} (ha : ∀ γ ∈ Γ, ∀ p : PairClass S, a (p.act γ) = a p)
    {g : ℝ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hl : VanishLow g) (hh : VanishHigh g) :
    pe S a g ∈ X.core Γ := by
  obtain ⟨K, hK, h⟩ := exists_compact_pe hB hO Γ
  exact X.mem_core_of_support (smooth_pe a hg hl)
    (fun γ P => pe_smul g (ha γ γ.2) P) hK (h a g hl hh)

end

end ArtinKP.C5
end

section
-- module Solutions.Artin.KP.C5_Profile
/-! # WP-C5, file 3: the profiles of MATH2 §1

* `rho`: smooth, `0` on `(−∞, 2]`, `1` on `[3, ∞)`; `rt τ = ρ(e^τ)` and its derivatives `rt1`, `rt2`.
* `gS s τ = ρ(e^τ) e^{sτ}`: the profile of the cut-off part `h_s` (`gS_log : gS s (log h) = ρ(h) h^s`).
* `lam F s = r · s(2 − s)`.
* `phiS F s τ = r e^{sτ} (−ρ̃''(τ) + (2 − 2s) ρ̃'(τ))`: the profile of the source `F_s`
  (`Lg_gS : (L − λ(s)) gS s = phiS F s`); smooth, supported in `[log 2, log 3]`, entire in `s`,
  bounded on `{‖s‖ ≤ M} × ℝ` (`exists_norm_phiS_le`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C5

noncomputable section

/-! ### The cut-off `ρ` -/

lemma rho_zero {h : ℝ} (hh : h ≤ 2) : rho h = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma rho_one {h : ℝ} (hh : 3 ≤ h) : rho h = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma contDiff_rho : ContDiff ℝ (⊤ : ℕ∞) rho :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

lemma contDiff_rt : ContDiff ℝ (⊤ : ℕ∞) rt :=
  Complex.ofRealCLM.contDiff.comp (contDiff_rho.comp Real.contDiff_exp)

lemma rt_low {τ : ℝ} (h : τ < Real.log 2) : rt τ = 0 := by
  unfold rt
  rw [rho_zero ((Real.lt_log_iff_exp_lt (by norm_num)).mp h).le]
  simp

lemma rt_high {τ : ℝ} (h : Real.log 3 < τ) : rt τ = 1 := by
  unfold rt
  rw [rho_one ((Real.log_lt_iff_lt_exp (by norm_num)).mp h).le]
  simp

lemma contDiff_rt1 : ContDiff ℝ (⊤ : ℕ∞) rt1 := by
  have h : ContDiff ℝ ((⊤ : ℕ∞) + 1) rt := contDiff_rt
  exact (contDiff_succ_iff_deriv.1 h).2.2

lemma contDiff_rt2 : ContDiff ℝ (⊤ : ℕ∞) rt2 := by
  have h : ContDiff ℝ ((⊤ : ℕ∞) + 1) rt1 := contDiff_rt1
  exact (contDiff_succ_iff_deriv.1 h).2.2

lemma vanishLow_rt : VanishLow rt := fun _ h => rt_low h

lemma vanishLow_rt1 : VanishLow rt1 := vanishLow_rt.deriv

lemma vanishLow_rt2 : VanishLow rt2 := vanishLow_rt1.deriv

lemma vanishHigh_rt1 : VanishHigh rt1 := by
  intro τ hτ
  have h : rt =ᶠ[𝓝 τ] fun _ => (1 : ℂ) := by
    filter_upwards [Ioi_mem_nhds hτ] with t ht using rt_high ht
  unfold rt1
  rw [h.deriv_eq]
  simp

lemma vanishHigh_rt2 : VanishHigh rt2 := vanishHigh_rt1.deriv

/-! ### The profile of `h_s` -/

variable {F : Type*} [Field F] [NumberField F]

/-! ### The eigenvalue and the profile of the source -/

lemma contDiff_phiS (s : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (phiS F s) :=
  contDiff_const.mul ((X.contDiff_cexp_mul s).mul
    (contDiff_rt2.neg.add (contDiff_const.mul contDiff_rt1)))

lemma vanishLow_phiS (s : ℂ) : VanishLow (phiS F s) := fun τ h => by
  unfold phiS
  rw [vanishLow_rt1 τ h, vanishLow_rt2 τ h]
  simp

lemma vanishHigh_phiS (s : ℂ) : VanishHigh (phiS F s) := fun τ h => by
  unfold phiS
  rw [vanishHigh_rt1 τ h, vanishHigh_rt2 τ h]
  simp

end

end ArtinKP.C5
end

section
-- module Solutions.Artin.KP.C5_Series
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

/-- Sums over row classes are WP-C5's `pe` on WP-B1's pair classes. -/
lemma tsum_eq_pe (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) (s : ℂ) (g : ℝ → ℂ) (Q : X F) :
    ∑' q : B.RowClass 𝔪, tildeC Ψ s q * g (Real.log (q.ht Q)) =
      pe (RO.SOf 𝔪) (wt h𝔪 Ψ s) g Q := by
  unfold pe
  rw [← (RO.rowClassEquiv h𝔪).tsum_eq]
  refine tsum_congr fun q => ?_
  rw [ht_rowClassEquiv]
  unfold wt
  rw [Equiv.symm_apply_apply]

lemma src_eq_pe (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) (s : ℂ) :
    src Ψ s = pe (RO.SOf 𝔪) (wt h𝔪 Ψ s) (phiS F s) :=
  funext fun Q => tsum_eq_pe h𝔪 Ψ s (phiS F s) Q

/-! ### The Eisenstein series on pair classes -/

/-! ### Invariance, regularity -/

/-! ### The source -/

/-- **`F_s` is in the core of `Γ\X`** (smooth, invariant, supported in `Γ · K`). -/
theorem src_mem_core (hG : Good 𝔪) {Γ : Subgroup (SL(2, 𝓞 F))} [Γ.FiniteIndex]
    {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) (s : ℂ) : src Ψ s ∈ X.core Γ := by
  rw [src_eq_pe hG.ne_bot]
  exact pe_mem_core (RO.sBezout hG) (RO.finiteCusps _)
    (fun γ hγ p => wt_act hG.ne_bot hΓ hγ s p) (contDiff_phiS s) (vanishLow_phiS s)
    (vanishHigh_phiS s)

/-- `F_s ∈ L²(Γ\X)` for every `s ∈ ℂ`. -/
theorem l2Rep_src_oai (hG : Good 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) (s : ℂ) : X.L2Rep Γ (src Ψ s) :=
  X.l2Rep_of_mem_core (src_mem_core hG hΓ s)

end

end ArtinKP.C5
end

theorem solution.{u_1} : type_of% @ArtinKP.C5.l2Rep_src_oai.{u_1} := @ArtinKP.C5.l2Rep_src_oai.{u_1}
