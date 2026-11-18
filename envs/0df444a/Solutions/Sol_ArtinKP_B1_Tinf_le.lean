-- Prove2me | solution 1 for ArtinKP.B1.Tinf_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:42:46.211252+00:00
-- url     : https://prove2.me/submissions/91b5adb5-5b83-4652-9c44-0e99efbdeccd

import Mathlib
import Definitions.Def_ArtinKPB015

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
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol
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
attribute [-simp] _root_.ArtinKP.RO.rowPair_c _root_.ArtinKP.RO.rowPair_d _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
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
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
attribute [-simp] _root_.ArtinKP.B.coe_latREquiv _root_.ArtinKP.B.embR_apply _root_.ArtinKP.X.chart1_symm_snd _root_.ArtinKP.X.chart1_v _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
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
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
attribute [-simp] _root_.ArtinKP.B.coe_latREquiv _root_.ArtinKP.B.embR_apply _root_.ArtinKP.X.chart1_symm_fst _root_.ArtinKP.X.chart1_symm_snd _root_.ArtinKP.X.chart1_v _root_.ArtinKP.X.chart1_x
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
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
attribute [-simp] _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
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
theorem Tinf_le_oai (S : Finset (FinitePlace F)) {σ : ℝ} (hσ : 2 < σ) :
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

theorem solution.{u_1} : type_of% @ArtinKP.B1.Tinf_le_oai.{u_1} := @ArtinKP.B1.Tinf_le_oai.{u_1}
