-- Prove2me | solution 1 for ArtinKP.RC.exists_compact_top_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:44:27.736197+00:00
-- url     : https://prove2.me/submissions/ea6abfb2-4b91-49ad-95a2-4676e1630c5f

import Mathlib
import Definitions.Def_ArtinKPB015
import Theorems.Thm_ArtinKP_B1_PairClass_exists_top

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

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Disjoint
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

end X

end

end ArtinKP.X
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

/-! ### Lemma M for pair classes -/

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

variable [IsTotallyComplex F] {S : Finset (FinitePlace F)}

/-! ### MATH2 1.4(d) -/

/-- **MATH2 1.4(d) for `SL₂(𝓞_F)`**: the set where all pair heights are `≤ T` is contained in
`SL₂(𝓞_F) · K` with `K` compact (`K = ⋃_i τ_i⁻¹ • box_i` over the cusp representatives). -/
theorem exists_compact_top_le_oai (hB : SBezout S) (hO : FiniteCusps S) (T : ℝ) :
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

/-! ### Finite volume -/

end

end ArtinKP.RC
end

theorem solution.{u_1} : type_of% @ArtinKP.RC.exists_compact_top_le_oai.{u_1} := @ArtinKP.RC.exists_compact_top_le_oai.{u_1}
