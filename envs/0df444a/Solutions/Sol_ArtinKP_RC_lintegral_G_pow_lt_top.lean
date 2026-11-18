-- Prove2me | solution 1 for ArtinKP.RC.lintegral_G_pow_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:44:03.118176+00:00
-- url     : https://prove2.me/submissions/64be3e37-1efb-4102-9ba6-392775275209

import Mathlib
import Definitions.Def_ArtinKPB015
import Theorems.Thm_ArtinKP_B1_lintegral_G_pow_lt_top
import Theorems.Thm_ArtinKP_X_X_isPOU_pou

section
-- module Solutions.Artin.KP.X_Quot
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

theorem instCountableQuot (H : Subgroup G) : Countable (G ⧸ H) :=
  inferInstanceAs (Countable (Quotient (QuotientGroup.leftRel H)))

/-! ### Multiplicity and existence of partitions of unity -/

end

end ArtinKP.X
end

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

end X

end

end ArtinKP.X
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

end PairClass

/-! ### The series without one cusp -/

/-! ### The function `G` -/

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

/-- **R1, without an upper bound for the height**: for every `τ ∈ SL₂(F)` there are `C, ρ` such
that every `Q` with `ht Q ≥ c` has a translate `g • Q` in the Siegel set, `g` upper triangular in
`τ SL₂(𝓞_F) τ⁻¹`. -/
theorem reduction_cusp_siegelSet (τ : SL(2, F)) : ∃ C ρ : ℝ, 1 ≤ C ∧ 0 < ρ ∧ ∀ c : ℝ, 0 < c →
    ∀ Q : X F, c ≤ X.ht Q → ∃ γ : SL(2, 𝓞 F), ∃ g : SL(2, F), g 1 0 = 0 ∧
      τ * intSL F γ = g * τ ∧ X.ht (g • Q) = X.ht Q ∧
      g • Q ∈ siegelSet F (min 1 (c / C ^ Fintype.card (InfinitePlace F))) ρ := by
  obtain ⟨C, ρ, hC, hρ, h⟩ := exists_reduced_conj τ
  set r := Fintype.card (InfinitePlace F) with hr
  have hr0 : r ≠ 0 := Fintype.card_ne_zero
  refine ⟨C, ρ, hC, hρ, fun c hc Q hcQ => ?_⟩
  obtain ⟨γ', hmem, hup, hht, hx, hbal⟩ := h Q
  obtain ⟨γ, hγ⟩ := mem_conjSub.mp hmem
  refine ⟨γ, intSL F γ', ?_, hγ, hht, fun w => ⟨hx w, ?_⟩⟩
  · rw [intSL_apply, hup, map_zero]
  · change min 1 (c / C ^ r) ≤ (γ' • Q).v w
    have hv := (γ' • Q).v_pos
    obtain ⟨-, hb2⟩ := balanced_bounds (by linarith : (0 : ℝ) ≤ C) hv hbal w
    have hprod : ∏ j, (γ' • Q).v j = X.ht Q := hht
    rw [hprod] at hb2
    have hCr : 0 < C ^ r := by positivity
    rcases le_total 1 ((γ' • Q).v w) with h1 | h1
    · exact (min_le_left _ _).trans h1
    · refine (min_le_right _ _).trans ?_
      have h2 : (γ' • Q).v w ^ r ≤ (γ' • Q).v w := pow_le_of_le_one (hv w).le h1 hr0
      rw [div_le_iff₀ hCr]
      nlinarith

end

end ArtinKP.RC
end

section
-- module Solutions.Artin.KP.X2_Prod
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol
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

lemma vol_spread_lt_top (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex] {B : Set (X F)}
    (hB : X.vol F B < ⊤) : X.vol F (spread Γ B) < ⊤ := by
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  haveI _iCQ := ArtinKP.X.instCountableQuot Γ
  cases nonempty_fintype (SL(2, 𝓞 F) ⧸ Γ)
  refine (measure_iUnion_le _).trans_lt ?_
  rw [tsum_fintype]
  refine ENNReal.sum_lt_top.mpr fun q _ => ?_
  have : (fun P : X F => (q.out⁻¹ : SL(2, 𝓞 F)) • P) '' B = (q.out⁻¹ : SL(2, 𝓞 F)) • B := rfl
  rw [this, measure_smul]
  exact hB

variable [IsTotallyComplex F] {S : Finset (FinitePlace F)}

/-! ### MATH2 1.4(d) -/

/-! ### Finite volume -/

omit [NumberField F] [IsTotallyComplex F] in
lemma nu1_Ici_lt_top {m : ℝ} (hm : 0 < m) : nu1 (Ici m) < ⊤ := by
  unfold nu1
  rw [withDensity_apply _ measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  have hsub : Ici m ∩ Ioi (0 : ℝ) ⊆ Ioi (m / 2) := fun a ha => by
    have : m ≤ a := ha.1
    change m / 2 < a
    linarith
  refine (lintegral_mono_set hsub).trans_lt ?_
  have hcongr : ∫⁻ a in Ioi (m / 2), ENNReal.ofReal ((a ^ 3)⁻¹) =
      ∫⁻ a in Ioi (m / 2), ENNReal.ofReal (a ^ (-3 : ℝ)) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun a ha => ?_
    have ha0 : 0 < a := lt_trans (half_pos hm) ha
    have : a ^ (-3 : ℝ) = (a ^ 3)⁻¹ := by
      rw [Real.rpow_neg ha0.le, ← Real.rpow_natCast]
      norm_num
    rw [this]
  rw [hcongr]
  exact (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) (half_pos hm)).lintegral_lt_top

omit [NumberField F] [IsTotallyComplex F] in
lemma H3.vol_siegel_lt_top (m B : ℝ) (hm : 0 < m) :
    H3.vol {Q : H3 | ‖Q.x‖ ≤ B ∧ m ≤ Q.v} < ⊤ := by
  have hT : MeasurableSet (Metric.closedBall (0 : ℂ) B ×ˢ Ici m) :=
    Metric.isClosed_closedBall.measurableSet.prod measurableSet_Ici
  have hsub : {Q : H3 | ‖Q.x‖ ≤ B ∧ m ≤ Q.v} ⊆
      H3.coe ⁻¹' (Metric.closedBall (0 : ℂ) B ×ˢ Ici m) := by
    rintro Q ⟨hx, hv⟩
    exact ⟨mem_closedBall_zero_iff.mpr hx, hv⟩
  refine (measure_mono hsub).trans_lt ?_
  rw [measurePreserving_coe.measure_preimage hT.nullMeasurableSet, Measure.prod_prod]
  exact ENNReal.mul_lt_top measure_closedBall_lt_top (nu1_Ici_lt_top hm)

omit [IsTotallyComplex F] in
/-- The unbounded Siegel set has finite volume. -/
theorem vol_siegelSet_lt_top {m B : ℝ} (hm : 0 < m) : X.vol F (siegelSet F m B) < ⊤ := by
  have : siegelSet F m B =
      Set.pi univ fun _ : InfinitePlace F => {Q : H3 | ‖Q.x‖ ≤ B ∧ m ≤ Q.v} := by
    ext P
    exact ⟨fun h w _ => h w, fun h w => h w (mem_univ w)⟩
  rw [this, X.vol, Measure.pi_pi]
  exact ENNReal.prod_lt_top fun w _ => H3.vol_siegel_lt_top m B hm

/-- `X = SL₂(𝓞_F) · B` with `vol B < ∞`. -/
theorem exists_cover_finite_vol (hB : SBezout S) (hO : FiniteCusps S) :
    ∃ B : Set (X F), X.vol F B < ⊤ ∧ ∀ P : X F, ∃ γ : SL(2, 𝓞 F), γ • P ∈ B := by
  obtain ⟨n, τ, hτ, hcov⟩ := hO
  obtain ⟨c₀, hc₀, hex⟩ := PairClass.exists_ht_ge hB
  choose C ρ hC hρ hred using fun i => reduction_cusp_siegelSet (τ i)
  have hcS : ∀ i, 0 < cS S (τ i)⁻¹ := fun i => lt_of_lt_of_le one_pos (one_le_cS _)
  have hc : ∀ i, 0 < c₀ / cS S (τ i)⁻¹ := fun i => div_pos hc₀ (hcS i)
  refine ⟨⋃ i, (τ i)⁻¹ •
      siegelSet F (min 1 (c₀ / cS S (τ i)⁻¹ / C i ^ Fintype.card (InfinitePlace F))) (ρ i),
    ?_, fun P => ?_⟩
  · refine (measure_iUnion_le _).trans_lt ?_
    rw [tsum_fintype]
    refine ENNReal.sum_lt_top.mpr fun i _ => ?_
    rw [measure_smul]
    exact vol_siegelSet_lt_top
      (lt_min one_pos (div_pos (hc i) (pow_pos (lt_of_lt_of_le one_pos (hC i)) _)))
  · obtain ⟨p₀, hp₀⟩ := hex P
    obtain ⟨i, γ₀, hi⟩ := hcov p₀
    have h1 : p₀.ht P = ((PairClass.inf S).actR (τ i) (hτ i)).ht (γ₀ • P) := by
      rw [hi, PairClass.ht_act]
    have hle := PairClass.ht_actR_le (PairClass.inf S) (τ i) (hτ i) (γ₀ • P)
    rw [PairClass.ht_inf, ← h1] at hle
    have hQ1 : c₀ / cS S (τ i)⁻¹ ≤ X.ht (τ i • γ₀ • P) := by
      rw [div_le_iff₀ (hcS i)]
      linarith [mul_comm (cS S (τ i)⁻¹) (X.ht (τ i • γ₀ • P))]
    obtain ⟨γ, g, -, hg, -, hmem⟩ := hred i (c₀ / cS S (τ i)⁻¹) (hc i) _ hQ1
    refine ⟨γ * γ₀, Set.mem_iUnion.mpr ⟨i, g • τ i • γ₀ • P, hmem, ?_⟩⟩
    have e : g • τ i • γ₀ • P = τ i • intSL F γ • γ₀ • P := by
      rw [← mul_smul g, ← hg, mul_smul]
    change (τ i)⁻¹ • g • τ i • γ₀ • P = (γ * γ₀) • P
    rw [e, inv_smul_smul, mul_smul]
    try rfl

end

section Abstract

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]
  [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]

/-- **Covering lemma**: if `G · B = α` then `∫_{G\α} f ≤ ∫_B f` for invariant `f ≥ 0`. -/
theorem lintegral_mul_pou_le_of_cover {η : α → ℝ≥0∞} (hη : IsPOU G η) {f : α → ℝ≥0∞}
    (hf : Measurable f) (hinv : ∀ (g : G) (a : α), f (g • a) = f a) {B : Set α}
    (hB : MeasurableSet B) (hcov : ∀ a, ∃ g : G, g • a ∈ B) :
    ∫⁻ a, f a * η a ∂μ ≤ ∫⁻ a in B, f a ∂μ := by
  have h1 : ∀ a, (1 : ℝ≥0∞) ≤ ∑' g : G, B.indicator (fun _ => (1 : ℝ≥0∞)) (g • a) := by
    intro a
    obtain ⟨g, hg⟩ := hcov a
    refine le_trans ?_ (ENNReal.le_tsum g)
    rw [indicator_of_mem hg]
  calc ∫⁻ a, f a * η a ∂μ
      ≤ ∫⁻ a, (f a * η a) * ∑' g : G, B.indicator (fun _ => (1 : ℝ≥0∞)) (g • a) ∂μ :=
        lintegral_mono fun a => by
          calc f a * η a = f a * η a * 1 := (mul_one _).symm
            _ ≤ _ := by gcongr; exact h1 a
    _ = ∫⁻ a, B.indicator (fun _ => (1 : ℝ≥0∞)) a * ∑' g : G, f (g • a) * η (g • a) ∂μ :=
        lintegral_tsum_swap (hf.mul hη.measurable) (measurable_const.indicator hB)
    _ = ∫⁻ a, B.indicator f a ∂μ := by
        refine lintegral_congr fun a => ?_
        simp_rw [hinv, ENNReal.tsum_mul_left, hη.tsum_eq, mul_one]
        by_cases ha : a ∈ B
        · simp [ha]
        · simp [ha]
    _ = ∫⁻ a in B, f a ∂μ := lintegral_indicator hB f

end Abstract

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- The volume of `Γ\X` is at most the volume of any set meeting every `Γ`-orbit. -/
theorem quotVol_univ_le (Γ : Subgroup (SL(2, 𝓞 F))) {B : Set (X F)}
    (hcov : ∀ P : X F, ∃ γ : Γ, γ • P ∈ B) : X.quotVol Γ Set.univ ≤ X.vol F B := by
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  have hη := X.isPOU_pou (F := F) Γ
  have hvol : X.quotVol Γ Set.univ = ∫⁻ P, 1 * X.pou Γ P ∂X.vol F := by
    have := X.lintegral_quotVol Γ hη (f := fun _ => 1) measurable_const
    simpa using this
  rw [hvol, ← measure_toMeasurable B]
  have h := lintegral_mul_pou_le_of_cover (μ := X.vol F) hη (f := fun _ => 1) measurable_const
    (fun _ _ => rfl) (measurableSet_toMeasurable (X.vol F) B)
    (fun P => (hcov P).imp fun γ hγ => subset_toMeasurable _ _ hγ)
  simpa using h

variable [IsTotallyComplex F] {S : Finset (FinitePlace F)}

/-- **V1: finite volume.**  `μ(Γ\X) < ∞` for `Γ` of finite index in `SL₂(𝓞_F)`. -/
theorem quotVol_univ_lt_top (hB : SBezout S) (hO : FiniteCusps S)
    (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex] : X.quotVol Γ Set.univ < ⊤ := by
  obtain ⟨B, hBv, hcov⟩ := exists_cover_finite_vol hB hO
  exact (quotVol_univ_le Γ fun P => exists_subgroup_smul_mem_spread Γ (hcov P)).trans_lt
    (vol_spread_lt_top Γ hBv)

/-- **`G ∈ L^k(Γ\X)` for every `k`** (`k = 1, 2`: MATH2 1.4(a),(b) as finiteness statements), for
`Γ` of finite index; only `SBezout S` and `FiniteCusps S` are assumed. -/
theorem lintegral_G_pow_lt_top_oai (hB : SBezout S) (hO : FiniteCusps S) {σ : ℝ} (hσ : 2 < σ)
    (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex] (k : ℕ) :
    ∫⁻ P, ENNReal.ofReal (G S σ P) ^ k * X.pou Γ P ∂X.vol F < ⊤ :=
  B1.lintegral_G_pow_lt_top hB hO hσ Γ (quotVol_univ_lt_top hB hO Γ) k

end

end ArtinKP.RC
end

theorem solution.{u_1} : type_of% @ArtinKP.RC.lintegral_G_pow_lt_top_oai.{u_1} := @ArtinKP.RC.lintegral_G_pow_lt_top_oai.{u_1}
