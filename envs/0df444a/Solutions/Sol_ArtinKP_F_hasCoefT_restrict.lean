-- Prove2me | solution 1 for ArtinKP.F.hasCoefT_restrict
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:04:04.397123+00:00
-- url     : https://prove2.me/submissions/6bc07fe4-7e7c-456c-a5c3-959a9c595ab4

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
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
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

/-! ### Primitive pairs and pair classes -/

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
-- module Solutions.Artin.KP.B7_Sum
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # B7_Sum: sums over residues modulo a principal ideal

For a commutative ring `R`, `c : R` and `f : R → ℂ`, `rsum c f` is the sum of `f` over chosen
representatives of `R ⧸ (c)` (the same `Function.surjInv` choice as `ArtinPrimitiveRoots.quotLift`).
For `f` periodic modulo `c` (`Per c f`) it does not depend on the choice, and we prove the
reindexing lemmas used for Gauss sums: translation, multiplication by a unit modulo `c`, the
Chinese remainder theorem, and the fibre formula for a function periodic modulo a divisor.
-/

namespace ArtinKP.B7

variable {R : Type*} [CommRing R]

lemma mk_rep (c : R) (x : R ⧸ Ideal.span {c}) :
    Ideal.Quotient.mk (Ideal.span {c}) (rep c x) = x :=
  Function.surjInv_eq Ideal.Quotient.mk_surjective x

lemma mk_eq_mk_iff {c a b : R} :
    Ideal.Quotient.mk (Ideal.span {c}) a = Ideal.Quotient.mk (Ideal.span {c}) b ↔ c ∣ a - b := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]

lemma dvd_rep_mk_sub (c a : R) : c ∣ rep c (Ideal.Quotient.mk (Ideal.span {c}) a) - a :=
  mk_eq_mk_iff.1 (mk_rep c _)

lemma Per.rep_mk {c : R} {f : R → ℂ} (hf : Per c f) (a : R) :
    f (rep c (Ideal.Quotient.mk (Ideal.span {c}) a)) = f a :=
  hf _ _ (dvd_rep_mk_sub c a)

lemma Per.of_dvd {c c' : R} {f : R → ℂ} (hf : Per c f) (h : c ∣ c') : Per c' f :=
  fun a b hab => hf a b (h.trans hab)

lemma rsum_congr {c : R} {f g : R → ℂ} (h : ∀ d, f d = g d) : rsum c f = rsum c g := by
  unfold rsum; exact finsum_congr fun x => h _

lemma rsum_mul_const (c : R) (f : R → ℂ) (z : ℂ) : rsum c (fun d => f d * z) = rsum c f * z := by
  unfold rsum; rw [finsum_mul]

lemma rsum_one (c : R) [Finite (R ⧸ Ideal.span {c})] :
    rsum c (fun _ => 1) = (Nat.card (R ⧸ Ideal.span {c}) : ℂ) := by
  unfold rsum
  have := Fintype.ofFinite (R ⧸ Ideal.span {c})
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
  simp

/-- Reindexing by a map of `R` that induces a permutation of the residues. -/
lemma rsum_comp {c : R} {f : R → ℂ} (hf : Per c f) (σ : R → R)
    (τ : (R ⧸ Ideal.span {c}) ≃ (R ⧸ Ideal.span {c}))
    (h : ∀ a, Ideal.Quotient.mk (Ideal.span {c}) (σ a) = τ (Ideal.Quotient.mk (Ideal.span {c}) a)) :
    rsum c (fun d => f (σ d)) = rsum c f := by
  unfold rsum
  refine Eq.trans ?_ (finsum_comp_equiv τ)
  refine finsum_congr fun x => hf _ _ ?_
  rw [← mk_eq_mk_iff, h, mk_rep, mk_rep]

/-- Translation invariance. -/
lemma rsum_add_right {c : R} {f : R → ℂ} (hf : Per c f) (a : R) :
    rsum c (fun d => f (d + a)) = rsum c f :=
  rsum_comp hf (fun d => d + a) (Equiv.addRight (Ideal.Quotient.mk (Ideal.span {c}) a))
    (fun d => by simp)

/-- **Fibre formula**: a function periodic modulo `c` summed modulo `c * c'`. -/
lemma rsum_mul_of_per [IsDomain R] {c c' : R} [Finite (R ⧸ Ideal.span {c})]
    [Finite (R ⧸ Ideal.span {c'})] (hc : c ≠ 0) {f : R → ℂ} (hf : Per c f) :
    rsum (c * c') f = (Nat.card (R ⧸ Ideal.span {c'}) : ℂ) * rsum c f := by
  set Φ : (R ⧸ Ideal.span {c}) × (R ⧸ Ideal.span {c'}) → R ⧸ Ideal.span {c * c'} :=
    fun p => Ideal.Quotient.mk _ (rep c p.1 + c * rep c' p.2) with hΦ
  have hbij : Function.Bijective Φ := by
    constructor
    · rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ hxy
      simp only [hΦ, mk_eq_mk_iff] at hxy
      have e1 : c ∣ rep c x₁ - rep c x₂ := by
        have := (dvd_mul_right c c').trans hxy
        have h2 : rep c x₁ - rep c x₂ =
            (rep c x₁ + c * rep c' y₁ - (rep c x₂ + c * rep c' y₂)) -
              c * (rep c' y₁ - rep c' y₂) := by ring
        rw [h2]; exact dvd_sub this (dvd_mul_right _ _)
      rw [← mk_eq_mk_iff, mk_rep, mk_rep] at e1
      subst e1
      have e2 : c * c' ∣ c * (rep c' y₁ - rep c' y₂) := by
        have h2 : c * (rep c' y₁ - rep c' y₂) =
            (rep c x₁ + c * rep c' y₁ - (rep c x₁ + c * rep c' y₂)) := by ring
        rw [h2]; exact hxy
      have e2' := (mul_dvd_mul_iff_left hc).1 e2
      rw [← mk_eq_mk_iff, mk_rep, mk_rep] at e2'
      rw [e2']
    · intro z
      obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨s, hs⟩ := dvd_rep_mk_sub c d
      obtain ⟨t, ht⟩ := dvd_rep_mk_sub c' (-s)
      refine ⟨(Ideal.Quotient.mk _ d, Ideal.Quotient.mk _ (-s)), ?_⟩
      simp only [hΦ, mk_eq_mk_iff]
      refine ⟨t, ?_⟩
      linear_combination hs + c * ht
  unfold rsum
  rw [← finsum_eq_of_bijective Φ hbij (g := fun z => f (rep (c * c') z))
    (f := fun p => f (rep c p.1)) (fun p => ?_)]
  · rw [finsum_curry _ (Set.toFinite _)]
    have := Fintype.ofFinite (R ⧸ Ideal.span {c'})
    have : ∀ a : R ⧸ Ideal.span {c}, (∑ᶠ _b : R ⧸ Ideal.span {c'}, f (rep c a)) =
        (Nat.card (R ⧸ Ideal.span {c'}) : ℂ) * f (rep c a) := by
      intro a
      rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
      simp
    simp only [this]
    rw [mul_finsum]
  · simp only [hΦ]
    rw [(hf.of_dvd (dvd_mul_right c c')).rep_mk]
    exact hf _ _ ⟨-rep c' p.2, by ring⟩

/-- Summing a function periodic modulo `c` over the residues modulo `c ^ (k+1)`. -/
lemma rsum_pow_of_per [IsDomain R] {c : R} [Finite (R ⧸ Ideal.span {c})] (hc : c ≠ 0)
    (hfin : ∀ k : ℕ, Finite (R ⧸ Ideal.span {c ^ k})) {f : R → ℂ} (hf : Per c f) (k : ℕ) :
    rsum (c ^ (k + 1)) f = (Nat.card (R ⧸ Ideal.span {c}) : ℂ) ^ k * rsum c f := by
  induction k with
  | zero => simp
  | succ k ih =>
    have := hfin (k + 1)
    rw [pow_succ c (k + 1), rsum_mul_of_per (pow_ne_zero _ hc) (hf.of_dvd (dvd_pow_self c (by omega))),
      ih, pow_succ]
    ring

end ArtinKP.B7
end

section
-- module Solutions.Artin.KP.B7_Gauss
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # B7_Gauss: the cubic Gauss sum `g(ν, c)` over a ring of `S`-integers, abstractly

`R` is a domain with fraction-type field `K` (in the application `R = SInt 𝔪`, `K = F`).

* `CubicSymbol R` is the interface to WP-A: the cubic exterior symbol `(d/c)`, with exactly the
  properties used here.
* `AddData R K` is an additive character of `K` trivial on `R` (in the application `sAddChar 𝔪`,
  see `B7_Link`).
* `gauss S A ν c = ∑_{d mod c} (d/c)⁻¹ e(ν d / c)` (terms with `(d, c) ≠ 1` vanish since
  `(d/c) = 0` there and `0⁻¹ = 0`).

Main results (MATH.md (B7)): `gauss_mul` (twisted multiplicativity), `gauss_mul_left`
(`g(μν, c) = (μ/c) g(ν, c)`), the prime-power table `gauss_prime_pow_le`,
`gauss_prime_pow_succ`, `gauss_prime_pow_eq_zero`, and the constant-term sums `csum_eq_phi`,
`csum_eq_zero`, `csum_of_cube`, `csum_eq_zero_of_val`, `csum_prime_pow`, `phi_prime_pow`.
-/

set_option linter.unusedSectionVars false

namespace ArtinKP.B7

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]

/-! ### The additive character on fractions -/

namespace AddData

variable (A : AddData R K)

omit A in
lemma map_ne_zero (A : AddData R K) {c : R} (hc : c ≠ 0) : algebraMap R K c ≠ 0 := fun h =>
  hc (A.inj (h.trans (map_zero _).symm))

lemma ψ_add (a b c : R) : A.ψ (a + b) c = A.ψ a c * A.ψ b c := by
  unfold ψ; rw [map_add, add_div, A.e_add]

lemma ψ_mul_self {c : R} (hc : c ≠ 0) (r : R) : A.ψ (c * r) c = 1 := by
  unfold ψ
  rw [map_mul, mul_div_cancel_left₀ _ (A.map_ne_zero hc), A.e_int]

lemma ψ_per {c : R} (hc : c ≠ 0) {a b : R} (h : c ∣ a - b) : A.ψ a c = A.ψ b c := by
  obtain ⟨r, hr⟩ := h
  have : a = b + c * r := by rw [← hr]; ring
  rw [this, ψ_add, ψ_mul_self A hc, mul_one]

lemma ψ_mul_right_cancel (a c : R) {c' : R} (hc' : c' ≠ 0) : A.ψ (a * c') (c * c') = A.ψ a c := by
  unfold ψ
  rw [map_mul, map_mul, mul_div_mul_right _ _ (A.map_ne_zero hc')]

end AddData

/-! ### Elementary facts about the symbol -/

/-! ### The Gauss sum -/

/-! ### Constant-term sums -/

/-! ### Prime powers -/

end ArtinKP.B7
end

section
-- module Solutions.Artin.T12.C3I_Res
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # C3I_Res: the residue rings `R / P^j R` at a prime `P ∉ S`

For a height-one prime `v` of `𝓞 F` outside `S = placesOf 𝔪`:
* `mem_map_pow_iff`: `r ∈ v^j R ↔ v(r) ≤ exp(-j)` for `r ∈ R`;
* `quotEquiv`: `𝓞/v^j ≃+* R/v^j R`; `natCard_quot`: `#(R/v^j R) = N(v)^j`;
* `isMaximal_map`: `v R` is maximal;
* `finsum_quot_fibre`: summing a function that only depends on the class mod `v^i R`
  over `R/v^j R` (`i ≤ j`) gives `N(v)^(j-i)` times the sum over `R/v^i R`.
-/

set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

section val

variable {v : HeightOneSpectrum (𝓞 F)}

/-- Discreteness: a valuation strictly above `exp(-(j+1))` is at least `exp(-j)`. -/
lemma exp_le_of_lt {γ : ℤᵐ⁰} {j : ℤ} (h : exp (j - 1) < γ) : exp j ≤ γ := by
  have hγ : γ ≠ 0 := ne_zero_of_lt h
  rw [← exp_log hγ] at h ⊢
  rw [exp_lt_exp] at h
  rw [exp_le_exp]
  omega

lemma exp_le_val_of_not_mem (hv : v ∉ placesOf 𝔪) (j : ℕ) (r : SInt 𝔪)
    (h : r ∉ (v.asIdeal ^ (j + 1)).map (algebraMap (𝓞 F) (SInt 𝔪))) :
    exp (-(j : ℤ)) ≤ v.valuation F (r : F) := by
  rw [mem_map_pow_iff hv, not_le] at h
  apply exp_le_of_lt
  convert h using 2
  push_cast; ring

lemma isExterior_mul {I J : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (hJ : IsExterior 𝔪 J) :
    IsExterior 𝔪 (I * J) := by
  refine ⟨mul_ne_zero hI.1 hJ.1, ?_⟩
  have h1 : IsCoprime I 𝔪 := Ideal.isCoprime_iff_sup_eq.mpr hI.2
  have h2 : IsCoprime J 𝔪 := Ideal.isCoprime_iff_sup_eq.mpr hJ.2
  exact Ideal.isCoprime_iff_sup_eq.mp (h1.mul_left h2)

lemma isExterior_pow {I : Ideal (𝓞 F)} (hI : IsExterior 𝔪 I) (n : ℕ) :
    IsExterior 𝔪 (I ^ n) := by
  induction n with
  | zero => rw [pow_zero, Ideal.one_eq_top]; exact ⟨top_ne_bot, top_sup_eq _⟩
  | succ k ih => rw [pow_succ]; exact isExterior_mul ih hI

/-- A uniformizer in `𝓞`. -/
lemma exists_uniformizer : ∃ p : 𝓞 F, v.valuation F (algebraMap (𝓞 F) F p) = exp (-1 : ℤ) := by
  obtain ⟨p, hp⟩ := v.intValuation_exists_uniformizer
  exact ⟨p, by rw [val_alg, hp]⟩

end val

end C3I

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.C3I_Add
attribute [-instance] _root_.ArtinKP.B1.PairClass.instNonempty _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # C3I_Add: the additive character `e`

* `HasWit 𝔪 x`: `x` has a witness `y` in the definition of `sAddChar` (`x - y ∈ R`, `y` integral
  at `S`). `hasWit_of_mul_mem`: true when `x I ⊆ R` for an ideal `I` coprime to `𝔪`; in particular
  `hasWit_div_gen`: `a / gen 𝔞` for `a ∈ R`, `𝔞` exterior.
* `sAddChar_eq_of_wit`: `e(x) = exp(-2πi Tr y)` for every witness; `sAddChar_add`: `e` is additive
  on elements with witnesses.
* `exists_trace_not_int`: for `P ∤ 𝔇`, some `z ∈ P⁻¹` has `Tr z ∉ ℤ`; `sAddChar_ne_one_of_dual`.
* `exists_sAddChar_ne_one`: primitivity at every level: for `x ∈ R ∖ P^j R` some `r ∈ R` has
  `e(x r / gen(P^j)) ≠ 1`.
-/

set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

variable {ι : F →+* ℂ}

/-! ### The inverse different -/

/-- For `P ∤ 𝔇`, some `z ∈ P⁻¹` has non-integral trace. -/
lemma exists_trace_not_int (P : Ideal (𝓞 F)) (hP0 : P ≠ ⊥)
    (hD : ¬ differentIdeal ℤ (𝓞 F) ≤ P) :
    ∃ z : F, (∀ p ∈ P, ∃ a : 𝓞 F, z * algebraMap (𝓞 F) F p = algebraMap (𝓞 F) F a) ∧
      ∀ n : ℤ, Algebra.trace ℚ F z ≠ n := by
  rw [differentialIdeal_le_iff (K := ℚ) (L := F) hP0, Submodule.map_le_iff_le_comap] at hD
  rw [SetLike.not_le_iff_exists] at hD
  obtain ⟨z, hz, hz'⟩ := hD
  have hP' : (P : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 := by
    simpa using hP0
  have hz2 : z ∈ ((P : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)⁻¹) := hz
  rw [FractionalIdeal.mem_inv_iff hP'] at hz2
  refine ⟨z, fun p hp => ?_, fun n hn => hz' ?_⟩
  · have := hz2 (algebraMap (𝓞 F) F p) ((FractionalIdeal.mem_coeIdeal _).2 ⟨p, hp, rfl⟩)
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).1 this
    exact ⟨a, ha.symm⟩
  · simp only [Submodule.mem_comap, LinearMap.coe_restrictScalars, Submodule.mem_one]
    exact ⟨n, by rw [hn]; simp⟩

/-- For `P` exterior and `z ∈ P⁻¹` with non-integral trace, `e(z) ≠ 1`. -/
lemma sAddChar_ne_one_of_dual (P : Ideal (𝓞 F)) (hPS : P ⊔ 𝔪 = ⊤) (z : F)
    (hz : ∀ p ∈ P, ∃ a : 𝓞 F, z * algebraMap (𝓞 F) F p = algebraMap (𝓞 F) F a)
    (htr : ∀ n : ℤ, Algebra.trace ℚ F z ≠ n) : sAddChar 𝔪 z ≠ 1 := by
  have hw : ∀ v ∈ placesOf 𝔪, v.valuation F z ≤ 1 := by
    intro v hv
    have hvm : 𝔪 ≤ v.asIdeal := hv
    have hPv : ¬ P ≤ v.asIdeal := by
      intro h
      apply v.isPrime.ne_top
      rw [eq_top_iff, ← hPS]
      exact sup_le h hvm
    obtain ⟨p, hp, hpv⟩ := SetLike.not_le_iff_exists.mp hPv
    obtain ⟨a, ha⟩ := hz p hp
    have h1 : v.valuation F (algebraMap (𝓞 F) F p) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hpv
    have := v.valuation_le_one (K := F) a
    change v.valuation F (algebraMap (𝓞 F) F a) ≤ 1 at this
    rw [← ha, map_mul, h1, mul_one] at this
    exact this
  rw [sAddChar_eq_of_wit (y := z) (by simp) hw]
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  apply htr (-n)
  have h2 : ((Algebra.trace ℚ F z : ℚ) : ℂ) = ((-n : ℤ) : ℂ) := by
    have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    apply mul_left_cancel₀ hpi
    push_cast
    linear_combination -hn
  exact_mod_cast h2

/-! ### Primitivity at every level -/

section prim

variable {v : HeightOneSpectrum (𝓞 F)}

/-- `z (v R) ⊆ R` for `z ∈ v⁻¹`. -/
lemma mul_mem_of_mem_map (z : F)
    (hz : ∀ p ∈ v.asIdeal, ∃ a : 𝓞 F, z * algebraMap (𝓞 F) F p = algebraMap (𝓞 F) F a)
    {y : SInt 𝔪} (hy : y ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    z * (y : F) ∈ (placesOf 𝔪).integer F := by
  rw [Ideal.map] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    obtain ⟨a, ha⟩ := hz p hp
    rw [coe_alg, ha]
    exact (algebraMap (𝓞 F) (SInt 𝔪) a).2
  | zero => simp
  | add x y _ _ hx hy => rw [Subalgebra.coe_add, mul_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [smul_eq_mul, Subalgebra.coe_mul, mul_left_comm]
    exact mul_mem a.2 hx

/-- Primitivity of `x ↦ e(x / gen(P^j))` on `R / P^j R`: for `x ∉ P^j R` there is `r ∈ R` with
`e(x r / gen(P^j)) ≠ 1`, when `P ∤ 𝔇`. -/
lemma exists_sAddChar_ne_one (g : AllowedGen ι 𝔪) (hv : v ∉ placesOf 𝔪)
    (hPS : v.asIdeal ⊔ 𝔪 = ⊤) (hD : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal) {j : ℕ} (hj : 1 ≤ j)
    (x : SInt 𝔪) (hx : x ∉ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪))) :
    ∃ r : SInt 𝔪, sAddChar 𝔪 ((x : F) * (r : F) / (g.gen (v.asIdeal ^ j) : F)) ≠ 1 := by
  obtain ⟨z, hz, htr⟩ := exists_trace_not_int v.asIdeal v.ne_bot hD
  have hez := sAddChar_ne_one_of_dual v.asIdeal hPS z hz htr
  have hext : IsExterior 𝔪 (v.asIdeal ^ j) :=
    isExterior_pow ⟨v.ne_bot, hPS⟩ j
  set B := g.gen (v.asIdeal ^ j)
  have hB0 : (B : F) ≠ 0 := C3B.gen_ne_zero g _ hext
  have hBmem : B ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← g.span_gen _ hext]; exact Ideal.mem_span_singleton_self _
  have hB1 : B ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    have : (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) ≤
        v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
      Ideal.map_mono (by simpa using Ideal.pow_le_pow_right (I := v.asIdeal) hj)
    exact this hBmem
  -- `w = z B ∈ R`
  have hwR : z * (B : F) ∈ (placesOf 𝔪).integer F := mul_mem_of_mem_map z hz hB1
  set w : SInt 𝔪 := ⟨z * (B : F), hwR⟩
  -- valuations
  have hvz : v.valuation F z ≤ exp (1 : ℤ) := by
    obtain ⟨p, hp⟩ := exists_uniformizer (v := v)
    have hpm : p ∈ v.asIdeal := by
      rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F), hp]
      exact exp_lt_exp.2 (by norm_num) |>.trans_eq exp_zero
    obtain ⟨a, ha⟩ := hz p hpm
    have h1 := v.valuation_le_one (K := F) a
    change v.valuation F (algebraMap (𝓞 F) F a) ≤ 1 at h1
    rw [← ha, map_mul, hp] at h1
    have : v.valuation F z * exp (-1 : ℤ) * exp 1 ≤ 1 * exp 1 := mul_le_mul_left h1 _
    rwa [mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one, one_mul] at this
  have hvB := val_le_of_mem hv j hBmem
  have hvw : v.valuation F (w : F) ≤ exp (1 - (j : ℤ)) := by
    change v.valuation F (z * (B : F)) ≤ _
    rw [map_mul, show (1 - (j : ℤ)) = 1 + (-(j : ℤ)) by ring, exp_add]
    exact mul_le_mul' hvz hvB
  have hvx : exp (1 - (j : ℤ)) ≤ v.valuation F (x : F) := by
    have := exp_le_val_of_not_mem hv (j - 1) x (by rwa [Nat.sub_add_cancel hj])
    convert this using 2
    push_cast [Nat.cast_sub hj]; ring
  have hx0 : (x : F) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hvx
    exact exp_ne_zero (le_antisymm hvx bot_le)
  have hvx0 : v.valuation F (x : F) ≠ 0 := by
    rw [Ne, map_eq_zero]; exact hx0
  -- `f = w / x` is `v`-integral
  have hvf : v.valuation F ((w : F) / (x : F)) ≤ 1 := by
    rw [map_div₀, div_le_one₀ (pos_iff_ne_zero.2 hvx0)]
    exact hvw.trans hvx
  obtain ⟨a, ha⟩ := exists_val_sub_le (v := v) j _ hvf
  -- `w - x a ∈ P^j R`
  set δ : SInt 𝔪 := w - x * algebraMap (𝓞 F) (SInt 𝔪) a
  have hδ : δ ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    apply mem_of_val_le hv j
    have : (δ : F) = (x : F) * ((w : F) / (x : F) - algebraMap (𝓞 F) F a) := by
      simp only [δ, Subalgebra.coe_sub, Subalgebra.coe_mul, coe_alg]
      field_simp
    rw [this, map_mul]
    calc v.valuation F (x : F) * v.valuation F ((w : F) / (x : F) - algebraMap (𝓞 F) F a)
        ≤ 1 * exp (-(j : ℤ)) := mul_le_mul' (val_le_one hv x) ha
      _ = _ := one_mul _
  refine ⟨algebraMap (𝓞 F) (SInt 𝔪) a, fun h1 => hez ?_⟩
  have hzeq : z = (x : F) * ((algebraMap (𝓞 F) (SInt 𝔪) a : SInt 𝔪) : F) / (B : F) +
      (δ : F) / (B : F) := by
    simp only [δ, Subalgebra.coe_sub, Subalgebra.coe_mul]
    change z = _ + (z * (B : F) - _) / (B : F)
    field_simp
    ring
  rw [hzeq, C3B.sAddChar_add_mem _ _ (C3B.div_gen_mem g _ hext δ hδ), h1]

end prim

end C3I

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.C3I_Gauss
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # C3I_Gauss: the additive character, Gauss sums and Davenport–Hasse on `L = R / P R`

* `psi g h : AddChar L ℂ`, `psi_mk : psi (mk x) = e(x / gen P)`, `psi_isPrimitive`.
* `card_sqrt`: `#{u | u² = w} = 1 + χ³(w)`; `jacobi_dh`: `χ(4) J(χ, χ) = J(χ³, χ)`.
* Gauss sums `g_j = gaussSum (χ^j) ψ`: `gs_mul_gs_inv`, `gs_three_sq`, `star_gs`, `dh`:
  `χ(4) g₁ g₃ = g₂²`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false


open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {v : HeightOneSpectrum (𝓞 F)}
  {ι : F →+* ℂ}

lemma quotLift_mk_sub {I : Ideal (SInt 𝔪)} (x : SInt 𝔪) :
    quotLift (Ideal.Quotient.mk I x) - x ∈ I := by
  rw [← Ideal.Quotient.eq]; exact Function.surjInv_eq Ideal.Quotient.mk_surjective _

lemma psi_apply (g : AllowedGen ι 𝔪) (h : Good 𝔪 v) (y) :
    psi g h y = sAddChar 𝔪 ((quotLift y : F) / (g.gen v.asIdeal : F)) := rfl

lemma psi_mk (g : AllowedGen ι 𝔪) (h : Good 𝔪 v) (x : SInt 𝔪) :
    psi g h (Ideal.Quotient.mk _ x) = sAddChar 𝔪 ((x : F) / (g.gen v.asIdeal : F)) :=
  sAddChar_div_congr g _ h.ext (quotLift_mk_sub x)

lemma psi_isPrimitive (g : AllowedGen ι 𝔪) (h : Good 𝔪 v) : (psi g h).IsPrimitive := by
  intro a ha hone
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hx : x ∉ (v.asIdeal ^ 1).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [pow_one]; rwa [Ne, Ideal.Quotient.eq_zero_iff_mem] at ha
  obtain ⟨r, hr⟩ := exists_sAddChar_ne_one g h.notS h.cop h.diff le_rfl x hx
  apply hr
  have := congrArg (fun φ => φ (Ideal.Quotient.mk _ r)) hone
  simp only [AddChar.mulShift_apply, AddChar.one_apply] at this
  rw [← map_mul, psi_mk, Subalgebra.coe_mul] at this
  rw [pow_one]
  exact this

/-! ### Characters on the finite field `L` -/

end C3I

end ArtinPrimitiveRoots
end

section
-- module Solutions.Artin.T12.L2B_Quot
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# L2B_Quot: exterior ideals of `𝓞 F` and of `R` (copied from L2A_FSQuot, prover A, to decouple)

* `exists_pow_mul_mem`: every `r ∈ R` has `𝔪^N r ⊆ 𝓞`.
* `mem_of_map_mem`: `I R ∩ 𝓞 = I` for `I + 𝔪 = 1`.
* `exists_sub_mem_map`: `𝓞 → R / I R` is onto for `I + 𝔪 = 1`; `finite_quot_map`,

-/

open NumberField IsDedekindDomain WithZero

namespace ArtinPrimitiveRoots.L2B

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

lemma quotHom_surjective (I : Ideal (𝓞 F)) (hI : I ⊔ 𝔪 = ⊤) :
    Function.Surjective (C3I.quotHom 𝔪 I) := by
  intro y
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨c, hc⟩ := exists_sub_mem_map I hI r
  exact ⟨Ideal.Quotient.mk _ c, by rw [C3I.quotHom_mk]; exact (Ideal.Quotient.eq.mpr hc).symm⟩

lemma finite_quot_map (I : Ideal (𝓞 F)) (hI0 : I ≠ ⊥) (hI : I ⊔ 𝔪 = ⊤) :
    Finite (SInt 𝔪 ⧸ I.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  have : Finite (𝓞 F ⧸ I) := Ring.HasFiniteQuotients.finiteQuotient hI0
  exact Finite.of_surjective _ (quotHom_surjective I hI)

end ArtinPrimitiveRoots.L2B
end

section
-- module Solutions.Artin.KP.B7_Link
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # B7_Link: the Gauss sums over `R = SInt 𝔪` and the normalization of the frozen statement

* `sAdd 𝔪 h𝔪 : AddData (SInt 𝔪) F` is `sAddChar 𝔪` (additive on all of `F`: `sAddChar_add_all`;
  trivial on `R`), so `gauss S (sAdd 𝔪 h𝔪) ν c = ∑_{d mod c} (d/c)⁻¹ sAddChar 𝔪 (ν d / c)`
  (`gauss_sAdd`).
* `finite_quot_span`: `R ⧸ (c)` is finite for `c ≠ 0`.
* At a good exterior prime `P` (`C3I.Good 𝔪 v`, automatic for `SmallPrimesDvd N₀ 𝔪`,
  `N₀ ≥ C3I.cutN F`) with `π = g.gen P` and a symbol with `(d/π) = χ_P(d)²`:
  `gaussP_one_eq_tau : g₁(π) = tau P 2 = conj (√q γ₂(P))`,
  `gaussP_two_eq_tau : g₂(π) = tau P 4 = √q γ₂(P)`, `γ₂(P) = gaussPhase g 2 P`,
  `gaussP_one_mul_two : g₁ g₂ = N P`, and the complete table `gauss_gen_table` in the form of
  `B7_System.tab` with `G = (ν₀/π) tau P 2`, `G' = (ν₀/π)² tau P 4`, `G G' = N P`, `conj G = G'`.
* `theta_ratio`: the solution of the formal system at `x₀ = q^{-4/3}` gives
  `q^{-1/3} C₁ = (ν₀/π)² · Wv P 1 · C₀` with `Wv P 1 = q^{-1/2} gaussPhase g 2 P` exactly as in the
  frozen statement (and `Wv P 0 = 1`, `Wv P 2 = 0 ↔ Ψ₂ = 0`).
-/

open NumberField IsDedekindDomain

namespace ArtinKP.B7

open ArtinPrimitiveRoots

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### The additive character -/

/-- `R ⧸ (c)` is finite for `c ≠ 0`. -/
theorem finite_quot_span (h𝔪 : 𝔪 ≠ ⊥) {c : SInt 𝔪} (hc : c ≠ 0) :
    Finite (SInt 𝔪 ⧸ Ideal.span {c}) := by
  have hcF : (c : F) ≠ 0 := fun h => hc (Subtype.ext h)
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (c : F)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbF : algebraMap (𝓞 F) F b ≠ 0 := by
    intro h; exact hb0 (by simpa using h)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hab
    exact hcF hab.symm
  have hI : Ideal.span ({a} : Set (𝓞 F)) ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨𝔄, hE, hmap⟩ := exists_exterior_map_eq 𝔪 h𝔪 _ hI
  have hle : 𝔄.map (algebraMap (𝓞 F) (SInt 𝔪)) ≤ Ideal.span {c} := by
    rw [← hmap, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_span_singleton]
    refine ⟨algebraMap (𝓞 F) (SInt 𝔪) b, Subtype.ext ?_⟩
    rw [Subalgebra.coe_mul, ← hab]
    show algebraMap (𝓞 F) F a = algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b * algebraMap (𝓞 F) F b
    field_simp
  have := L2B.finite_quot_map (𝔪 := 𝔪) 𝔄 hE.1 hE.2
  exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle)

/-! ### Transport of residue sums to the quotient by an equal ideal -/

/-! ### A good exterior prime -/

section prime

variable {v : HeightOneSpectrum (𝓞 F)} {ι : F →+* ℂ}
variable (h : C3I.Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (g : AllowedGen ι 𝔪)
  (h𝔪 : 𝔪 ≠ ⊥) (S : CubicSymbol (SInt 𝔪))
  (hS : ∀ d : SInt 𝔪, S.sym d (g.gen v.asIdeal) = sexticResidueSymbol ι 𝔪 v.asIdeal d ^ 2)

include h in
lemma card_quot_gen :
    Nat.card (SInt 𝔪 ⧸ Ideal.span {g.gen v.asIdeal}) = Ideal.absNorm v.asIdeal :=
  (congrArg (fun I : Ideal (SInt 𝔪) => Nat.card (SInt 𝔪 ⧸ I)) (span_gen h g)).trans (C3I.natCard_L h)

include h h𝔪 in
lemma finite_quot_gen_pow (k : ℕ) : Finite (SInt 𝔪 ⧸ Ideal.span {g.gen v.asIdeal ^ k}) :=
  finite_quot_span h𝔪 (pow_ne_zero _ (gen_ne_zero h g))

include h in
/-- Primitivity: `e(a₀/π) ≠ 1` for some `a₀ ∈ R`. -/
lemma exists_ψ_ne_one : ∃ a₀ : SInt 𝔪, (sAdd 𝔪 h𝔪).ψ a₀ (g.gen v.asIdeal) ≠ 1 := by
  have := C3I.isMaximal_v h
  let _ := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have hp := C3I.psi_isPrimitive g h
  by_contra hcon
  push Not at hcon
  refine hp (a := 1) one_ne_zero ?_
  ext y
  rw [AddChar.mulShift_apply, one_mul, AddChar.one_apply, C3I.psi_apply]
  exact hcon (quotLift y)

end prime

end ArtinKP.B7
end

section
-- module Solutions.Artin.KP.S_Basic
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.S.GSection.instAdd _root_.ArtinKP.S.GSection.instAddCommMonoid _root_.ArtinKP.S.GSection.instCoeFunForallComplexForallForall _root_.ArtinKP.S.GSection.instSMulComplex _root_.ArtinKP.S.GSection.instZero _root_.ArtinKP.S.TSection.instCoeFunForallComplexForallRow _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.B.Row.inf_c _root_.ArtinKP.B.Row.inf_d _root_.ArtinKP.G1.scal_apply _root_.ArtinKP.RO.rowClassEquiv_mk _root_.ArtinKP.RO.rowPair_c _root_.ArtinKP.RO.rowPair_d _root_.ArtinKP.S.GSection.add_apply _root_.ArtinKP.S.GSection.nT_apply _root_.ArtinKP.S.GSection.smulFun_apply _root_.ArtinKP.S.GSection.smul_apply _root_.ArtinKP.S.GSection.twist_apply _root_.ArtinKP.S.GSection.zero_apply _root_.ArtinKP.S.TSection.add_apply _root_.ArtinKP.S.TSection.smulFun_apply _root_.ArtinKP.S.TSection.smul_apply _root_.ArtinKP.S.TSection.translate_apply _root_.ArtinKP.S.TSection.zero_apply _root_.ArtinKP.S2.cubicSymbol_sym
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

/-! ### The pairing `⟨x, y⟩ = ι (x, y)_S` on `F` -/

/-! ### Kubota's `σ_S` on a pair and a matrix -/

/-! ### Primitive rows -/

variable {𝔪 : Ideal (𝓞 F)}

/-! ### The Kubota symbol on rows -/

/-! ### The matrices `w` and `n(t)` -/

section kappa2

variable (ι : F →+* ℂ) (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

include P hG hz6

/-- `κ(c, d + ct) = κ(c, d)`. -/
theorem kappaRow_n (p : Row 𝔪) (t : SInt 𝔪) : kappaRow ι (p.act (nMat t)) = kappaRow ι p := by
  have hk : kappa ι 𝔪 (nMat t) = 1 := by
    rw [kappa, if_pos (nMat_10 t)]
  rw [kappaRow_act ι P hG hz6, hk, mul_one]
  have h1 : Xs (0 : F) 1 = 1 := Xs_zero 1
  have e : sig ι P 𝔪 (p.c : F) (p.d : F) (((nMat t).1 0 0 : SInt 𝔪) : F)
      (((nMat t).1 0 1 : SInt 𝔪) : F) (((nMat t).1 1 0 : SInt 𝔪) : F)
      (((nMat t).1 1 1 : SInt 𝔪) : F) = 1 := by
    simp only [sig, nMat_00, nMat_01, nMat_10, nMat_11]
    push_cast
    rw [show (p.c : F) * 1 + (p.d : F) * 0 = p.c by ring, h1, div_one]
    by_cases hc : (p.c : F) = 0
    · have hd : (p.d : F) ≠ 0 := p.ne_zero.resolve_left (not_not.mpr hc)
      simp [hc, div_self hd]
    · simp [Xs_of_ne _ hc, div_self hc]
  rw [e, inv_one, mul_one]

end kappa2

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

theorem Ninf_mul (x y : F) : Ninf (x * y) = Ninf x * Ninf y := by
  simp only [Ninf, map_mul, Finset.prod_mul_distrib]

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

/-! ### Height form (MATH2 §0.2) -/

section height

variable {ι : F →+* ℂ}

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
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.K_Bessel
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-K, file 1: the K-Bessel function

`besselK μ z = ½ ∫_0^∞ t^{μ−1} exp(−(z/2)(t + 1/t)) dt` (`μ : ℂ`, `z : ℝ`; meaningful for `z > 0`),
defined as half the Mellin transform of `besselKer z`.  Mathlib only.

* `besselK_differentiable`: entire in `μ`;
* `besselK_neg`: `K_{−μ} = K_μ`;
* `besselK_ofReal`, `besselKR_pos`: real and positive for real `μ`;
* `norm_besselK_le`: `‖K_μ(z)‖ ≤ K_{Re μ}(z)`;
* `besselKR_le_exp_mul`: `K_μ(z) ≤ e^{−(z−z₀)} K_μ(z₀)` for `z ≥ z₀ > 0`;
* `besselKR_le_gamma`: `K_μ(z) ≤ ½ Γ(|μ|) (z/2)^{−|μ|}` (`μ ≠ 0`);
* `besselKR_le_two_mul`: `K_μ(z) ≤ 2 K_M(z)` for `|μ| ≤ M`;
* `besselKR_le_min`: `K_μ(z) ≤ C min(z^{−|μ|}, z^{−N})` uniformly for `a ≤ |μ| ≤ M ≤ N`;
* `besselK_eq_schlafli`: the Schläfli form `½ (z/2)^{−μ} ∫ t^{μ−1} exp(−t − z²/(4t)) dt`.
-/

namespace ArtinKP.K

open MeasureTheory Set Filter Asymptotics Topology

noncomputable section

/-- The Schläfli form: `K_μ(z) = ½ (z/2)^{−μ} ∫_0^∞ t^{μ−1} exp(−t − z²/(4t)) dt` for `z > 0`
(OpenAI's `schlafliBesselK`). -/
theorem besselK_eq_schlafli (μ : ℂ) {z : ℝ} (hz : 0 < z) :
    besselK μ z = (1 / 2 : ℂ) * ((z / 2 : ℝ) : ℂ) ^ (-μ) *
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (μ - 1) * Complex.exp (-(t : ℂ) - (z : ℂ) ^ 2 / (4 * t)) := by
  have h := mellin_comp_mul_left
    (fun t : ℝ => Complex.exp (-(t : ℂ) - (z : ℂ) ^ 2 / (4 * t))) μ (half_pos hz)
  have hfun : (fun t : ℝ => Complex.exp (-((z / 2 * t : ℝ) : ℂ) - (z : ℂ) ^ 2 / (4 * (z / 2 * t : ℝ))))
      = fun t => (besselKer z t : ℂ) := by
    funext t
    unfold besselKer
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    by_cases ht : t = 0
    · subst ht; simp
    · have hzc : (z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hz.ne'
      have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht
      field_simp
      ring
  rw [hfun] at h
  unfold besselK
  rw [h, smul_eq_mul, mul_assoc]
  rfl

end

end ArtinKP.K
end

section
-- module Solutions.Artin.KP.K_Jacquet
attribute [-instance] _root_.ArtinKP.X.instSigmaFiniteE1Mu1 _root_.ArtinKP.X.instSigmaFiniteXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-! ## Radial integrals on `ℂ` (copied from OpenAI) -/

lemma sourceFrequency_inner (z freq : ℂ) : inner ℝ z (2*starRingEnd ℂ freq) = 2*(freq*z).re := by
  rw [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply]
  change ((2 * starRingEnd ℂ freq) * starRingEnd ℂ z).re = _
  simp [Complex.mul_re, Complex.mul_im]
  ring

lemma traceIntegral_eq_fourier (f : ℂ → ℂ) (freq : ℂ) :
    (∫ z : ℂ, f z * archChar (-freq*z)) = 𝓕 f (2*starRingEnd ℂ freq) := by
  rw [Real.fourier_eq']
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    dsimp only
    rw [sourceFrequency_inner]
    change f z *
      Complex.exp (2*Real.pi*Complex.I*((-freq*z)+starRingEnd ℂ (-freq*z))) = _
    simp only [smul_eq_mul]
    rw [mul_comm (f z)]
    congr 1
    congr 1
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring)

lemma hyperbolicKernel_laplace (s : ℂ) (hs : 0 < s.re) (z : ℂ) :
    hyperbolicKernel s z * Complex.Gamma s =
      ∫ t : ℝ in Set.Ioi 0, (t : ℂ)^(s-1) *
        Complex.exp (-((1+‖z‖^2 : ℝ) : ℂ) * t) := by
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs
    (by positivity : 0 < 1+‖z‖^2)
  simp only [neg_mul]
  rw [h]
  congr 1
  rw [hyperbolicKernel, one_div, Complex.inv_cpow_ofReal_nonneg (by positivity),
    Complex.cpow_neg]

lemma source_gaussian_fourier (t : ℝ) (ht : 0 < t) (freq : ℂ) :
    𝓕 (fun z : ℂ => Complex.exp (-(t : ℂ)*‖z‖^2)) (2*starRingEnd ℂ freq) =
      (Real.pi : ℂ)/t * Complex.exp (-(4*Real.pi^2*‖freq‖^2 : ℝ)/t) := by
  rw [fourier_gaussian_innerProductSpace (by simpa using ht)]
  norm_num only [Complex.finrank_real_complex, Nat.cast_ofNat, div_self (by norm_num : (2:ℂ)≠0),
    Complex.cpow_one, norm_mul, Complex.norm_conj, Complex.norm_ofNat]
  congr 2
  push_cast
  ring

lemma norm_gaussianMixture (s freq : ℂ) (t : ℝ) (ht : 0 < t) (z : ℂ) :
    ‖gaussianMixture s freq t z‖ =
      t ^ (s.re-1) * Real.exp (-t) * Real.exp (-t*‖z‖^2) := by
  simp only [gaussianMixture, norm_mul, archChar_norm, mul_one,
    Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re,
    Complex.norm_exp, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, ← Complex.ofReal_pow, Complex.neg_im, neg_zero, zero_mul, sub_zero]

lemma gaussianMixture_slice_integrable (s freq : ℂ) (t : ℝ) (ht : 0 < t) :
    Integrable (gaussianMixture s freq t) := by
  have hg : Integrable (fun z : ℂ => Complex.exp (-(t : ℂ)*‖z‖^2)) := by
    simpa only [zero_mul, add_zero] using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (by simpa using ht : 0 < (t : ℂ).re) 0 (0 : ℂ)
  apply ((hg.const_mul ((t : ℂ)^(s-1)*Complex.exp (-t))).norm).mono'
  · unfold gaussianMixture
    change AEStronglyMeasurable (fun z : ℂ => (t : ℂ)^(s-1)*Complex.exp (-t)*
      Complex.exp (-(t : ℂ)*‖z‖^2) *
      Complex.exp (2*Real.pi*Complex.I*((-freq*z)+starRingEnd ℂ (-freq*z))))
    fun_prop
  · exact Eventually.of_forall fun z => by
      simp only [gaussianMixture, norm_mul, archChar_norm, mul_one, le_refl]

lemma integral_norm_gaussianMixture (s freq : ℂ) (t : ℝ) (ht : 0 < t) :
    (∫ z : ℂ, ‖gaussianMixture s freq t z‖) =
      Real.pi * (Real.exp (-t)*t^(s.re-2)) := by
  simp_rw [norm_gaussianMixture s freq t ht]
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm ht]
  norm_num only [Complex.finrank_real_complex, Nat.cast_ofNat, div_self (by norm_num : (2:ℝ)≠0),
    Real.rpow_one]
  have hp : t^(s.re-1)/t = t^(s.re-2) := by
    calc
      t^(s.re-1)/t = t^(s.re-1)/t^(1:ℝ) := by rw [Real.rpow_one]
      _ = t^((s.re-1)-1) := (Real.rpow_sub ht _ _).symm
      _ = _ := by congr 1; ring
  calc
    t^(s.re-1)*Real.exp (-t)*(Real.pi/t) = Real.pi*(Real.exp (-t)*(t^(s.re-1)/t)) := by ring
    _ = _ := by rw [hp]

theorem gaussianMixture_integrable (s freq : ℂ) (hs : 1 < s.re) :
    Integrable (fun p : ℝ × ℂ => gaussianMixture s freq p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod volume) := by
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℂ => gaussianMixture s freq p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod volume) := by
    unfold gaussianMixture
    change AEStronglyMeasurable (fun p : ℝ × ℂ =>
      (p.1 : ℂ)^(s-1)*Complex.exp (-p.1)*Complex.exp (-(p.1 : ℂ)*‖p.2‖^2)*
      Complex.exp (2*Real.pi*Complex.I*((-freq*p.2)+starRingEnd ℂ (-freq*p.2)))) _
    fun_prop
  apply (integrable_prod_iff hmeas).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact gaussianMixture_slice_integrable s freq t ht
  · have hgamma := (Real.GammaIntegral_convergent (by linarith : 0 < s.re-1)).const_mul Real.pi
    apply hgamma.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [integral_norm_gaussianMixture s freq t ht]
    congr 2
    ring_nf

lemma gaussianMixture_laplace_form (s freq : ℂ) (t : ℝ) (z : ℂ) :
    gaussianMixture s freq t z =
      ((t : ℂ)^(s-1) * Complex.exp (-((1+‖z‖^2 : ℝ) : ℂ)*t)) *
        archChar (-freq*z) := by
  have he : Complex.exp (-(t : ℂ))*Complex.exp (-(t : ℂ)*‖z‖^2) =
      Complex.exp (-((1+‖z‖^2 : ℝ) : ℂ)*t) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = (t : ℂ)^(s-1) * (Complex.exp (-(t : ℂ))*Complex.exp (-(t : ℂ)*‖z‖^2)) *
        archChar (-freq*z) := by unfold gaussianMixture; ring
    _ = _ := by rw [he]

lemma integral_gaussianMixture_t (s freq : ℂ) (hs : 0 < s.re) (z : ℂ) :
    (∫ t : ℝ in Set.Ioi 0, gaussianMixture s freq t z) =
      (hyperbolicKernel s z * Complex.Gamma s)*archChar (-freq*z) := by
  simp_rw [gaussianMixture_laplace_form]
  rw [integral_mul_const, ← hyperbolicKernel_laplace s hs z]

lemma integral_gaussianMixture_z (s freq : ℂ) (t : ℝ) (ht : 0 < t) :
    (∫ z : ℂ, gaussianMixture s freq t z) =
      (Real.pi : ℂ) * ((t : ℂ)^(s-2) *
        Complex.exp (-(t : ℂ) - (4*Real.pi^2*‖freq‖^2 : ℝ)/t)) := by
  have hfac : (fun z : ℂ => gaussianMixture s freq t z) =
      (fun z : ℂ => ((t : ℂ)^(s-1)*Complex.exp (-t))*
        (Complex.exp (-(t : ℂ)*‖z‖^2)*archChar (-freq*z))) := by
    funext z
    unfold gaussianMixture
    ring
  rw [hfac, integral_const_mul, traceIntegral_eq_fourier, source_gaussian_fourier t ht freq]
  have hp : (t : ℂ)^(s-1)/(t : ℂ) = (t : ℂ)^(s-2) := by
    calc
      _ = (t : ℂ)^(s-1)/(t : ℂ)^(1 : ℂ) := by rw [Complex.cpow_one]
      _ = (t : ℂ)^((s-1)-1) := (Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr ht.ne')).symm
      _ = _ := by congr 1; ring
  calc
    _ = (Real.pi : ℂ)*(((t : ℂ)^(s-1)/t)*
        (Complex.exp (-(t : ℂ))*Complex.exp (-(4*Real.pi^2*‖freq‖^2 : ℝ)/t))) := by ring
    _ = _ := by rw [hp, ← Complex.exp_add]; congr 2; ring_nf

theorem sourceFourierKernel_gamma (s freq : ℂ) (hs : 1 < s.re) :
    sourceFourierKernel s freq * Complex.Gamma s =
      (Real.pi : ℂ) * ∫ t : ℝ in Set.Ioi 0,
        (t : ℂ)^(s-2) * Complex.exp (-(t : ℂ) - (4*Real.pi^2*‖freq‖^2 : ℝ)/t) := by
  have hmix := gaussianMixture_integrable s freq hs
  calc
    _ = ∫ z : ℂ, (hyperbolicKernel s z * Complex.Gamma s)*
        archChar (-freq*z) := by
      rw [sourceFourierKernel, ← integral_mul_const]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by ring
    _ = ∫ z : ℂ, ∫ t : ℝ in Set.Ioi 0, gaussianMixture s freq t z := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => (integral_gaussianMixture_t s freq (by linarith) z).symm
    _ = ∫ t : ℝ in Set.Ioi 0, ∫ z : ℂ, gaussianMixture s freq t z :=
      (integral_integral_swap hmix).symm
    _ = _ := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact integral_gaussianMixture_z s freq t ht

/-! ## The Bessel form (ours, for `besselK`) -/

/-- `∫ (1+|z|²)^{−s} e(−Tr(freq z)) dz = (2π/Γ(s)) (2π|freq|)^{s−1} K_{s−1}(4π|freq|)`. -/
theorem sourceFourierKernel_bessel (s freq : ℂ) (hs : 1 < s.re) (hf : freq ≠ 0) :
    sourceFourierKernel s freq =
      (2*Real.pi : ℂ)/Complex.Gamma s * ((2*Real.pi*‖freq‖ : ℝ) : ℂ)^(s-1) *
        besselK (s-1) (4*Real.pi*‖freq‖) := by
  have hg := Complex.Gamma_ne_zero_of_re_pos (show 0 < s.re by linarith)
  have hz : 0 < 4*Real.pi*‖freq‖ := by
    have := norm_pos_iff.2 hf
    positivity
  have hz2 : (4*Real.pi*‖freq‖)/2 = 2*Real.pi*‖freq‖ := by ring
  have hzc : ((2*Real.pi*‖freq‖ : ℝ) : ℂ) ≠ 0 := by
    rw [← hz2]; exact Complex.ofReal_ne_zero.2 (half_pos hz).ne'
  have hp : ((2*Real.pi*‖freq‖ : ℝ) : ℂ)^(s-1) * ((2*Real.pi*‖freq‖ : ℝ) : ℂ)^(-(s-1)) = 1 := by
    rw [← Complex.cpow_add _ _ hzc, add_neg_cancel, Complex.cpow_zero]
  have hK := besselK_eq_schlafli (s-1) hz
  rw [hz2] at hK
  have hint : (∫ t : ℝ in Set.Ioi 0,
        (t : ℂ)^(s-2) * Complex.exp (-(t : ℂ) - (4*Real.pi^2*‖freq‖^2 : ℝ)/t)) =
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1 - 1) *
        Complex.exp (-(t : ℂ) - ((4*Real.pi*‖freq‖ : ℝ) : ℂ) ^ 2 / (4 * t)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    rw [show s-2=(s-1)-1 by ring]
    apply congrArg (fun w : ℂ => (t : ℂ)^((s-1)-1)*Complex.exp w)
    push_cast
    ring
  have hG := sourceFourierKernel_gamma s freq hs
  rw [hint] at hG
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff hg, hG, hK]
  linear_combination (-(Real.pi : ℂ) * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1 - 1) *
        Complex.exp (-(t : ℂ) - ((4*Real.pi*‖freq‖ : ℝ) : ℂ) ^ 2 / (4 * t))) * hp

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

/-- The Whittaker function: for `ν ≠ 0`,
`∫_ℂ (v/(|x|²+v²))^s e(−Tr(νx)) dx = (2π/Γ(s)) (2π|ν|)^{s−1} · v · K_{s−1}(4π|ν|v)`. -/
theorem jacquet_eq (s : ℂ) (hs : 1 < s.re) {ν : ℂ} (hν : ν ≠ 0) {v : ℝ} (hv : 0 < v) :
    jacquet s ν v = (2 * Real.pi : ℂ) / Complex.Gamma s * ((2 * Real.pi * ‖ν‖ : ℝ) : ℂ) ^ (s - 1) *
      (v : ℂ) * besselK (s - 1) (4 * Real.pi * ‖ν‖ * v) := by
  have hνv : ν * (v : ℂ) ≠ 0 := mul_ne_zero hν (Complex.ofReal_ne_zero.2 hv.ne')
  have hn : ‖ν * (v : ℂ)‖ = ‖ν‖ * v := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hv.le]
  have hvc : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hv.ne'
  rw [jacquet_eq_sourceFourierKernel s ν hv, sourceFourierKernel_bessel s _ hs hνv, hn]
  have h1 : ((2 * Real.pi * (‖ν‖ * v) : ℝ) : ℂ) ^ (s - 1) =
      ((2 * Real.pi * ‖ν‖ : ℝ) : ℂ) ^ (s - 1) * (v : ℂ) ^ (s - 1) := by
    rw [← mul_assoc, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) hv.le]
  have h2 : (v : ℂ) ^ (2 - s) * (v : ℂ) ^ (s - 1) = (v : ℂ) := by
    rw [← Complex.cpow_add _ _ hvc, show 2 - s + (s - 1) = 1 by ring, Complex.cpow_one]
  rw [h1, show 4 * Real.pi * (‖ν‖ * v) = 4 * Real.pi * ‖ν‖ * v by ring]
  linear_combination ((2 * Real.pi : ℂ) / Complex.Gamma s * ((2 * Real.pi * ‖ν‖ : ℝ) : ℂ) ^ (s - 1) *
    besselK (s - 1) (4 * Real.pi * ‖ν‖ * v)) * h2

/-- The same in the normalization `(2π^s/Γ(s)) (2|ν|)^{s−1} v K_{s−1}(4π|ν|v)`. -/
theorem jacquet_eq' (s : ℂ) (hs : 1 < s.re) {ν : ℂ} (hν : ν ≠ 0) {v : ℝ} (hv : 0 < v) :
    jacquet s ν v = 2 * (Real.pi : ℂ) ^ s / Complex.Gamma s * ((2 * ‖ν‖ : ℝ) : ℂ) ^ (s - 1) *
      (v : ℂ) * besselK (s - 1) (4 * Real.pi * ‖ν‖ * v) := by
  rw [jacquet_eq s hs hν hv]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have h1 : ((2 * Real.pi * ‖ν‖ : ℝ) : ℂ) ^ (s - 1) =
      (Real.pi : ℂ) ^ (s - 1) * ((2 * ‖ν‖ : ℝ) : ℂ) ^ (s - 1) := by
    rw [show (2 * Real.pi * ‖ν‖ : ℝ) = Real.pi * (2 * ‖ν‖) by ring, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le (by positivity)]
  have h2 : (Real.pi : ℂ) * (Real.pi : ℂ) ^ (s - 1) = (Real.pi : ℂ) ^ s := by
    have h := Complex.cpow_add (x := (Real.pi : ℂ)) 1 (s - 1) hpi
    rw [Complex.cpow_one, show (1 : ℂ) + (s - 1) = s by ring] at h
    exact h.symm
  rw [h1, ← h2]
  ring

/-! ## Holomorphy in `s` -/

end

end ArtinKP.K
end

section
-- module Solutions.Artin.KP.B_FourArch
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.B.coe_latREquiv _root_.ArtinKP.B.embR_apply
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

theorem continuous_archChar : Continuous archChar := by
  unfold archChar
  fun_prop

theorem continuous_eInf : Continuous (eInf : (InfinitePlace F → ℂ) → ℂ) :=
  continuous_finsetProd _ fun w _ =>
    continuous_archChar.comp (continuous_apply w).neg

theorem emb_mul (a b : F) : emb (a * b) = emb a * emb b := by
  ext w
  simp

/-! ### The `S_f`-character -/

theorem psiS_apply [IsTotallyComplex F] (h𝔪 : 𝔪 ≠ ⊥) (x : F) :
    psiS h𝔪 x = sAddChar 𝔪 x * conj (eInf (emb x)) := rfl

/-- `e_∞(x) = sAddChar(x) · conj ψ_{S_f}(x)` for `x ∈ F` (MATH2 §0.2). -/
theorem eInf_emb_eq [IsTotallyComplex F] (h𝔪 : 𝔪 ≠ ⊥) (x : F) :
    eInf (emb x) = sAddChar 𝔪 x * conj (psiS h𝔪 x) := by
  have h1 : sAddChar 𝔪 x * conj (sAddChar 𝔪 x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_sAddChar h𝔪]
    simp
  rw [psiS_apply, map_mul, Complex.conj_conj, ← mul_assoc, h1, one_mul]

/-- `ψ_{S_f}` is trivial on `𝔩_0`. -/
theorem psiS_small [IsTotallyComplex F] (h𝔪 : 𝔪 ≠ ⊥) {x : F} (hx : Small 𝔪 0 x) :
    psiS h𝔪 x = 1 := by
  have h2 : ∀ v ∈ placesOf 𝔪, v.valuation F x ≤ 1 := fun v hv => by
    have := hx v hv
    simpa using this
  rw [psiS_apply, C3I.sAddChar_eq_of_wit (y := x) (by simp) h2, ← eInf_emb, eInf_mul_conj]

/-! ### The archimedean kernel -/

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

theorem chiInf_emb (ν a : F) : chiInf ν (emb a) = conj (eInf (emb (ν * a))) := by
  rw [chiInf, emb_mul]

theorem continuous_chiInf (ν : F) : Continuous (chiInf ν) :=
  Complex.continuous_conj.comp (continuous_eInf.comp (continuous_const.mul continuous_id))

/-! ### Shifted kernels -/

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
-- module Solutions.Artin.KP.B_FourThm
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.G1.scal_apply
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

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (Φ : GSection ι P 𝔪)
  (s : ℂ) (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) (M : ℤ)

/-- `conj e_∞(ν ·)` is `Λ_M`-periodic when `M` is valid for `ν`. -/
theorem chiInf_transLat {ν : SInt 𝔪} (hV : ValidDepth hG Φ (ν : F) M) (b : transLat 𝔪 M)
    (x : InfinitePlace F → ℂ) :
    chiInf (ν : F) ((b : InfinitePlace F → ℂ) + x) = chiInf (ν : F) x := by
  obtain ⟨b₀, hb₀, hb⟩ := b.2
  have h1 : chiInf (ν : F) (b : InfinitePlace F → ℂ) = 1 := by
    rw [← hb, embR_apply, chiInf_emb, eInf_emb_eq hG.ne_bot,
      C3B.sAddChar_of_mem _ (mul_mem ν.2 b₀.2), hV.char _ hb₀]
    simp
  rw [chiInf_add, h1, one_mul]

theorem Winf_eq {s : ℂ} (hs : 1 < s.re) {ν : F} (hν : ν ≠ 0) {v : InfinitePlace F → ℝ}
    (hv : ∀ w, 0 < v w) :
    Winf s ν v = ∏ w : InfinitePlace F,
      (2 * (Real.pi : ℂ) ^ s / Complex.Gamma s * ((2 * ‖w.embedding ν‖ : ℝ) : ℂ) ^ (s - 1)
        * (v w : ℂ) * besselK (s - 1) (4 * Real.pi * ‖w.embedding ν‖ * v w)) :=
  Finset.prod_congr rfl fun w _ => by
    rw [jacquet_eq' s hs (neg_ne_zero.mpr ((map_ne_zero _).mpr hν)) (hv w), norm_neg]

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.C5_Series
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

variable [IsTotallyComplex F]

/-! ### The Eisenstein series on pair classes -/

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
-- module Solutions.Artin.KP.F_Alg_Sum
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-FA, part 1: summation tools for cube periodicity (MATH2 §5)

* `tsum_orbit_rel`: reindexing of a sum over orbits of a group action along an equivariant
  partial bijection given as a relation (used for rows modulo units).
* `IsReps c T`: `T` is a complete set of representatives of `R ⧸ (c)`; `sum_reps`: sums over `T`
  of periodic functions are `B7.rsum`s; affine substitution; the counts and the vanishing of
  twisted sums used in the strata of Proposition 5.4.
* `sum_reps_addChar` (MATH2 §5.1): `∑_{t ∈ T} e(μ t / π^n) = q^n · 1[π^n ∣ μ]` — the character sum
  behind `(U u)_ν = q³ · 1[v_P(ν) ≥ 0] · u_{νπ³}`.
-/

set_option autoImplicit false

namespace ArtinKP.FA

open ArtinKP.B7

/-! ### Sums over orbits -/

/-! ### Complete sets of representatives -/

section reps

variable {R : Type*} [CommRing R]

/-- A sum over a complete set of representatives is the residue sum. -/
theorem sum_reps {c : R} {T : Finset R} (hT : IsReps c T) {f : R → ℂ} (hf : Per c f) :
    ∑ t ∈ T, f t = rsum c f := by
  classical
  let e : {t // t ∈ T} → R ⧸ Ideal.span {c} := fun t => Ideal.Quotient.mk _ t.1
  have he : Function.Bijective e := by
    constructor
    · intro t t' h
      have h' : c ∣ t.1 - t'.1 := mk_eq_mk_iff.1 h
      obtain ⟨u, -, hu⟩ := hT t.1
      have h1 := hu t.1 ⟨t.2, by simp⟩
      have h2 := hu t'.1 ⟨t'.2, h'⟩
      exact Subtype.ext (h1.trans h2.symm)
    · intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨t, ⟨ht, hdvd⟩, -⟩ := hT a
      exact ⟨⟨t, ht⟩, (mk_eq_mk_iff.2 hdvd).symm⟩
  unfold rsum
  rw [← finsum_eq_of_bijective e he (f := fun t : {t // t ∈ T} => f t.1)
    (g := fun x => f (rep c x)) (fun t => (hf.rep_mk t.1).symm)]
  exact ((finsum_eq_sum_of_fintype _).trans (Finset.sum_coe_sort T f)).symm

variable [IsDomain R] {π : R} (hπ : π ≠ 0) (hfin : ∀ k : ℕ, Finite (R ⧸ Ideal.span {π ^ k}))

include hπ hfin in
/-- `#(R/π^n) = q^n`. -/
lemma rsum_pow_one (n : ℕ) :
    rsum (π ^ n) (fun _ => (1 : ℂ)) = (Nat.card (R ⧸ Ideal.span {π}) : ℂ) ^ n := by
  have h1 := hfin 1
  rw [pow_one] at h1
  cases n with
  | zero =>
    rw [pow_zero, pow_zero]
    have : Subsingleton (R ⧸ Ideal.span {(1 : R)}) :=
      Ideal.Quotient.subsingleton_iff.2 (by simp)
    rw [rsum_one, Nat.card_of_subsingleton (0 : R ⧸ Ideal.span {(1 : R)})]
    simp
  | succ k =>
    rw [rsum_pow_of_per hπ hfin (fun _ _ _ => rfl), rsum_one, pow_succ]

end reps

/-! ### The additive character sum of §5.1 -/

section addchar

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] (A : AddData R K)
  {π : R} (hπ : π ≠ 0) (hmax : (Ideal.span {π}).IsMaximal)
  (hfin : ∀ k : ℕ, Finite (R ⧸ Ideal.span {π ^ k}))

include hπ hmax hfin in
open Classical in
/-- **MATH2 §5.1, the character sum.**  For a complete set `T` of representatives modulo `π^n`
and an additive character `e` trivial on `R` but not on `π⁻¹R`:
`∑_{t ∈ T} e(μ t / π^n) = q^n` if `π^n ∣ μ`, and `0` otherwise. -/
theorem sum_reps_addChar {a₀ : R} (ha₀ : A.ψ a₀ π ≠ 1) (n : ℕ) {T : Finset R}
    (hT : IsReps (π ^ n) T) (μ : R) :
    ∑ t ∈ T, A.ψ (μ * t) (π ^ n)
      = if π ^ n ∣ μ then (Nat.card (R ⧸ Ideal.span {π}) : ℂ) ^ n else 0 := by
  have hπn : π ^ n ≠ 0 := pow_ne_zero _ hπ
  have hper : Per (π ^ n) (fun t => A.ψ (μ * t) (π ^ n)) := fun a b hab =>
    A.ψ_per hπn (by rw [← mul_sub]; exact hab.mul_left μ)
  rw [sum_reps hT hper]
  split_ifs with hdvd
  · obtain ⟨r, rfl⟩ := hdvd
    rw [← rsum_pow_one hπ hfin n]
    exact rsum_congr fun t => by rw [mul_assoc]; exact A.ψ_mul_self hπn _
  · -- the exact power of `π` in `μ`
    have hex : ∃ k, ¬ π ^ (k + 1) ∣ μ := by
      cases n with
      | zero => exact absurd (by simp) hdvd
      | succ n => exact ⟨n, hdvd⟩
    have hspec := Nat.find_spec hex
    have hmin := fun (m : ℕ) (h : m < Nat.find hex) => Nat.find_min hex h
    set k := Nat.find hex with hk
    have hkn : k + 1 ≤ n := by
      by_contra hlt
      rw [not_le] at hlt
      rcases Nat.eq_zero_or_pos n with h1 | h1
      · rw [h1, pow_zero] at hdvd; exact hdvd (one_dvd _)
      · have := hmin (n - 1) (by omega)
        rw [not_not] at this
        have hn : n - 1 + 1 = n := by omega
        rw [hn] at this
        exact hdvd this
    have hdk : π ^ k ∣ μ := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · rw [h0, pow_zero]; exact one_dvd _
      · have := hmin (k - 1) (by omega)
        rw [not_not, Nat.sub_add_cancel hpos] at this
        exact this
    obtain ⟨μ₀, hμ⟩ := hdk
    have hμ₀ : ¬ π ∣ μ₀ := by
      rintro ⟨r, rfl⟩
      apply hspec
      rw [hμ, pow_succ, ← mul_assoc]
      exact Dvd.intro _ rfl
    obtain ⟨x, y, hxy⟩ := (isCoprime_iff_not_dvd hmax μ₀).2 hμ₀
    obtain ⟨l, rfl⟩ : ∃ l, n = k + 1 + l := ⟨n - (k + 1), by omega⟩
    set b : R := x * a₀ * π ^ l with hb
    have hz : A.ψ (μ * b) (π ^ (k + 1 + l)) = A.ψ a₀ π := by
      have e1 : μ * b = (μ₀ * (x * a₀)) * π ^ (k + l) := by rw [hμ, hb, pow_add]; ring
      have e2 : π ^ (k + 1 + l) = π * π ^ (k + l) := by ring
      rw [e1, e2, A.ψ_mul_right_cancel _ _ (pow_ne_zero _ hπ)]
      refine A.ψ_per hπ ⟨-(y * a₀), ?_⟩
      linear_combination a₀ * hxy
    have e1 := rsum_add_right hper b
    have e2 : rsum (π ^ (k + 1 + l)) (fun d => A.ψ (μ * (d + b)) (π ^ (k + 1 + l)))
        = rsum (π ^ (k + 1 + l)) (fun d => A.ψ (μ * d) (π ^ (k + 1 + l))) * A.ψ a₀ π := by
      rw [← rsum_mul_const]
      exact rsum_congr fun d => by rw [mul_add, A.ψ_add, hz]
    rw [e2] at e1
    by_contra hne
    apply ha₀
    exact mul_left_cancel₀ hne (e1.trans (mul_one _).symm)

end addchar

end ArtinKP.FA
end

section
-- module Solutions.Artin.KP.F_Alg_Link
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-FA, part 5: the hypotheses of `F_Alg_*` at an allowed generator

* `PrimeElt.of_span`: `PrimeElt` from `span {π} = P·R`, maximality and a nontrivial symbol;
* `primeElt_gen`: `PrimeElt ι 𝔪 v (g.gen v.asIdeal)` at a good exterior prime, for any
  `S : CubicSymbol (SInt 𝔪)` that agrees with `cubicExt` (the same hypotheses as `E.pairingHS`
  and `B7_Link`);
* `sum_reps_sAddChar`: the character sum of MATH2 §5.1 for `sAddChar` at `g.gen P`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.FA

open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
  {v : HeightOneSpectrum (𝓞 F)} {ι : F →+* ℂ}

section gen

variable (h : C3I.Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (g : AllowedGen ι 𝔪)
  (h𝔪 : 𝔪 ≠ ⊥) (S : CubicSymbol (SInt 𝔪))
  (hS : ∀ d : SInt 𝔪, S.sym d (g.gen v.asIdeal) = sexticResidueSymbol ι 𝔪 v.asIdeal d ^ 2)
  (hsym : ∀ d c : SInt 𝔪, c ≠ 0 → S.sym d c = cubicExt ι 𝔪 d c)

include h h𝔪 in
open Classical in
/-- **MATH2 §5.1** for `sAddChar`: `∑_{t ∈ T} e(μ t/π^n) = (N P)^n · 1[π^n ∣ μ]`, `π = g.gen P`. -/
theorem sum_reps_sAddChar (n : ℕ) {T : Finset (SInt 𝔪)} (hT : IsReps (g.gen v.asIdeal ^ n) T)
    (μ : SInt 𝔪) :
    ∑ t ∈ T, sAddChar 𝔪 ((μ : F) * (t : F) / (g.gen v.asIdeal : F) ^ n)
      = if g.gen v.asIdeal ^ n ∣ μ then (Ideal.absNorm v.asIdeal : ℂ) ^ n else 0 := by
  obtain ⟨a₀, ha₀⟩ := exists_ψ_ne_one h g h𝔪
  have := sum_reps_addChar (sAdd 𝔪 h𝔪) (gen_ne_zero h g) (isMaximal_span_gen h g)
    (finite_quot_gen_pow h g h𝔪) ha₀ n hT μ
  rw [card_quot_gen h g] at this
  rw [← this]
  refine Finset.sum_congr rfl fun t _ => ?_
  change _ = sAddChar 𝔪 _
  congr 1

end gen

end ArtinKP.FA
end
end

section
-- module Solutions.Artin.KP.F_Eis_Op
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-FB, part 2: the maps `g_t` on `X F`, the operator `U`, and the product formula at `π`

MATH2 §5.1: `g_t : (x, v) ↦ ((x + t)/π³, v/|π³|)` is the action of the `GL₂(F)` matrix
`[[1, t], [0, π³]]`, of determinant `π³`; it is **not** in `SL₂(F)`, and the tree's action on
`X F` is of `SL(2, F)` only.  So the map is defined in coordinates, for an arbitrary `a ≠ 0` in
place of `π³`:

* `gmap a ha t : X F → X F`, `(x, v) ↦ ((x + t)/a, v/|a|)` (ordinary moduli at each place);
  `gmap_eq_torus_trans` (it is `X.torus ∘ X.trans`), `measurePreserving_gmap`, `continuous_gmap`;
* `Nh a = ∏_w |a|_w` (ordinary moduli; `Nh a ^ 2 = B.Ninf a`, so `Nh a = N_∞(a)^{1/2}`);
* `pairHt_gmap`: `I_{(c,d)}(g_t Q) = Nh a · I_{(c, c t + a d)}(Q)`
  (MATH2: `N_∞(π)^{3/2}` for `a = π³`); `ht_gmap`;
* `U a ha T u Q = ∑_{t ∈ T} u (g_t Q)`;
* `Ninf_mul_absS_of_span`: `N_∞(π) · |π|_{S_f} = N P` for a generator `π` of `P·R`, `P` exterior
  (the product formula; WP-FA §6 item 2), and `Ninf_mul_absS_gen` at `g.gen P`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.FB

open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E ArtinKP.FA ArtinKP.X ArtinKP.B

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### `Nh`: the product of the ordinary moduli -/

theorem Nh_pos {a : F} (ha : a ≠ 0) : 0 < Nh a :=
  Finset.prod_pos fun _ _ => norm_pos_iff.2 ((map_ne_zero _).2 ha)

theorem Nh_nonneg (a : F) : 0 ≤ Nh a := Finset.prod_nonneg fun _ _ => norm_nonneg _

theorem Nh_sq (a : F) : Nh a ^ 2 = Ninf a := by
  unfold Nh Ninf
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun w _ => (Complex.normSq_eq_norm_sq _).symm

theorem Nh_pow (a : F) (n : ℕ) : Nh (a ^ n) = Nh a ^ n := by
  simp only [Nh, map_pow, norm_pow, Finset.prod_pow]

/-- `Nh(a)^s = N_∞(a)^{s/2}` as complex powers. -/
theorem Nh_cpow {a : F} (ha : a ≠ 0) (s : ℂ) :
    ((Nh a : ℝ) : ℂ) ^ s = ((Ninf a : ℝ) : ℂ) ^ (s / 2) := by
  have h0 : ((Nh a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Nh_pos ha).ne'
  rw [← Nh_sq, sq, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (Nh_nonneg a) (Nh_nonneg a),
    ← Complex.cpow_add _ _ h0]
  congr 1
  ring

/-! ### The maps `g_t` -/

/-! ### The operator `U` -/

/-! ### The product formula at a generator of an exterior prime -/

end ArtinKP.FB
end
end

section
-- module Solutions.Artin.KP.F_Eis_Fourier
attribute [-instance] _root_.ArtinKP.B.instCountableIdxI _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.B1.instCountablePairClass _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instSigmaFiniteE1Mu1 _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.B.coe_latREquiv _root_.ArtinKP.B.embR_apply
/-!
# WP-FB, part 4: the operator `U` on Fourier coefficients (MATH2 §5.1)

Vocabulary of WP-B (`B_FourArch`): `emb : F →+ ℂ^r`, `eInf`, and the character
`chiInf ν x = conj e_∞(ν x)` against which the `ν`-th coefficient is taken; a coefficient is an
integral over a cell `D` (a fundamental domain of a lattice `L ⊂ ℂ^r` of periods).

* `sum_eInf_reps`: `∑_{t ∈ T} e_∞(μ t/πⁿ) = (N P)ⁿ · 1[πⁿ ∣ μ]` for `T` deep
  (`FA.sum_reps_sAddChar` and `B.psiS_small`);
* `setIntegral_image_mulE`: the change of variables `x = a·y` on `ℂ^r`, Jacobian `N_∞(a)`;
* `setIntegral_translate`, `integrableOn_translate`: integrals of periodic functions over a
  cell are translation invariant;
* `coeff_sum_translate`: on `ℂ^r`, for an `L`-periodic `h`,
  `∫_{aD} (∑_t h((x+t)/a)) conj e_∞(νx) dx = N_∞(a) (∑_t e_∞(νt)) ∫_D h(y) conj e_∞(νa·y) dy`;
* `coeff_U`: the same for `U a T u` at height `v`;
* `coeff_U_gen`: **`(Uu)_ν(v) = q³ · 1[ν ∈ R] · u_{νπ³}(v/|π³|)`** at `π = g.gen P`
  (cells `π³D` and `D`; the factor `N_∞(π³) = vol(π³D)/vol(D)` is the normalization of the cell).
-/

set_option autoImplicit false

open scoped ComplexConjugate Pointwise
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.FB

open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E ArtinKP.FA ArtinKP.X ArtinKP.B ArtinKP.B1

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
  {v : HeightOneSpectrum (𝓞 F)} {ι : F →+* ℂ}

/-! ### The character sum in `e_∞` form -/

open Classical in
/-- **MATH2 §5.1, character sum**: for `T` a complete set of representatives of `R/πⁿR` with
`μ t/πⁿ` integral at `S_f` for all `t ∈ T`, `∑_t e_∞(μ t/πⁿ) = (N P)ⁿ · 1[πⁿ ∣ μ]`. -/
theorem sum_eInf_reps [IsTotallyComplex F] (h : C3I.Good 𝔪 v) (g : AllowedGen ι 𝔪) (h𝔪 : 𝔪 ≠ ⊥)
    (n : ℕ) {T : Finset (SInt 𝔪)} (hT : IsReps (g.gen v.asIdeal ^ n) T) (μ : SInt 𝔪)
    (hdeep : ∀ t ∈ T, Small 𝔪 0 ((μ : F) * (t : F) / (g.gen v.asIdeal : F) ^ n)) :
    ∑ t ∈ T, eInf (emb ((μ : F) * (t : F) / (g.gen v.asIdeal : F) ^ n))
      = if g.gen v.asIdeal ^ n ∣ μ then (Ideal.absNorm v.asIdeal : ℂ) ^ n else 0 := by
  rw [← sum_reps_sAddChar h g h𝔪 n hT μ]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [eInf_emb_eq h𝔪, psiS_small h𝔪 (hdeep t ht), map_one, mul_one]

/-! ### Scaling on `ℂ^r` -/

theorem mulE_apply (A y : InfinitePlace F → ℂ) : mulE A y = A * y := by
  ext w
  simp [mulE]

theorem det_mulE (A : InfinitePlace F → ℂ) :
    LinearMap.det (mulE A) = ∏ w, Complex.normSq (A w) := by
  rw [mulE, LinearMap.det_pi]
  refine Finset.prod_congr rfl fun w _ => ?_
  change LinearMap.det (Algebra.lmul ℝ ℂ (A w)) = _
  rw [← Algebra.norm_apply, Algebra.norm_complex_apply]

/-- Change of variables `x = A·y` on `ℂ^r`: the Jacobian is `∏_w |A_w|²`. -/
theorem setIntegral_image_mulE {A : InfinitePlace F → ℂ} (hA : ∀ w, A w ≠ 0)
    {D : Set (InfinitePlace F → ℂ)} (hD : MeasurableSet D) (G : (InfinitePlace F → ℂ) → ℂ) :
    ∫ x in (fun y => A * y) '' D, G x
      = ((∏ w, Complex.normSq (A w) : ℝ) : ℂ) * ∫ y in D, G (A * y) := by
  have e : (fun y : InfinitePlace F → ℂ => A * y)
      = ⇑(LinearMap.toContinuousLinearMap (mulE A)) := funext fun y => (mulE_apply A y).symm
  have hinj : Set.InjOn (fun y : InfinitePlace F → ℂ => A * y) D := by
    intro y _ y' _ hyy
    funext w
    exact mul_left_cancel₀ (hA w) (congrFun hyy w)
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume hD
    (f := fun y : InfinitePlace F → ℂ => A * y)
    (f' := fun _ => LinearMap.toContinuousLinearMap (mulE A))
    (fun x _ => by
      rw [e]
      exact (LinearMap.toContinuousLinearMap (mulE A)).hasFDerivAt.hasFDerivWithinAt) hinj G
  rw [h]
  have hdet : (LinearMap.toContinuousLinearMap (mulE A)).det = ∏ w, Complex.normSq (A w) := by
    rw [ContinuousLinearMap.det, LinearMap.coe_toContinuousLinearMap, det_mulE]
  simp only [hdet]
  rw [abs_of_nonneg (Finset.prod_nonneg fun w _ => Complex.normSq_nonneg _), integral_smul,
    Complex.real_smul]

/-! ### Translation invariance over a cell -/

section cell

variable {L : AddSubgroup (InfinitePlace F → ℂ)} [Countable L]
  {D : Set (InfinitePlace F → ℂ)}

theorem preimage_add_right_vadd (c : InfinitePlace F → ℂ) (D : Set (InfinitePlace F → ℂ)) :
    (fun y => y + c) ⁻¹' (c +ᵥ D) = D := by
  ext y
  rw [Set.mem_preimage, Set.mem_vadd_set]
  constructor
  · rintro ⟨d, hd, hdy⟩
    have : d = y := by
      rw [vadd_eq_add, add_comm] at hdy
      exact add_right_cancel hdy
    exact this ▸ hd
  · intro hy
    exact ⟨y, hy, by rw [vadd_eq_add, add_comm]⟩

/-- The integral of an `L`-periodic function over a cell is invariant under translation of the
argument. -/
theorem setIntegral_translate (hD : IsAddFundamentalDomain L D volume)
    {G : (InfinitePlace F → ℂ) → ℂ}
    (hG : ∀ (b : L) (x : InfinitePlace F → ℂ), G ((b : InfinitePlace F → ℂ) + x) = G x)
    (c : InfinitePlace F → ℂ) : ∫ y in D, G (y + c) = ∫ y in D, G y := by
  have hD' : IsAddFundamentalDomain L (c +ᵥ D) volume := hD.vadd_of_comm c
  have h1 := (measurePreserving_add_right (volume : Measure (InfinitePlace F → ℂ))
    c).setIntegral_preimage_emb (measurableEmbedding_addRight c) G (c +ᵥ D)
  rw [preimage_add_right_vadd] at h1
  rw [h1]
  exact hD'.setIntegral_eq hD fun b x => hG b x

theorem integrableOn_translate (hD : IsAddFundamentalDomain L D volume)
    {G : (InfinitePlace F → ℂ) → ℂ}
    (hG : ∀ (b : L) (x : InfinitePlace F → ℂ), G ((b : InfinitePlace F → ℂ) + x) = G x)
    (hint : IntegrableOn G D) (c : InfinitePlace F → ℂ) :
    IntegrableOn (fun y => G (y + c)) D := by
  have hD' : IsAddFundamentalDomain L (c +ᵥ D) volume := hD.vadd_of_comm c
  have h1 := (measurePreserving_add_right (volume : Measure (InfinitePlace F → ℂ))
    c).integrableOn_comp_preimage (measurableEmbedding_addRight c) (f := G) (s := c +ᵥ D)
  rw [preimage_add_right_vadd] at h1
  exact h1.2 ((hD'.integrableOn_iff hD fun b x => hG b x).2 hint)

/-- **The operator `∑_t h((x + t)/a)` on Fourier coefficients**, on `ℂ^r`: for an `L`-periodic
`h`, integrable over the cell `D`, and `ν` with `conj e_∞(νa ·)` trivial on `L`,
`∫_{aD} (∑_t h((x+t)/a)) conj e_∞(νx) dx = N_∞(a) (∑_t e_∞(νt)) ∫_D h(y) conj e_∞(νa y) dy`. -/
theorem coeff_sum_translate (hDm : MeasurableSet D) (hD : IsAddFundamentalDomain L D volume)
    {a : F} (ha : a ≠ 0) (T : Finset (SInt 𝔪)) (h : (InfinitePlace F → ℂ) → ℂ)
    (hper : ∀ (b : L) (x : InfinitePlace F → ℂ), h ((b : InfinitePlace F → ℂ) + x) = h x)
    (hint : IntegrableOn h D) (ν : F)
    (hν : ∀ b : L, chiInf (ν * a) (b : InfinitePlace F → ℂ) = 1) :
    ∫ x in (fun y => emb a * y) '' D, (∑ t ∈ T, h ((x + emb (t : F)) / emb a)) * chiInf ν x
      = ((Ninf a : ℝ) : ℂ) * ((∑ t ∈ T, eInf (emb (ν * (t : F))))
          * ∫ y in D, h y * chiInf (ν * a) y) := by
  have hA : ∀ w : InfinitePlace F, emb a w ≠ 0 := fun w => by
    rw [emb_apply]
    exact (map_ne_zero _).2 ha
  rw [setIntegral_image_mulE hA hDm]
  congr 1
  set G : (InfinitePlace F → ℂ) → ℂ := fun y => h y * chiInf (ν * a) y with hGdef
  have hGper : ∀ (b : L) (x : InfinitePlace F → ℂ), G ((b : InfinitePlace F → ℂ) + x) = G x := by
    intro b x
    simp only [hGdef]
    rw [hper, chiInf_add, hν, one_mul]
  have hGint : IntegrableOn G D := by
    refine Integrable.mono hint
      (hint.aestronglyMeasurable.mul (continuous_chiInf (ν * a)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => ?_)
    simp only [hGdef]
    rw [norm_mul, norm_chiInf, mul_one]
  have key : ∀ y : InfinitePlace F → ℂ,
      (∑ t ∈ T, h ((emb a * y + emb (t : F)) / emb a)) * chiInf ν (emb a * y)
        = ∑ t ∈ T, eInf (emb (ν * (t : F))) * G (y + emb ((t : F) / a)) := by
    intro y
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    have e1 : (emb a * y + emb (t : F)) / emb a = y + emb ((t : F) / a) := by
      funext w
      have := hA w
      simp only [Pi.div_apply, Pi.add_apply, Pi.mul_apply, emb_apply, map_div₀] at this ⊢
      field_simp
    have e2 : chiInf ν (emb a * y) = chiInf (ν * a) y := by
      rw [chiInf, chiInf, emb_mul, mul_assoc]
    have e3 : eInf (emb (ν * (t : F))) * chiInf (ν * a) (emb ((t : F) / a)) = 1 := by
      rw [chiInf_emb]
      have : ν * a * ((t : F) / a) = ν * (t : F) := by field_simp
      rw [this, eInf_mul_conj]
    simp only [hGdef]
    rw [e1, e2, chiInf_add]
    calc h (y + emb ((t : F) / a)) * chiInf (ν * a) y
        = (eInf (emb (ν * (t : F))) * chiInf (ν * a) (emb ((t : F) / a)))
            * (h (y + emb ((t : F) / a)) * chiInf (ν * a) y) := by rw [e3, one_mul]
      _ = _ := by ring
  simp only [key]
  rw [integral_finset_sum T fun t _ =>
    (integrableOn_translate hD hGper hGint (emb ((t : F) / a))).const_mul _, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [integral_const_mul, setIntegral_translate hD hGper]

/-- The same for the operator `U a T` at height `v`: the `ν`-th coefficient of `U u` over the
cell `aD` at height `v` is `N_∞(a) (∑_t e_∞(νt))` times the `νa`-th coefficient of `u` over `D`
at height `v/|a|`. -/
theorem coeff_U (hDm : MeasurableSet D) (hD : IsAddFundamentalDomain L D volume)
    {a : F} (ha : a ≠ 0) (T : Finset (SInt 𝔪)) (u : X F → ℂ)
    (vv : InfinitePlace F → ℝ) (hvv : ∀ w, 0 < vv w)
    (hper : ∀ (b : L) (x : InfinitePlace F → ℂ),
      u (X.mk ((b : InfinitePlace F → ℂ) + x) (fun w => vv w / ‖w.embedding a‖)
          (fun w => div_pos (hvv w) (norm_pos_iff.2 ((map_ne_zero _).2 ha))))
        = u (X.mk x (fun w => vv w / ‖w.embedding a‖)
          (fun w => div_pos (hvv w) (norm_pos_iff.2 ((map_ne_zero _).2 ha)))))
    (hint : IntegrableOn (fun y => u (X.mk y (fun w => vv w / ‖w.embedding a‖)
      (fun w => div_pos (hvv w) (norm_pos_iff.2 ((map_ne_zero _).2 ha))))) D)
    (ν : F) (hν : ∀ b : L, chiInf (ν * a) (b : InfinitePlace F → ℂ) = 1) :
    ∫ x in (fun y => emb a * y) '' D, U a ha T u (X.mk x vv hvv) * chiInf ν x
      = ((Ninf a : ℝ) : ℂ) * ((∑ t ∈ T, eInf (emb (ν * (t : F))))
          * ∫ y in D, u (X.mk y (fun w => vv w / ‖w.embedding a‖)
              (fun w => div_pos (hvv w) (norm_pos_iff.2 ((map_ne_zero _).2 ha))))
            * chiInf (ν * a) y) :=
  coeff_sum_translate hDm hD ha T _ hper hint ν hν

open Classical in
/-- **MATH2 §5.1**: `(Uu)_ν(v) = q³ · 1[ν ∈ R] · u_{νπ³}(v/|π³|)` for `π = g.gen P`, `q = N P`,
`ν = μ/π³` with `μ ∈ R`.  Coefficients are taken over the cell `π³D` on the left and `D` on the
right (`vol(π³D) = N_∞(π³) vol(D)`); `u(·, v/|π³|)` is `L`-periodic and integrable over `D`,
`conj e_∞(μ ·)` is trivial on `L`, and `T` is deep enough that `ν t` is integral at `S_f`. -/
theorem coeff_U_gen [IsTotallyComplex F] (h : C3I.Good 𝔪 v) (g : AllowedGen ι 𝔪) (h𝔪 : 𝔪 ≠ ⊥)
    (hDm : MeasurableSet D) (hD : IsAddFundamentalDomain L D volume)
    {T : Finset (SInt 𝔪)} (hT : IsReps (g.gen v.asIdeal ^ 3) T) (u : X F → ℂ)
    (vv : InfinitePlace F → ℝ) (hvv : ∀ w, 0 < vv w)
    (hπ : (g.gen v.asIdeal : F) ^ 3 ≠ 0)
    (hper : ∀ (b : L) (x : InfinitePlace F → ℂ),
      u (X.mk ((b : InfinitePlace F → ℂ) + x)
          (fun w => vv w / ‖w.embedding ((g.gen v.asIdeal : F) ^ 3)‖)
          (fun w => div_pos (hvv w) (norm_pos_iff.2 ((map_ne_zero _).2 hπ))))
        = u (X.mk x (fun w => vv w / ‖w.embedding ((g.gen v.asIdeal : F) ^ 3)‖)
          (fun w => div_pos (hvv w) (norm_pos_iff.2 ((map_ne_zero _).2 hπ)))))
    (hint : IntegrableOn (fun y => u (X.mk y
      (fun w => vv w / ‖w.embedding ((g.gen v.asIdeal : F) ^ 3)‖)
      (fun w => div_pos (hvv w) (norm_pos_iff.2 ((map_ne_zero _).2 hπ))))) D)
    (μ : SInt 𝔪) (hμ : ∀ b : L, chiInf (μ : F) (b : InfinitePlace F → ℂ) = 1)
    (hdeep : ∀ t ∈ T, Small 𝔪 0 ((μ : F) * (t : F) / (g.gen v.asIdeal : F) ^ 3)) :
    ∫ x in (fun y => emb ((g.gen v.asIdeal : F) ^ 3) * y) '' D,
        U ((g.gen v.asIdeal : F) ^ 3) hπ T u (X.mk x vv hvv)
          * chiInf ((μ : F) / (g.gen v.asIdeal : F) ^ 3) x
      = ((Ninf ((g.gen v.asIdeal : F) ^ 3) : ℝ) : ℂ) *
        ((if g.gen v.asIdeal ^ 3 ∣ μ then (Ideal.absNorm v.asIdeal : ℂ) ^ 3 else 0)
          * ∫ y in D, u (X.mk y (fun w => vv w / ‖w.embedding ((g.gen v.asIdeal : F) ^ 3)‖)
              (fun w => div_pos (hvv w) (norm_pos_iff.2 ((map_ne_zero _).2 hπ))))
            * chiInf (μ : F) y) := by
  have e : (μ : F) / (g.gen v.asIdeal : F) ^ 3 * (g.gen v.asIdeal : F) ^ 3 = (μ : F) :=
    div_mul_cancel₀ _ hπ
  have key := coeff_U hDm hD hπ T u vv hvv hper hint ((μ : F) / (g.gen v.asIdeal : F) ^ 3)
    (by rw [e]; exact hμ)
  rw [key, e, ← sum_eInf_reps h g h𝔪 3 hT μ hdeep]
  congr 2
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 2
  ring

end cell

end ArtinKP.FB
end
end

section
-- module Solutions.Artin.KP.F_Eis_Main
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-FB, part 3: Proposition 5.4 for the Eisenstein series `B.eis`, `Re s > 2` (MATH2 §5.3)

With `Ψ = Φ.twist`, `Ψ♯ = (Φ.sharp π).twist`, `q = #(R/πR) = N P`, `T` a complete set of
representatives of `R/π³R` deep for `Φ`, and `U = FB.U (π³) T`:

  `U (eis Ψ s) Q = Nh(π³)^s · [ q³·(q^{-s})³ · eis Ψ♯ s Q + (1 − q²·(q^{-s})³) · eis (restrict Ψ♯) s Q ]`

pointwise in `Q : X F`, for every `s` with `Re s > 2`; `Nh(π³)^s = N_∞(π)^{3s/2}`
(`Nh_pi_cube_cpow`), `q³(q^{-s})³ = q^{3-3s}`, `q²(q^{-s})³ = q^{2-3s}` (`q_cpow_three`,
`q_cpow_two`).

* `primeElt_gen'`: `FA.PrimeElt` at `g.gen P`, unconditional (S2's cubic symbol);
* `fQ`, `fQ_pi`, `fQ_unit`: the summand `f = I_p(Q)^s` and its two homogeneities;
* `term_gmap`, `eis_gmap`: `eis Ψ s (g_t Q) = Nh(π³)^s · ∑' gU`;
* `U_eis_primeElt`: the identity for any `PrimeElt`, with FA's constants;
* `U_eis`: the same with `X = (q^{-s})³` under `N_∞(π)|π|_{S_f} = q`;
* `U_eis_gen`, `exists_U_eis_gen`: at an allowed generator of a good exterior prime, all
  hypotheses discharged; the second also produces the deep `T`, uniformly in `s`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.FB

open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E ArtinKP.FA ArtinKP.X ArtinKP.B

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
  {v : HeightOneSpectrum (𝓞 F)} {ι : F →+* ℂ}

/-! ### The summand `f = I_p(Q)^s` -/

/-! ### The Eisenstein series at `g_t Q` -/

/-! ### Rewriting the constants in MATH2's form -/

/-- `Nh(π³)^s = N_∞(π)^{3s/2}`. -/
theorem Nh_pi_cube_cpow {a : F} (ha : a ≠ 0) (s : ℂ) :
    ((Nh (a ^ 3) : ℝ) : ℂ) ^ s = ((Ninf a : ℝ) : ℂ) ^ (3 * s / 2) := by
  have h0 : 0 ≤ Nh a := Nh_nonneg a
  have hN : ((Ninf a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Ninf_pos ha).ne'
  rw [Nh_pow, pow_three, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg h0 (mul_nonneg h0 h0), Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg h0 h0,
    Nh_cpow ha, ← Complex.cpow_add _ _ hN, ← Complex.cpow_add _ _ hN]
  congr 1
  ring

/-- `q³ (q^{-s})³ = q^{3-3s}`. -/
theorem q_cpow_three {q : ℕ} (hq : q ≠ 0) (s : ℂ) :
    (q : ℂ) ^ 3 * ((q : ℂ) ^ (-s)) ^ 3 = (q : ℂ) ^ (3 - 3 * s) := by
  have h0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  rw [← Complex.cpow_nat_mul, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ h0]
  congr 1; push_cast; ring

/-- `q² (q^{-s})³ = q^{2-3s}`. -/
theorem q_cpow_two {q : ℕ} (hq : q ≠ 0) (s : ℂ) :
    (q : ℂ) ^ 2 * ((q : ℂ) ^ (-s)) ^ 3 = (q : ℂ) ^ (2 - 3 * s) := by
  have h0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  rw [← Complex.cpow_nat_mul, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ h0]
  congr 1; push_cast; ring

/-! ### At an allowed generator of a good exterior prime -/

/-! ### Regularity in `s` and `Q`, and almost-everywhere classes

What a later package needs to continue the identity of `U_eis_gen` analytically: `T` does not
depend on `s` (`exists_U_eis_gen`); both sides are holomorphic in `s` on `Re s > 2` for each
`Q` (`differentiableOn_U_eis`, `B.differentiableOn_eis`) and continuous in `Q`; and `U` is
defined on almost-everywhere classes (`U_ae_congr`, from `measurePreserving_gmap`), so it acts
on `L²_loc`-valued functions of `s`. -/

end ArtinKP.FB
end
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

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.T_Lat
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-! ### The two families of lattices -/

/-! ### Cells -/

lemma integrableOn_of_bdd {D : Set (InfinitePlace F → ℂ)} {n : ℕ}
    (h : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) {f : (InfinitePlace F → ℂ) → ℂ} (hf : Continuous f) :
    IntegrableOn f D volume := by
  have hsub : D ⊆ Metric.closedBall (0 : InfinitePlace F → ℂ) n := fun x hx => by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)]
    exact h x hx
  exact (hf.continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set hsub

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.T_Vanish
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-T, file 8: vanishing of the coefficients at characters outside the full dual lattice

Let `Γ`, `Γ'` be of finite index, both fixing `Ψ`, `D` a bounded strict cell of `Λ_Γ` and
`ν' ∈ RF.dualLat Γ`.  If `e_{ν'}(g) ≠ 1` for some `g ∈ Λ_{Γ'}`, then the `ν'`-th Fourier
coefficient over `D` vanishes: for the series (`integral_eis_eChar_eq_zero`, `Re s > 2`), for the
continuation (`Afun_eChar_eq_zero`, on `E.slit`) and for `θ_Ψ` (**`coeff_theta_eq_zero`**).

For a genuine section `Φ` the group `Γ'` can be taken with `Λ_{Γ'} ⊇ Λ_M` for every depth `M ≥ 0`
of unipotent invariance (`transLat_le_latN_stabGroup`), whence
**`coeff_theta_eq_zero_of_transLat`**: only the characters trivial on `Λ_M` contribute to `θ`.
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
  {ι : F →+* ℂ}

/-- `E_Ψ(·, v)` is periodic under the translation lattice of any group fixing `Ψ`. -/
theorem eis_add_latN (h𝔪 : 𝔪 ≠ ⊥) {Γ' : Subgroup (SL(2, 𝓞 F))} {Ψ : TSection ι 𝔪}
    (hΓ' : Inv Γ' Ψ) (s : ℂ) {g : InfinitePlace F → ℂ} (hg : g ∈ latN Γ')
    (x : InfinitePlace F → ℂ) (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) :
    eis Ψ s (X.mk (x + g) v hv) = eis Ψ s (X.mk x v hv) := by
  obtain ⟨β, hβ, rfl⟩ := hg
  have h1 : eis Ψ s (nInt β • X.mk x v hv) = eis Ψ s (X.mk x v hv) :=
    isInv_eis h𝔪 hΓ' s ⟨nInt β, hβ⟩ (X.mk x v hv)
  rw [nInt_smul_mk] at h1
  rw [embO_apply, h1]

/-! ### Genuine sections: the stabilizer contains `n(Λ_M)` -/

section genuine

variable {P : CubicPkg F} (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  (Φ : GSection ι P 𝔪)

lemma inv_stabGroup (Ψ : TSection ι 𝔪) : Inv (stabGroup Ψ) Ψ := fun _ hγ => hγ

lemma intMat_nInt (β : 𝓞 F) :
    RO.intMat 𝔪 (nInt β) = S.nMat (algebraMap (𝓞 F) (SInt 𝔪) β) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [RO.intMat, nInt_coe, S.nMat]

/-- `Λ_M ⊆ Λ_{stab}` for a depth `M ≥ 0` of unipotent invariance of `Φ`. -/
theorem transLat_le_latN_stabGroup {M : ℤ} (hM : 0 ≤ M)
    (hunip : ∀ b : F, Small 𝔪 M b → ∀ (s : ℂ) (c d : F), Φ s c (d + c * b) = Φ s c d) :
    transLat 𝔪 M ≤ latN (stabGroup (Φ.twist hG hz6)) := by
  intro g hg
  obtain ⟨β, -, hβ⟩ := transLat_le_latO hM hg
  obtain ⟨b, hb, hbg⟩ := hg
  have hβb : ((β : 𝓞 F) : F) = (b : F) := by
    have h0 : emb (((β : 𝓞 F) : F) - (b : F)) = 0 := by
      rw [map_sub, sub_eq_zero]
      have h1 : emb ((β : 𝓞 F) : F) = g := hβ
      have h2 : emb (b : F) = g := hbg
      rw [h1, h2]
    exact sub_eq_zero.mp (emb_eq_zero h0)
  refine ⟨β, ?_, hβ⟩
  change RO.intMat 𝔪 (nInt β) ∈ (Φ.twist hG hz6).stab
  rw [intMat_nInt, TSection.mem_stab]
  intro s p
  rw [GSection.twist_apply, GSection.twist_apply, kappaRow_n ι P hG hz6, act_nMat_c,
    act_nMat_d]
  have hsm : Small 𝔪 M ((β : 𝓞 F) : F) := by
    rw [hβb]; exact hb
  have h3 := hunip _ hsm s (p.c : F) (p.d : F)
  push_cast
  rw [add_comm]
  rw [h3]

end genuine

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.F_Per_Mean
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-F, file 1: means over cells of admissible lattices; scaled lattices

* `Adm A`: the lattice `A ⊂ ℂ^r` lies between `emb(I)` (`I` a nonzero ideal) and `emb(𝓞_F)`.
  `latN Γ`, `transLat 𝔪 M` (`M ≥ 0`) and `scaleLat a (transLat 𝔪 M)` (`a ∈ R`, `M` large) are
  admissible.
* `mean_adm`: a continuous `A₁`-periodic function whose integrals over all translates of a cell of
  `A₂` are `vol·I` has integral `vol(D₁)·I` over every bounded strict cell of `A₁` (`T.mean_eq`).
* `scaleLat a L`, `scaleSet a D`: the lattice `a·L` and its cell `a·D`.
* `hasCoef_adm`: `T.hasCoef_latN` for cells of any admissible lattice of periods.
* `const_adm`: the constant term of `E_Φ` over such a cell (`B.const_term_mCoeff`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.F

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N
  ArtinKP.T

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

/-! ### Admissible lattices -/

/-! ### Scaled lattices and cells -/

lemma exists_bdd_scaleSet (a : F) {D : Set (InfinitePlace F → ℂ)} {n : ℕ}
    (h : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) : ∃ n' : ℕ, ∀ x ∈ scaleSet a D, ∀ w, ‖x w‖ ≤ n' := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖emb a‖
  refine ⟨N * n, ?_⟩
  rintro x ⟨y, hy, rfl⟩ w
  change ‖emb a w * y w‖ ≤ _
  rw [norm_mul]
  push_cast
  exact mul_le_mul ((norm_le_pi_norm (emb a) w).trans hN) (h y hy w) (norm_nonneg _)
    (Nat.cast_nonneg _)

/-- `vol(a·D) = N_∞(a)·vol(D)`. -/
lemma volume_scaleSet {a : F} (ha : a ≠ 0) {D : Set (InfinitePlace F → ℂ)}
    (hD : MeasurableSet D) :
    (((volume (scaleSet a D)).toReal : ℝ) : ℂ)
      = ((Ninf a : ℝ) : ℂ) * (((volume D).toReal : ℝ) : ℂ) := by
  have hA : ∀ w : InfinitePlace F, emb a w ≠ 0 := fun w => by
    rw [emb_apply]; exact (map_ne_zero _).2 ha
  have h := FB.setIntegral_image_mulE hA hD (fun _ => (1 : ℂ))
  rw [setIntegral_const, setIntegral_const] at h
  simp only [Complex.real_smul, mul_one, measureReal_def] at h
  rw [scaleSet, h]
  rfl

/-! ### Coefficients over cells of admissible lattices -/

end

end ArtinKP.F
end

section
-- module Solutions.Artin.KP.F_Per_Sharp
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-F, file 2: `Φ♯` and `Ã(π)³`

* `sharp_sharp_inv`: `Φ ↦ Φ♯` (at `π`) is inverted by `♯` at `π⁻¹`.
* **`iterate_act`**: `Ã(π)³ Φ = |π|_{S_f}^{-3} • Φ♯` as genuine sections (MATH2 §4.4, last display).
* `Lam_sharp`: `Lam Φ♯ c μ = |π|³ · Lam Φ c (π³ μ)`; `mCoeff_sharp`: `m_{Φ♯} = |π|³ m_Φ`.
* `sharp_zero_one`: `Φ♯_s(0, 1) = |π|^{3s} Φ_s(0, 1)`.
-/

open scoped ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.F

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.B7 ArtinKP.E

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (Φ : GSection ι P 𝔪)

lemma cpow_pos_eq {x : ℝ} (hx : 0 < x) (z : ℂ) :
    ((x : ℝ) : ℂ) ^ z = Complex.exp ((Real.log x : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), Complex.ofReal_log hx.le]

end

end ArtinKP.F
end

section
-- module Solutions.Artin.KP.F_Per_U
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-F, file 3: Proposition 5.4 integrated against a character over a cell

`U_coeff`: for `Re s > 2`, a cell `D` of `Λ_M` (`M ≥ 0` valid for `(Φ, μ)`), `a = π³`:

`N_∞(π)^{3s/2}·[q^{3−3s} ∫_{aD} E_{Ψ♯} χ_{μ/a} + (1 − q^{2−3s}) ∫_{aD} E_{Ψ♯ρ_∞} χ_{μ/a}]
   = N_∞(a)·1[π³ ∣ μ]·q³·∫_D E_Ψ(·, v/|a|) χ_μ`

(`FB.U_eis_gen` integrated; the left side by linearity, the right side by `FB.coeff_U_gen`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.F

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N
  ArtinKP.T ArtinKP.B7 ArtinKP.FA

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F} {v : HeightOneSpectrum (𝓞 F)}

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (h : C3I.Good 𝔪 v)
  (g : AllowedGen ι 𝔪) (Φ : GSection ι P 𝔪)

lemma chiInf_transLat_one {M : ℤ} {μ : SInt 𝔪} (hV : ValidDepth hG Φ (μ : F) M)
    {b : InfinitePlace F → ℂ} (hb : b ∈ transLat 𝔪 M) : chiInf (μ : F) b = 1 := by
  have h1 := chiInf_transLat hG Φ M hV ⟨b, hb⟩ 0
  rw [chiInf_add] at h1
  have h0 : chiInf (μ : F) (0 : InfinitePlace F → ℂ) ≠ 0 := by
    intro h0
    have := norm_chiInf (μ : F) (0 : InfinitePlace F → ℂ)
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  exact mul_right_cancel₀ h0 (by rw [one_mul]; exact h1)

lemma continuous_eis_chi (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) {s : ℂ} (hs : 2 < s.re)
    (vv : InfinitePlace F → ℝ) (hvv : ∀ w, 0 < vv w) (ν : F) :
    Continuous fun x : InfinitePlace F → ℂ => eis Ψ s (X.mk x vv hvv) * chiInf ν x :=
  ((continuous_eis h𝔪 Ψ hs).comp (continuous_mk_x vv hvv)).mul (continuous_chiInf ν)

open Classical in
include hG hz6 in
/-- **Proposition 5.4 on Fourier coefficients over a cell.** -/
theorem U_coeff {T : Finset (SInt 𝔪)} (hT : IsU hG hz6 h g Φ T) {M : ℤ} (hM : 0 ≤ M)
    (μ : SInt 𝔪) (hV : ValidDepth hG Φ (μ : F) M)
    (hdeep : ∀ t ∈ T, Small 𝔪 0 ((μ : F) * (t : F) / (g.gen v.asIdeal : F) ^ 3))
    {D : Set (InfinitePlace F → ℂ)} (hD : PCell (transLat 𝔪 M) D) {n : ℕ}
    (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) {s : ℂ} (hs : 2 < s.re) (vv : InfinitePlace F → ℝ)
    (hvv : ∀ w, 0 < vv w) :
    ((Ninf (g.gen v.asIdeal : F) : ℝ) : ℂ) ^ (3 * s / 2) *
      ((Ideal.absNorm v.asIdeal : ℂ) ^ (3 - 3 * s)
        * (∫ x in scaleSet ((g.gen v.asIdeal : F) ^ 3) D,
            eis ((Φ.sharp hG (g.gen v.asIdeal : F) (gen_coe_ne_zero h g)).twist hG hz6) s
              (X.mk x vv hvv) * chiInf ((μ : F) / (g.gen v.asIdeal : F) ^ 3) x)
        + (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (2 - 3 * s))
          * (∫ x in scaleSet ((g.gen v.asIdeal : F) ^ 3) D,
            eis (TSection.restrict v (not_le_of_good h)
              ((Φ.sharp hG (g.gen v.asIdeal : F) (gen_coe_ne_zero h g)).twist hG hz6)) s
              (X.mk x vv hvv) * chiInf ((μ : F) / (g.gen v.asIdeal : F) ^ 3) x))
      = ((Ninf ((g.gen v.asIdeal : F) ^ 3) : ℝ) : ℂ) *
        ((if g.gen v.asIdeal ^ 3 ∣ μ then (Ideal.absNorm v.asIdeal : ℂ) ^ 3 else 0)
          * ∫ y in D, eis (Φ.twist hG hz6) s
              (X.mk y (fun w => vv w / ‖w.embedding ((g.gen v.asIdeal : F) ^ 3)‖)
                (fun w => div_pos (hvv w) (norm_pos_iff.2 ((map_ne_zero _).2
                  (pow_ne_zero 3 (gen_coe_ne_zero h g))))))
            * chiInf (μ : F) y) := by
  have h𝔪 := hG.ne_bot
  have hπ3 : (g.gen v.asIdeal : F) ^ 3 ≠ 0 := pow_ne_zero 3 (gen_coe_ne_zero h g)
  have hΓ := inv_stabGroup (Φ.twist hG hz6)
  have hle := transLat_le_latN_stabGroup hG hz6 Φ hM hV.unip
  have key := FB.coeff_U_gen h g h𝔪 hD.meas (hD.isAddFundamentalDomain volume) hT.1
    (eis (Φ.twist hG hz6) s) vv hvv hπ3
    (fun b x => by
      rw [add_comm]
      exact eis_add_latN h𝔪 hΓ s (hle b.2) x _ _)
    (integrableOn_of_bdd hb ((continuous_eis h𝔪 _ hs).comp (continuous_mk_x _ _)))
    μ (fun b => chiInf_transLat_one hG Φ hV b.2) hdeep
  rw [← key]
  obtain ⟨n', hn'⟩ := exists_bdd_scaleSet ((g.gen v.asIdeal : F) ^ 3) hb
  have hi1 := integrableOn_of_bdd hn' (continuous_eis_chi h𝔪
    ((Φ.sharp hG (g.gen v.asIdeal : F) (gen_coe_ne_zero h g)).twist hG hz6) hs vv hvv
    ((μ : F) / (g.gen v.asIdeal : F) ^ 3))
  have hi2 := integrableOn_of_bdd hn' (continuous_eis_chi h𝔪
    (TSection.restrict v (not_le_of_good h)
      ((Φ.sharp hG (g.gen v.asIdeal : F) (gen_coe_ne_zero h g)).twist hG hz6)) hs vv hvv
    ((μ : F) / (g.gen v.asIdeal : F) ^ 3))
  have hpt : ∀ x : InfinitePlace F → ℂ,
      FB.U ((g.gen v.asIdeal : F) ^ 3) hπ3 T (eis (Φ.twist hG hz6) s) (X.mk x vv hvv)
          * chiInf ((μ : F) / (g.gen v.asIdeal : F) ^ 3) x
        = ((Ninf (g.gen v.asIdeal : F) : ℝ) : ℂ) ^ (3 * s / 2)
            * ((Ideal.absNorm v.asIdeal : ℂ) ^ (3 - 3 * s)
              * (eis ((Φ.sharp hG (g.gen v.asIdeal : F) (gen_coe_ne_zero h g)).twist hG hz6) s
                (X.mk x vv hvv) * chiInf ((μ : F) / (g.gen v.asIdeal : F) ^ 3) x))
          + ((Ninf (g.gen v.asIdeal : F) : ℝ) : ℂ) ^ (3 * s / 2)
            * ((1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (2 - 3 * s))
              * (eis (TSection.restrict v (not_le_of_good h)
                  ((Φ.sharp hG (g.gen v.asIdeal : F) (gen_coe_ne_zero h g)).twist hG hz6)) s
                (X.mk x vv hvv) * chiInf ((μ : F) / (g.gen v.asIdeal : F) ^ 3) x)) := by
    intro x
    rw [hT.2 s hs, rhs54]
    ring
  change _ = ∫ x in scaleSet ((g.gen v.asIdeal : F) ^ 3) D, _
  simp only [hpt]
  rw [integral_add ((hi1.const_mul _).const_mul _) ((hi2.const_mul _).const_mul _)]
  simp only [integral_const_mul]
  rw [mul_add]

end

end ArtinKP.F
end

section
-- module Solutions.Artin.KP.F_Per_Const
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-F, file 4: the constant term of `E_{Ψρ_∞}` (Lemma 5.2 for `ρ_∞`, by Proposition 5.4)

MATH2 proves `m_{Φρ_∞} = m_Φ / L_P` by unfolding with a congruence condition.  Here it is read off
from Proposition 5.4 at the frequency `0`: `U E_Φ = N^{3s/2}[q^{3−3s} E_{Φ♯} + (1−q^{2−3s}) E_{Φ♯ρ_∞}]`,
the constant term of `U E_Φ` is `q³` times that of `E_Φ` at height `v/|π³|`, and
`m_{Φ♯} = |π|³ m_Φ`.  Result (`mD_restrict`): for every genuine section `Φ₁`, `Re s > 2`,

  `mD D (restrict (Φ₁.twist)) s = (1 − q^{3−3s})/(1 − q^{2−3s}) · mD D (Φ₁.twist) s`,

and hence `zPsi (restrict Ψ₁) = q/(q+1) · zPsi Ψ₁` (`zPsi_restrict`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.F

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N
  ArtinKP.T ArtinKP.B7 ArtinKP.FA

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F} {v : HeightOneSpectrum (𝓞 F)}

/-! ### Algebra -/

lemma ratio_den_ne_zero {q : ℕ} (hq : 1 < q) {s : ℂ} (hs : 1 < s.re) :
    1 - (q : ℂ) ^ 2 * ((q : ℂ) ^ (-s)) ^ 3 ≠ 0 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hn : ‖(q : ℂ) ^ 2 * ((q : ℂ) ^ (-s)) ^ 3‖ < 1 := by
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_natCast,
      Complex.norm_natCast_cpow_of_pos (by omega : 0 < q), Complex.neg_re,
      ← Real.rpow_natCast ((q : ℝ) ^ (-s.re)) 3, ← Real.rpow_mul hq0.le,
      ← Real.rpow_natCast (q : ℝ) 2, ← Real.rpow_add hq0]
    apply Real.rpow_lt_one_of_one_lt_of_neg hq1
    push_cast
    linarith
  intro h0
  have : (q : ℂ) ^ 2 * ((q : ℂ) ^ (-s)) ^ 3 = 1 := (sub_eq_zero.mp h0).symm
  rw [this, norm_one] at hn
  exact lt_irrefl _ hn

/-! ### Powers of positive reals -/

lemma inv_pow_three_eq {x : ℝ} (hx : 0 < x) :
    ((x : ℝ) : ℂ)⁻¹ ^ 3 = Complex.exp ((Real.log x : ℂ) * (-3)) := by
  rw [← cpow_pos_eq hx, show (-3 : ℂ) = -((3 : ℕ) : ℂ) by norm_num, Complex.cpow_neg,
    Complex.cpow_natCast, inv_pow]

lemma cpow_fact2 {n : ℝ} (hn : 0 < n) (s : ℂ) :
    ((n : ℝ) : ℂ) ^ (3 * s / 2) * ((n : ℝ) : ℂ)⁻¹ ^ 3 = ((n : ℝ) : ℂ) ^ (3 * (-(2 - s)) / 2) := by
  rw [inv_pow_three_eq hn, cpow_pos_eq hn, cpow_pos_eq hn, ← Complex.exp_add]
  congr 1
  ring

/-! ### The constant term of `E_{Φ♯ρ_∞}` over scaled cells -/

section gen

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (h : C3I.Good 𝔪 v)
  (g : AllowedGen ι 𝔪) (Φ : GSection ι P 𝔪)

include h in
lemma one_lt_absNorm : 1 < Ideal.absNorm v.asIdeal := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
  exact_mod_cast this

lemma Ninf_pow_three (a : F) :
    ((Ninf (a ^ 3) : ℝ) : ℂ) = ((Ninf a : ℝ) : ℂ) ^ 3 := by
  rw [pow_succ, pow_succ, pow_one, Ninf_mul, Ninf_mul]
  push_cast
  ring

end gen

end

end ArtinKP.F
end

section
-- module Solutions.Artin.KP.F_Per_Main
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-F, file 7: Theorem F1 (cube periodicity) and `E.Theta.PER`

* `Winf_scale`: `W_s(νa; v/|a|) = N_∞(a)^{(s−2)/2} · W_s(ν; v)`.
* `hasCoefT_restrict`: the `ν`-th Fourier coefficient of `E_{Φ♯ρ_∞}` over the cell `π³D`, from
  Proposition 5.4 (`U_coeff`): the coefficient series is
  `(1 − q^{2−3s})⁻¹ · (q³ N_∞(π)⁻³ 𝔞_Φ(νπ³, s) − q^{3−3s} 𝔞_{Φ♯}(ν, s))`.
* **`tau_sharp`** (Theorem F1): `τ_{Φ♯}(ν) = |π|_{S_f}³ · τ_Φ(νπ³)`.
* **`per`**: `(T.theta hG hz6).PER (g.gen P)`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.F

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N
  ArtinKP.T ArtinKP.B7 ArtinKP.FA ArtinKP.N2

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F} {v : HeightOneSpectrum (𝓞 F)}

/-! ### Scaling of the archimedean factor -/

/-- **`W_s(νa; v/|a|) = (∏_w |a_w|)^{s−2} · W_s(ν; v)`** (MATH2 §5.4 (3)). -/
theorem Winf_scale {s : ℂ} (hs : 1 < s.re) {ν a : F} (hν : ν ≠ 0) (ha : a ≠ 0)
    (vv : InfinitePlace F → ℝ) (hvv : ∀ w, 0 < vv w) :
    Winf s (ν * a) (fun w => vv w / ‖w.embedding a‖)
      = ((FB.Nh a : ℝ) : ℂ) ^ (s - 2) * Winf s ν vv := by
  have hva : ∀ w : InfinitePlace F, 0 < ‖w.embedding a‖ := fun w =>
    norm_pos_iff.2 ((map_ne_zero _).2 ha)
  rw [Winf_eq hs (mul_ne_zero hν ha) (fun w => div_pos (hvv w) (hva w)), Winf_eq hs hν hvv,
    FB.Nh, cpow_prod_nonneg _ _ (fun w => (hva w).le), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hy := hva w
  have hy0 : ((‖w.embedding a‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have e1 : ((2 * ‖w.embedding (ν * a)‖ : ℝ) : ℂ) ^ (s - 1)
      = ((2 * ‖w.embedding ν‖ : ℝ) : ℂ) ^ (s - 1) * ((‖w.embedding a‖ : ℝ) : ℂ) ^ (s - 2)
        * ((‖w.embedding a‖ : ℝ) : ℂ) := by
    rw [map_mul, norm_mul, ← mul_assoc, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (by positivity) hy.le, mul_assoc]
    congr 1
    have : s - 1 = (s - 2) + 1 := by ring
    rw [this, Complex.cpow_add _ _ hy0, Complex.cpow_one]
  have e2 : (4 * Real.pi * ‖w.embedding (ν * a)‖ * (vv w / ‖w.embedding a‖) : ℝ)
      = 4 * Real.pi * ‖w.embedding ν‖ * vv w := by
    rw [map_mul, norm_mul]
    field_simp
  rw [e1, e2]
  push_cast
  field_simp

/-! ### Algebra -/

lemma alg_coef (A x q n ni V k W aP aS IR : ℂ) (hA : A ≠ 0) (hd : 1 - q ^ 2 * x ^ 3 ≠ 0)
    (E : A * (q ^ 3 * x ^ 3 * (n ^ 3 * V * k * W * aS) + (1 - q ^ 2 * x ^ 3) * IR)
      = n ^ 3 * (q ^ 3 * (V * k * (A * ni ^ 3 * W) * aP))) :
    IR = n ^ 3 * V * k * W
      * ((1 - q ^ 2 * x ^ 3)⁻¹ * (q ^ 3 * ni ^ 3 * aP + (-(q ^ 3 * x ^ 3)) * aS)) := by
  apply mul_left_cancel₀ (mul_ne_zero hA hd)
  have hr : (1 - q ^ 2 * x ^ 3) * (1 - q ^ 2 * x ^ 3)⁻¹ = 1 := mul_inv_cancel₀ hd
  linear_combination E
    - A * n ^ 3 * V * k * W * (q ^ 3 * ni ^ 3 * aP + (-(q ^ 3 * x ^ 3)) * aS) * hr

section gen

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (h : C3I.Good 𝔪 v)
  (g : AllowedGen ι 𝔪) (Φ : GSection ι P 𝔪)

open Classical in
include hG hz6 in
/-- **The `ν`-th Fourier coefficient of `E_{Φ♯ρ_∞}`** over the scaled cell `π³D`, `D` a cell of
`Λ_M` (Proposition 5.4 on coefficients). -/
theorem hasCoefT_restrict_oai {ν : SInt 𝔪} (hν : ν ≠ 0) {Tr : Finset (SInt 𝔪)}
    (hT : IsU hG hz6 h g Φ Tr)
    (hdeep : ∀ t ∈ Tr, Small 𝔪 0
      (((ν * g.gen v.asIdeal ^ 3 : SInt 𝔪) : F) * (t : F) / (g.gen v.asIdeal : F) ^ 3))
    {M : ℤ} (hM : 0 ≤ M)
    (hV : ValidDepth hG Φ ((ν * g.gen v.asIdeal ^ 3 : SInt 𝔪) : F) M)
    {D : Set (InfinitePlace F → ℂ)} (hD : PCell (transLat 𝔪 M) D) {n : ℕ}
    (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n)
    (hc1 : HasCoef hG hz6 Φ (ν * g.gen v.asIdeal ^ 3) D (T.kap 𝔪 0))
    (hc2 : HasCoef hG hz6 (Φ.sharp hG (g.gen v.asIdeal : F) (gen_coe_ne_zero h g)) ν
      (scaleSet ((g.gen v.asIdeal : F) ^ 3) D) (T.kap 𝔪 0)) :
    HasCoefT (TSection.restrict v (not_le_of_good h)
        ((Φ.sharp hG (g.gen v.asIdeal : F) (gen_coe_ne_zero h g)).twist hG hz6)) (ν : F)
      (bR hG hz6 h g Φ ν) (scaleSet ((g.gen v.asIdeal : F) ^ 3) D) (T.kap 𝔪 0) := by
  intro s hs vv hvv
  have h𝔪 := hG.ne_bot
  have hπ : (g.gen v.asIdeal : F) ≠ 0 := gen_coe_ne_zero h g
  have hπ3 : (g.gen v.asIdeal : F) ^ 3 ≠ 0 := pow_ne_zero 3 hπ
  have hnpos : 0 < Ninf (g.gen v.asIdeal : F) := Ninf_pos hπ
  have hq0 : Ideal.absNorm v.asIdeal ≠ 0 := by have := one_lt_absNorm h; omega
  have hνF : (ν : F) ≠ 0 := T.coe_ne_zero hν
  have eμ : ((ν * g.gen v.asIdeal ^ 3 : SInt 𝔪) : F) = (ν : F) * (g.gen v.asIdeal : F) ^ 3 := rfl
  have eμ' : ((ν * g.gen v.asIdeal ^ 3 : SInt 𝔪) : F) / (g.gen v.asIdeal : F) ^ 3 = (ν : F) := by
    rw [eμ]; field_simp
  have E0 := U_coeff hG hz6 h g Φ hT hM (ν * g.gen v.asIdeal ^ 3) hV hdeep hD hb hs vv hvv
  rw [eμ', if_pos (Dvd.intro_left _ rfl)] at E0
  have h2 := hc2 s hs vv hvv
  have h1 := hc1 s hs (fun w => vv w / ‖w.embedding ((g.gen v.asIdeal : F) ^ 3)‖)
    (fun w => div_pos (hvv w) (norm_pos_iff.2 ((map_ne_zero _).2 hπ3)))
  have hNh : ((FB.Nh ((g.gen v.asIdeal : F) ^ 3) : ℝ) : ℂ) ^ (s - 2)
      = ((Ninf (g.gen v.asIdeal : F) : ℝ) : ℂ) ^ (3 * s / 2)
        * ((Ninf (g.gen v.asIdeal : F) : ℝ) : ℂ)⁻¹ ^ 3 := by
    rw [FB.Nh_pi_cube_cpow hπ, cpow_fact2 hnpos s]
    congr 1
    ring
  rw [h2, h1, eμ, Winf_scale (by linarith) hνF hπ3 vv hvv, volume_scaleSet hπ3 hD.meas,
    Ninf_pow_three, hNh, ← FB.q_cpow_three hq0 s, ← FB.q_cpow_two hq0 s] at E0
  rw [volume_scaleSet hπ3 hD.meas, Ninf_pow_three, bR]
  have hA : ((Ninf (g.gen v.asIdeal : F) : ℝ) : ℂ) ^ (3 * s / 2) ≠ 0 := by
    rw [cpow_pos_eq hnpos]; exact Complex.exp_ne_zero _
  have hd := ratio_den_ne_zero (one_lt_absNorm h) (s := s) (by linarith)
  refine alg_coef _ _ _ _ _ _ _ _ _ _ _ hA hd ?_
  linear_combination E0

end gen

end

end ArtinKP.F
end

theorem solution.{u_1} : type_of% @ArtinKP.F.hasCoefT_restrict_oai.{u_1} := @ArtinKP.F.hasCoefT_restrict_oai.{u_1}
