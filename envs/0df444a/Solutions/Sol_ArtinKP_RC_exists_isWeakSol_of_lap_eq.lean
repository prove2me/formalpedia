-- Prove2me | solution 1 for ArtinKP.RC.exists_isWeakSol_of_lap_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:47:43.199963+00:00
-- url     : https://prove2.me/submissions/daf69eb1-a71f-48e1-aaa6-87bed8ed953c

import Mathlib
import Definitions.Def_ArtinKPB015
import Theorems.Thm_ArtinKP_RC_exists_compact_top_le
import Theorems.Thm_ArtinKP_RC_exists_single
import Theorems.Thm_ArtinKP_RC_grad2_chi_le
import Theorems.Thm_ArtinKP_RC_smooth_chi
import Theorems.Thm_ArtinKP_X_X_exists_isWeakSol_of_lap_eq_of_cutoff

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
attribute [-simp] _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
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

/-! ### Upper triangular elements, translations and the torus -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Discrete
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
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
-- module Solutions.Artin.KP.X_Units
attribute [-instance] _root_.ArtinKP.B1.instDiscreteTopologySubtypeE₂MemSubmoduleIntPairLattice _root_.ArtinKP.X.instDiscreteTopologySubtypeMixedSpaceMemSubmoduleIntLattice
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

end

end ArtinKP.B1
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

lemma theta_zero {t : ℝ} (h : t ≤ 1) : theta t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma theta_one {t : ℝ} (h : 2 ≤ t) : theta t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma theta_nonneg (t : ℝ) : 0 ≤ theta t := Real.smoothTransition.nonneg _

lemma theta_le_one (t : ℝ) : theta t ≤ 1 := Real.smoothTransition.le_one _

lemma contDiff_theta : ContDiff ℝ (⊤ : ℕ∞) theta :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

lemma exists_deriv_theta_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |deriv theta t| ≤ C := by
  have hcont : Continuous (deriv theta) := contDiff_theta.continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  by_cases h1 : t < 1
  · have : theta =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds h1] with s hs
      exact theta_zero (le_of_lt hs)
    rw [this.deriv_eq]
    simp
  by_cases h2 : 2 < t
  · have : theta =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds h2] with s hs
      exact theta_one (le_of_lt hs)
    rw [this.deriv_eq]
    simp
  · exact (hC t ⟨not_lt.mp h1, not_lt.mp h2⟩).trans (le_max_left _ _)

/-- `ϑ(log h / (n+1)) = 0` for `h ≤ 2`. -/
lemma theta_log_eq_zero (n : ℕ) {h : ℝ} (h0 : 0 < h) (h2 : h ≤ 2) :
    theta (Real.log h / ((n : ℝ) + 1)) = 0 := by
  refine theta_zero ?_
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [div_le_one hn]
  have h3 : Real.log h ≤ 1 := by
    rw [Real.log_le_iff_le_exp h0]
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {S : Finset (FinitePlace F)}

/-! ### Local finiteness -/

/-! ### The cut-offs -/

lemma chi_eq_of_single {n : ℕ} {P : X F} {p₁ : PairClass S}
    (h : ∀ p : PairClass S, p ≠ p₁ → theta (Real.log (p.ht P) / ((n : ℝ) + 1)) = 0) :
    chi S n P = 1 - theta (Real.log (p₁.ht P) / ((n : ℝ) + 1)) := by
  unfold chi
  rw [tsum_eq_single p₁ h]

lemma chi_eventually (S : Finset (FinitePlace F)) (n : ℕ) (P₀ : X F) :
    ∃ p₁ : PairClass S, ∀ᶠ P in 𝓝 P₀,
      chi S n P = 1 - theta (Real.log (p₁.ht P) / ((n : ℝ) + 1)) := by
  obtain ⟨p₁, h⟩ := exists_single S n P₀
  exact ⟨p₁, h.mono fun P hP => chi_eq_of_single hP⟩

lemma chi_nonneg (S : Finset (FinitePlace F)) (n : ℕ) (P : X F) : 0 ≤ chi S n P := by
  obtain ⟨p₁, h⟩ := chi_eventually S n P
  rw [h.self_of_nhds]
  linarith [theta_le_one (Real.log (p₁.ht P) / ((n : ℝ) + 1))]

lemma chi_le_one (S : Finset (FinitePlace F)) (n : ℕ) (P : X F) : chi S n P ≤ 1 := by
  obtain ⟨p₁, h⟩ := chi_eventually S n P
  rw [h.self_of_nhds]
  linarith [theta_nonneg (Real.log (p₁.ht P) / ((n : ℝ) + 1))]

/-- `χ_n` is `SL₂(𝓞_F)`-invariant. -/
lemma chi_smul (n : ℕ) (γ : SL(2, 𝓞 F)) (P : X F) : chi S n (γ • P) = chi S n P := by
  unfold chi
  have e := (PairClass.actEquiv (S := S) γ).tsum_eq
    fun p : PairClass S => theta (Real.log (p.ht P) / ((n : ℝ) + 1))
  rw [← e]
  congr 1
  refine tsum_congr fun p => ?_
  change _ = theta (Real.log ((p.act γ).ht P) / ((n : ℝ) + 1))
  rw [PairClass.ht_act]

/-- `χ_n = 1` where all heights are `≤ e^{n+1}`. -/
lemma chi_eq_one {n : ℕ} {P : X F}
    (h : ∀ p : PairClass S, p.ht P ≤ Real.exp ((n : ℝ) + 1)) : chi S n P = 1 := by
  unfold chi
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have : ∀ p : PairClass S, theta (Real.log (p.ht P) / ((n : ℝ) + 1)) = 0 := fun p => by
    refine theta_zero ?_
    rw [div_le_one hn, Real.log_le_iff_le_exp (p.ht_pos P)]
    exact h p
  simp [this]

/-- `χ_n ≠ 0` only where all heights are `≤ e^{2(n+1)}`. -/
lemma le_of_chi_ne_zero {n : ℕ} {P : X F} (h : chi S n P ≠ 0) (p : PairClass S) :
    p.ht P ≤ Real.exp (2 * ((n : ℝ) + 1)) := by
  by_contra hp
  push Not at hp
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 : 1 < p.ht P := lt_of_le_of_lt (Real.one_le_exp (by positivity)) hp
  have hsingle : ∀ p' : PairClass S, p' ≠ p →
      theta (Real.log (p'.ht P) / ((n : ℝ) + 1)) = 0 := fun p' hp' => by
    refine theta_log_eq_zero n (p'.ht_pos P) ?_
    by_contra h2
    exact hp' (PairClass.eq_of_one_lt_ht (by linarith) h1)
  apply h
  rw [chi_eq_of_single hsingle, theta_one, sub_self]
  rw [le_div_iff₀ hn, Real.le_log_iff_exp_le (p.ht_pos P)]
  exact hp.le

/-- `χ_n → 1` pointwise. -/
lemma tendsto_chi (S : Finset (FinitePlace F)) (P : X F) :
    Tendsto (fun n => chi S n P) atTop (𝓝 1) := by
  obtain ⟨p₀, hp₀⟩ := PairClass.exists_max_ht S P
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ⌈Real.log (p₀.ht P)⌉₊] with n hn
  refine (chi_eq_one fun p => ?_).symm
  refine (hp₀ p).trans ?_
  rw [← Real.log_le_iff_le_exp (p₀.ht_pos P)]
  have h1 : Real.log (p₀.ht P) ≤ (⌈Real.log (p₀.ht P)⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (⌈Real.log (p₀.ht P)⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-! ### Smoothness and the gradient bound -/

/-! ### The cut-off sequence for `X.exists_weakSol` -/

/-- **The cut-offs of MATH2 §1.6**, in the form of the hypotheses of `X.exists_weakSol`. -/
theorem exists_cutoffs (hB : SBezout S) (hO : FiniteCusps S) (Γ : Subgroup (SL(2, 𝓞 F)))
    [Γ.FiniteIndex] :
    ∃ (χ : ℕ → X F → ℝ) (ε : ℕ → ℝ),
      (∀ n, X.Smooth fun P => (χ n P : ℂ)) ∧
      (∀ n, X.IsInv Γ (χ n)) ∧
      (∀ n, ∃ K : Set (X F), IsCompact K ∧ ∀ P, χ n P ≠ 0 → ∃ γ : Γ, γ • P ∈ K) ∧
      (∀ n P, 0 ≤ χ n P) ∧ (∀ n P, χ n P ≤ 1) ∧
      (∀ P, Tendsto (fun n => χ n P) atTop (𝓝 1)) ∧
      Tendsto ε atTop (𝓝 0) ∧
      ∀ n P, X.grad2 (fun P => (χ n P : ℂ)) P ≤ ε n := by
  obtain ⟨C, -, hC⟩ := exists_deriv_theta_bound
  refine ⟨chi S, fun n => (Fintype.card (InfinitePlace F) : ℝ) * (C / ((n : ℝ) + 1)) ^ 2,
    smooth_chi S, fun n γ P => chi_smul n (γ : SL(2, 𝓞 F)) P, fun n => ?_, chi_nonneg S,
    chi_le_one S, tendsto_chi S, ?_, grad2_chi_le hC S⟩
  · obtain ⟨K, hK, h⟩ := exists_compact_top_le_subgroup hB hO Γ (Real.exp (2 * ((n : ℝ) + 1)))
    exact ⟨K, hK, fun P hP => h P (le_of_chi_ne_zero hP)⟩
  · have h1 : Tendsto (fun n : ℕ => C / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C
      simpa [div_eq_mul_inv] using this
    have h2 := (h1.pow 2).const_mul (Fintype.card (InfinitePlace F) : ℝ)
    simpa using h2

/-- **`X.exists_weakSol` with the cut-offs supplied** (MATH2 §1.6 for `Γ` of finite index): a
smooth `Γ`-invariant `u ∈ L²(Γ\X)` with `Δu = λu + f` pointwise, `f ∈ L²(Γ\X)`, is in `H¹(Γ\X)`
and is the weak solution. -/
theorem exists_isWeakSol_of_lap_eq_oai (hB : SBezout S) (hO : FiniteCusps S) {Γ : Subgroup (SL(2, 𝓞 F))}
    [Γ.FiniteIndex] {u f : X F → ℂ} (hu : X.Smooth u) (hu2 : X.L2Rep Γ u) (hf2 : X.L2Rep Γ f)
    (lam : ℂ) (heq : ∀ P, X.lap u P = lam * u P + f P) :
    ∃ x : X.H1 Γ, (X.energy Γ).j x = X.toL2 Γ u hu2 ∧
      (X.energy Γ).IsWeakSol lam (X.toL2 Γ f hf2) x := by
  obtain ⟨χ, ε, h1, h2, h3, h4, h5, h6, h7, h8⟩ := exists_cutoffs hB hO Γ
  exact X.exists_isWeakSol_of_lap_eq_of_cutoff hu hu2 hf2 lam heq χ h1 h2 h3 h4 h5 h6 ε h7 h8

end

end ArtinKP.RC
end

theorem solution.{u_1} : type_of% @ArtinKP.RC.exists_isWeakSol_of_lap_eq_oai.{u_1} := @ArtinKP.RC.exists_isWeakSol_of_lap_eq_oai.{u_1}
