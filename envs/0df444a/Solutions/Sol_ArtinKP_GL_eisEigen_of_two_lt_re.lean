-- Prove2me | solution 1 for ArtinKP.GL.eisEigen_of_two_lt_re
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:43:38.841803+00:00
-- url     : https://prove2.me/submissions/d26a1bda-7afc-4b94-9cbb-729c32efa3ae

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

section
-- module Solutions.Artin.KP.X_H3
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulGinfX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatComplexH3 _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulGinfX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatComplexH3 _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatXVol _root_.ArtinKP.X.instSigmaFiniteH3Vol _root_.ArtinKP.X.instSigmaFiniteXVol
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

end X

/-! ### Topology and measure -/

/-! ### Upper triangular elements, translations and the torus -/

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

/-- **(B1), locally uniform.** -/
theorem exists_summable_majorant (S : Finset (FinitePlace F)) {K : Set (X F)} (hK : IsCompact K)
    {σ₁ σ₂ : ℝ} (hσ₁ : 2 < σ₁) (hσ : σ₁ ≤ σ₂) :
    ∃ u : PairClass S → ℝ, Summable u ∧ ∀ P ∈ K, ∀ σ ∈ Set.Icc σ₁ σ₂, ∀ p : PairClass S,
      p.ht P ^ σ ≤ u p := by
  have := exists_summable_majorant_sHt S (fun p : PairClass S => (p.out.c, p.out.d))
    (fun p => ⟨p.out.hc, p.out.hd⟩) (fun p => p.out.ne_zero) out_family_inj hK hσ₁ hσ
  simpa only [← ht_eq_out] using this

/-- Complex exponents: `‖ht_p(P)^s‖ ≤ u p` for `P ∈ K`, `σ₁ ≤ Re s ≤ σ₂`; hence the series
`∑_p Ψ(p) ht_p(P)^s` with bounded `Ψ` converges absolutely and uniformly there (Weierstrass). -/
theorem exists_summable_majorant_cpow (S : Finset (FinitePlace F)) {K : Set (X F)}
    (hK : IsCompact K) {σ₁ σ₂ : ℝ} (hσ₁ : 2 < σ₁) (hσ : σ₁ ≤ σ₂) :
    ∃ u : PairClass S → ℝ, Summable u ∧ ∀ P ∈ K, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      ∀ p : PairClass S, ‖((p.ht P : ℝ) : ℂ) ^ s‖ ≤ u p := by
  obtain ⟨u, hu, hub⟩ := exists_summable_majorant S hK hσ₁ hσ
  refine ⟨u, hu, fun P hP s h1 h2 p => ?_⟩
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (p.ht_pos P)]
  exact hub P hP s.re ⟨h1, h2⟩ p

end PairClass

/-! ### Lemma M for pair classes -/

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.B_Def
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
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

/-! ### The product formula for `S`-units -/

/-! ### Rows modulo `S`-units -/

/-- The `S`-normalized height of a row: `I_p(Q) / ‖p‖`. -/
theorem sHt_row (p : Row 𝔪) (Q : X F) :
    X.sHt (sPl 𝔪) (p.c : F) (p.d : F) Q = X.pairHt (p.c : F) (p.d : F) Q / p.norm := by
  unfold X.sHt Row.norm
  rw [sNorm_sPl]

/-! ### Convergence of the height series over row classes (from WP-B1) -/

/-! ### The summand and the series -/

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

theorem term_out_eq (Ψ : TSection ι 𝔪) (s : ℂ) (Q : X F) (q : RowClass 𝔪) :
    term (Ψ s) s Q q.out = tildeC Ψ s q * ((q.ht Q : ℝ) : ℂ) ^ s :=
  term_eq_tilde Ψ s Q q.out

/-- **Orbit form** (MATH2 §0.2): `E_Ψ(Q, s) = ∑_q Ψ̃_s(q) · ht_q(Q)^s`. -/
theorem eis_eq_tsum_ht (Ψ : TSection ι 𝔪) (s : ℂ) (Q : X F) :
    eis Ψ s Q = ∑' q : RowClass 𝔪, tildeC Ψ s q * ((q.ht Q : ℝ) : ℂ) ^ s := by
  rw [eis_def]
  exact tsum_congr fun q => term_out_eq Ψ s Q q

/-! ### Bounds and convergence -/

end height

end ArtinKP.B
end
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
-- module Solutions.Artin.KP.X2_Chart
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol
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

lemma chart_v (y : Coord F) (w : InfinitePlace F) : (chart F y).v w = Real.exp (y w).2 := rfl

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
-- module Solutions.Artin.KP.X2_Calc
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX
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

theorem instIsAddHaarMeasureCoordVolume : (volume : Measure (Coord F)).IsAddHaarMeasure :=
  haveI _iHCR := ArtinKP.X.instIsAddHaarMeasureProdComplexRealVolume_solutions
  have h : (volume : Measure (Coord F)) = Measure.pi fun _ : InfinitePlace F => (volume : Measure E1) := rfl
  h ▸ { toIsFiniteMeasureOnCompacts := inferInstance
        toIsAddLeftInvariant := inferInstance
        toIsOpenPosMeasure := inferInstance }

/-! ### Regularity -/

lemma contDiff_pd_top {U : Coord F → ℂ} (h : ContDiff ℝ (⊤ : ℕ∞) U)
    (w : InfinitePlace F) (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (pd w k U) :=
  contDiff_pd h (by exact le_rfl) w k

lemma contDiff_acoef (k : Fin 3) (w : InfinitePlace F) :
    ContDiff ℝ (⊤ : ℕ∞) fun y : Coord F => ((acoef k (y w) : ℝ) : ℂ) := by
  unfold acoef
  split_ifs
  · exact contDiff_const
  · have h : ContDiff ℝ (⊤ : ℕ∞) (fun y : Coord F => Real.exp (2 * (y w).2)) := by fun_prop
    exact Complex.ofRealCLM.contDiff.comp h

lemma contDiff_lapE {U : Coord F → ℂ} (h : ContDiff ℝ (⊤ : ℕ∞) U) :
    ContDiff ℝ (⊤ : ℕ∞) (lapE U) := by
  unfold lapE
  refine ContDiff.sum fun w _ => ContDiff.add (ContDiff.sum fun k _ => ContDiff.neg ?_) ?_
  · exact (contDiff_acoef k w).mul (contDiff_pd_top (contDiff_pd_top h w k) w k)
  · exact contDiff_const.mul (contDiff_pd_top h w 2)

/-! ### Algebraic rules -/

/-! ### The weights `ρ · a_k` -/

lemma Ls_apply (y : Coord F) : Ls y = ∑ w, (y w).2 := by
  simp [Ls]

lemma Lw_apply (w : InfinitePlace F) (y : Coord F) : Lw w y = (y w).2 := rfl

lemma mC_eq (w : InfinitePlace F) (k : Fin 3) (y : Coord F) :
    mC w k y = ((Real.exp (Lk w k y) : ℝ) : ℂ) := by
  unfold mC rho acoef Lk
  split_ifs
  · simp [Ls_apply]
  · rw [← Real.exp_add]
    simp [Ls_apply, Lw_apply]

lemma mC_two (w : InfinitePlace F) (y : Coord F) : mC w 2 y = (rho y : ℂ) := by
  simp [mC, acoef]

lemma hasFDerivAt_mC (w : InfinitePlace F) (k : Fin 3) (y : Coord F) :
    HasFDerivAt (mC w k) (Complex.ofRealCLM.comp (Real.exp (Lk w k y) • Lk w k)) y := by
  have h : mC w k = fun y => ((Real.exp (Lk w k y) : ℝ) : ℂ) := funext (mC_eq w k)
  rw [h]
  exact Complex.ofRealCLM.hasFDerivAt.comp y (Lk w k).hasFDerivAt.exp

lemma contDiff_mC (w : InfinitePlace F) (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (mC w k) := by
  have h : mC w k = fun y => ((Real.exp (Lk w k y) : ℝ) : ℂ) := funext (mC_eq w k)
  rw [h]
  exact Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (Lk w k).contDiff)

lemma Lk_bvec (w : InfinitePlace F) (k : Fin 3) : ((Lk w k (bvec w k) : ℝ) : ℂ) = cco k := by
  have h1 : ∀ k, Ls (bvec w k) = (e1 k).2 := by
    intro k
    rw [Ls_apply]
    unfold bvec
    rw [Finset.sum_eq_single w]
    · simp
    · intro w' _ hw'
      simp [hw']
    · simp
  have h2 : ∀ k, Lw w (bvec w k) = (e1 k).2 := by
    intro k
    simp [Lw_apply, bvec]
  fin_cases k <;> simp [Lk, cco, h1, h2]

lemma fderiv_mC_bvec (w : InfinitePlace F) (k : Fin 3) (y : Coord F) :
    fderiv ℝ (mC w k) y (bvec w k) = cco k * mC w k y := by
  rw [(hasFDerivAt_mC w k y).fderiv, mC_eq, ← Lk_bvec w k]
  simp
  ring

/-! ### Green's identity on the chart -/

lemma integrable_cmul {c A B : Coord F → ℂ} (hc : Continuous c) (hA : Continuous A)
    (hB : Continuous B) (h : HasCompactSupport A ∨ HasCompactSupport B) :
    Integrable (fun y => c y * (A y * B y)) := by
  refine (hc.mul (hA.mul hB)).integrable_of_hasCompactSupport ?_
  rcases h with h | h
  · exact (h.mul_right (f' := B)).mul_left (f := c)
  · exact (h.mul_left (f := A)).mul_left (f := c)

lemma ibp_term {U T : Coord F → ℂ} (hU : ContDiff ℝ 2 U) (hT : ContDiff ℝ 1 T)
    (hc : HasCompactSupport T ∨ HasCompactSupport U) (w : InfinitePlace F) (k : Fin 3) :
    ∫ y, mC w k y * (T y * pd w k (pd w k U) y) =
      -(∫ y, mC w k y * (pd w k T y * pd w k U y)) - cco k * ∫ y, mC w k y * (T y * pd w k U y) := by
  haveI _iHCo := ArtinKP.X.instIsAddHaarMeasureCoordVolume (F := F)
  have hm := contDiff_mC (F := F) w k
  have hmc : Continuous (mC (F := F) w k) := hm.continuous
  have hTc : Continuous T := hT.continuous
  have hpT : Continuous (pd w k T) := (contDiff_pd (m := 0) hT (by simp) w k).continuous
  have hpU1 : ContDiff ℝ 1 (pd w k U) := contDiff_pd hU (by norm_num) w k
  have hpU : Continuous (pd w k U) := hpU1.continuous
  have hppU : Continuous (pd w k (pd w k U)) :=
    (contDiff_pd (m := 0) hpU1 (by simp) w k).continuous
  have hc1 : HasCompactSupport T ∨ HasCompactSupport (pd w k U) :=
    hc.imp id fun h => h.fderiv_apply (𝕜 := ℝ) (bvec w k)
  have hc2 : HasCompactSupport T ∨ HasCompactSupport (pd w k (pd w k U)) :=
    hc1.imp id fun h => h.fderiv_apply (𝕜 := ℝ) (bvec w k)
  have hc3 : HasCompactSupport (pd w k T) ∨ HasCompactSupport (pd w k U) :=
    hc1.imp (fun h => h.fderiv_apply (𝕜 := ℝ) (bvec w k)) id
  have hTd : Differentiable ℝ T := hT.differentiable (by simp)
  have hmd : Differentiable ℝ (mC (F := F) w k) := hm.differentiable (by simp)
  have hfd : ∀ y, fderiv ℝ (fun y => mC w k y * T y) y (bvec w k) =
      mC w k y * pd w k T y + cco k * (mC w k y * T y) := by
    intro y
    rw [fderiv_fun_mul (hmd y) (hTd y)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      fderiv_mC_bvec]
    unfold pd
    ring
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Coord F)))
    (f := fun y => mC w k y * T y) (g := pd w k U) (v := bvec w k) ?_ ?_ ?_
    (fun y _ => (hmd y).mul (hTd y)) (fun y _ => hpU1.differentiable (by simp) y)
  · have e1 : ∀ y, (mC w k y * T y) * fderiv ℝ (pd w k U) y (bvec w k) =
        mC w k y * (T y * pd w k (pd w k U) y) := fun y => by unfold pd; ring
    have e2 : ∀ y, fderiv ℝ (fun y => mC w k y * T y) y (bvec w k) * pd w k U y =
        mC w k y * (pd w k T y * pd w k U y) + cco k * (mC w k y * (T y * pd w k U y)) :=
      fun y => by rw [hfd]; ring
    simp_rw [e1, e2] at key
    rw [key, integral_add (integrable_cmul hmc hpT hpU hc3)
      ((integrable_cmul hmc hTc hpU hc1).const_mul _), integral_const_mul]
    ring
  · have e2 : (fun y => fderiv ℝ (fun y => mC w k y * T y) y (bvec w k) * pd w k U y) =
        fun y => mC w k y * (pd w k T y * pd w k U y) + cco k * (mC w k y * (T y * pd w k U y)) :=
      funext fun y => by rw [hfd]; ring
    rw [e2]
    exact (integrable_cmul hmc hpT hpU hc3).add ((integrable_cmul hmc hTc hpU hc1).const_mul _)
  · have e1 : (fun y => (mC w k y * T y) * fderiv ℝ (pd w k U) y (bvec w k)) =
        fun y => mC w k y * (T y * pd w k (pd w k U) y) := funext fun y => by unfold pd; ring
    rw [e1]
    exact integrable_cmul hmc hTc hppU hc2
  · have e1 : (fun y => (mC w k y * T y) * pd w k U y) =
        fun y => mC w k y * (T y * pd w k U y) := funext fun y => by ring
    rw [e1]
    exact integrable_cmul hmc hTc hpU hc1

/-- **Green's identity in the chart**: `∫ ρ T ΔU = ∫ ρ Γ(T, U)` if `T` or `U` has compact
support. -/
theorem green_E {U T : Coord F → ℂ} (hU : ContDiff ℝ 2 U) (hT : ContDiff ℝ 1 T)
    (hc : HasCompactSupport T ∨ HasCompactSupport U) :
    ∫ y, (rho y : ℂ) * (T y * lapE U y) = ∫ y, (rho y : ℂ) * gamE T U y := by
  have hTc : Continuous T := hT.continuous
  have hpT : ∀ w k, Continuous (pd w k T) :=
    fun w k => (contDiff_pd (m := 0) hT (by simp) w k).continuous
  have hpU1 : ∀ w k, ContDiff ℝ 1 (pd w k U) := fun w k => contDiff_pd hU (by norm_num) w k
  have hpU : ∀ w k, Continuous (pd w k U) := fun w k => (hpU1 w k).continuous
  have hppU : ∀ w k, Continuous (pd w k (pd w k U)) :=
    fun w k => (contDiff_pd (m := 0) (hpU1 w k) (by simp) w k).continuous
  have hmc : ∀ w k, Continuous (mC (F := F) w k) := fun w k => (contDiff_mC w k).continuous
  have hc1 : ∀ w k, HasCompactSupport T ∨ HasCompactSupport (pd w k U) :=
    fun w k => hc.imp id fun h => h.fderiv_apply (𝕜 := ℝ) (bvec w k)
  have hc2 : ∀ w k, HasCompactSupport T ∨ HasCompactSupport (pd w k (pd w k U)) :=
    fun w k => (hc1 w k).imp id fun h => h.fderiv_apply (𝕜 := ℝ) (bvec w k)
  have hc3 : ∀ w k, HasCompactSupport (pd w k T) ∨ HasCompactSupport (pd w k U) :=
    fun w k => (hc1 w k).imp (fun h => h.fderiv_apply (𝕜 := ℝ) (bvec w k)) id
  have h1 : ∀ y, (rho y : ℂ) * (T y * lapE U y) =
      ∑ w, ((∑ k, -(mC w k y * (T y * pd w k (pd w k U) y))) +
        2 * (mC w 2 y * (T y * pd w 2 U y))) := by
    intro y
    unfold lapE
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum, mC_two]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      unfold mC
      push_cast
      ring
    · ring
  have h2 : ∀ y, (rho y : ℂ) * gamE T U y =
      ∑ w, ∑ k, mC w k y * (pd w k T y * pd w k U y) := by
    intro y
    unfold gamE
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold mC
    push_cast
    ring
  simp_rw [h1, h2]
  rw [integral_finsetSum, integral_finsetSum]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [integral_add, integral_finsetSum, integral_finsetSum, integral_const_mul]
    · simp_rw [integral_neg, ibp_term hU hT hc]
      simp only [Fin.sum_univ_three, cco]
      simp
      ring
    · exact fun k _ => integrable_cmul (hmc w k) (hpT w k) (hpU w k) (hc3 w k)
    · exact fun k _ => (integrable_cmul (hmc w k) hTc (hppU w k) (hc2 w k)).neg
    · exact integrable_finsetSum _
        fun k _ => (integrable_cmul (hmc w k) hTc (hppU w k) (hc2 w k)).neg
    · exact (integrable_cmul (hmc w 2) hTc (hpU w 2) (hc1 w 2)).const_mul _
  · exact fun w _ => integrable_finsetSum _
      fun k _ => integrable_cmul (hmc w k) (hpT w k) (hpU w k) (hc3 w k)
  · exact fun w _ => (integrable_finsetSum _
      fun k _ => (integrable_cmul (hmc w k) hTc (hppU w k) (hc2 w k)).neg).add
        ((integrable_cmul (hmc w 2) hTc (hpU w 2) (hc1 w 2)).const_mul _)

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

/-- Integrals against `muE` are Lebesgue integrals with the weight `rho`. -/
lemma integral_muE (f : Coord F → ℂ) : ∫ y, f y ∂muE F = ∫ y, (rho y : ℂ) * f y := by
  unfold muE
  rw [integral_withDensity_eq_integral_toReal_smul (by unfold rho; fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [ENNReal.toReal_ofReal (rho_pos y).le]
  rw [Complex.real_smul]

/-- **The Laplacian commutes with measure-preserving isometries** (weak proof). -/
theorem lapE_comp_of_iso {Φ Ψ : Coord F → Coord F} (hΦ : IsoHalf Φ) (hΨ : IsoHalf Ψ)
    (h1 : ∀ y, Φ (Ψ y) = y) (h2 : ∀ y, Ψ (Φ y) = y)
    (hμ : MeasurePreserving Φ (muE F) (muE F))
    {U : Coord F → ℂ} (hU : ContDiff ℝ (⊤ : ℕ∞) U) (y : Coord F) :
    lapE (fun z => U (Φ z)) y = lapE U (Φ y) := by
  let e : Coord F ≃ₜ Coord F :=
    { toFun := Φ
      invFun := Ψ
      left_inv := h2
      right_inv := h1
      continuous_toFun := hΦ.smooth.continuous
      continuous_invFun := hΨ.smooth.continuous }
  have hUΦ : ContDiff ℝ (⊤ : ℕ∞) (fun z => U (Φ z)) := hU.comp hΦ.smooth
  have hrc : Continuous fun y : Coord F => (rho y : ℂ) :=
    Complex.continuous_ofReal.comp continuous_rho
  have hl1 : Continuous (lapE fun z => U (Φ z)) := (contDiff_lapE hUΦ).continuous
  have hl2 : Continuous fun y => lapE U (Φ y) :=
    (contDiff_lapE hU).continuous.comp hΦ.smooth.continuous
  set D : Coord F → ℂ := fun y => (rho y : ℂ) * (lapE (fun z => U (Φ z)) y - lapE U (Φ y))
    with hD
  have hDc : Continuous D := hrc.mul (hl1.sub hl2)
  have hzero : ∀ᵐ y ∂(volume : Measure (Coord F)), D y = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hDc.locallyIntegrable) fun g hg hgc => ?_
    set T : Coord F → ℂ := fun y => (g y : ℂ) with hT
    have hTs : ContDiff ℝ (⊤ : ℕ∞) T := Complex.ofRealCLM.contDiff.comp hg
    have hTc : HasCompactSupport T := hgc.comp_left Complex.ofReal_zero
    set S : Coord F → ℂ := fun z => T (Ψ z) with hS
    have hSs : ContDiff ℝ (⊤ : ℕ∞) S := hTs.comp hΨ.smooth
    have hSc : HasCompactSupport S := hTc.comp_isClosedEmbedding e.symm.isClosedEmbedding
    have hTS : T = fun z => S (Φ z) := by
      funext z; simp only [hS, h2]
    have two : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
    have one : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
    have step1 := green_E (hUΦ.of_le two) (hTs.of_le one) (Or.inl hTc)
    have step2 : ∀ y, gamE T (fun z => U (Φ z)) y = gamE S U (Φ y) := by
      intro y
      rw [hTS]
      exact hΦ.gam_comp S U y ((hSs.differentiable (by simp)) _) ((hU.differentiable (by simp)) _)
    have step3 : ∫ y, (rho y : ℂ) * gamE S U (Φ y) = ∫ y, (rho y : ℂ) * gamE S U y := by
      rw [← integral_muE, ← integral_muE]
      exact hμ.integral_comp e.measurableEmbedding _
    have step4 := green_E (hU.of_le two) (hSs.of_le one) (Or.inl hSc)
    have step5 : ∫ y, (rho y : ℂ) * (S y * lapE U y) =
        ∫ y, (rho y : ℂ) * (T y * lapE U (Φ y)) := by
      rw [← integral_muE, ← integral_muE]
      rw [← hμ.integral_comp e.measurableEmbedding (fun y => S y * lapE U y)]
      rw [hTS]
    have hsplit : ∀ y, g y • D y =
        (rho y : ℂ) * (T y * lapE (fun z => U (Φ z)) y) - (rho y : ℂ) * (T y * lapE U (Φ y)) := by
      intro y
      simp only [hD, hT, Complex.real_smul]
      ring
    simp_rw [hsplit]
    rw [integral_sub (integrable_cmul hrc hTs.continuous hl1 (Or.inl hTc))
      (integrable_cmul hrc hTs.continuous hl2 (Or.inl hTc)), step1]
    simp_rw [step2]
    rw [step3, ← step4, step5, sub_self]
  have hD0 : D = 0 := (hDc.ae_eq_iff_eq volume continuous_zero).1 hzero
  have := congrFun hD0 y
  simp only [hD, Pi.zero_apply, mul_eq_zero, Complex.ofReal_eq_zero, (rho_pos y).ne',
    false_or] at this
  exact sub_eq_zero.1 this

/-! ### The action of `G∞` in the chart -/

lemma chart_actE (g : Ginf F) (y : Coord F) : chart F (actE g y) = g • chart F y := by
  simp [actE]

lemma actE_inv_actE (g : Ginf F) (y : Coord F) : actE g⁻¹ (actE g y) = y := by
  unfold actE
  rw [Homeomorph.apply_symm_apply, inv_smul_smul, Homeomorph.symm_apply_apply]

lemma actE_actE_inv (g : Ginf F) (y : Coord F) : actE g (actE g⁻¹ y) = y := by
  have := actE_inv_actE g⁻¹ y
  rwa [inv_inv] at this

theorem isoHalf_actE (g : Ginf F) : IsoHalf (actE g) := by
  choose φ hφ hg using fun w => mem_iso1 (g w)
  have : actE g = fun (y : Coord F) w => φ w (y w) := by
    funext y w
    change chart1.symm (g w • chart1 (y w)) = _
    rw [hg w, Homeomorph.symm_apply_apply]
  rw [this]
  exact isoHalf_pi hφ

theorem measurePreserving_actE (g : Ginf F) : MeasurePreserving (actE g) (muE F) (muE F) := by
  have h1 := measurePreserving_chart F
  have h2 := measurePreserving_Ginf_smul g
  have h3 : MeasurePreserving (chart F).symm (X.vol F) (muE F) :=
    h1.symm (chart F).toMeasurableEquiv
  exact h3.comp (h2.comp h1)

theorem lapE_actE (g : Ginf F) {U : Coord F → ℂ} (hU : ContDiff ℝ (⊤ : ℕ∞) U) (y : Coord F) :
    lapE (fun z => U (actE g z)) y = lapE U (actE g y) :=
  lapE_comp_of_iso (isoHalf_actE g) (isoHalf_actE g⁻¹) (actE_actE_inv g) (actE_inv_actE g)
    (measurePreserving_actE g) hU y

/-! ### Calculus on `X` -/

/-- **The Laplacian commutes with `G∞`.** -/
theorem X.lap_comp_Ginf {u : X F → ℂ} (hu : X.Smooth u) (g : Ginf F) (P : X F) :
    X.lap (fun P => u (g • P)) P = X.lap u (g • P) := by
  unfold X.lap
  have : (fun y => u (g • chart F y)) = fun y => (fun z => u (chart F z)) (actE g y) := by
    funext y; simp only [chart_actE]
  have hu' : ContDiff ℝ (⊤ : ℕ∞) fun y => u (chart F y) := hu
  rw [this, lapE_actE g hu']
  congr 1
  simp [actE]

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

lemma Ls_bvec (w : InfinitePlace F) (k : Fin 3) : Ls (bvec w k) = (e1 k).2 := by
  rw [Ls_apply]
  unfold bvec
  rw [Finset.sum_eq_single w]
  · simp
  · intro w' _ hw'
    simp [hw']
  · simp

/-- `log ht` is `∑_w t_w` in the chart. -/
lemma log_ht_chart (y : Coord F) : Real.log (X.ht (chart F y)) = Ls y := by
  unfold X.ht
  rw [Real.log_prod fun w _ => (X.v_pos _ w).ne', Ls_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [chart_v, Real.log_exp]

lemma pd_comp_Ls {G : ℝ → ℂ} (hG : Differentiable ℝ G) (w : InfinitePlace F) (k : Fin 3) :
    pd w k (fun y : Coord F => G (Ls y)) = fun y => ((e1 k).2 : ℂ) * deriv G (Ls y) := by
  funext y
  unfold pd
  have h : HasFDerivAt (fun y : Coord F => G (Ls y)) ((fderiv ℝ G (Ls y)).comp Ls) y :=
    (hG (Ls y)).hasFDerivAt.comp y Ls.hasFDerivAt
  rw [h.fderiv, ContinuousLinearMap.comp_apply, Ls_bvec, fderiv_eq_smul_deriv, Complex.real_smul]

lemma contDiff_comp_Ls {G : ℝ → ℂ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    ContDiff ℝ (⊤ : ℕ∞) fun y : Coord F => G (Ls y) := hG.comp (Ls (F := F)).contDiff

lemma lapE_comp_Ls {G : ℝ → ℂ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) (y : Coord F) :
    lapE (fun y : Coord F => G (Ls y)) y =
      (Fintype.card (InfinitePlace F) : ℂ) * (-deriv (deriv G) (Ls y) + 2 * deriv G (Ls y)) := by
  have hG1 : Differentiable ℝ G := hG.differentiable (by simp)
  have hG' : ContDiff ℝ (⊤ : ℕ∞) (deriv G) := by
    have h : ContDiff ℝ ((⊤ : ℕ∞) + 1) G := hG
    exact (contDiff_succ_iff_deriv.1 h).2.2
  have hG2 : Differentiable ℝ (deriv G) := hG'.differentiable (by simp)
  unfold lapE
  have h1 : ∀ w : InfinitePlace F, ∀ k : Fin 3,
      pd w k (pd w k fun y : Coord F => G (Ls y)) y =
        ((e1 k).2 : ℂ) * (((e1 k).2 : ℂ) * deriv (deriv G) (Ls y)) := by
    intro w k
    rw [pd_comp_Ls hG1 w k]
    have h2 : pd w k (fun y : Coord F => ((e1 k).2 : ℂ) * deriv G (Ls y)) y =
        ((e1 k).2 : ℂ) * pd w k (fun y : Coord F => deriv G (Ls y)) y :=
      pd_const_mul ((hG2 (Ls y)).comp y Ls.differentiableAt) _ w k
    rw [h2, pd_comp_Ls hG2 w k]
  simp_rw [h1, pd_comp_Ls hG1]
  simp [Fin.sum_univ_three, acoef]
  ring

/-! ### Functions of the height on `X` -/

/-- A smooth function of `log ht` is smooth on `X`. -/
theorem X.smooth_comp_log_ht {G : ℝ → ℂ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    X.Smooth fun P : X F => G (Real.log (X.ht P)) := by
  unfold X.Smooth
  simp_rw [log_ht_chart]
  exact contDiff_comp_Ls hG

/-- `Δ (G ∘ log ht) = r (-G'' + 2G') ∘ log ht`. -/
theorem X.lap_comp_log_ht {G : ℝ → ℂ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) (P : X F) :
    X.lap (fun P : X F => G (Real.log (X.ht P))) P =
      (Fintype.card (InfinitePlace F) : ℂ) *
        (-deriv (deriv G) (Real.log (X.ht P)) + 2 * deriv G (Real.log (X.ht P))) := by
  unfold X.lap
  simp_rw [log_ht_chart]
  rw [lapE_comp_Ls hG, ← log_ht_chart, Homeomorph.apply_symm_apply]

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

/-- `Δ (G ∘ log I_{(c,d)}) = r (-G'' + 2G') ∘ log I_{(c,d)}`. -/
theorem X.lap_comp_log_pairHt {G : ℝ → ℂ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) {c d : F}
    (h : c ≠ 0 ∨ d ≠ 0) (P : X F) :
    X.lap (fun P : X F => G (Real.log (X.pairHt c d P))) P =
      (Fintype.card (InfinitePlace F) : ℂ) *
        (-deriv (deriv G) (Real.log (X.pairHt c d P)) + 2 * deriv G (Real.log (X.pairHt c d P))) := by
  obtain ⟨γ, rfl, rfl⟩ := exists_bottom_row h
  simp_rw [← X.ht_smul]
  have h1 := X.lap_comp_Ginf (X.smooth_comp_log_ht (F := F) hG) (sigma F γ) P
  rw [X.lap_comp_log_ht hG] at h1
  exact h1

/-! ### Eigenfunctions -/

lemma ofReal_cpow_eq_exp {x : ℝ} (hx : 0 < x) (s : ℂ) :
    ((x : ℝ) : ℂ) ^ s = Complex.exp (s * (Real.log x : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hx.ne'), ← Complex.ofReal_log hx.le,
    mul_comm]

lemma contDiff_cexp_mul (s : ℂ) : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => Complex.exp (s * (t : ℂ)) :=
  Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)

lemma deriv_cexp_mul (s : ℂ) :
    deriv (fun t : ℝ => Complex.exp (s * (t : ℂ))) =
      fun t : ℝ => s * Complex.exp (s * (t : ℂ)) := by
  funext t
  have h1 : HasDerivAt (fun t : ℝ => s * (t : ℂ)) s t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul s
  have := h1.cexp
  rw [this.deriv, mul_comm]

lemma deriv_deriv_cexp_mul (s : ℂ) (t : ℝ) :
    deriv (deriv fun t : ℝ => Complex.exp (s * (t : ℂ))) t = s * (s * Complex.exp (s * (t : ℂ))) := by
  rw [deriv_cexp_mul]
  have h1 : HasDerivAt (fun t : ℝ => s * (t : ℂ)) s t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul s
  have := (h1.cexp).const_mul s
  rw [this.deriv]
  ring

/-- **`I_{(c,d)}^s` is an eigenfunction of the Laplacian with eigenvalue `r s(2 - s)`**
(`r` = number of infinite places; each `Δ_w` contributes `s(2 - s)`). -/
theorem X.lap_pairHt_cpow {c d : F} (h : c ≠ 0 ∨ d ≠ 0) (s : ℂ) (P : X F) :
    X.lap (fun P : X F => ((X.pairHt c d P : ℝ) : ℂ) ^ s) P =
      (Fintype.card (InfinitePlace F) : ℂ) * (s * (2 - s)) * ((X.pairHt c d P : ℝ) : ℂ) ^ s := by
  have h0 : (fun P : X F => ((X.pairHt c d P : ℝ) : ℂ) ^ s) =
      fun P : X F => (fun t : ℝ => Complex.exp (s * (t : ℂ))) (Real.log (X.pairHt c d P)) := by
    funext P
    exact ofReal_cpow_eq_exp (X.pairHt_pos h P) s
  rw [h0, X.lap_comp_log_pairHt (contDiff_cexp_mul s) h, deriv_deriv_cexp_mul, deriv_cexp_mul,
    ofReal_cpow_eq_exp (X.pairHt_pos h P) s]
  ring

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.C5_Series
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

variable [IsTotallyComplex F]

/-! ### The Eisenstein series on pair classes -/

lemma eis_eq_tsum_pair (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) (s : ℂ) (Q : X F) :
    eis Ψ s Q = ∑' p : PairClass (RO.SOf 𝔪), wt h𝔪 Ψ s p * ((p.ht Q : ℝ) : ℂ) ^ s := by
  rw [eis_eq_tsum_ht, ← (RO.rowClassEquiv h𝔪).tsum_eq]
  refine tsum_congr fun q => ?_
  rw [ht_rowClassEquiv]
  unfold wt
  rw [Equiv.symm_apply_apply]

/-! ### Invariance, regularity -/

/-! ### The source -/

end

end ArtinKP.C5
end

section
-- module Solutions.Artin.KP.RF_Deriv1
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulGinfX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX
/-!
# WP-RF, part 5: derivative bounds of all orders for one factor of `ht_p^s` (stub D1, local part)

One factor of a pair height in the logarithmic chart `E1 = ℂ × ℝ ∋ (x, t)`, `v = e^t`:
`phi s c d (x, t) = (e^t / (|c x + d|² + |c|² e^{2t}))^s`.

**Method** (no Faà di Bruno, no explicit higher derivatives).  The vector
`Z = (u₁, u₂, q, r, U)`, `u = x̄/ρ`, `q = e^{2t}/ρ`, `r = 1/ρ`, `ρ = |x|² + e^{2t}`,
`U = κ·(e^t/ρ)^s`, satisfies a *polynomial autonomous system* `DZ = P(Z)` (`hasFDerivAt_Zfun`).
For such a system every iterated derivative is a smooth function of `Z` itself, the same for all
solutions (`exists_iter_poly`).  On `t ≥ -T` the vector `(u, q, r)` stays in a compact set, and
normalizing `U = 1` at the point gives

`place_bound`: `‖D^n (phi s c d)(y)‖ ≤ M · |phi s c d y|` for all `(c, d) ≠ 0` and all `y` with
`y.2 ≥ -T`, `M = M(s, n, T)`.  (For `n = 1, 2` this is (H2) of MATH2 §0.1.)
-/

set_option autoImplicit false

open scoped ComplexConjugate

noncomputable section

namespace ArtinKP.RF

/-! ### Polynomial autonomous systems -/

section system

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V]
  [NormedSpace ℝ V]

/-- If `DZ = P(Z)` with `P` smooth, then `D^n Z = P_n(Z)` with `P_n` smooth and independent of
the solution `Z`. -/
theorem exists_iter_poly (P : V → E →L[ℝ] V) (hP : ContDiff ℝ (⊤ : ℕ∞) P) (n : ℕ) :
    ∃ Pn : V → ContinuousMultilinearMap ℝ (fun _ : Fin n => E) V, ContDiff ℝ (⊤ : ℕ∞) Pn ∧
      ∀ Z : E → V, (∀ y, HasFDerivAt Z (P (Z y)) y) → ∀ y, iteratedFDeriv ℝ n Z y = Pn (Z y) := by
  induction n with
  | zero =>
    refine ⟨fun z => (continuousMultilinearCurryFin0 ℝ E V).symm z,
      (continuousMultilinearCurryFin0 ℝ E V).symm.contDiff, fun Z _ y => rfl⟩
  | succ n ih =>
    obtain ⟨Pn, hPn, hn⟩ := ih
    have hPn' : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ Pn) := hPn.fderiv_right (by exact le_rfl)
    have hc : ContDiff ℝ (⊤ : ℕ∞) fun z => (fderiv ℝ Pn z).comp (P z) := hPn'.clm_comp hP
    let L : (E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => E) V) →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => E) V :=
      ((continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n + 1) => E) V).symm.toContinuousLinearEquiv : _ ≃L[ℝ] _)
    have hc' : ContDiff ℝ (⊤ : ℕ∞) fun z =>
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) V).symm
          ((fderiv ℝ Pn z).comp (P z)) := ContDiff.continuousLinearMap_comp L hc
    refine ⟨fun z => (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) V).symm
        ((fderiv ℝ Pn z).comp (P z)), hc', fun Z hZ y => ?_⟩
    have h1 : iteratedFDeriv ℝ n Z = fun y => Pn (Z y) := funext (hn Z hZ)
    have hd : DifferentiableAt ℝ Pn (Z y) :=
      (hPn.differentiable (by simp)).differentiableAt
    have h2 : fderiv ℝ (iteratedFDeriv ℝ n Z) y = (fderiv ℝ Pn (Z y)).comp (P (Z y)) := by
      rw [h1]
      exact (hd.hasFDerivAt.comp y (hZ y)).fderiv
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, h2]

/-- Solutions of a smooth autonomous system are smooth. -/
theorem contDiff_of_system (P : V → E →L[ℝ] V) (hP : ContDiff ℝ (⊤ : ℕ∞) P) (Z : E → V)
    (hZ : ∀ y, HasFDerivAt Z (P (Z y)) y) : ContDiff ℝ (⊤ : ℕ∞) Z := by
  refine contDiff_of_differentiable_iteratedFDeriv fun m _ => ?_
  obtain ⟨Pm, hPm, hm⟩ := exists_iter_poly P hP m
  rw [show iteratedFDeriv ℝ m Z = fun y => Pm (Z y) from funext (hm Z hZ)]
  exact (hPm.differentiable (by simp)).comp fun y => (hZ y).differentiableAt

end system

/-! ### The system of one factor -/

lemma Psys_apply (s : ℂ) (z : V5) (k : E1') : Psys s z k = pfun s z k := rfl

lemma contDiff_Psys (s : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (Psys s) := by
  rw [contDiff_clm_apply_iff]
  intro k
  simp only [Psys_apply]
  unfold pfun mfun
  have hm : ContDiff ℝ (⊤ : ℕ∞) fun z : V5 =>
      2 * z.1 * k.1.re + 2 * z.2.1 * k.1.im + 2 * z.2.2.1 * k.2 := by fun_prop
  refine ContDiff.prodMk (by fun_prop) (ContDiff.prodMk (by fun_prop)
    (ContDiff.prodMk (by fun_prop) (ContDiff.prodMk (by fun_prop) ?_)))
  have h5 : ContDiff ℝ (⊤ : ℕ∞) fun z : V5 => z.2.2.2.2 := by fun_prop
  exact (contDiff_const.mul h5).mul
    (Complex.ofRealCLM.contDiff.comp (contDiff_const.sub hm))

lemma rho0_pos (y : E1') : 0 < rho0 y := by unfold rho0; positivity

theorem hasFDerivAt_Zfun (s κ : ℂ) (y : E1') :
    HasFDerivAt (Zfun s κ) (Psys s (Zfun s κ y)) y := by
  have hρ0 : rho0 y ≠ 0 := (rho0_pos y).ne'
  set h1 : E1' →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℝ) with hh1
  set h2 : E1' →L[ℝ] ℝ := Complex.imCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℝ) with hh2
  set tau : E1' →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℂ ℝ with htau
  have hA : HasFDerivAt (fun y : E1' => y.1.re) h1 y := h1.hasFDerivAt
  have hB : HasFDerivAt (fun y : E1' => y.1.im) h2 y := h2.hasFDerivAt
  have hT : HasFDerivAt (fun y : E1' => y.2) tau y := tau.hasFDerivAt
  have hE := (hT.const_mul (2 : ℝ)).exp
  have hρ : HasFDerivAt rho0 _ y := ((hA.pow 2).add (hB.pow 2)).add hE
  have hr : HasFDerivAt (fun y => (rho0 y)⁻¹) _ y := (hasDerivAt_inv hρ0).comp_hasFDerivAt y hρ
  have hu1 := hA.mul hr
  have hu2 := hB.mul hr
  have hq := hE.mul hr
  have hℓ := hT.sub (hρ.log hρ0)
  have hU := (((Complex.ofRealCLM.hasFDerivAt.comp y hℓ).const_mul s).cexp).const_mul κ
  have h := hu1.prodMk (hu2.prodMk (hq.prodMk (hr.prodMk hU)))
  refine h.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun k => ?_
  have hrho : rho0 y = y.1.re ^ 2 + y.1.im ^ 2 + Real.exp (2 * y.2) := rfl
  simp only [Psys_apply, pfun, mfun, Zfun, ContinuousLinearMap.prod_apply,
    add_apply, sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply, hh1, hh2, htau,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Complex.reCLM_apply,
    Complex.imCLM_apply, Complex.ofRealCLM_apply, smul_eq_mul, Function.comp_apply,
    Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · field_simp
    ring
  · field_simp
    ring
  · field_simp
    ring
  · field_simp
    ring
  · simp only [Pi.sub_apply]
    generalize Complex.exp (s * ((y.2 - Real.log (rho0 y) : ℝ) : ℂ)) = X
    push_cast
    field_simp
    ring

theorem hasFDerivAt_Zfun' (s κ : ℂ) (y : E1') :
    HasFDerivAt (Zfun' s κ) (Psys s (Zfun' s κ y)) y := by
  set tau : E1' →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℂ ℝ with htau
  have hT : HasFDerivAt (fun y : E1' => y.2) tau y := tau.hasFDerivAt
  have hU := (((Complex.ofRealCLM.hasFDerivAt.comp y hT).const_mul s).cexp).const_mul κ
  have h0 : HasFDerivAt (fun _ : E1' => (0 : ℝ)) (0 : E1' →L[ℝ] ℝ) y := hasFDerivAt_const _ _
  have h := h0.prodMk (h0.prodMk (h0.prodMk (h0.prodMk hU)))
  refine h.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun k => ?_
  simp only [Psys_apply, pfun, mfun, Zfun', ContinuousLinearMap.prod_apply,
    zero_apply, smul_apply,
    ContinuousLinearMap.comp_apply, htau, ContinuousLinearMap.coe_snd', Complex.ofRealCLM_apply,
    smul_eq_mul, Function.comp_apply, Prod.mk.injEq, zero_mul, mul_zero, sub_zero, add_zero,
    neg_zero, true_and]
  ring

lemma pi5_apply (z : V5) : pi5 z = z.2.2.2.2 := rfl

/-- The bound for all solutions with last coordinate `κ ψ`. -/
theorem bound_of_sol (s : ℂ) (n : ℕ) (R : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (ψ : E1' → ℂ) (Z : ℂ → E1' → V5),
      (∀ κ y, HasFDerivAt (Z κ) (Psys s (Z κ y)) y) → (∀ κ y, pi5 (Z κ y) = κ * ψ y) →
      ∀ y₀ : E1', ψ y₀ ≠ 0 → ‖Z (ψ y₀)⁻¹ y₀‖ ≤ R →
        ‖iteratedFDeriv ℝ n ψ y₀‖ ≤ M * ‖ψ y₀‖ := by
  obtain ⟨Pn, hPn, hn⟩ := exists_iter_poly (Psys s) (contDiff_Psys s) n
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : V5) R).exists_bound_of_continuousOn
    hPn.continuous.continuousOn
  refine ⟨‖pi5‖ * max C 0, mul_nonneg (norm_nonneg _) (le_max_right _ _),
    fun ψ Z hZ hπ y₀ hψ hR => ?_⟩
  set κ := (ψ y₀)⁻¹ with hκ
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (Z κ) :=
    contDiff_of_system (Psys s) (contDiff_Psys s) (Z κ) (hZ κ)
  have e1 : ψ = fun y => ψ y₀ • (pi5 ∘ Z κ) y := by
    funext y
    rw [Function.comp_apply, hπ, hκ, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hψ, one_mul]
  have hsm' : ContDiff ℝ (⊤ : ℕ∞) (pi5 ∘ Z κ) := pi5.contDiff.comp hsm
  have e2 : iteratedFDeriv ℝ n ψ y₀ = ψ y₀ • iteratedFDeriv ℝ n (pi5 ∘ Z κ) y₀ := by
    conv_lhs => rw [e1]
    exact iteratedFDeriv_const_smul_apply' (hsm'.contDiffAt.of_le (by exact_mod_cast le_top))
  have e3 : iteratedFDeriv ℝ n (pi5 ∘ Z κ) y₀
      = pi5.compContinuousMultilinearMap (iteratedFDeriv ℝ n (Z κ) y₀) :=
    pi5.iteratedFDeriv_comp_left hsm.contDiffAt (by exact_mod_cast le_top)
  rw [e2, norm_smul, e3, hn (Z κ) (hZ κ) y₀, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  exact mul_le_mul_of_nonneg_left
    ((hC _ (mem_closedBall_zero_iff.mpr hR)).trans (le_max_left _ _)) (norm_nonneg _)

/-! ### One factor of a pair height -/

lemma rho_pos {c d : ℂ} (h : c ≠ 0 ∨ d ≠ 0) (y : E1') : 0 < rho c d y := by
  unfold rho
  by_cases hc : c = 0
  · subst hc
    have hd : d ≠ 0 := by simpa using h
    simpa using Complex.normSq_pos.mpr hd
  · have : 0 < Complex.normSq c * Real.exp (2 * y.2) :=
      mul_pos (Complex.normSq_pos.mpr hc) (Real.exp_pos _)
    have := Complex.normSq_nonneg (c * y.1 + d)
    linarith

lemma rho_eq_of_ne {c : ℂ} (hc : c ≠ 0) (d : ℂ) (y : E1') :
    rho c d y = Complex.normSq c * rho0 (y + (d / c, 0)) := by
  unfold rho rho0
  have e : c * y.1 + d = c * (y.1 + d / c) := by field_simp
  rw [e, Complex.normSq_mul, Complex.normSq_apply (y.1 + d / c)]
  simp only [Prod.fst_add, Prod.snd_add, add_zero]
  ring

lemma phi_eq_of_ne (s : ℂ) {c : ℂ} (hc : c ≠ 0) (d : ℂ) :
    phi s c d = fun y => Complex.exp (-(s * (Real.log (Complex.normSq c) : ℂ))) •
      phi0 s (y + (d / c, 0)) := by
  funext y
  have hn : 0 < Complex.normSq c := Complex.normSq_pos.mpr hc
  rw [phi, phi0, rho_eq_of_ne hc, Real.log_mul hn.ne' (rho0_pos _).ne', smul_eq_mul,
    ← Complex.exp_add]
  congr 1
  simp only [Prod.snd_add, add_zero]
  push_cast
  ring

lemma phi_eq_of_eq (s : ℂ) (d : ℂ) :
    phi s 0 d = fun y => Complex.exp (-(s * (Real.log (Complex.normSq d) : ℂ))) •
      Complex.exp (s * (y.2 : ℂ)) := by
  funext y
  rw [phi, rho, smul_eq_mul, ← Complex.exp_add]
  congr 1
  simp only [zero_mul, zero_add, map_zero, add_zero]
  push_cast
  ring

lemma norm_Zfun_le (s : ℂ) {T : ℝ} {y : E1'} (hy : -T ≤ y.2) :
    ‖Zfun s (phi0 s y)⁻¹ y‖ ≤ Real.exp T + Real.exp (2 * T) + 1 := by
  have hρ := rho0_pos y
  have hρe : Real.exp (2 * y.2) ≤ rho0 y := by
    unfold rho0; nlinarith [sq_nonneg y.1.re, sq_nonneg y.1.im]
  have heT : Real.exp (-y.2) ≤ Real.exp T := Real.exp_le_exp.mpr (by linarith)
  have he2T : Real.exp (-(2 * y.2)) ≤ Real.exp (2 * T) := Real.exp_le_exp.mpr (by linarith)
  have hE := Real.exp_pos T
  have hE2 := Real.exp_pos (2 * T)
  have hr : (rho0 y)⁻¹ ≤ Real.exp (2 * T) := by
    refine le_trans ?_ he2T
    rw [Real.exp_neg]
    exact inv_anti₀ (Real.exp_pos _) hρe
  have hsq : Real.exp (2 * y.2) = Real.exp y.2 ^ 2 := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have hu : ∀ a : ℝ, a ^ 2 ≤ y.1.re ^ 2 + y.1.im ^ 2 → |a * (rho0 y)⁻¹| ≤ Real.exp T := by
    intro a ha
    rw [abs_mul, abs_of_pos (inv_pos.mpr hρ), ← div_eq_mul_inv, div_le_iff₀ hρ]
    have h1 : 2 * |a| * Real.exp y.2 ≤ rho0 y := by
      unfold rho0
      rw [hsq]
      nlinarith [sq_nonneg (|a| - Real.exp y.2), sq_abs a]
    have h2 : 1 ≤ Real.exp T * Real.exp y.2 := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
    have h3 : 0 ≤ |a| := abs_nonneg a
    nlinarith [Real.exp_pos y.2, mul_nonneg h3 (Real.exp_pos y.2).le]
  have h5 : ‖(phi0 s y)⁻¹ * Complex.exp (s * ((y.2 - Real.log (rho0 y) : ℝ) : ℂ))‖ = 1 := by
    rw [phi0, inv_mul_cancel₀ (Complex.exp_ne_zero _), norm_one]
  unfold Zfun
  refine norm_prod_le_iff.mpr ⟨?_, norm_prod_le_iff.mpr ⟨?_, norm_prod_le_iff.mpr ⟨?_,
    norm_prod_le_iff.mpr ⟨?_, ?_⟩⟩⟩⟩
  · rw [Real.norm_eq_abs]
    have := hu y.1.re (by nlinarith [sq_nonneg y.1.im])
    linarith
  · rw [Real.norm_eq_abs]
    have := hu y.1.im (by nlinarith [sq_nonneg y.1.re])
    linarith
  · rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (inv_pos.mpr hρ)),
      ← div_eq_mul_inv]
    have : Real.exp (2 * y.2) / rho0 y ≤ 1 := (div_le_one hρ).mpr hρe
    linarith
  · rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)]
    linarith
  · rw [h5]; linarith

lemma norm_Zfun'_le (s : ℂ) (T : ℝ) (y : E1') :
    ‖Zfun' s (Complex.exp (s * (y.2 : ℂ)))⁻¹ y‖ ≤ Real.exp T + Real.exp (2 * T) + 1 := by
  have hE := Real.exp_pos T
  have hE2 := Real.exp_pos (2 * T)
  have h5 : ‖(Complex.exp (s * (y.2 : ℂ)))⁻¹ * Complex.exp (s * (y.2 : ℂ))‖ = 1 := by
    rw [inv_mul_cancel₀ (Complex.exp_ne_zero _), norm_one]
  unfold Zfun'
  refine norm_prod_le_iff.mpr ⟨?_, norm_prod_le_iff.mpr ⟨?_, norm_prod_le_iff.mpr ⟨?_,
    norm_prod_le_iff.mpr ⟨?_, ?_⟩⟩⟩⟩
  · rw [norm_zero]; linarith
  · rw [norm_zero]; linarith
  · rw [norm_zero]; linarith
  · rw [norm_zero]; linarith
  · rw [h5]; linarith

/-- **Derivative bounds of all orders for one factor**, uniform in the pair `(c, d) ≠ 0` and in
`x`, locally uniform in `t`. -/
theorem place_bound (s : ℂ) (n : ℕ) (T : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ c d : ℂ, (c ≠ 0 ∨ d ≠ 0) → ∀ y : E1', -T ≤ y.2 →
      ‖iteratedFDeriv ℝ n (phi s c d) y‖ ≤ M * ‖phi s c d y‖ := by
  obtain ⟨M, hM0, hM⟩ := bound_of_sol s n (Real.exp T + Real.exp (2 * T) + 1)
  have hphi0 : ∀ y : E1', -T ≤ y.2 → ‖iteratedFDeriv ℝ n (phi0 s) y‖ ≤ M * ‖phi0 s y‖ :=
    fun y hy => hM (phi0 s) (Zfun s) (hasFDerivAt_Zfun s) (fun κ y => rfl) y
      (Complex.exp_ne_zero _) (norm_Zfun_le s hy)
  have hexp : ∀ y : E1', ‖iteratedFDeriv ℝ n (fun y : E1' => Complex.exp (s * (y.2 : ℂ))) y‖
      ≤ M * ‖Complex.exp (s * (y.2 : ℂ))‖ :=
    fun y => hM (fun y : E1' => Complex.exp (s * (y.2 : ℂ))) (Zfun' s) (hasFDerivAt_Zfun' s)
      (fun κ y => rfl) y (Complex.exp_ne_zero _) (norm_Zfun'_le s T y)
  have hsm0 : ContDiff ℝ (⊤ : ℕ∞) (phi0 s) := by
    have := contDiff_of_system (Psys s) (contDiff_Psys s) (Zfun s 1) (hasFDerivAt_Zfun s 1)
    have h2 : phi0 s = pi5 ∘ Zfun s 1 := by
      funext y; simp [pi5_apply, Zfun, phi0]
    rw [h2]; exact pi5.contDiff.comp this
  have hsme : ContDiff ℝ (⊤ : ℕ∞) (fun y : E1' => Complex.exp (s * (y.2 : ℂ))) := by
    have := contDiff_of_system (Psys s) (contDiff_Psys s) (Zfun' s 1) (hasFDerivAt_Zfun' s 1)
    have h2 : (fun y : E1' => Complex.exp (s * (y.2 : ℂ))) = pi5 ∘ Zfun' s 1 := by
      funext y; simp [pi5_apply, Zfun']
    rw [h2]; exact pi5.contDiff.comp this
  refine ⟨M, hM0, fun c d hcd y hy => ?_⟩
  by_cases hc : c = 0
  · subst hc
    rw [phi_eq_of_eq]
    rw [iteratedFDeriv_const_smul_apply' (hsme.contDiffAt.of_le (by exact_mod_cast le_top)),
      norm_smul, norm_smul]
    calc ‖Complex.exp (-(s * (Real.log (Complex.normSq d) : ℂ)))‖ *
          ‖iteratedFDeriv ℝ n (fun y : E1' => Complex.exp (s * (y.2 : ℂ))) y‖
        ≤ ‖Complex.exp (-(s * (Real.log (Complex.normSq d) : ℂ)))‖ *
          (M * ‖Complex.exp (s * (y.2 : ℂ))‖) :=
          mul_le_mul_of_nonneg_left (hexp y) (norm_nonneg _)
      _ = _ := by ring
  · rw [phi_eq_of_ne s hc]
    have hsm1 : ContDiff ℝ (⊤ : ℕ∞) (fun y : E1' => phi0 s (y + (d / c, 0))) :=
      hsm0.comp (contDiff_id.add contDiff_const)
    rw [iteratedFDeriv_const_smul_apply' (hsm1.contDiffAt.of_le (by exact_mod_cast le_top)),
      norm_smul, norm_smul, iteratedFDeriv_comp_add_right]
    have hy' : -T ≤ (y + ((d / c, 0) : E1')).2 := by simpa using hy
    calc ‖Complex.exp (-(s * (Real.log (Complex.normSq c) : ℂ)))‖ *
          ‖iteratedFDeriv ℝ n (phi0 s) (y + (d / c, 0))‖
        ≤ ‖Complex.exp (-(s * (Real.log (Complex.normSq c) : ℂ)))‖ *
          (M * ‖phi0 s (y + (d / c, 0))‖) :=
          mul_le_mul_of_nonneg_left (hphi0 _ hy') (norm_nonneg _)
      _ = _ := by ring

theorem contDiff_phi (s : ℂ) {c d : ℂ} (h : c ≠ 0 ∨ d ≠ 0) : ContDiff ℝ (⊤ : ℕ∞) (phi s c d) := by
  have hρ : ContDiff ℝ (⊤ : ℕ∞) (rho c d) := by
    unfold rho
    have h1 : ContDiff ℝ (⊤ : ℕ∞) fun y : E1' => c * y.1 + d :=
      (contDiff_const.mul contDiff_fst).add contDiff_const
    have h2 : ContDiff ℝ (⊤ : ℕ∞) fun y : E1' => Complex.normSq (c * y.1 + d) := by
      simp only [Complex.normSq_apply]
      have hre : ContDiff ℝ (⊤ : ℕ∞) fun y : E1' => (c * y.1 + d).re :=
        Complex.reCLM.contDiff.comp h1
      have him : ContDiff ℝ (⊤ : ℕ∞) fun y : E1' => (c * y.1 + d).im :=
        Complex.imCLM.contDiff.comp h1
      exact (hre.mul hre).add (him.mul him)
    exact h2.add (contDiff_const.mul (Real.contDiff_exp.comp (contDiff_const.mul contDiff_snd)))
  unfold phi
  refine Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp ?_))
  exact contDiff_snd.sub (hρ.log fun y => (rho_pos h y).ne')

end ArtinKP.RF
end
end

section
-- module Solutions.Artin.KP.RF_Series
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulGinfX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX
/-!
# WP-RF, part 6: series of smooth functions with locally uniformly summable derivatives

`tsum_smooth_local`: if every `f i : E → ℂ` is smooth and, around every point and for every
order `k`, the `k`-th derivatives are bounded on the unit ball by a summable family, then
`y ↦ ∑' i, f i y` is smooth and every iterated derivative is the sum of the iterated derivatives
of the terms.  (Mathlib's `contDiff_tsum` asks for *global* bounds; the local version is obtained
by multiplying with a bump function.)
-/

set_option autoImplicit false

open Filter Topology

noncomputable section

namespace ArtinKP.RF

variable {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem tsum_smooth_local (f : α → E → ℂ) (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hloc : ∀ (y₀ : E) (k : ℕ), ∃ u : α → ℝ, Summable u ∧
      ∀ i, ∀ y ∈ Metric.ball y₀ 1, ‖iteratedFDeriv ℝ k (f i) y‖ ≤ u i) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => ∑' i, f i y) ∧
      ∀ (k : ℕ) (y : E), HasSum (fun i => iteratedFDeriv ℝ k (f i) y)
        (iteratedFDeriv ℝ k (fun y => ∑' i, f i y) y) := by
  have key : ∀ y₀ : E, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => ∑' i, f i y) y₀ ∧
      ∀ k : ℕ, HasSum (fun i => iteratedFDeriv ℝ k (f i) y₀)
        (iteratedFDeriv ℝ k (fun y => ∑' i, f i y) y₀) := by
    intro y₀
    let χ : ContDiffBump y₀ := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
    have hχ : ContDiff ℝ (⊤ : ℕ∞) (χ : E → ℝ) := χ.contDiff
    have hχb : ∀ j : ℕ, ∃ C : ℝ, ∀ x : E, ‖iteratedFDeriv ℝ j (χ : E → ℝ) x‖ ≤ C := fun j =>
      (hχ.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
        (χ.hasCompactSupport.iteratedFDeriv j)
    choose Cχ hCχ using hχb
    have hCχ0 : ∀ j, 0 ≤ Cχ j := fun j => (norm_nonneg _).trans (hCχ j y₀)
    choose u hu hub using hloc y₀
    have hu0 : ∀ k i, 0 ≤ u k i := fun k i =>
      (norm_nonneg _).trans (hub k i y₀ (Metric.mem_ball_self one_pos))
    set g : α → E → ℂ := fun i y => χ y • f i y with hg
    have hgs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (g i) := fun i => hχ.smul (hf i)
    set v : ℕ → α → ℝ := fun k i =>
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * Cχ j * u (k - j) i with hv
    have hvs : ∀ k, Summable (v k) := fun k =>
      summable_sum fun j _ => (hu (k - j)).mul_left _
    have hv0 : ∀ k i, 0 ≤ v k i := fun k i =>
      Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCχ0 j)) (hu0 _ i)
    have hbound : ∀ (k : ℕ) (i : α) (x : E), ‖iteratedFDeriv ℝ k (g i) x‖ ≤ v k i := by
      intro k i x
      by_cases hx : x ∈ Metric.ball y₀ 1
      · refine (norm_iteratedFDeriv_smul_le hχ (hf i) x (n := k)
          (by exact_mod_cast le_top)).trans ?_
        refine Finset.sum_le_sum fun j _ => ?_
        have h1 := hCχ j x
        have h2 := hub (k - j) i x hx
        have h3 : (0 : ℝ) ≤ k.choose j := Nat.cast_nonneg _
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 h3) h2 (norm_nonneg _)
          (mul_nonneg h3 (hCχ0 j))
      · have hts : x ∉ tsupport (g i) := by
          intro hmem
          have h1 : tsupport (g i) ⊆ tsupport (χ : E → ℝ) := tsupport_smul_subset_left _ _
          have h2 := h1 hmem
          rw [χ.tsupport_eq] at h2
          apply hx
          rw [Metric.mem_ball]
          have h3 : dist x y₀ ≤ 1 / 2 := Metric.mem_closedBall.mp h2
          linarith
        have h0 : iteratedFDeriv ℝ k (g i) x = 0 := by
          by_contra hne
          exact hts (support_iteratedFDeriv_subset k hne)
        rw [h0, norm_zero]
        exact hv0 k i
    have hG : ContDiff ℝ (⊤ : ℕ∞) (fun y => ∑' i, g i y) :=
      contDiff_tsum hgs (fun k _ => hvs k) (fun k i x _ => hbound k i x)
    have hGD : ∀ k : ℕ, iteratedFDeriv ℝ k (fun y => ∑' i, g i y) y₀
        = ∑' i, iteratedFDeriv ℝ k (g i) y₀ := fun k =>
      iteratedFDeriv_tsum_apply hgs (fun k _ => hvs k) (fun k i x _ => hbound k i x)
        (by exact_mod_cast le_top) y₀
    have hball : Metric.ball y₀ (1 / 4) ∈ 𝓝 y₀ := Metric.ball_mem_nhds y₀ (by norm_num)
    have hone : ∀ y ∈ Metric.ball y₀ (1 / 4), (χ y : ℝ) = 1 := fun y hy =>
      χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
    have heqi : ∀ i, f i =ᶠ[𝓝 y₀] g i := fun i => by
      filter_upwards [hball] with y hy
      rw [hg]; simp only; rw [hone y hy, one_smul]
    have heq : (fun y => ∑' i, f i y) =ᶠ[𝓝 y₀] fun y => ∑' i, g i y := by
      filter_upwards [hball] with y hy
      refine tsum_congr fun i => ?_
      rw [hg]; simp only; rw [hone y hy, one_smul]
    refine ⟨hG.contDiffAt.congr_of_eventuallyEq heq, fun k => ?_⟩
    have hsum : Summable fun i => iteratedFDeriv ℝ k (f i) y₀ :=
      Summable.of_norm_bounded (hu k) fun i => hub k i y₀ (Metric.mem_ball_self one_pos)
    have e1 : iteratedFDeriv ℝ k (fun y => ∑' i, f i y) y₀
        = ∑' i, iteratedFDeriv ℝ k (f i) y₀ := by
      rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds, hGD k]
      exact tsum_congr fun i => ((heqi i).iteratedFDeriv ℝ k).eq_of_nhds.symm
    rw [e1]
    exact hsum.hasSum
  exact ⟨contDiff_iff_contDiffAt.mpr fun y => (key y).1, fun k y => (key y).2 k⟩

end ArtinKP.RF
end
end

section
-- module Solutions.Artin.KP.RF_Deriv2
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup
/-!
# WP-RF, part 7: derivative bounds for `I_{(c,d)}^s` and differentiation of the series (stub D1)

In the logarithmic chart `Coord F ∋ y = (x_w, t_w)_w`:

* `Uc s c d y = ∏_w phi s (σ_w c) (σ_w d) (y w) = I_{(c,d)}(chart y)^s` (`Uc_eq`);
* `Uc_bound`: `‖D^n (I_{(c,d)}^s ∘ chart)(y)‖ ≤ M · I_{(c,d)}(chart y)^{Re s}` for all pairs
  `(c, d) ≠ 0` of `F` and all `y` with `t_w ≥ -T`; `M = M(s, n, T)`.  All orders `n`, uniform in
  the pair and in `x`.  (`n = 1, 2`: the scaled first and second derivatives of D1.)
* `hasSum_lapE`: the chart Laplacian of a series which may be differentiated termwise twice.
* **`smooth_tsum_pairHt_cpow`, `lap_tsum_pairHt_cpow`**: for any family of pairs `(c_i, d_i)` and
  coefficients `a_i` with a locally uniform summable majorant of `|a_i| I_i^{Re s}`,
  `E(P) = ∑' i, a_i I_i(P)^s` is `X.Smooth` and `X.lap E = r s (2 - s) E`.
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

lemma norm_projC_le (w : InfinitePlace F) : ‖projC w‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by
    rw [one_mul]; exact norm_le_pi_norm y w

lemma emb_ne {c d : F} (h : c ≠ 0 ∨ d ≠ 0) (w : InfinitePlace F) :
    w.embedding c ≠ 0 ∨ w.embedding d ≠ 0 :=
  h.imp (fun h => (map_ne_zero _).mpr h) (fun h => (map_ne_zero _).mpr h)

lemma rowDen_chart (c d : ℂ) (p : E1) : H3.rowDen c d (chart1 p) = rho c d p := by
  unfold H3.rowDen rho
  rw [chart1_x, chart1_v, sq, ← Real.exp_add]
  congr 3
  ring

theorem Uc_eq {c d : F} (h : c ≠ 0 ∨ d ≠ 0) (s : ℂ) (y : Coord F) :
    Uc s c d y = ((X.pairHt c d (chart F y) : ℝ) : ℂ) ^ s := by
  rw [ofReal_cpow_eq_exp (X.pairHt_pos h _) s, X.pairHt_eq_prod, Real.log_prod]
  · rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum, Uc]
    refine Finset.prod_congr rfl fun w _ => ?_
    have hr : (0 : ℝ) < rho (w.embedding c) (w.embedding d) (y w) := rho_pos (emb_ne h w) _
    have e1 : H3.rowDen (w.embedding c) (w.embedding d) (chart F y w)
        = rho (w.embedding c) (w.embedding d) (y w) := rowDen_chart _ _ _
    rw [phi, e1, chart_v, Real.log_div (Real.exp_pos _).ne' hr.ne', Real.log_exp]
  · intro w _
    have hr : (0 : ℝ) < H3.rowDen (w.embedding c) (w.embedding d) (chart F y w) :=
      H3.rowDen_pos (emb_ne h w) _
    exact (div_pos ((chart F y).v_pos w) hr).ne'

theorem contDiff_Uc {c d : F} (h : c ≠ 0 ∨ d ≠ 0) (s : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (Uc s c d) := by
  unfold Uc
  exact contDiff_prod fun w _ => (contDiff_phi s (emb_ne h w)).comp (projC w).contDiff

/-- **Derivative bounds of all orders for `I_{(c,d)}^s`** in the chart, uniform in the pair. -/
theorem Uc_bound (s : ℂ) (n : ℕ) (T : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ c d : F, (c ≠ 0 ∨ d ≠ 0) → ∀ y : Coord F, (∀ w, -T ≤ (y w).2) →
      ‖iteratedFDeriv ℝ n (Uc s c d) y‖ ≤ M * ‖Uc s c d y‖ := by
  classical
  choose Mk hMk0 hMk using fun k => place_bound s k T
  refine ⟨∑ p ∈ (Finset.univ : Finset (InfinitePlace F)).sym n,
      ((p : Multiset (InfinitePlace F)).countPerms : ℝ) *
        ∏ j, Mk ((p : Multiset (InfinitePlace F)).count j),
    Finset.sum_nonneg fun p _ => mul_nonneg (Nat.cast_nonneg _)
      (Finset.prod_nonneg fun j _ => hMk0 _), fun c d h y hy => ?_⟩
  set f : InfinitePlace F → Coord F → ℂ := fun j y =>
    phi s (j.embedding c) (j.embedding d) (y j) with hf
  have hfs : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j) := fun j =>
    (contDiff_phi s (emb_ne h j)).comp (projC j).contDiff
  have hterm : ∀ (j : InfinitePlace F) (k : ℕ), ‖iteratedFDeriv ℝ k (f j) y‖
      ≤ Mk k * ‖phi s (j.embedding c) (j.embedding d) (y j)‖ := by
    intro j k
    have e : f j = phi s (j.embedding c) (j.embedding d) ∘ projC j := rfl
    rw [e, (projC j).iteratedFDeriv_comp_right (contDiff_phi s (emb_ne h j)) y
      (i := k) (by exact_mod_cast le_top)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have h1 : ∏ _i : Fin k, ‖projC j‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => norm_projC_le j
    calc ‖iteratedFDeriv ℝ k (phi s (j.embedding c) (j.embedding d)) (projC j y)‖
          * ∏ _i : Fin k, ‖projC j‖
        ≤ ‖iteratedFDeriv ℝ k (phi s (j.embedding c) (j.embedding d)) (projC j y)‖ * 1 :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ ≤ _ := by
          rw [mul_one]
          exact hMk k _ _ (emb_ne h j) _ (hy j)
  have hprod := norm_iteratedFDeriv_prod_le (𝕜 := ℝ) (u := (Finset.univ : Finset (InfinitePlace F)))
    (f := f) (N := ((⊤ : ℕ∞) : WithTop ℕ∞)) (fun j _ => hfs j) (x := y) (n := n)
    (by exact_mod_cast le_top)
  have e0 : Uc s c d = fun y => ∏ j ∈ (Finset.univ : Finset (InfinitePlace F)), f j y := rfl
  rw [e0]
  refine hprod.trans ?_
  rw [norm_prod, Finset.sum_mul]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  exact Finset.prod_le_prod (fun j _ => norm_nonneg _) fun j _ => hterm j _

/-! ### Termwise Laplacian -/

lemma pd_eq_iter (U : Coord F → ℂ) (w : InfinitePlace F) (k : Fin 3) (y : Coord F) :
    pd w k U y = iteratedFDeriv ℝ 1 U y fun _ => bvec w k := by
  rw [iteratedFDeriv_one_apply]; rfl

lemma pd_pd_eq_iter {U : Coord F → ℂ} (hU : ContDiff ℝ (⊤ : ℕ∞) U) (w : InfinitePlace F)
    (k : Fin 3) (y : Coord F) :
    pd w k (pd w k U) y = iteratedFDeriv ℝ 2 U y fun _ => bvec w k := by
  have hd : DifferentiableAt ℝ (fderiv ℝ U) y :=
    ((hU.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by exact le_rfl)).differentiable
      (by simp)).differentiableAt
  rw [iteratedFDeriv_two_apply]
  show fderiv ℝ (fun z => fderiv ℝ U z (bvec w k)) y (bvec w k) = _
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

/-- The chart Laplacian of a series that may be differentiated termwise (orders 1 and 2). -/
theorem hasSum_lapE {α : Type*} {f : α → Coord F → ℂ} (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hS : ContDiff ℝ (⊤ : ℕ∞) fun y => ∑' i, f i y)
    (hD : ∀ (k : ℕ) (y : Coord F), HasSum (fun i => iteratedFDeriv ℝ k (f i) y)
      (iteratedFDeriv ℝ k (fun y => ∑' i, f i y) y)) (y : Coord F) :
    HasSum (fun i => lapE (f i) y) (lapE (fun y => ∑' i, f i y) y) := by
  have h1 : ∀ (w : InfinitePlace F) (k : Fin 3),
      HasSum (fun i => pd w k (f i) y) (pd w k (fun y => ∑' i, f i y) y) := by
    intro w k
    simp only [pd_eq_iter]
    exact ContinuousMultilinearMap.hasSum_eval (hD 1 y) _
  have h2 : ∀ (w : InfinitePlace F) (k : Fin 3),
      HasSum (fun i => pd w k (pd w k (f i)) y)
        (pd w k (pd w k (fun y => ∑' i, f i y)) y) := by
    intro w k
    rw [pd_pd_eq_iter hS]
    simp only [pd_pd_eq_iter (hf _)]
    exact ContinuousMultilinearMap.hasSum_eval (hD 2 y) _
  unfold lapE
  refine hasSum_sum fun w _ => ?_
  exact (hasSum_sum fun k _ => ((h2 w k).mul_left _).neg).add ((h1 w 2).mul_left 2)

/-! ### The series `∑ a_i I_i^s` -/

section series

variable {α : Type*} (c d : α → F) (a : α → ℂ) (s : ℂ)

/-- The hypotheses of `tsum_smooth_local` for `f i = a_i · I_i^s ∘ chart`. -/
lemma series_local (hne : ∀ i, c i ≠ 0 ∨ d i ≠ 0)
    (hmaj : ∀ K : Set (X F), IsCompact K → ∃ u : α → ℝ, Summable u ∧
      ∀ i, ∀ P ∈ K, ‖a i‖ * X.pairHt (c i) (d i) P ^ s.re ≤ u i)
    (y₀ : Coord F) (k : ℕ) : ∃ u : α → ℝ, Summable u ∧ ∀ i, ∀ y ∈ Metric.ball y₀ 1,
      ‖iteratedFDeriv ℝ k (fun y => a i * Uc s (c i) (d i) y) y‖ ≤ u i := by
  obtain ⟨M, hM0, hM⟩ := Uc_bound (F := F) s k (‖y₀‖ + 1)
  obtain ⟨u, hu, hub⟩ := hmaj (chart F '' Metric.closedBall y₀ 1)
    ((isCompact_closedBall y₀ 1).image (chart F).continuous)
  refine ⟨fun i => M * u i, hu.mul_left M, fun i y hy => ?_⟩
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (Uc s (c i) (d i)) := contDiff_Uc (hne i) s
  have e : (fun y => a i * Uc s (c i) (d i) y) = fun y => a i • Uc s (c i) (d i) y := rfl
  rw [e, iteratedFDeriv_const_smul_apply' (hsm.contDiffAt.of_le (by exact_mod_cast le_top)),
    norm_smul]
  have hyT : ∀ w, -(‖y₀‖ + 1) ≤ (y w).2 := by
    intro w
    have h1 : ‖(y w).2‖ ≤ ‖y w‖ := norm_snd_le _
    have h2 : ‖y w‖ ≤ ‖y‖ := norm_le_pi_norm y w
    have h3 : ‖y‖ ≤ ‖y₀‖ + 1 := by
      have h4 : ‖y - y₀‖ < 1 := mem_ball_iff_norm.mp hy
      have h5 : ‖y‖ ≤ ‖y₀‖ + ‖y - y₀‖ := by
        have := norm_add_le y₀ (y - y₀)
        rwa [add_sub_cancel] at this
      linarith
    have h6 := neg_abs_le (y w).2
    rw [Real.norm_eq_abs] at h1
    linarith
  have hb := hM (c i) (d i) (hne i) y hyT
  have hnorm : ‖Uc s (c i) (d i) y‖ = X.pairHt (c i) (d i) (chart F y) ^ s.re := by
    rw [Uc_eq (hne i), Complex.norm_cpow_eq_rpow_re_of_pos (X.pairHt_pos (hne i) _)]
  have hmem : chart F y ∈ chart F '' Metric.closedBall y₀ 1 :=
    ⟨y, Metric.ball_subset_closedBall hy, rfl⟩
  calc ‖a i‖ * ‖iteratedFDeriv ℝ k (Uc s (c i) (d i)) y‖
      ≤ ‖a i‖ * (M * ‖Uc s (c i) (d i) y‖) := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = M * (‖a i‖ * X.pairHt (c i) (d i) (chart F y) ^ s.re) := by rw [hnorm]; ring
    _ ≤ M * u i := mul_le_mul_of_nonneg_left (hub i _ hmem) hM0

lemma series_chart (hne : ∀ i, c i ≠ 0 ∨ d i ≠ 0) :
    (fun y => (fun P : X F => ∑' i, a i * ((X.pairHt (c i) (d i) P : ℝ) : ℂ) ^ s) (chart F y))
      = fun y => ∑' i, a i * Uc s (c i) (d i) y := by
  funext y
  exact tsum_congr fun i => by rw [Uc_eq (hne i)]

/-- **D1, smoothness of the series.**  If `|a_i| I_i^{Re s}` has a summable majorant on every
compact set, then `P ↦ ∑' i, a_i I_i(P)^s` is smooth on `X`. -/
theorem smooth_tsum_pairHt_cpow (hne : ∀ i, c i ≠ 0 ∨ d i ≠ 0)
    (hmaj : ∀ K : Set (X F), IsCompact K → ∃ u : α → ℝ, Summable u ∧
      ∀ i, ∀ P ∈ K, ‖a i‖ * X.pairHt (c i) (d i) P ^ s.re ≤ u i) :
    X.Smooth fun P : X F => ∑' i, a i * ((X.pairHt (c i) (d i) P : ℝ) : ℂ) ^ s := by
  unfold X.Smooth
  rw [series_chart c d a s hne]
  exact (tsum_smooth_local (fun i y => a i * Uc s (c i) (d i) y)
    (fun i => contDiff_const.mul (contDiff_Uc (hne i) s))
    (series_local c d a s hne hmaj)).1

/-- **D1, the Laplacian of the series is taken termwise**: the series is an eigenfunction with
eigenvalue `r s (2 - s)`. -/
theorem lap_tsum_pairHt_cpow (hne : ∀ i, c i ≠ 0 ∨ d i ≠ 0)
    (hmaj : ∀ K : Set (X F), IsCompact K → ∃ u : α → ℝ, Summable u ∧
      ∀ i, ∀ P ∈ K, ‖a i‖ * X.pairHt (c i) (d i) P ^ s.re ≤ u i) (P : X F) :
    X.lap (fun P : X F => ∑' i, a i * ((X.pairHt (c i) (d i) P : ℝ) : ℂ) ^ s) P =
      (Fintype.card (InfinitePlace F) : ℂ) * (s * (2 - s)) *
        ∑' i, a i * ((X.pairHt (c i) (d i) P : ℝ) : ℂ) ^ s := by
  have hfs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) fun y => a i * Uc s (c i) (d i) y :=
    fun i => contDiff_const.mul (contDiff_Uc (hne i) s)
  obtain ⟨hS, hD⟩ := tsum_smooth_local (fun i y => a i * Uc s (c i) (d i) y) hfs
    (series_local c d a s hne hmaj)
  set y := (chart F).symm P with hy
  have hP : chart F y = P := (chart F).apply_symm_apply P
  have hsum := hasSum_lapE hfs hS hD y
  have hterm : ∀ i, lapE (fun y => a i * Uc s (c i) (d i) y) y =
      (Fintype.card (InfinitePlace F) : ℂ) * (s * (2 - s)) *
        (a i * ((X.pairHt (c i) (d i) P : ℝ) : ℂ) ^ s) := by
    intro i
    rw [lapE_const_mul ((contDiff_Uc (hne i) s).of_le two_le_top)]
    have h1 := X.lap_pairHt_cpow (hne i) s P
    unfold X.lap at h1
    have h2 : (fun y => ((X.pairHt (c i) (d i) (chart F y) : ℝ) : ℂ) ^ s) = Uc s (c i) (d i) :=
      funext fun y => (Uc_eq (hne i) s y).symm
    rw [h2] at h1
    rw [h1]
    ring
  unfold X.lap
  rw [series_chart c d a s hne, ← hsum.tsum_eq, tsum_congr hterm, tsum_mul_left]

end series

end

end ArtinKP.RF
end

section
-- module Solutions.Artin.KP.RF_Eis
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup
/-!
# WP-RF, part 8: the series over pair classes (stub D1 of WP-B1, in B1's indexing)

For `Re s > 2` and bounded coefficients `a : PairClass S → ℂ`,
`E(P) = ∑' p, a p · ht_p(P)^s` is `X.Smooth` and `X.lap E = r s (2 - s) E`
(`smooth_tsum_ht_cpow`, `lap_tsum_ht_cpow`).  This is `RF_Deriv2` with B1's majorant
`PairClass.exists_summable_majorant_cpow`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace ArtinKP.RF

open ArtinKP.X ArtinKP.B1

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F]
  (S : Finset (FinitePlace F))

lemma ht_cpow_eq (a : PairClass S → ℂ) (s : ℂ) (p : PairClass S) (P : X F) :
    a p * ((p.ht P : ℝ) : ℂ) ^ s =
      coefS S a s p * ((X.pairHt p.out.c p.out.d P : ℝ) : ℂ) ^ s := by
  have hN := X.sNorm_pos S p.out.ne_zero
  have hI := X.pairHt_pos p.out.ne_zero P
  rw [ofReal_cpow_eq_exp (p.ht_pos P), ofReal_cpow_eq_exp hI, coefS, mul_assoc,
    ← Complex.exp_add, PairClass.ht_eq_out, X.sHt, Real.log_div hI.ne' hN.ne']
  congr 2
  push_cast
  ring

lemma series_ht_eq (a : PairClass S → ℂ) (s : ℂ) :
    (fun P : X F => ∑' p : PairClass S, a p * ((p.ht P : ℝ) : ℂ) ^ s) =
      fun P : X F => ∑' p : PairClass S,
        coefS S a s p * ((X.pairHt p.out.c p.out.d P : ℝ) : ℂ) ^ s :=
  funext fun P => tsum_congr fun p => ht_cpow_eq S a s p P

lemma majorant_ht (a : PairClass S → ℂ) {A : ℝ} (ha : ∀ p, ‖a p‖ ≤ A) {s : ℂ}
    (hs : 2 < s.re) (K : Set (X F)) (hK : IsCompact K) :
    ∃ u : PairClass S → ℝ, Summable u ∧ ∀ p, ∀ P ∈ K,
      ‖coefS S a s p‖ * X.pairHt p.out.c p.out.d P ^ s.re ≤ u p := by
  obtain ⟨u, hu, hub⟩ := PairClass.exists_summable_majorant_cpow S hK hs le_rfl
  refine ⟨fun p => A * u p, hu.mul_left A, fun p P hP => ?_⟩
  have hI := X.pairHt_pos p.out.ne_zero P
  have h1 := hub P hP s le_rfl le_rfl p
  have h0 : 0 ≤ u p := (norm_nonneg _).trans h1
  have e : ‖coefS S a s p‖ * X.pairHt p.out.c p.out.d P ^ s.re
      = ‖a p‖ * ‖((p.ht P : ℝ) : ℂ) ^ s‖ := by
    rw [← Complex.norm_cpow_eq_rpow_re_of_pos hI s, ← norm_mul, ← norm_mul, ht_cpow_eq]
  rw [e]
  exact mul_le_mul (ha p) h1 (norm_nonneg _) ((norm_nonneg _).trans (ha p))

/-- **D1 for the series over pair classes: smoothness.** -/
theorem smooth_tsum_ht_cpow (a : PairClass S → ℂ) {A : ℝ} (ha : ∀ p, ‖a p‖ ≤ A) {s : ℂ}
    (hs : 2 < s.re) :
    X.Smooth fun P : X F => ∑' p : PairClass S, a p * ((p.ht P : ℝ) : ℂ) ^ s := by
  rw [series_ht_eq]
  exact smooth_tsum_pairHt_cpow (fun p : PairClass S => p.out.c) (fun p => p.out.d)
    (coefS S a s) s (fun p => p.out.ne_zero) (majorant_ht S a ha hs)

/-- **D1 for the series over pair classes: `(Δ - r s (2 - s)) E = 0`.** -/
theorem lap_tsum_ht_cpow (a : PairClass S → ℂ) {A : ℝ} (ha : ∀ p, ‖a p‖ ≤ A) {s : ℂ}
    (hs : 2 < s.re) (P : X F) :
    X.lap (fun P : X F => ∑' p : PairClass S, a p * ((p.ht P : ℝ) : ℂ) ^ s) P =
      (Fintype.card (InfinitePlace F) : ℂ) * (s * (2 - s)) *
        ∑' p : PairClass S, a p * ((p.ht P : ℝ) : ℂ) ^ s := by
  have e : ∑' p : PairClass S, a p * ((p.ht P : ℝ) : ℂ) ^ s =
      ∑' p : PairClass S, coefS S a s p * ((X.pairHt p.out.c p.out.d P : ℝ) : ℂ) ^ s :=
    tsum_congr fun p => ht_cpow_eq S a s p P
  rw [series_ht_eq, e]
  exact lap_tsum_pairHt_cpow (fun p : PairClass S => p.out.c) (fun p => p.out.d)
    (coefS S a s) s (fun p => p.out.ne_zero) (majorant_ht S a ha hs) P

end

end ArtinKP.RF
end

section
-- module Solutions.Artin.KP.GL_Eis
/-!
# WP-GL, part 1: D1 discharged — `C5.EisEigen Ψ s` for `Re s > 2`, and WP-C5 unconditionally

`eisEigen`: for every twisted section `Ψ` and `2 < Re s`, the Eisenstein series `B.eis Ψ s` is
`X.Smooth` and `Δ E = r s (2 - s) E`.  Proof: `C5.eis_eq_tsum_pair` writes the series over
`B1.PairClass (RO.SOf 𝔪)` with the bounded weights `C5.wt` (`C5.exists_wt_bound`), and
`RF.smooth_tsum_ht_cpow`, `RF.lap_tsum_ht_cpow` are WP-RF's D1 for such series.

Then the six theorems of WP-C5 that carried the hypothesis `EisEigen Ψ s`, restated without it.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter IsDedekindDomain

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.GL

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.CAbs ArtinKP.C5

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {ι : F →+* ℂ}
variable [IsTotallyComplex F]

/-- **D1 for the Eisenstein series**: `E_Ψ(·, s)` is smooth and `Δ E = r s (2 - s) E` for
`Re s > 2`. -/
theorem eisEigen_of_two_lt_re_oai (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) {s : ℂ} (hs : 2 < s.re) : EisEigen Ψ s := by
  obtain ⟨Bd, -, hBd⟩ := exists_wt_bound h𝔪 Ψ ‖s‖
  have ha : ∀ p : PairClass (RO.SOf 𝔪), ‖wt h𝔪 Ψ s p‖ ≤ Bd := hBd s le_rfl
  have e : (fun Q : X F => eis Ψ s Q) =
      fun Q : X F => ∑' p : PairClass (RO.SOf 𝔪), wt h𝔪 Ψ s p * ((p.ht Q : ℝ) : ℂ) ^ s :=
    funext fun Q => eis_eq_tsum_pair h𝔪 Ψ s Q
  refine ⟨?_, fun Q => ?_⟩
  · rw [e]
    exact RF.smooth_tsum_ht_cpow (RO.SOf 𝔪) (wt h𝔪 Ψ s) ha hs
  · rw [e, RF.lap_tsum_ht_cpow (RO.SOf 𝔪) (wt h𝔪 Ψ s) ha hs Q, eis_eq_tsum_pair h𝔪 Ψ s Q]
    rfl

/-! ### WP-C5 without the hypothesis -/

end

end ArtinKP.GL
end

theorem solution.{u_1} : type_of% @ArtinKP.GL.eisEigen_of_two_lt_re_oai.{u_1} := @ArtinKP.GL.eisEigen_of_two_lt_re_oai.{u_1}
