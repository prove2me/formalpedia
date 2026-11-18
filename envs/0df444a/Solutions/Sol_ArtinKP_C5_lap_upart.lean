-- Prove2me | solution 1 for ArtinKP.C5.lap_upart
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:42:49.470524+00:00
-- url     : https://prove2.me/submissions/4f1c3a2c-9dc7-4b9e-ac21-f1878a3a2f23

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
import Theorems.Thm_ArtinKP_C5_exists_single

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
-- module Solutions.Artin.KP.B1_Pairs
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
attribute [-simp] _root_.ArtinKP.RO.rowPair_c _root_.ArtinKP.RO.rowPair_d
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

/-! ### Lemma M for pair classes -/

end

end ArtinKP.B1
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

lemma pd_congr {U W : Coord F → ℂ} {y : Coord F} (h : U =ᶠ[nhds y] W)
    (w : InfinitePlace F) (k : Fin 3) : pd w k U =ᶠ[nhds y] pd w k W := by
  filter_upwards [h.eventually_nhds] with z hz
  unfold pd
  rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hz]

lemma lapE_congr {U W : Coord F → ℂ} {y : Coord F} (h : U =ᶠ[nhds y] W) :
    lapE U y = lapE W y := by
  unfold lapE
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [(pd_congr (pd_congr h w k) w k).self_of_nhds]
  · rw [(pd_congr h w 2).self_of_nhds]

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

lemma X.Smooth.comp_Ginf {u : X F → ℂ} (hu : X.Smooth u) (g : Ginf F) :
    X.Smooth fun P => u (g • P) := by
  unfold X.Smooth
  have : (fun y => u (g • chart F y)) = fun y => (fun z => u (chart F z)) (actE g y) := by
    funext y; simp only [chart_actE]
  rw [this]
  have hu' : ContDiff ℝ (⊤ : ℕ∞) fun y => u (chart F y) := hu
  exact hu'.comp (isoHalf_actE g).smooth

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

lemma eventuallyEq_chart {β : Type*} {u w : X F → β} {P : X F} (h : u =ᶠ[𝓝 P] w) :
    (fun y => u (chart F y)) =ᶠ[𝓝 ((chart F).symm P)] fun y => w (chart F y) := by
  have ht : Tendsto (chart F) (𝓝 ((chart F).symm P)) (𝓝 P) := by
    have := (chart F).continuous.continuousAt (x := (chart F).symm P)
    rwa [ContinuousAt, Homeomorph.apply_symm_apply] at this
  exact ht.eventually h

lemma X.lap_congr {u w : X F → ℂ} {P : X F} (h : u =ᶠ[𝓝 P] w) : X.lap u P = X.lap w P :=
  lapE_congr (eventuallyEq_chart h)

/-! ### Invariance -/

/-! ### Local finiteness and averaging -/

/-! ### Unfolding -/

/-! ### Green's identity on the quotient -/

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

/-- A smooth function of the logarithm of a pair height is smooth. -/
theorem X.smooth_comp_log_pairHt {G : ℝ → ℂ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) {c d : F}
    (h : c ≠ 0 ∨ d ≠ 0) : X.Smooth fun P : X F => G (Real.log (X.pairHt c d P)) := by
  obtain ⟨γ, rfl, rfl⟩ := exists_bottom_row h
  simp_rw [← X.ht_smul]
  exact (X.smooth_comp_log_ht hG).comp_Ginf (sigma F γ)

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

lemma contDiff_cexp_mul (s : ℂ) : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => Complex.exp (s * (t : ℂ)) :=
  Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.C5_PE
attribute [-simp] _root_.ArtinKP.RO.rowClassEquiv_mk
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

lemma contDiff_shift {g : ℝ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (ℓ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (shift g ℓ) :=
  hg.comp (contDiff_id.sub contDiff_const)

lemma deriv_shift (g : ℝ → ℂ) (ℓ : ℝ) : deriv (shift g ℓ) = shift (deriv g) ℓ := by
  funext τ
  exact deriv_comp_sub_const g ℓ τ

variable {F : Type*} [Field F] [NumberField F]

lemma VanishLow.Lg {g : ℝ → ℂ} (hg : VanishLow g) : VanishLow (Lg F g) := by
  intro τ hτ
  unfold C5.Lg
  rw [hg.deriv.deriv τ hτ, hg.deriv τ hτ]
  simp

lemma Lg_shift (g : ℝ → ℂ) (ℓ τ : ℝ) : Lg F (shift g ℓ) τ = Lg F g (τ - ℓ) := by
  unfold Lg
  rw [deriv_shift, deriv_shift]
  rfl

variable [IsTotallyComplex F] {S : Finset (FinitePlace F)}

/-! ### Locally a single term -/

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

lemma pe_single (S : Finset (FinitePlace F)) (P : X F) :
    ∃ p₁ : PairClass S, ∀ (a : PairClass S → ℂ) (g : ℝ → ℂ), VanishLow g →
      pe S a g P = a p₁ * g (Real.log (p₁.ht P)) := by
  obtain ⟨p₁, h⟩ := pe_eventually S P
  exact ⟨p₁, h.self_of_nhds⟩

/-! ### Algebra -/

lemma pe_lin_profile (a : PairClass S → ℂ) {g₁ g₂ : ℝ → ℂ} (h₁ : VanishLow g₁)
    (h₂ : VanishLow g₂) (c : ℂ) (P : X F) :
    pe S a (fun τ => c * g₁ τ + g₂ τ) P = c * pe S a g₁ P + pe S a g₂ P := by
  obtain ⟨p₁, h⟩ := pe_single S P
  have h₃ : VanishLow fun τ => c * g₁ τ + g₂ τ := fun τ hτ => by
    simp [h₁ τ hτ, h₂ τ hτ]
  rw [h a _ h₃, h a _ h₁, h a _ h₂]
  ring

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

/-- **`Δ (pe a g) = pe a (r(−g'' + 2g'))`.** -/
theorem lap_pe (a : PairClass S → ℂ) {g : ℝ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hv : VanishLow g) (P : X F) : X.lap (pe S a g) P = pe S a (Lg F g) P := by
  obtain ⟨p₁, h1, h⟩ := pe_eventuallyEq S a hv P
  rw [X.lap_congr h, h1 a _ hv.Lg,
    X.lap_const_mul (X.smooth_comp_log_pairHt (contDiff_shift hg _) p₁.out.ne_zero),
    X.lap_comp_log_pairHt (contDiff_shift hg _) p₁.out.ne_zero, term_eq_shift (Lg F g)]
  congr 1
  have := Lg_shift (F := F) g (Real.log (X.sNorm S p₁.out.c p₁.out.d))
    (Real.log (X.pairHt p₁.out.c p₁.out.d P))
  unfold Lg at this
  unfold shift Lg
  exact this

/-! ### Support -/

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

lemma contDiff_rho : ContDiff ℝ (⊤ : ℕ∞) rho :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

lemma contDiff_rt : ContDiff ℝ (⊤ : ℕ∞) rt :=
  Complex.ofRealCLM.contDiff.comp (contDiff_rho.comp Real.contDiff_exp)

lemma rt_low {τ : ℝ} (h : τ < Real.log 2) : rt τ = 0 := by
  unfold rt
  rw [rho_zero ((Real.lt_log_iff_exp_lt (by norm_num)).mp h).le]
  simp

lemma contDiff_rt1 : ContDiff ℝ (⊤ : ℕ∞) rt1 := by
  have h : ContDiff ℝ ((⊤ : ℕ∞) + 1) rt := contDiff_rt
  exact (contDiff_succ_iff_deriv.1 h).2.2

lemma hasDerivAt_rt (τ : ℝ) : HasDerivAt rt (rt1 τ) τ :=
  ((contDiff_rt.differentiable (by simp)) τ).hasDerivAt

lemma hasDerivAt_rt1 (τ : ℝ) : HasDerivAt rt1 (rt2 τ) τ :=
  ((contDiff_rt1.differentiable (by simp)) τ).hasDerivAt

lemma vanishLow_rt : VanishLow rt := fun _ h => rt_low h

lemma vanishLow_rt1 : VanishLow rt1 := vanishLow_rt.deriv

lemma vanishLow_rt2 : VanishLow rt2 := vanishLow_rt1.deriv

/-! ### The profile of `h_s` -/

lemma contDiff_gS (s : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (gS s) :=
  contDiff_rt.mul (X.contDiff_cexp_mul s)

lemma vanishLow_gS (s : ℂ) : VanishLow (gS s) := fun τ h => by
  unfold gS
  rw [rt_low h, zero_mul]

lemma hasDerivAt_cexp_mul (s : ℂ) (τ : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (s * (t : ℂ))) (Complex.exp (s * (τ : ℂ)) * s) τ := by
  have h1 : HasDerivAt (fun t : ℝ => s * (t : ℂ)) s τ := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := τ)).const_mul s
  exact h1.cexp

lemma deriv_gS (s : ℂ) :
    deriv (gS s) = fun τ : ℝ => rt1 τ * Complex.exp (s * (τ : ℂ)) +
      rt τ * (Complex.exp (s * (τ : ℂ)) * s) := by
  funext τ
  exact ((hasDerivAt_rt τ).mul (hasDerivAt_cexp_mul s τ)).deriv

lemma deriv_deriv_gS (s : ℂ) (τ : ℝ) :
    deriv (deriv (gS s)) τ = rt2 τ * Complex.exp (s * (τ : ℂ)) +
      rt1 τ * (Complex.exp (s * (τ : ℂ)) * s) +
      (rt1 τ * (Complex.exp (s * (τ : ℂ)) * s) + rt τ * (Complex.exp (s * (τ : ℂ)) * s * s)) := by
  rw [deriv_gS]
  exact (((hasDerivAt_rt1 τ).mul (hasDerivAt_cexp_mul s τ)).add
    ((hasDerivAt_rt τ).mul ((hasDerivAt_cexp_mul s τ).mul_const s))).deriv

variable {F : Type*} [Field F] [NumberField F]

/-! ### The eigenvalue and the profile of the source -/

/-- **`L (gS s) = λ(s) · gS s + φ_s`.** -/
lemma Lg_gS (s : ℂ) (τ : ℝ) : Lg F (gS s) τ = lam F s * gS s τ + phiS F s τ := by
  unfold Lg
  rw [deriv_deriv_gS, deriv_gS]
  unfold lam phiS gS
  ring

lemma vanishLow_phiS (s : ℂ) : VanishLow (phiS F s) := fun τ h => by
  unfold phiS
  rw [vanishLow_rt1 τ h, vanishLow_rt2 τ h]
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

lemma hpart_eq_pe (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) (s : ℂ) :
    hpart Ψ s = pe (RO.SOf 𝔪) (wt h𝔪 Ψ s) (gS s) :=
  funext fun Q => tsum_eq_pe h𝔪 Ψ s (gS s) Q

lemma src_eq_pe (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) (s : ℂ) :
    src Ψ s = pe (RO.SOf 𝔪) (wt h𝔪 Ψ s) (phiS F s) :=
  funext fun Q => tsum_eq_pe h𝔪 Ψ s (phiS F s) Q

/-! ### The Eisenstein series on pair classes -/

/-! ### Invariance, regularity -/

/-- `h_s` is smooth, for every `s ∈ ℂ`. -/
theorem smooth_hpart (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) (s : ℂ) : X.Smooth (hpart Ψ s) := by
  rw [hpart_eq_pe h𝔪]
  exact smooth_pe _ (contDiff_gS s) (vanishLow_gS s)

/-- **`Δ h_s = λ(s) h_s + F_s`**, for every `s ∈ ℂ`. -/
theorem lap_hpart (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) (s : ℂ) (Q : X F) :
    X.lap (hpart Ψ s) Q = lam F s * hpart Ψ s Q + src Ψ s Q := by
  rw [hpart_eq_pe h𝔪, src_eq_pe h𝔪, lap_pe _ (contDiff_gS s) (vanishLow_gS s)]
  have : Lg F (gS s) = fun τ => lam F s * gS s τ + phiS F s τ := funext fun τ => Lg_gS s τ
  rw [this, pe_lin_profile _ (vanishLow_gS s) (vanishLow_phiS s)]

/-- **`(Δ − λ(s)) u_s = −F_s`** pointwise (given D1). -/
theorem lap_upart_oai (h𝔪 : 𝔪 ≠ ⊥) {Ψ : TSection ι 𝔪} {s : ℂ} (hD : EisEigen Ψ s) (Q : X F) :
    X.lap (upart Ψ s) Q = lam F s * upart Ψ s Q + -src Ψ s Q := by
  have hh := smooth_hpart h𝔪 Ψ s
  have e : upart Ψ s = fun Q => eis Ψ s Q + (-1 : ℂ) * hpart Ψ s Q := by
    funext Q; unfold upart; ring
  rw [e, X.lap_add hD.1 (hh.const_mul _), X.lap_const_mul hh, hD.2, lap_hpart h𝔪]
  ring

/-! ### The source -/

end

end ArtinKP.C5
end

theorem solution.{u_1} : type_of% @ArtinKP.C5.lap_upart_oai.{u_1} := @ArtinKP.C5.lap_upart_oai.{u_1}
