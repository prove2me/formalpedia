-- Prove2me | solution 1 for ArtinKP.N2.zRes_congr
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:13:42.950869+00:00
-- url     : https://prove2.me/submissions/04836d3b-839a-472b-ba0f-afdcab82ae1f

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
import Theorems.Thm_ArtinKP_C5_differentiableOn_functional_resPart
import Theorems.Thm_ArtinKP_C5_exists_norm_hpart_le
import Theorems.Thm_ArtinKP_C5_exists_single
import Theorems.Thm_ArtinKP_C5_tendsto_ray_functional_resPart_theta
import Theorems.Thm_ArtinKP_GL_eisEigen_of_two_lt_re
import Theorems.Thm_ArtinKP_N_Acoef_eq
import Theorems.Thm_ArtinKP_N_cf_eis
import Theorems.Thm_ArtinKP_N_integral_box_theta_eq_of_tendsto_ray
import Theorems.Thm_ArtinKP_N2_mD_eq_of_le
import Theorems.Thm_ArtinKP_X_X_isPOU_pou
import Theorems.Thm_ArtinKP_X_X_tsum_indicator_box_le_boxMult

section
-- module Solutions.Artin.KP.X_H3
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulGinfX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatComplexH3 _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulGinfX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatComplexH3 _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instSMulInvariantMeasureGinfXVol _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatComplexH3Vol _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatXVol _root_.ArtinKP.X.instSigmaFiniteH3Vol _root_.ArtinKP.X.instSigmaFiniteXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
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

lemma X.continuous_ht : Continuous (X.ht : X F → ℝ) :=
  continuous_finsetProd _ fun w _ => X.continuous_v w

/-! ### Upper triangular elements, translations and the torus -/

end

end ArtinKP.X
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
-- module Solutions.Artin.KP.B1_Pairs
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma chart_v (y : Coord F) (w : InfinitePlace F) : (chart F y).v w = Real.exp (y w).2 := rfl

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Calc
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
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
-- module Solutions.Artin.KP.X_L2
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
attribute [-instance] _root_.ArtinKP.B1.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatSub _root_.ArtinKP.N.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
-- module Solutions.Artin.KP.X2_Core
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-! ### Invariance -/

/-! ### Local finiteness and averaging -/

/-! ### Unfolding -/

/-! ### Green's identity on the quotient -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.C5_Holo
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
-- module Solutions.Artin.KP.X2_Eigen
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
-- module Solutions.Artin.KP.C5_PE
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma contDiff_shift {g : ℝ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (ℓ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (shift g ℓ) :=
  hg.comp (contDiff_id.sub contDiff_const)

variable {F : Type*} [Field F] [NumberField F]

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

end

end ArtinKP.C5
end

section
-- module Solutions.Artin.KP.C5_Profile
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-! ### The profile of `h_s` -/

lemma contDiff_gS (s : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (gS s) :=
  contDiff_rt.mul (X.contDiff_cexp_mul s)

lemma vanishLow_gS (s : ℂ) : VanishLow (gS s) := fun τ h => by
  unfold gS
  rw [rt_low h, zero_mul]

lemma differentiable_gS (τ : ℝ) : Differentiable ℂ fun s : ℂ => gS s τ := by
  unfold gS
  fun_prop

/-! ### The eigenvalue and the profile of the source -/

end

end ArtinKP.C5
end

section
-- module Solutions.Artin.KP.C5_Series
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma differentiable_wt (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) (p : PairClass (RO.SOf 𝔪)) :
    Differentiable ℂ fun s : ℂ => wt h𝔪 Ψ s p := by
  unfold wt tildeC TSection.tilde
  set r : Row 𝔪 := ((RO.rowClassEquiv h𝔪).symm p).out
  have hn : ((r.norm : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr r.norm_pos.ne'
  exact (Ψ.holo r).mul (differentiable_id.const_cpow (Or.inl hn))

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

/-! ### The Eisenstein series on pair classes -/

/-! ### Invariance, regularity -/

/-- `h_s` is smooth, for every `s ∈ ℂ`. -/
theorem smooth_hpart (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) (s : ℂ) : X.Smooth (hpart Ψ s) := by
  rw [hpart_eq_pe h𝔪]
  exact smooth_pe _ (contDiff_gS s) (vanishLow_gS s)

/-! ### The source -/

/-- `s ↦ h_s(Q)` is entire. -/
theorem differentiable_hpart (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) (Q : X F) :
    Differentiable ℂ fun s : ℂ => hpart Ψ s Q := by
  obtain ⟨p₁, h⟩ := pe_single (RO.SOf 𝔪) Q
  have e : (fun s : ℂ => hpart Ψ s Q) =
      fun s => wt h𝔪 Ψ s p₁ * gS s (Real.log (p₁.ht Q)) := by
    funext s
    rw [hpart_eq_pe h𝔪, h _ _ (vanishLow_gS s)]
  rw [e]
  exact (differentiable_wt h𝔪 Ψ p₁).mul (differentiable_gS _)

end

end ArtinKP.C5
end

section
-- module Solutions.Artin.KP.C5_Main
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-C5, file 5: (C5), the continuation and the limit (C7)

`Γ ≤ SL₂(𝓞_F)` of finite index, `Ψ` a twisted section with `Inv Γ Ψ`, `hG : Good 𝔪`.

* `srcL2 Γ Ψ s = [F_s]`, `uL2 Γ Ψ s = [u_s]` in `X.L2 Γ` (total functions: `0` when the
  representative is not square integrable); `differentiable_srcL2`: `s ↦ [F_s]` is **entire**.
* `Omega = {s | λ(s) ∉ [0, ∞)} = {Re s ≠ 1} ∖ [0, 2]` (`lam_mem_resolventDomain_iff`),
  `slit_subset_Omega`.
* `resPart Γ Ψ s = −Res(λ(s)) [F_s]`; **(C5)** `uL2_eq_resPart : [u_s] = −Res(λ(s))[F_s]` for
  `Re s > 2` (given D1 = `EisEigen Ψ s`); `differentiableOn_resPart`: holomorphic on `Omega`.
* `Eext Γ Ψ s = h_s + lift (resPart Γ Ψ s)`: the continued series; `Eext_ae_eq`.
* **(C7)** `theta Γ Ψ = −c₀ • P_{λ₀}[F_{4/3}]`, `c₀ = 3/(2r)`, `λ₀ = 8r/9`;
  `tendsto_ray_resPart`: `(s_t − s₀) • resPart(s_t) → θ` along `s_t = 4/3 + t(1 + i)`;
  `exists_isWeakEigen_theta`, `inner_coreLap_theta`, `proj_theta`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter IsDedekindDomain

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C5

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.CAbs

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {ι : F →+* ℂ}

/-! ### The eigenvalue function -/

/-- The slit half-plane of `E_Model` lies in the resolvent region. -/
theorem slit_subset_Omega : E.slit ⊆ Omega := fun _ hs =>
  ⟨ne_of_gt hs.1, fun h0 => Or.inr (hs.2 h0)⟩

/-! ### The classes in `L²(Γ\X)` -/

/-! ### (C5) -/

/-! ### Continuation -/

/-! ### The limit (C7) -/

/-! ### `θ` is a weak eigenfunction -/

end

end ArtinKP.C5
end

section
-- module Solutions.Artin.KP.RF_Strip
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
attribute [-instance] _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma Cell.vol_ne_zero {D : Set (InfinitePlace F → ℂ)} {n₀ : ℕ} (h : Cell Γ D n₀) :
    volume D ≠ 0 :=
  h.fund.measure_ne_zero (NeZero.ne _)

/-- Every subgroup of finite index has a cell. -/
theorem exists_cell (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex] :
    ∃ (D : Set (InfinitePlace F → ℂ)) (n₀ : ℕ), Cell Γ D n₀ := by
  obtain ⟨D, hD, hb, hfund⟩ := exists_fundamental_translations Γ (exists_ideal_translations Γ)
  obtain ⟨R, hR⟩ := hb.exists_norm_le
  obtain ⟨N, hN⟩ := exists_nat_ge R
  exact ⟨D, N, Cell.of_hfund hD hfund fun x hx w =>
    (norm_le_pi_norm x w).trans ((hR x hx).trans hN)⟩

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

/-! ### Fubini: a function with vanishing `x`-integrals over `D` is killed by `cf` -/

/-! ### The shape -/

lemma isCompact_box (n : ℕ) : IsCompact (X.box n : Set (X F)) :=
  isCompact_siegelBox (F := F) (m := 1 / ((n : ℝ) + 1)) (M := (n : ℝ) + 1) (B := n)
    (by positivity)

lemma continuous_htC (s : ℂ) : Continuous (htC s : X F → ℂ) := by
  unfold htC
  refine (Complex.continuous_ofReal.comp X.continuous_ht).cpow continuous_const fun P => ?_
  exact Or.inl (by simpa using X.ht_pos P)

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.N_Cont
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma isOpen_slit : IsOpen E.slit := by
  have h : E.slit = {s : ℂ | 1 < s.re} ∩ ({s : ℂ | s.im ≠ 0} ∪ {s : ℂ | 2 < s.re}) := by
    ext s
    simp only [E.slit, mem_ofPred_eq, mem_inter_iff, mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by by_cases h : s.im = 0; exacts [Or.inr (h2 h), Or.inl h]⟩
    · rintro ⟨h1, h2 | h2⟩
      · exact ⟨h1, fun h => absurd h h2⟩
      · exact ⟨h1, fun _ => h2⟩
  rw [h]
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_ne_fun Complex.continuous_im continuous_const).union
      (isOpen_lt continuous_const Complex.continuous_re))

lemma ray_mem_slit {t : ℝ} (ht : 0 < t) : ray t ∈ E.slit := by
  have hre : (ray t).re = 4 / 3 + t := by
    simp only [ray, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.I_re, Complex.div_ofNat_re, Complex.re_ofNat]
    ring
  have him : (ray t).im = t := by
    simp only [ray, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_im, Complex.I_im, Complex.div_ofNat_im, Complex.im_ofNat]
    ring
  exact ⟨by rw [hre]; linarith, fun h => by rw [him] at h; exact absurd h ht.ne'⟩

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

theorem differentiable_hInt (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) (n : ℕ) {ψ : X F → ℂ}
    (hψ : Measurable ψ) {C : ℝ} (hC : ∀ P, ‖ψ P‖ ≤ C) : Differentiable ℂ (hInt Ψ n ψ) := by
  intro s₀
  obtain ⟨Ch, hCh0, hCh⟩ := exists_norm_hpart_le h𝔪 Ψ (‖s₀‖ + 1) (isCompact_box (F := F) n)
  refine differentiableAt_setIntegral (X.measurableSet_box n) (X.vol_box_lt_top n).ne
    (R := 1) (B₀ := C * Ch) one_pos
    (fun s _ => (Complex.continuous_conj.measurable.comp hψ).mul
      (smooth_hpart h𝔪 Ψ s).continuous.measurable)
    (fun P _ => ((differentiable_hpart h𝔪 Ψ P).const_mul _).differentiableOn)
    (fun s hs P hP => ?_)
  rw [norm_mul, RCLike.norm_conj]
  have hs' : ‖s‖ ≤ ‖s₀‖ + 1 := by
    have h1 : ‖s - s₀‖ < 1 := mem_ball_iff_norm.mp hs
    have h2 : ‖s‖ ≤ ‖s₀‖ + ‖s - s₀‖ := by
      calc ‖s‖ = ‖s₀ + (s - s₀)‖ := by rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    linarith
  exact mul_le_mul (hC P) (hCh s hs' P hP) (norm_nonneg _) ((norm_nonneg _).trans (hC P))

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
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap _root_.ArtinKP.S2.cubicSymbol_sym
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

include hG hΓ in
theorem differentiableOn_Acoef (hDm : MeasurableSet D) (n : ℕ) (hφ : Measurable φ)
    (hφ1 : ∀ v, ‖φ v‖ ≤ 1) : DifferentiableOn ℂ (Acoef Γ Ψ D n φ) E.slit := by
  have h1 : DifferentiableOn ℂ (fun s => cf D n φ (X.lift Γ (resPart Γ Ψ s))) E.slit := by
    have := (differentiableOn_functional_resPart hG Γ hΓ (X.coeffFunctional Γ n (stripFn D 0 φ)
      (measurable_stripFn hDm 0 hφ) 1 (norm_stripFn_le D 0 hφ1))).mono slit_subset_Omega
    exact this.congr fun s _ => (coeffFunctional_eq_cf hDm n hφ hφ1 _).symm
  have h2 := (differentiable_hInt hG.ne_bot Ψ n (measurable_stripFn hDm 0 hφ)
    (norm_stripFn_le D 0 hφ1)).differentiableOn (s := E.slit)
  have h3 : DifferentiableOn ℂ (fun s => Ψ s (Row.inf 𝔪) * cf D n φ (htC s)) E.slit :=
    ((Ψ.holo _).mul (differentiable_cf_htC hDm n hφ hφ1)).differentiableOn
  exact (h1.add h2).sub h3

include hG hΓ hE in
/-- **The cross identity on `E.slit`** (MATH2 §2.1(c)). -/
theorem Acoef_cross (hD : Cell Γ D n) (hφ : Measurable φ) (hφ1 : ∀ v, ‖φ v‖ ≤ 1)
    (hD' : Cell Γ D n') (hφ' : Measurable φ') (hφ1' : ∀ v, ‖φ' v‖ ≤ 1) {s : ℂ}
    (hs : s ∈ E.slit) :
    Acoef Γ Ψ D n φ s * cf D n' φ' (htC (2 - s))
      = Acoef Γ Ψ D n' φ' s * cf D n φ (htC (2 - s)) := by
  have hP : Differentiable ℂ fun s : ℂ => cf D n φ (htC (2 - s)) :=
    (differentiable_cf_htC hD.meas n hφ hφ1).comp ((differentiable_const (2 : ℂ)).sub
      differentiable_id)
  have hP' : Differentiable ℂ fun s : ℂ => cf D n' φ' (htC (2 - s)) :=
    (differentiable_cf_htC hD'.meas n' hφ' hφ1').comp ((differentiable_const (2 : ℂ)).sub
      differentiable_id)
  have hl : DifferentiableOn ℂ (fun s => Acoef Γ Ψ D n φ s * cf D n' φ' (htC (2 - s))) E.slit :=
    (differentiableOn_Acoef hG hΓ hD.meas n hφ hφ1).mul hP'.differentiableOn
  have hr : DifferentiableOn ℂ (fun s => Acoef Γ Ψ D n' φ' s * cf D n φ (htC (2 - s))) E.slit :=
    (differentiableOn_Acoef hG hΓ hD'.meas n' hφ' hφ1').mul hP.differentiableOn
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ) (z₀ := (3 : ℂ))
    (hl.analyticOnNhd isOpen_slit) (hr.analyticOnNhd isOpen_slit)
    E.isPreconnected_slit ⟨by norm_num, fun _ => by norm_num⟩ ?_ hs
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show (2 : ℝ) < (3 : ℂ).re by norm_num)] with s hs
  have hs' : 2 < s.re := hs
  simp only [Acoef_eq hG hΓ hD hφ hφ1 hs' (hE s hs'),
    Acoef_eq hG hΓ hD' hφ' hφ1' hs' (hE s hs')]
  ring

/-! ### The continued coefficient and its residue -/

include hG hΓ hE in
/-- **The shape of the constant term of the continuation**: on `E.slit`,
`cf(Eext) − Ψ_s(0,1) cf(ht^s) = mext(s) · cf(ht^{2−s})` for every test pair. -/
theorem Acoef_eq_mext (hD : Cell Γ D n) (hn : 1 ≤ n) (hD' : Cell Γ D n') (hφ' : Measurable φ')
    (hφ1' : ∀ v, ‖φ' v‖ ≤ 1) {s : ℂ} (hs : s ∈ E.slit) :
    Acoef Γ Ψ D n' φ' s = mext Γ Ψ D n s * cf D n' φ' (htC (2 - s)) := by
  have h := Acoef_cross hG hΓ hE hD (measurable_phase (2 - s)) (norm_phase_le (2 - s)) hD' hφ'
    hφ1' hs
  unfold mext
  rw [div_mul_eq_mul_div, eq_div_iff (cf_phase_ne_zero hD hn (2 - s))]
  exact h.symm

include hG hΓ in
theorem mext_eq_mD (hD : Cell Γ D n) (hn : 1 ≤ n) {s : ℂ} (hs : 2 < s.re)
    (hEs : EisEigen Ψ s) : mext Γ Ψ D n s = mD D Ψ s := by
  unfold mext
  rw [Acoef_eq hG hΓ hD (measurable_phase (2 - s)) (norm_phase_le (2 - s)) hs hEs,
    mul_div_assoc, div_self (cf_phase_ne_zero hD hn (2 - s)), mul_one]

include hG hΓ hE in
theorem differentiableOn_mext (hD : Cell Γ D n) (hn : 1 ≤ n) :
    DifferentiableOn ℂ (mext Γ Ψ D n) E.slit := by
  intro s₁ hs₁
  refine DifferentiableAt.differentiableWithinAt ?_
  set φ₁ : (InfinitePlace F → ℝ) → ℂ := phase (2 - s₁) with hφ₁
  have hP : Differentiable ℂ fun s : ℂ => cf D n φ₁ (htC (2 - s)) :=
    (differentiable_cf_htC hD.meas n (measurable_phase _) (norm_phase_le _)).comp
      ((differentiable_const (2 : ℂ)).sub differentiable_id)
  have hne : ∀ᶠ s in 𝓝 s₁, cf D n φ₁ (htC (2 - s)) ≠ 0 :=
    hP.continuous.continuousAt.eventually_ne (cf_phase_ne_zero hD hn (2 - s₁))
  have heq : mext Γ Ψ D n =ᶠ[𝓝 s₁]
      fun s => Acoef Γ Ψ D n φ₁ s / cf D n φ₁ (htC (2 - s)) := by
    filter_upwards [hne, isOpen_slit.mem_nhds hs₁] with s hs hslit
    rw [eq_div_iff hs]
    exact (Acoef_eq_mext hG hΓ hE hD hn hD (measurable_phase _) (norm_phase_le _) hslit).symm
  have hA := (differentiableOn_Acoef hG hΓ hD.meas n (measurable_phase (2 - s₁))
    (norm_phase_le (2 - s₁)) s₁ hs₁).differentiableAt (isOpen_slit.mem_nhds hs₁)
  exact (hA.div (hP s₁) (cf_phase_ne_zero hD hn (2 - s₁))).congr_of_eventuallyEq heq

include hG hΓ in
theorem tendsto_ray_Acoef (hDm : MeasurableSet D) (n : ℕ) (hφ : Measurable φ)
    (hφ1 : ∀ v, ‖φ v‖ ≤ 1) :
    Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) * Acoef Γ Ψ D n φ (ray t)) (𝓝[>] 0)
      (𝓝 (cf D n φ (X.lift Γ (theta Γ Ψ)))) := by
  have h1 := tendsto_ray_functional_resPart_theta hG Γ hΓ (X.coeffFunctional Γ n (stripFn D 0 φ)
    (measurable_stripFn hDm 0 hφ) 1 (norm_stripFn_le D 0 hφ1))
  have h2 := tendsto_ray_mul_zero (g := hInt Ψ n (stripFn D 0 φ))
    (differentiable_hInt hG.ne_bot Ψ n (measurable_stripFn hDm 0 hφ)
      (norm_stripFn_le D 0 hφ1)).continuous.continuousAt
  have h3 := tendsto_ray_mul_zero (g := fun s => Ψ s (Row.inf 𝔪) * cf D n φ (htC s))
    ((Ψ.holo _).mul (differentiable_cf_htC hDm n hφ hφ1)).continuous.continuousAt
  have h4 := (h1.add h2).sub h3
  rw [add_zero, sub_zero, coeffFunctional_eq_cf hDm n hφ hφ1] at h4
  refine h4.congr fun t => ?_
  simp only [coeffFunctional_eq_cf hDm n hφ hφ1, Acoef, ray]
  ring

include hG hΓ hE in
/-- `(s_t − s₀)·mext(s_t) → zRes` along the ray. -/
theorem tendsto_ray_mext (hD : Cell Γ D n) (hn : 1 ≤ n) :
    Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) * mext Γ Ψ D n (ray t)) (𝓝[>] 0)
      (𝓝 (zRes Γ Ψ D n)) := by
  set φ₁ : (InfinitePlace F → ℝ) → ℂ := phase (2 / 3) with hφ₁
  have hP : Differentiable ℂ fun s : ℂ => cf D n φ₁ (htC (2 - s)) :=
    (differentiable_cf_htC hD.meas n (measurable_phase _) (norm_phase_le _)).comp
      ((differentiable_const (2 : ℂ)).sub differentiable_id)
  have hPt : Tendsto (fun t : ℝ => cf D n φ₁ (htC (2 - ray t))) (𝓝[>] 0)
      (𝓝 (cf D n φ₁ (htC (2 / 3)))) := by
    have h := (hP.continuous.tendsto (4 / 3)).comp tendsto_ray
    have e : (2 : ℂ) - 4 / 3 = 2 / 3 := by norm_num
    rw [e] at h
    exact h
  have hne := cf_phase_ne_zero hD hn (2 / 3 : ℂ)
  have hA := tendsto_ray_Acoef hG hΓ hD.meas n (measurable_phase (2 / 3))
    (norm_phase_le (2 / 3))
  have hdiv := hA.div hPt hne
  refine hdiv.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hPt.eventually_ne hne] with t ht hnt
  simp only [Pi.div_apply]
  rw [Acoef_eq_mext hG hΓ hE hD hn hD (measurable_phase _) (norm_phase_le _) (ray_mem_slit ht)]
  field_simp
  rfl

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

end

/-! ### `‖θ‖² = −c₀⟪F, θ⟫` -/

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.N2_Lattice
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ}

/-! ### Strict cells -/

/-! ### Periodicity of the tail -/

/-! ### Independence of `mD` -/

/-- **`mD` does not depend on the cell nor on the group** (`Re s > 2`). -/
theorem mD_congr (h𝔪 : 𝔪 ≠ ⊥) {Γ₁ Γ₂ : Subgroup (SL(2, 𝓞 F))} [Γ₁.FiniteIndex]
    [Γ₂.FiniteIndex] {Ψ : TSection ι 𝔪} (hΓ₁ : Inv Γ₁ Ψ) (hΓ₂ : Inv Γ₂ Ψ) {s : ℂ}
    (hs : 2 < s.re) {D₁ D₂ : Set (InfinitePlace F → ℂ)} {n₁ n₂ : ℕ} (hD₁ : Cell Γ₁ D₁ n₁)
    (hD₂ : Cell Γ₂ D₂ n₂) : mD D₁ Ψ s = mD D₂ Ψ s := by
  obtain ⟨E₁, m₁, hE₁, hf₁, -, -, hc₁⟩ := exists_strict_cell Γ₁
  obtain ⟨E₂, m₂, hE₂, hf₂, -, -, hc₂⟩ := exists_strict_cell Γ₂
  obtain ⟨E₃, m₃, hc₃⟩ := exists_cell (Γ₁ ⊓ Γ₂)
  rw [mD_eq_of_le h𝔪 hΓ₁ le_rfl hs hE₁ hf₁ hc₁ hD₁,
    ← mD_eq_of_le h𝔪 hΓ₁ inf_le_left hs hE₁ hf₁ hc₁ hc₃,
    mD_eq_of_le h𝔪 hΓ₂ inf_le_right hs hE₂ hf₂ hc₂ hc₃,
    ← mD_eq_of_le h𝔪 hΓ₂ le_rfl hs hE₂ hf₂ hc₂ hD₂]

/-! ### Independence of `zRes` -/

/-- **`zRes Γ Ψ D n` does not depend on `(Γ, D, n)`.** -/
theorem zRes_congr_oai (hG : Good 𝔪) {Γ₁ Γ₂ : Subgroup (SL(2, 𝓞 F))} [Γ₁.FiniteIndex]
    [Γ₂.FiniteIndex] {Ψ : TSection ι 𝔪} (hΓ₁ : Inv Γ₁ Ψ) (hΓ₂ : Inv Γ₂ Ψ)
    {D₁ D₂ : Set (InfinitePlace F → ℂ)} {n₁ n₂ : ℕ} (hD₁ : Cell Γ₁ D₁ n₁) (hn₁ : 1 ≤ n₁)
    (hD₂ : Cell Γ₂ D₂ n₂) (hn₂ : 1 ≤ n₂) : zRes Γ₁ Ψ D₁ n₁ = zRes Γ₂ Ψ D₂ n₂ := by
  have hE : ∀ s : ℂ, 2 < s.re → EisEigen Ψ s := fun s hs => GL.eisEigen_of_two_lt_re hG.ne_bot Ψ hs
  exact zRes_eq_of_continuation hG hΓ₁ hE hD₁ hn₁ (differentiableOn_mext hG hΓ₂ hE hD₂ hn₂)
    (fun s hs => (mext_eq_mD hG hΓ₂ hD₂ hn₂ hs (hE s hs)).trans
      (mD_congr hG.ne_bot hΓ₁ hΓ₂ hs hD₁ hD₂).symm)
    (tendsto_ray_mext hG hΓ₂ hE hD₂ hn₂)

end

end ArtinKP.N2
end

theorem solution.{u_1} : type_of% @ArtinKP.N2.zRes_congr_oai.{u_1} := @ArtinKP.N2.zRes_congr_oai.{u_1}
