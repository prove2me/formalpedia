-- Prove2me | solution 1 for ArtinKP.N2.orbit_integral_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:13:40.693237+00:00
-- url     : https://prove2.me/submissions/42c353c1-926c-4cb4-a902-5dba1f3438a0

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
import Theorems.Thm_ArtinKP_C5_exists_single
import Theorems.Thm_ArtinKP_N2_cusp_integral_eq_zero
import Theorems.Thm_ArtinKP_N2_lintegral_lift_pou_ne_top
import Theorems.Thm_ArtinKP_X_X_isPOU_pou

section
-- module Solutions.Artin.KP.X_Quot
attribute [-instance] _root_.ArtinKP.B1.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatSub _root_.ArtinKP.N.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinKP.X.instMeasurableConstSMulGinfX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instSMulInvariantMeasureGinfXVol _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma quotProdEquiv_apply (H : Subgroup G) (p : (G ⧸ H) × H) :
    quotProdEquiv H p = p.1.out * (p.2 : G) := rfl

theorem isPOU_pouRestrict (H : Subgroup G) {η : α → ℝ≥0∞} (hη : IsPOU G η) :
    IsPOU H (pouRestrict H η) := by
  haveI _iCQ := instCountableQuot H
  refine ⟨Measurable.ennreal_tsum fun q => hη.measurable.comp (measurable_const_smul _), ?_⟩
  intro a
  unfold pouRestrict
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_prod (f := fun (q : G ⧸ H) (h : H) => η (q.out • h • a)),
    ← hη.tsum_eq a, ← (quotProdEquiv H).tsum_eq]
  refine tsum_congr fun p => ?_
  rw [quotProdEquiv_apply, mul_smul]
  rfl

/-- **Unfolding** (nonnegative form):
`∫_{G\α} (Σ_{γ ∈ H\G} f(γ a)) u(a) = ∫_{H\α} f(a) u(a)` for `f` `H`-invariant and `u`
`G`-invariant, the two quotient integrals being computed with any partitions of unity. -/
theorem lintegral_autom_mul_eq (H : Subgroup G) {η ηH : α → ℝ≥0∞} (hη : IsPOU G η)
    (hηH : IsPOU H ηH) {f u : α → ℝ≥0∞} (hf : Measurable f) (hu : Measurable u)
    (hfinv : ∀ (h : H) (a : α), f (h • a) = f a) (huinv : ∀ (g : G) (a : α), u (g • a) = u a) :
    ∫⁻ a, autom H f a * u a * η a ∂μ = ∫⁻ a, f a * u a * ηH a ∂μ := by
  haveI _iCQ := instCountableQuot H
  have hm : ∀ g : G, Measurable fun a : α => g • a := fun g => measurable_const_smul g
  calc ∫⁻ a, autom H f a * u a * η a ∂μ
      = ∑' q : G ⧸ H, ∫⁻ a, f (q.out⁻¹ • a) * u a * η a ∂μ := by
        unfold autom
        simp_rw [← ENNReal.tsum_mul_right]
        exact lintegral_tsum fun q =>
          (((hf.comp (hm _)).mul hu).mul hη.measurable).aemeasurable
    _ = ∑' q : G ⧸ H, ∫⁻ a, f a * u a * η (q.out • a) ∂μ := by
        refine tsum_congr fun q => ?_
        have hF : Measurable fun a => f (q.out⁻¹ • a) * u a * η a :=
          ((hf.comp (hm _)).mul hu).mul hη.measurable
        rw [← lintegral_comp_smul (μ := μ) q.out hF]
        refine lintegral_congr fun a => ?_
        simp [huinv]
    _ = ∫⁻ a, f a * u a * pouRestrict H η a ∂μ := by
        unfold pouRestrict
        simp_rw [← ENNReal.tsum_mul_left]
        exact (lintegral_tsum fun q =>
          ((hf.mul hu).mul (hη.measurable.comp (hm _))).aemeasurable).symm
    _ = ∫⁻ a, f a * u a * ηH a ∂μ := by
        have hfu : Measurable fun a => f a * u a := hf.mul hu
        exact lintegral_mul_pou_eq (G := H) (isPOU_pouRestrict H hη) hηH hfu
          (fun h a => by
            change f (h • a) * u ((h : G) • a) = _
            rw [hfinv, huinv])

/-! ### Multiplicity and existence of partitions of unity -/

end

end ArtinKP.X
end

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

open H3

lemma smul_def (g : SL(2, ℂ)) (P : H3) : g • P = mob g P := rfl

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

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Discrete
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-! ### Lemma M for pair classes -/

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.B1_Cusp
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma liftQ_smul (u : Lp ℂ 2 (quotMeasure G η μ)) (g : G) (a : α) :
    liftQ u (g • a) = liftQ u a := by
  unfold liftQ; rw [mk_smul]

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Fourier
attribute [-instance] _root_.ArtinKP.B1.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatSub _root_.ArtinKP.N.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma X.lift_smul (Γ : Subgroup (SL(2, 𝓞 F))) (u : X.L2 Γ) (γ : Γ) (P : X F) :
    X.lift Γ u (γ • P) = X.lift Γ u P :=
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  liftQ_smul u γ P

lemma X.stronglyMeasurable_lift (Γ : Subgroup (SL(2, 𝓞 F))) (u : X.L2 Γ) :
    StronglyMeasurable (X.lift Γ u) :=
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  stronglyMeasurable_liftQ u

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_QuotC
attribute [-instance] _root_.ArtinKP.B1.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatSub _root_.ArtinKP.N.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinKP.X.instMeasurableConstSMulGinfX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instSMulInvariantMeasureGinfXVol _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-X, file 8: unfolding for complex-valued functions (absolutely convergent case)

Complex versions of the Tonelli lemmas of `X_Quot`, under an absolute-integrability hypothesis
stated as finiteness of a lower integral.  Weights are the real numbers `(η a).toReal`.
-/

open scoped ENNReal
open MeasureTheory Set

set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]
  [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]

lemma IsPOU.le_one {η : α → ℝ≥0∞} (hη : IsPOU G η) (a : α) : η a ≤ 1 := by
  have h := ENNReal.le_tsum (f := fun g : G => η (g • a)) 1
  rwa [one_smul, hη.tsum_eq] at h

lemma IsPOU.ne_top {η : α → ℝ≥0∞} (hη : IsPOU G η) (a : α) : η a ≠ ⊤ :=
  ((hη.le_one a).trans_lt ENNReal.one_lt_top).ne

lemma IsPOU.enorm_toReal {η : α → ℝ≥0∞} (hη : IsPOU G η) (a : α) :
    ‖(((η a).toReal : ℝ) : ℂ)‖ₑ = η a := by
  rw [← ofReal_norm, Complex.norm_real, ofReal_norm]
  exact Real.enorm_toReal (hη.ne_top a)

lemma IsPOU.tsum_toReal {η : α → ℝ≥0∞} (hη : IsPOU G η) (a : α) :
    ∑' g : G, (((η (g • a)).toReal : ℝ) : ℂ) = 1 := by
  rw [← Complex.ofReal_tsum, ← ENNReal.tsum_toReal_eq (fun g => hη.ne_top _), hη.tsum_eq]
  simp

lemma IsPOU.measurable_toReal {η : α → ℝ≥0∞} (hη : IsPOU G η) :
    Measurable fun a => (((η a).toReal : ℝ) : ℂ) :=
  Complex.measurable_ofReal.comp hη.measurable.ennreal_toReal

/-- **Complex Tonelli swap**: `∫ φ · Σ_g ψ(g a) = ∫ ψ · Σ_g φ(g a)` when
`∫ |φ| Σ_g |ψ(g a)| < ∞`. -/
theorem integral_tsum_swap {φ ψ : α → ℂ} (hφ : Measurable φ) (hψ : Measurable ψ)
    (hfin : ∫⁻ a, ‖φ a‖ₑ * ∑' g : G, ‖ψ (g • a)‖ₑ ∂μ ≠ ⊤) :
    ∫ a, φ a * ∑' g : G, ψ (g • a) ∂μ = ∫ a, ψ a * ∑' g : G, φ (g • a) ∂μ := by
  have hm : ∀ g : G, Measurable fun a : α => g • a := fun g => measurable_const_smul g
  have h1 : ∑' g : G, ∫⁻ a, ‖φ a * ψ (g • a)‖ₑ ∂μ ≠ ⊤ := by
    have : ∑' g : G, ∫⁻ a, ‖φ a * ψ (g • a)‖ₑ ∂μ = ∫⁻ a, ‖φ a‖ₑ * ∑' g : G, ‖ψ (g • a)‖ₑ ∂μ := by
      simp_rw [enorm_mul, ← ENNReal.tsum_mul_left]
      exact (lintegral_tsum fun g =>
        (hφ.enorm.mul (hψ.comp (hm g)).enorm).aemeasurable).symm
    rwa [this]
  have h2 : ∀ g : G, ∫⁻ a, ‖ψ a * φ (g⁻¹ • a)‖ₑ ∂μ = ∫⁻ a, ‖φ a * ψ (g • a)‖ₑ ∂μ := by
    intro g
    have hF : Measurable fun a => ‖ψ a * φ (g⁻¹ • a)‖ₑ := (hψ.mul (hφ.comp (hm g⁻¹))).enorm
    rw [← lintegral_comp_smul (μ := μ) g hF]
    refine lintegral_congr fun a => ?_
    simp [mul_comm]
  calc ∫ a, φ a * ∑' g : G, ψ (g • a) ∂μ
      = ∫ a, ∑' g : G, φ a * ψ (g • a) ∂μ := by simp_rw [tsum_mul_left]
    _ = ∑' g : G, ∫ a, φ a * ψ (g • a) ∂μ :=
        integral_tsum (f := fun (g : G) a => φ a * ψ (g • a))
          (fun g => (hφ.mul (hψ.comp (hm g))).aestronglyMeasurable) h1
    _ = ∑' g : G, ∫ a, ψ a * φ (g⁻¹ • a) ∂μ := by
        refine tsum_congr fun g => ?_
        rw [← integral_smul_eq_self (μ := μ) (fun a => ψ a * φ (g⁻¹ • a)) (g := g)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
        change φ a * ψ (g • a) = ψ (g • a) * φ (g⁻¹ • g • a)
        rw [inv_smul_smul, mul_comm]
    _ = ∫ a, ∑' g : G, ψ a * φ (g⁻¹ • a) ∂μ :=
        (integral_tsum (f := fun (g : G) a => ψ a * φ (g⁻¹ • a))
          (fun g => (hψ.mul (hφ.comp (hm g⁻¹))).aestronglyMeasurable)
          (by simp_rw [h2]; exact h1)).symm
    _ = ∫ a, ψ a * ∑' g : G, φ (g⁻¹ • a) ∂μ := by simp_rw [tsum_mul_left]
    _ = ∫ a, ψ a * ∑' g : G, φ (g • a) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
        change ψ a * _ = ψ a * _
        congr 1
        exact (Equiv.inv G).tsum_eq (fun g : G => φ (g • a))

/-- **Independence of the partition of unity**, complex form. -/
theorem integral_mul_pou_eq {η η' : α → ℝ≥0∞} (hη : IsPOU G η) (hη' : IsPOU G η')
    {f : α → ℂ} (hf : Measurable f) (hinv : ∀ (g : G) (a : α), f (g • a) = f a)
    (hfin : ∫⁻ a, ‖f a‖ₑ * η a ∂μ ≠ ⊤) :
    ∫ a, f a * (((η a).toReal : ℝ) : ℂ) ∂μ = ∫ a, f a * (((η' a).toReal : ℝ) : ℂ) ∂μ := by
  have hφ : Measurable fun a => f a * (((η a).toReal : ℝ) : ℂ) := hf.mul hη.measurable_toReal
  have h := integral_tsum_swap (G := G) (μ := μ) hφ hη'.measurable_toReal (by
    simp_rw [hη'.enorm_toReal, hη'.tsum_eq, mul_one, enorm_mul, hη.enorm_toReal]
    exact hfin)
  simp only [hη'.tsum_toReal, mul_one, hinv, tsum_mul_left, hη.tsum_toReal] at h
  rw [h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun a => mul_comm _ _)

lemma IsPOU.pouRestrict_toReal (H : Subgroup G) {η : α → ℝ≥0∞} (hη : IsPOU G η) (a : α) :
    (((pouRestrict H η a).toReal : ℝ) : ℂ) = ∑' q : G ⧸ H, (((η (q.out • a)).toReal : ℝ) : ℂ) := by
  unfold pouRestrict
  rw [ENNReal.tsum_toReal_eq (fun q => hη.ne_top _), Complex.ofReal_tsum]

/-- **Unfolding** (absolutely convergent form):
`∫_{G\α} (Σ_{γ ∈ H\G} f(γ a)) u(a) = ∫_{H\α} f(a) u(a)` for measurable `f` `H`-invariant and `u`
`G`-invariant with `∫_{H\α} |f| |u| < ∞`. -/
theorem integral_automC_mul_eq (H : Subgroup G) {η ηH : α → ℝ≥0∞} (hη : IsPOU G η)
    (hηH : IsPOU H ηH) {f u : α → ℂ} (hf : Measurable f) (hu : Measurable u)
    (hfinv : ∀ (h : H) (a : α), f (h • a) = f a) (huinv : ∀ (g : G) (a : α), u (g • a) = u a)
    (hfin : ∫⁻ a, ‖f a‖ₑ * ‖u a‖ₑ * ηH a ∂μ ≠ ⊤) :
    ∫ a, automC H f a * u a * (((η a).toReal : ℝ) : ℂ) ∂μ =
      ∫ a, f a * u a * (((ηH a).toReal : ℝ) : ℂ) ∂μ := by
  haveI _iCQ := ArtinKP.X.instCountableQuot H
  have hm : ∀ g : G, Measurable fun a : α => g • a := fun g => measurable_const_smul g
  have hηc := hη.measurable_toReal
  have hR := isPOU_pouRestrict H hη
  -- absolute convergence, in two equivalent forms
  have hfin' : ∫⁻ a, ‖f a‖ₑ * ‖u a‖ₑ * pouRestrict H η a ∂μ ≠ ⊤ := by
    have hfu : Measurable fun a => ‖f a‖ₑ * ‖u a‖ₑ := hf.enorm.mul hu.enorm
    rw [lintegral_mul_pou_eq (G := H) (μ := μ) hR hηH hfu (fun h a => by
      change ‖f (h • a)‖ₑ * ‖u ((h : G) • a)‖ₑ = _
      rw [hfinv, huinv])]
    exact hfin
  have e2 : ∑' q : G ⧸ H, ∫⁻ a, ‖f a * u a * (((η (q.out • a)).toReal : ℝ) : ℂ)‖ₑ ∂μ =
      ∫⁻ a, ‖f a‖ₑ * ‖u a‖ₑ * pouRestrict H η a ∂μ := by
    unfold pouRestrict
    simp_rw [enorm_mul, hη.enorm_toReal, ← ENNReal.tsum_mul_left]
    exact (lintegral_tsum fun q =>
      ((hf.enorm.mul hu.enorm).mul (hη.measurable.comp (hm _))).aemeasurable).symm
  have e1 : ∀ q : G ⧸ H, ∫⁻ a, ‖f (q.out⁻¹ • a) * u a * (((η a).toReal : ℝ) : ℂ)‖ₑ ∂μ =
      ∫⁻ a, ‖f a * u a * (((η (q.out • a)).toReal : ℝ) : ℂ)‖ₑ ∂μ := by
    intro q
    have hF : Measurable fun a => ‖f (q.out⁻¹ • a) * u a * (((η a).toReal : ℝ) : ℂ)‖ₑ :=
      (((hf.comp (hm _)).mul hu).mul hηc).enorm
    rw [← lintegral_comp_smul (μ := μ) q.out hF]
    refine lintegral_congr fun a => ?_
    simp [huinv]
  calc ∫ a, automC H f a * u a * (((η a).toReal : ℝ) : ℂ) ∂μ
      = ∫ a, ∑' q : G ⧸ H, f (q.out⁻¹ • a) * u a * (((η a).toReal : ℝ) : ℂ) ∂μ := by
        unfold automC
        simp_rw [← tsum_mul_right]
    _ = ∑' q : G ⧸ H, ∫ a, f (q.out⁻¹ • a) * u a * (((η a).toReal : ℝ) : ℂ) ∂μ :=
        integral_tsum (f := fun (q : G ⧸ H) a => f (q.out⁻¹ • a) * u a * (((η a).toReal : ℝ) : ℂ))
          (fun q => (((hf.comp (hm _)).mul hu).mul hηc).aestronglyMeasurable)
          (by simp_rw [e1]; rw [e2]; exact hfin')
    _ = ∑' q : G ⧸ H, ∫ a, f a * u a * (((η (q.out • a)).toReal : ℝ) : ℂ) ∂μ := by
        refine tsum_congr fun q => ?_
        rw [← integral_smul_eq_self (μ := μ)
          (fun a => f (q.out⁻¹ • a) * u a * (((η a).toReal : ℝ) : ℂ)) (g := q.out)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
        simp [huinv]
    _ = ∫ a, ∑' q : G ⧸ H, f a * u a * (((η (q.out • a)).toReal : ℝ) : ℂ) ∂μ :=
        (integral_tsum (f := fun (q : G ⧸ H) a => f a * u a * (((η (q.out • a)).toReal : ℝ) : ℂ))
          (fun q => ((hf.mul hu).mul (hηc.comp (hm _))).aestronglyMeasurable)
          (by rw [e2]; exact hfin')).symm
    _ = ∫ a, f a * u a * (((pouRestrict H η a).toReal : ℝ) : ℂ) ∂μ := by
        simp_rw [hη.pouRestrict_toReal H, tsum_mul_left]
    _ = ∫ a, f a * u a * (((ηH a).toReal : ℝ) : ℂ) ∂μ := by
        have hfu : Measurable fun a => f a * u a := hf.mul hu
        refine integral_mul_pou_eq (G := H) hR hηH hfu (fun h a => ?_) ?_
        · change f (h • a) * u ((h : G) • a) = _
          rw [hfinv, huinv]
        · simp_rw [enorm_mul]; exact hfin'

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

variable {F : Type*} [Field F] [NumberField F]

variable [IsTotallyComplex F] {S : Finset (FinitePlace F)}

/-! ### Locally a single term -/

lemma log_ht_lt {p : PairClass S} {P : X F} (h : p.ht P < 3 / 2) :
    Real.log (p.ht P) < Real.log 2 :=
  Real.log_lt_log (p.ht_pos P) (by linarith)

/-! ### Algebra -/

/-! ### Smoothness and the Laplacian -/

/-! ### Support -/

end

end ArtinKP.C5
end

section
-- module Solutions.Artin.KP.RO_Bridge
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

variable [IsTotallyComplex F]

/-- The height of a row class: `ht_p(P) = I_p(P) / ‖p‖`. -/
theorem ht_rowClass (h𝔪 : 𝔪 ≠ ⊥) (p : Row 𝔪) (P : X F) :
    (rowClass h𝔪 p).ht P = X.pairHt (p.c : F) (p.d : F) P / p.norm := by
  change X.sHt (SOf 𝔪) (p.c : F) (p.d : F) P = _
  unfold X.sHt Row.norm
  rw [sNorm_SOf]

end

end ArtinKP.RO
end

section
-- module Solutions.Artin.KP.N2_Cusp
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-N2, file 3: the cusp `σ⁻¹∞` of a finite-index `Γ` (step 3 of stub N-1)

For `σ ∈ SL₂(R)`, `p₀ = rowClass (Row.bot σ)` (the class with `ht_{p₀}(P) = ht(σP)/‖p₀‖`) and
`K = stab Γ p₀`:

* `exists_ideal_conj`: `σ Γ σ⁻¹` contains the translations by a nonzero ideal of `𝓞_F`.
* `cuspSetup`: the `CuspSetup` of file 2 for `τ = σ`, `K`, the group
  `Γ₂ = Γ' ⊓ Γ(𝔫)` and a strict cell of it (`Γ'` any group, `𝔫` from `exists_ideal_conj`).
* **`cusp_integral_eq_zero`**: if the constant term of `θ_Γ(Ψ)` vanishes at the cusp `σ⁻¹∞`
  (`N.CuspVanish`), then `∫_{K\X} c(ht(σP)) θ(P) = 0` for every bounded measurable `c`.
  The passage from the cell of `CuspVanish` to the cell of `Γ₂` is `zRes_congr`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N2

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ}

/-! ### The class of a bottom row -/

lemma ht_rowClass_bot (h𝔪 : 𝔪 ≠ ⊥) (σ : SL(2, SInt 𝔪)) (P : X F) :
    (RO.rowClass h𝔪 (Row.bot σ)).ht P = X.ht (toF 𝔪 σ • P) / (Row.bot σ).norm := by
  rw [RO.ht_rowClass, X.ht_smul]
  rfl

end

end ArtinKP.N2
end

section
-- module Solutions.Artin.KP.N2_Main
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-N2, file 4: stub N-1 (`N.CuspOrth`) and the unconditional Corollary N

* `Orb Γ S`: the (finitely many) `Γ`-orbits of pair classes; `orbEquiv`: an orbit is `Γ / stab`.
* `pe_decomp`, `pe_aOrb`: the pseudo-Eisenstein series is the finite sum over the orbits of the
  sums `Σ_{γ ∈ stab\Γ} g(log ht_{p₀}(γP))` (steps 1 of stub N-1).
* `orbit_integral_eq_zero`: unfolding to the stabilizer (step 2) and `cusp_integral_eq_zero`.
* **`inner_src_theta_eq_zero`**: `⟪[F_{4/3}], θ⟫ = 0` if the constant terms of `θ` vanish at the
  finitely many cusps `cuspMat Γ o` (one per orbit `o` in the support of the weights).
* **`cuspOrth`**: stub N-1, with no hypothesis left.
* **`corollaryN`, `corollaryN_of_continuation`**: Corollary N of MATH2 §2.2, unconditional.
* `zPsi`: the intrinsic residue `z_Ψ`; `zRes_eq_zPsi`; `theta_eq_zero_iff`,
  `theta_eq_zero_iff_reps` (all `σ`, resp. the finitely many representatives).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N2

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ}

/-! ### Orbits of pair classes -/

lemma orbEquiv_apply (Γ : Subgroup (SL(2, 𝓞 F))) {S : Finset (FinitePlace F)} (p₀ : PairClass S)
    (q : Γ ⧸ stab Γ p₀) :
    ((orbEquiv Γ p₀ q : {p : PairClass S // orbOf Γ p = orbOf Γ p₀}) : PairClass S)
      = p₀.act (((q.out)⁻¹ : Γ) : SL(2, 𝓞 F)) := rfl

/-! ### The pseudo-Eisenstein series by orbits -/

/-! ### `L¹` bounds -/

/-- At most one class contributes to a profile vanishing below height `2`. -/
lemma autom_enorm_le (Γ : Subgroup (SL(2, 𝓞 F))) {S : Finset (FinitePlace F)} (p₀ : PairClass S)
    {g : ℝ → ℂ} (hg : VanishLow g) {C : ℝ} (hC : ∀ τ, ‖g τ‖ ≤ C) (P : X F) :
    autom (stab Γ p₀) (fun P => ‖g (Real.log (p₀.ht P))‖ₑ) P ≤ ENNReal.ofReal C := by
  unfold autom
  have h1 : ∀ q : Γ ⧸ stab Γ p₀, ‖g (Real.log (p₀.ht ((q.out)⁻¹ • P)))‖ₑ
      = (fun p : PairClass S => ‖g (Real.log (p.ht P))‖ₑ)
          ((orbEquiv Γ p₀ q : {p : PairClass S // orbOf Γ p = orbOf Γ p₀}) : PairClass S) := by
    intro q
    rw [orbEquiv_apply]
    change _ = ‖g (Real.log ((p₀.act (((q.out)⁻¹ : Γ) : SL(2, 𝓞 F))).ht P))‖ₑ
    rw [PairClass.ht_act]
    rfl
  rw [tsum_congr h1]
  have hinj : Function.Injective fun q : Γ ⧸ stab Γ p₀ =>
      ((orbEquiv Γ p₀ q : {p : PairClass S // orbOf Γ p = orbOf Γ p₀}) : PairClass S) :=
    Subtype.val_injective.comp (orbEquiv Γ p₀).injective
  refine (ENNReal.tsum_comp_le_tsum_of_injective hinj
    (fun p : PairClass S => ‖g (Real.log (p.ht P))‖ₑ)).trans ?_
  obtain ⟨p₁, h⟩ := C5.exists_single S P
  have h' := h.self_of_nhds
  rw [tsum_eq_single p₁ (fun p hp => by
    rw [hg _ (log_ht_lt (h' p hp)), enorm_zero])]
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hC _)

/-! ### One orbit -/

section orbit

variable (Pk : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  {Γ : Subgroup (SL(2, 𝓞 F))} [Γ.FiniteIndex] {Ψ : TSection ι 𝔪}

include hG in
/-- **Steps 2–4 for one orbit.** -/
theorem orbit_integral_eq_zero_oai (hΓ : Inv Γ Ψ) (σ : SL(2, SInt 𝔪))
    (hv : CuspVanish Pk hG hz6 Γ Ψ σ) {p₀ : PairClass (RO.SOf 𝔪)}
    (hp₀ : RO.rowClass hG.ne_bot (Row.bot σ) = p₀) {g : ℝ → ℂ} (hgm : Measurable g)
    (hgl : VanishLow g) {C : ℝ} (hC : ∀ τ, ‖g τ‖ ≤ C) :
    ∫ P, automC (stab Γ p₀) (fun P => g (Real.log (p₀.ht P))) P * X.lift Γ (theta Γ Ψ) P
      * (((X.pou Γ P).toReal : ℝ) : ℂ) ∂X.vol F = 0 := by
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  subst hp₀
  set p₀ := RO.rowClass hG.ne_bot (Row.bot σ) with hp₀
  set u := X.lift Γ (theta Γ Ψ) with hu
  set f : X F → ℂ := fun P => g (Real.log (p₀.ht P)) with hf
  have hum : Measurable u := (X.stronglyMeasurable_lift Γ _).measurable
  have hfm : Measurable f :=
    hgm.comp (Real.measurable_log.comp p₀.continuous_ht.measurable)
  have hfinv : ∀ (k : stab Γ p₀) (P : X F), f (k • P) = f P := by
    intro k P
    have h1 := PairClass.ht_act p₀ ((k : Γ) : SL(2, 𝓞 F)) P
    rw [k.2] at h1
    simp only [hf]
    rw [h1]
    rfl
  have huinv : ∀ (γ : Γ) (P : X F), u (γ • P) = u P := fun γ P => X.lift_smul Γ _ γ P
  have hηK := isPOU_pouRestrict (stab Γ p₀) (X.isPOU_pou Γ)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hfin : ∫⁻ P, ‖f P‖ₑ * ‖u P‖ₑ * pouRestrict (stab Γ p₀) (X.pou Γ) P ∂X.vol F ≠ ⊤ := by
    rw [← lintegral_autom_mul_eq (G := Γ) (μ := X.vol F) (stab Γ p₀) (X.isPOU_pou Γ) hηK
      (f := fun P => ‖f P‖ₑ) (u := fun P => ‖u P‖ₑ) hfm.enorm hum.enorm
      (fun k P => by rw [hfinv]) (fun γ P => by rw [huinv])]
    have hle : ∫⁻ P, autom (stab Γ p₀) (fun P => ‖f P‖ₑ) P * ‖u P‖ₑ * X.pou Γ P ∂X.vol F
        ≤ ∫⁻ P, ENNReal.ofReal C * (‖u P‖ₑ * X.pou Γ P) ∂X.vol F := by
      refine lintegral_mono fun P => ?_
      rw [mul_assoc]
      exact mul_le_mul' (autom_enorm_le Γ p₀ hgl hC P) le_rfl
    refine ne_top_of_le_ne_top ?_ hle
    have e : ∫⁻ P, ENNReal.ofReal C * (‖u P‖ₑ * X.pou Γ P) ∂X.vol F
        = ENNReal.ofReal C * ∫⁻ P, ‖u P‖ₑ * X.pou Γ P ∂X.vol F :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    rw [e]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_lift_pou_ne_top hG Γ _)
  rw [integral_automC_mul_eq (G := Γ) (μ := X.vol F) (stab Γ p₀) (X.isPOU_pou Γ) hηK hfm hum
    hfinv huinv hfin]
  -- the profile in cusp coordinates
  set N : ℝ := (Row.bot σ).norm with hN
  set c : ℝ → ℂ := fun t => (((C + 1)⁻¹ : ℝ) : ℂ) * g (Real.log (t / N)) with hc
  have hC1 : (0 : ℝ) < C + 1 := by linarith
  have hcm : Measurable c :=
    measurable_const.mul (hgm.comp (Real.measurable_log.comp (measurable_id.div_const N)))
  have hc1 : ∀ t, ‖c t‖ ≤ 1 := by
    intro t
    rw [hc]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (inv_pos.mpr hC1), inv_mul_le_iff₀ hC1, mul_one]
    exact (hC _).trans (by linarith)
  have hfc : ∀ P : X F, f P = ((C + 1 : ℝ) : ℂ) * c (X.ht (toF 𝔪 σ • P)) := by
    intro P
    simp only [hf, hc, hp₀]
    rw [ht_rowClass_bot, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hC1.ne',
      Complex.ofReal_one, one_mul]
  have hfin' : ∫⁻ P, ‖c (X.ht (toF 𝔪 σ • P))‖ₑ * ‖u P‖ₑ
      * pouRestrict (stab Γ p₀) (X.pou Γ) P ∂X.vol F ≠ ⊤ := by
    refine ne_top_of_le_ne_top hfin (lintegral_mono fun P => ?_)
    refine mul_le_mul' (mul_le_mul' ?_ le_rfl) le_rfl
    have h1 : (1 : ℝ≥0∞) ≤ ‖((C + 1 : ℝ) : ℂ)‖ₑ := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC1]
      exact ENNReal.one_le_ofReal.mpr (by linarith)
    have e : ‖f P‖ₑ = ‖((C + 1 : ℝ) : ℂ)‖ₑ * ‖c (X.ht (toF 𝔪 σ • P))‖ₑ := by
      rw [hfc P]; exact enorm_mul _ _
    rw [e]
    calc ‖c (X.ht (toF 𝔪 σ • P))‖ₑ = 1 * ‖c (X.ht (toF 𝔪 σ • P))‖ₑ := (one_mul _).symm
      _ ≤ _ := mul_le_mul' h1 le_rfl
  have hzero := cusp_integral_eq_zero Pk hG hz6 hΓ σ hv hcm hc1 hηK hfin'
  have h2 : ∀ P : X F, f P * u P * (((pouRestrict (stab Γ p₀) (X.pou Γ) P).toReal : ℝ) : ℂ)
      = ((C + 1 : ℝ) : ℂ) * (c (X.ht (toF 𝔪 σ • P)) * u P
        * (((pouRestrict (stab Γ p₀) (X.pou Γ) P).toReal : ℝ) : ℂ)) := fun P => by
    rw [hfc P]; ring
  rw [integral_congr_ae (Eventually.of_forall h2), integral_const_mul, hzero, mul_zero]

end orbit

/-! ### Cusp representatives -/

/-! ### Stub N-1 -/

end

end ArtinKP.N2
end

theorem solution.{u_1} : type_of% @ArtinKP.N2.orbit_integral_eq_zero_oai.{u_1} := @ArtinKP.N2.orbit_integral_eq_zero_oai.{u_1}
