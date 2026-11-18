-- Prove2me | solution 1 for ArtinKP.N.integral_box_theta_eq_of_tendsto_ray
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:45:48.782194+00:00
-- url     : https://prove2.me/submissions/13f509cd-7b2e-4595-b4b8-156af0e11c3c

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
import Definitions.Def_ArtinKPB015
import Theorems.Thm_ArtinKP_B_continuous_eis
import Theorems.Thm_ArtinKP_C5_differentiableOn_functional_resPart
import Theorems.Thm_ArtinKP_C5_exists_norm_hpart_le
import Theorems.Thm_ArtinKP_C5_exists_single
import Theorems.Thm_ArtinKP_C5_l2Rep_src
import Theorems.Thm_ArtinKP_C5_lap_upart
import Theorems.Thm_ArtinKP_C5_norm_upart_le
import Theorems.Thm_ArtinKP_C5_tendsto_ray_functional_resPart_theta
import Theorems.Thm_ArtinKP_RC_exists_isWeakSol_of_lap_eq
import Theorems.Thm_ArtinKP_RC_lintegral_G_pow_lt_top
import Theorems.Thm_ArtinKP_X_X_isPOU_pou
import Theorems.Thm_ArtinKP_X_X_tsum_indicator_box_le_boxMult

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

/-! ### The product formula for `S`-units -/

theorem Ninf_pos {x : F} (hx : x ≠ 0) : 0 < Ninf x :=
  Finset.prod_pos fun _ _ => Complex.normSq_pos.mpr ((map_ne_zero _).mpr hx)

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

/-! ### Convergence of the height series over row classes (from WP-B1) -/

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
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
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

section analytic

variable [IsTotallyComplex F]

theorem measurable_eis (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) {s : ℂ} (hs : 2 < s.re) :
    Measurable fun Q : X F => eis Ψ s Q :=
  (continuous_eis h𝔪 Ψ hs).measurable

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
-- module Solutions.Artin.KP.X_L2
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
attribute [-instance] _root_.ArtinKP.B1.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatSub _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol
attribute [-simp] _root_.ArtinKP.X.chart1_symm_fst _root_.ArtinKP.X.chart1_symm_snd _root_.ArtinKP.X.chart1_v _root_.ArtinKP.X.chart1_x _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
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

/-! ### Invariance -/

/-! ### Local finiteness and averaging -/

/-! ### Unfolding -/

/-! ### Green's identity on the quotient -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.CAbs_Residue
/-!
# WP-C-abs, part 1: the strong residue of the resolvent of a bounded self-adjoint operator

`T` bounded self-adjoint on a complex Hilbert space `H`, `t₀` real, `P₀` the orthogonal projection
onto `ker (T - t₀)`.  For `z → t₀` inside a cone `|Re (z - t₀)| ≤ C * |Im z|`,
`(t₀ - z) • (T - z)⁻¹ x → P₀ x` for every `x` (MATH.md, Lemma C1).  No spectral theorem is used.
-/

namespace ArtinKP.CAbs

open Filter Topology ComplexConjugate
open scoped InnerProductSpace NNReal

set_option linter.unusedSectionVars false

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `⟪x, x⟫ = ‖x‖²` with the `Complex.ofReal` cast. -/
lemma inner_self_eq_ofReal (x : H) : ⟪x, x⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  simp [inner_self_eq_norm_sq_to_K]

end

end ArtinKP.CAbs
end

section
-- module Solutions.Artin.KP.CAbs_Form
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulGinfX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX
attribute [-simp] _root_.ArtinKP.X.SymmOp.energySpace_j
/-!
# WP-C-abs, part 2: the form operator and the variational resolvent

Abstract setting (MATH.md §3.1): `H` plays `L²`, `V` plays `H¹`.  The data is a bounded map
`j : V →L[ℂ] H`, injective, with dense range and `‖j u‖ ≤ ‖u‖`.  The Dirichlet form is *defined* by
`𝔇(u, u') := ⟪u, u'⟫_V - ⟪j u, j u'⟫_H`, so that `‖u‖_V² = ‖j u‖² + 𝔇(u, u)` holds by definition.
Mathlib convention: inner products are conjugate-linear in the first and linear in the second
argument, so the "unknown" sits in the second slot and the test vector `u'` in the first.

* `T = j ∘ j†` (Riesz: `⟪j† f, u'⟫_V = ⟪f, j u'⟫_H`); bounded, self-adjoint, `0 ≤ T ≤ 1`, injective.
* `Res lam = T * (1 - (lam + 1) T)⁻¹` for `lam ∈ ℂ ∖ [0, ∞)`; `ResV lam f ∈ V` is the unique weak
  solution of `𝔇(u', u) - lam ⟪j u', j u⟫ = ⟪j u', f⟫` and `j (ResV lam f) = Res lam f`.
* `lam ↦ Res lam` is analytic (operator norm) on `ℂ ∖ [0, ∞)`.
-/

namespace ArtinKP.CAbs

open Filter Topology ComplexConjugate
open scoped InnerProductSpace NNReal

set_option linter.unusedSectionVars false

noncomputable section

/-- Elementary lower bound behind the invertibility of `1 - μ T` for `μ ∉ [1, ∞)`. -/
lemma exists_lower_bound {μ : ℂ} (hμ : μ.re < 1 ∨ μ.im ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ a n : ℝ, 0 ≤ a → a ≤ n → c * n ≤ ‖(n : ℂ) - conj μ * a‖ := by
  by_cases him : μ.im = 0
  · have hre : μ.re < 1 := by
      rcases hμ with h | h
      · exact h
      · exact absurd him h
    refine ⟨min 1 (1 - μ.re), lt_min one_pos (by linarith), fun a n ha han => ?_⟩
    have h1 : ((n : ℂ) - conj μ * a).re = n - μ.re * a := by simp
    have h2 : n - μ.re * a ≤ ‖(n : ℂ) - conj μ * a‖ := by
      rw [← h1]; exact Complex.re_le_norm _
    refine le_trans ?_ h2
    have hn : 0 ≤ n := ha.trans han
    by_cases hle : μ.re ≤ 0
    · have : min 1 (1 - μ.re) * n ≤ 1 * n := by
        gcongr; exact min_le_left _ _
      nlinarith
    · push_neg at hle
      have : min 1 (1 - μ.re) * n ≤ (1 - μ.re) * n := by
        gcongr; exact min_le_right _ _
      nlinarith
  · have hμ0 : μ ≠ 0 := fun h => him (by simp [h])
    have hpos : 0 < ‖μ‖ := norm_pos_iff.mpr hμ0
    refine ⟨|μ.im| / ‖μ‖, div_pos (abs_pos.mpr him) hpos, fun a n ha han => ?_⟩
    have hn : 0 ≤ n := ha.trans han
    have h1 : (μ * ((n : ℂ) - conj μ * a)).im = μ.im * n := by
      have : μ * ((n : ℂ) - conj μ * a) = μ * n - ((Complex.normSq μ * a : ℝ) : ℂ) := by
        rw [mul_sub, ← mul_assoc, Complex.mul_conj]; push_cast; ring
      rw [this, Complex.sub_im, Complex.ofReal_im, Complex.im_mul_ofReal]; ring
    have h2 : |μ.im| * n ≤ ‖μ‖ * ‖(n : ℂ) - conj μ * a‖ := by
      rw [← norm_mul]
      have := Complex.abs_im_le_norm (μ * ((n : ℂ) - conj μ * a))
      rw [h1, abs_mul, abs_of_nonneg hn] at this
      exact this
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos, mul_comm _ ‖μ‖]
    exact h2

namespace EnergySpace

variable {V : Type*} {H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : EnergySpace V H)

/-- The Dirichlet form is nonnegative: `𝔇(u, u) = ‖u‖² - ‖j u‖² ≥ 0`. -/
lemma form_self (u : V) : E.form u u = ((‖u‖ ^ 2 - ‖E.j u‖ ^ 2 : ℝ) : ℂ) := by
  simp only [form, inner_self_eq_ofReal]
  push_cast; ring

lemma form_self_nonneg (u : V) : 0 ≤ ‖u‖ ^ 2 - ‖E.j u‖ ^ 2 := by
  have := E.norm_le u
  nlinarith [norm_nonneg (E.j u), norm_nonneg u]

lemma inner_riesz_right (f : H) (u : V) : ⟪u, E.riesz f⟫_ℂ = ⟪E.j u, f⟫_ℂ :=
  ContinuousLinearMap.adjoint_inner_right E.j u f

lemma T_apply (f : H) : E.T f = E.j (E.riesz f) := rfl

lemma inner_T (f g : H) : ⟪E.T f, g⟫_ℂ = ⟪E.riesz f, E.riesz g⟫_ℂ := by
  rw [T_apply, inner_riesz_right]

lemma inner_T_self (f : H) : ⟪E.T f, f⟫_ℂ = ((‖E.riesz f‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_T, inner_self_eq_ofReal]

lemma norm_riesz_le (f : H) : ‖E.riesz f‖ ≤ ‖f‖ := by
  by_cases h0 : ‖E.riesz f‖ = 0
  · rw [h0]; exact norm_nonneg _
  have hpos : 0 < ‖E.riesz f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  have h1 : ‖E.riesz f‖ ^ 2 = ‖⟪E.T f, f⟫_ℂ‖ := by
    rw [inner_T_self, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h2 : ‖⟪E.T f, f⟫_ℂ‖ ≤ ‖E.riesz f‖ * ‖f‖ :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (E.norm_le _) (norm_nonneg _))
  have h3 : ‖E.riesz f‖ * ‖E.riesz f‖ ≤ ‖E.riesz f‖ * ‖f‖ := by nlinarith
  exact le_of_mul_le_mul_left h3 hpos

/-- `1 - μ T` is invertible for `μ ∉ [1, ∞)`. -/
lemma isUnit_one_sub_smul_T {μ : ℂ} (hμ : μ.re < 1 ∨ μ.im ≠ 0) :
    IsUnit (1 - μ • E.T : H →L[ℂ] H) := by
  obtain ⟨c, hc, hbound⟩ := exists_lower_bound hμ
  refine ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map _
    (c := ⟨c, hc.le⟩) (by exact_mod_cast hc) fun x => ?_
  have h : ⟪(1 - μ • E.T : H →L[ℂ] H) x, x⟫_ℂ =
      ((‖x‖ ^ 2 : ℝ) : ℂ) - conj μ * ((‖E.riesz x‖ ^ 2 : ℝ) : ℂ) := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.smul_apply, inner_sub_left, inner_smul_left, inner_T_self,
      inner_self_eq_ofReal]
  rw [h]
  have h2 := hbound (‖E.riesz x‖ ^ 2) (‖x‖ ^ 2) (sq_nonneg _)
    (pow_le_pow_left₀ (norm_nonneg _) (E.norm_riesz_le x) 2)
  rw [mul_comm]
  exact h2

lemma isUnit_of_mem_resolventDomain {lam : ℂ} (h : lam ∈ resolventDomain) :
    IsUnit (1 - (lam + 1) • E.T : H →L[ℂ] H) := by
  apply E.isUnit_one_sub_smul_T
  rcases h with h | h
  · left; simp; linarith
  · right; simpa using h

lemma one_sub_smul_T_G_apply {lam : ℂ} (h : lam ∈ resolventDomain) (f : H) :
    (1 - (lam + 1) • E.T : H →L[ℂ] H) (E.G lam f) = f := by
  have := Ring.mul_inverse_cancel _ (E.isUnit_of_mem_resolventDomain h)
  exact congrArg (fun A : H →L[ℂ] H => A f) this

lemma isWeakEigen_iff_isWeakSol_zero {lam : ℂ} {u : V} :
    E.IsWeakEigen lam u ↔ E.IsWeakSol lam 0 u := by
  simp [IsWeakEigen, IsWeakSol, sub_eq_zero]

/-- Strong form of the weak equation: `u - (lam + 1) riesz (j u) = riesz f`. -/
lemma isWeakSol_iff {lam : ℂ} {f : H} {u : V} :
    E.IsWeakSol lam f u ↔ u - (lam + 1) • E.riesz (E.j u) = E.riesz f := by
  constructor
  · intro h
    refine ext_inner_left ℂ fun u' => ?_
    rw [inner_sub_right, inner_smul_right, inner_riesz_right, inner_riesz_right, ← h u']
    simp only [form]; ring
  · intro h u'
    have := congrArg (fun w => ⟪u', w⟫_ℂ) h
    simp only [inner_sub_right, inner_smul_right, inner_riesz_right] at this
    rw [← this]; simp only [form]; ring

lemma isWeakEigen_iff {lam : ℂ} {u : V} :
    E.IsWeakEigen lam u ↔ u = (lam + 1) • E.riesz (E.j u) := by
  rw [isWeakEigen_iff_isWeakSol_zero, isWeakSol_iff, map_zero, sub_eq_zero]

/-- For `lam ∉ [0, ∞)` the only weak `lam`-eigenvector is `0`. -/
lemma eq_zero_of_isWeakEigen {lam : ℂ} (hlam : lam ∈ resolventDomain) {u : V}
    (hu : E.IsWeakEigen lam u) : u = 0 := by
  have h := hu u
  rw [form_self, inner_self_eq_ofReal] at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  rw [Complex.re_mul_ofReal, Complex.ofReal_re] at hre
  rw [Complex.im_mul_ofReal, Complex.ofReal_im] at him
  have hju : ‖E.j u‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖E.j u‖ ^ 2 := by positivity
    rcases hlam with hl | hl
    · have := E.form_self_nonneg u
      nlinarith
    · have : lam.im = 0 := by
        rcases mul_eq_zero.mp him.symm with h0 | h0
        · exact h0
        · exact absurd h0 hpos.ne'
      exact hl this
  have : E.j u = 0 := norm_eq_zero.mp hju
  exact E.injective (by rw [this, map_zero])

/-- **Existence**: `ResV lam f` solves the weak resolvent equation. -/
theorem isWeakSol_ResV {lam : ℂ} (hlam : lam ∈ resolventDomain) (f : H) :
    E.IsWeakSol lam f (E.ResV lam f) := by
  rw [isWeakSol_iff]
  have h := E.one_sub_smul_T_G_apply hlam f
  have h2 : E.riesz ((1 - (lam + 1) • E.T : H →L[ℂ] H) (E.G lam f)) = E.riesz f := by rw [h]
  rw [← h2]
  simp [ResV, T_apply]

/-- **Uniqueness**: a weak solution equals `ResV lam f`. -/
theorem IsWeakSol.eq_ResV {lam : ℂ} (hlam : lam ∈ resolventDomain) {f : H} {u : V}
    (hu : E.IsWeakSol lam f u) : u = E.ResV lam f := by
  have h1 := (E.isWeakSol_iff).mp hu
  have h2 := (E.isWeakSol_iff).mp (E.isWeakSol_ResV hlam f)
  have h3 : E.IsWeakEigen lam (u - E.ResV lam f) := by
    rw [isWeakEigen_iff, map_sub, map_sub, smul_sub]
    rw [← h2] at h1
    rw [sub_eq_sub_iff_add_eq_add] at h1 ⊢
    rw [h1, add_comm]
  exact sub_eq_zero.mp (E.eq_zero_of_isWeakEigen hlam h3)

/-- Characterization of `Res lam f` inside `H`. -/
theorem eq_Res_iff {lam : ℂ} (hlam : lam ∈ resolventDomain) {f h : H} :
    h = E.Res lam f ↔ ∃ u : V, E.j u = h ∧ E.IsWeakSol lam f u := by
  constructor
  · rintro rfl
    exact ⟨E.ResV lam f, rfl, E.isWeakSol_ResV hlam f⟩
  · rintro ⟨u, rfl, hu⟩
    rw [hu.eq_ResV E hlam]; rfl

end EnergySpace

end

end ArtinKP.CAbs
end

section
-- module Solutions.Artin.KP.X2_H1
attribute [-instance] _root_.ArtinKP.B1.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatSub _root_.ArtinKP.X.instContinuousConstSMulSubgroup
/-! # WP-X2, file 5: the geometric core and the energy space `H¹(Γ \ X)`

* `X.toL2 Γ f h : L²(Γ\X)` — the class of a measurable `Γ`-invariant function that is square
  integrable modulo `Γ` (`X.L2Rep Γ f`), with `X.inner_toL2`, `X.norm_sq_toL2`;
* `X.core Γ` — the functions `∑_{γ ∈ Γ} φ ∘ γ`, `φ ∈ C_c^∞(X)` (equivalently: smooth,
  `Γ`-invariant, support compact modulo `Γ`; see `X.mem_core_of_tsupport` in `X2_Weak`);
* `X.symmOp Γ : SymmOp (L²(Γ\X))` — the Laplacian on the core: dense domain, symmetric,
  nonnegative, with `⟪w, Δw⟫ = ∫_{Γ\X} ∑_w v_w² |∇_w w|²` (`X.inner_coreL2_coreLap_self`);
* `X.H1 Γ`, `X.energy Γ : CAbs.EnergySpace (X.H1 Γ) (X.L2 Γ)`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F] (Γ : Subgroup (SL(2, 𝓞 F)))

/-! ### Classes of invariant functions -/

variable {Γ}

variable (Γ)

variable {Γ}

variable (Γ)

variable {Γ}

/-- The pull-back of the class of `f` is `f` almost everywhere. -/
lemma X.lift_toL2 {f : X F → ℂ} (h : X.L2Rep Γ f) : X.lift Γ (X.toL2 Γ f h) =ᵐ[X.vol F] f := by
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  have h1 := liftQ_ae_eq (X.isPOU_pou Γ) (MemLp.coeFn_toLp h.memLp)
  refine h1.trans (Filter.Eventually.of_forall fun P => ?_)
  exact X.desc_mk h.inv P

/-! ### Local integrability of pull-backs -/

/-! ### The core -/

/-! ### Density of the core -/

/-! ### The symmetric operator and the energy space -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.C5_Holo
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
-- module Solutions.Artin.KP.X2_Cutoff
/-! # WP-X2, file 7: the height cut-off lemma

`X.exists_weakSol`: a smooth `Γ`-invariant `u ∈ L²(Γ\X)` with `Δu = λu + f` pointwise,
`f ∈ L²(Γ\X)`, lies in `H¹(Γ\X)` and is a weak solution against all of `H¹`, given cut-offs
`χ_n` (smooth, invariant, `0 ≤ χ_n ≤ 1`, compact support modulo `Γ`, `χ_n → 1` pointwise,
`∑_w v_w²|∇_w χ_n|² ≤ ε_n → 0`).  This is MATH2 §1.6; the only completeness input is the
existence of the cut-offs (MATH2 §1.4(d)).

The energy of `χ u` is computed by the IMS localisation formula (`X.ims`)
`∫ |∇(χu)|² = ∫ χ² Re(ū Δu) + ∫ |u|² |∇χ|²`, so finiteness of the energy of `u` is not assumed.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F] {Γ : Subgroup (SL(2, 𝓞 F))}

lemma X.Smooth.sub {u w : X F → ℂ} (hu : X.Smooth u) (hw : X.Smooth w) :
    X.Smooth fun P => u P - w P := ContDiff.sub hu.contDiff hw.contDiff

/-! ### Testing against the core -/

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
-- module Solutions.Artin.KP.C5_PE
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

lemma wt_rowClass (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) (s : ℂ) (r : Row 𝔪) :
    wt h𝔪 Ψ s (RO.rowClass h𝔪 r) = Ψ.tilde s r := by
  unfold wt
  have : (RO.rowClassEquiv h𝔪).symm (RO.rowClass h𝔪 r) = B.RowClass.mk r := by
    rw [Equiv.symm_apply_eq]
    rfl
  rw [this, tildeC_mk]

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

lemma differentiable_wt (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) (p : PairClass (RO.SOf 𝔪)) :
    Differentiable ℂ fun s : ℂ => wt h𝔪 Ψ s p := by
  unfold wt tildeC TSection.tilde
  set r : Row 𝔪 := ((RO.rowClassEquiv h𝔪).symm p).out
  have hn : ((r.norm : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr r.norm_pos.ne'
  exact (Ψ.holo r).mul (differentiable_id.const_cpow (Or.inl hn))

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

lemma hpart_eq_pe (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) (s : ℂ) :
    hpart Ψ s = pe (RO.SOf 𝔪) (wt h𝔪 Ψ s) (gS s) :=
  funext fun Q => tsum_eq_pe h𝔪 Ψ s (gS s) Q

/-! ### The Eisenstein series on pair classes -/

/-! ### Invariance, regularity -/

lemma smul_eq_toF (γ : SL(2, 𝓞 F)) (Q : X F) : γ • Q = toF 𝔪 (RO.intMat 𝔪 γ) • Q :=
  (toF_map_int_smul (𝔪 := 𝔪) γ Q).symm

lemma isInv_eis (h𝔪 : 𝔪 ≠ ⊥) {Γ : Subgroup (SL(2, 𝓞 F))} {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ)
    (s : ℂ) : X.IsInv Γ fun Q : X F => eis Ψ s Q := fun γ Q => by
  change eis Ψ s ((γ : SL(2, 𝓞 F)) • Q) = eis Ψ s Q
  rw [smul_eq_toF (𝔪 := 𝔪), eis_smul_of_mem_stab h𝔪 (hΓ γ γ.2)]

lemma isInv_pe_wt (h𝔪 : 𝔪 ≠ ⊥) {Γ : Subgroup (SL(2, 𝓞 F))} {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ)
    (s : ℂ) (g : ℝ → ℂ) : X.IsInv Γ (pe (RO.SOf 𝔪) (wt h𝔪 Ψ s) g) := fun γ Q =>
  pe_smul g (fun p => wt_act h𝔪 hΓ γ.2 s p) Q

lemma isInv_hpart (h𝔪 : 𝔪 ≠ ⊥) {Γ : Subgroup (SL(2, 𝓞 F))} {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ)
    (s : ℂ) : X.IsInv Γ (hpart Ψ s) := by
  rw [hpart_eq_pe h𝔪]
  exact isInv_pe_wt h𝔪 hΓ s _

lemma isInv_upart (h𝔪 : 𝔪 ≠ ⊥) {Γ : Subgroup (SL(2, 𝓞 F))} {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ)
    (s : ℂ) : X.IsInv Γ (upart Ψ s) := fun γ Q => by
  have h1 : eis Ψ s (γ • Q) = eis Ψ s Q := isInv_eis h𝔪 hΓ s γ Q
  have h2 : hpart Ψ s (γ • Q) = hpart Ψ s Q := isInv_hpart h𝔪 hΓ s γ Q
  unfold upart
  rw [h1, h2]

/-- `h_s` is smooth, for every `s ∈ ℂ`. -/
theorem smooth_hpart (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) (s : ℂ) : X.Smooth (hpart Ψ s) := by
  rw [hpart_eq_pe h𝔪]
  exact smooth_pe _ (contDiff_gS s) (vanishLow_gS s)

theorem smooth_upart (h𝔪 : 𝔪 ≠ ⊥) {Ψ : TSection ι 𝔪} {s : ℂ} (hD : EisEigen Ψ s) :
    X.Smooth (upart Ψ s) :=
  hD.1.sub (smooth_hpart h𝔪 Ψ s)

lemma measurable_upart (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) {s : ℂ} (hs : 2 < s.re) :
    Measurable (upart Ψ s) :=
  (measurable_eis h𝔪 Ψ hs).sub (smooth_hpart h𝔪 Ψ s).continuous.measurable

/-- **`u_s ∈ L²(Γ\X)`** for `Re s > 2` (MATH2 1.4(b); `G` bounded, finite volume). -/
theorem l2Rep_upart (hG : Good 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) {s : ℂ} (hs : 2 < s.re) : X.L2Rep Γ (upart Ψ s) := by
  have h𝔪 := hG.ne_bot
  obtain ⟨Bd, hB0, hB⟩ := exists_wt_bound h𝔪 Ψ ‖s‖
  refine X.L2Rep.of_lintegral (measurable_upart h𝔪 Ψ hs) (isInv_upart h𝔪 hΓ s) ?_
  have hfin := RC.lintegral_G_pow_lt_top (RO.sBezout hG) (RO.finiteCusps (RO.SOf 𝔪)) hs Γ 2
  have hle : ∀ P : X F, ‖upart Ψ s P‖ₑ ^ (2 : ℝ) * X.pou Γ P ≤
      ENNReal.ofReal Bd ^ 2 * (ENNReal.ofReal (G (RO.SOf 𝔪) s.re P) ^ 2 * X.pou Γ P) := by
    intro P
    have h1 : ‖upart Ψ s P‖ₑ ≤ ENNReal.ofReal Bd * ENNReal.ofReal (G (RO.SOf 𝔪) s.re P) := by
      rw [← ofReal_norm, ← ENNReal.ofReal_mul hB0]
      exact ENNReal.ofReal_le_ofReal (norm_upart_le h𝔪 Ψ hs hB0 (hB s le_rfl) P)
    rw [ENNReal.rpow_two, ← mul_assoc, ← mul_pow]
    gcongr
  refine ((lintegral_mono hle).trans_lt ?_).ne
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hfin

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

lemma card_pos' : (0 : ℝ) < (Fintype.card (InfinitePlace F) : ℝ) := by
  exact_mod_cast Fintype.card_pos

lemma lam_re (s : ℂ) : (lam F s).re =
    (Fintype.card (InfinitePlace F) : ℝ) * (s.re * (2 - s.re) + s.im ^ 2) := by
  unfold lam
  simp [Complex.mul_re]
  ring

lemma lam_im (s : ℂ) : (lam F s).im =
    (Fintype.card (InfinitePlace F) : ℝ) * (2 * s.im * (1 - s.re)) := by
  unfold lam
  simp [Complex.mul_im]
  ring

/-- **`λ(s) ∉ [0, ∞)` iff `Re s ≠ 1` and `s ∉ [0, 2]`.** -/
theorem lam_mem_resolventDomain_iff (s : ℂ) : lam F s ∈ resolventDomain ↔ s ∈ Omega := by
  have hr := card_pos' (F := F)
  change ((lam F s).re < 0 ∨ (lam F s).im ≠ 0) ↔ _
  rw [lam_re, lam_im]
  constructor
  · rintro (h | h)
    · have h1 : s.re * (2 - s.re) + s.im ^ 2 < 0 := by
        by_contra hc
        exact absurd h (not_lt.mpr (mul_nonneg hr.le (not_lt.mp hc)))
      refine ⟨fun h1' => ?_, fun h0 => ?_⟩
      · rw [h1'] at h1
        nlinarith [sq_nonneg s.im]
      · rw [h0] at h1
        by_contra hc
        push Not at hc
        nlinarith [hc.1, hc.2]
    · have h1 : 2 * s.im * (1 - s.re) ≠ 0 := fun h0 => h (by rw [h0, mul_zero])
      refine ⟨fun h1' => h1 (by rw [h1']; ring), fun h0 => absurd (by rw [h0]; ring) h1⟩
  · rintro ⟨h1, h2⟩
    by_cases h0 : s.im = 0
    · left
      rw [h0]
      have : s.re * (2 - s.re) < 0 := by
        rcases h2 h0 with h | h <;> nlinarith
      nlinarith
    · right
      refine mul_ne_zero hr.ne' (mul_ne_zero (mul_ne_zero two_ne_zero h0) ?_)
      exact sub_ne_zero.mpr (Ne.symm h1)

/-- The slit half-plane of `E_Model` lies in the resolvent region. -/
theorem slit_subset_Omega : E.slit ⊆ Omega := fun _ hs =>
  ⟨ne_of_gt hs.1, fun h0 => Or.inr (hs.2 h0)⟩

lemma mem_Omega_of_two_lt_re {s : ℂ} (hs : 2 < s.re) : s ∈ Omega :=
  ⟨by linarith, fun _ => Or.inr hs⟩

/-! ### The classes in `L²(Γ\X)` -/

lemma srcL2_eq {Γ : Subgroup (SL(2, 𝓞 F))} {Ψ : TSection ι 𝔪} {s : ℂ}
    (h : X.L2Rep Γ (src Ψ s)) : srcL2 Γ Ψ s = X.toL2 Γ (src Ψ s) h := dif_pos h

lemma uL2_eq {Γ : Subgroup (SL(2, 𝓞 F))} {Ψ : TSection ι 𝔪} {s : ℂ}
    (h : X.L2Rep Γ (upart Ψ s)) : uL2 Γ Ψ s = X.toL2 Γ (upart Ψ s) h := dif_pos h

variable [IsTotallyComplex F]

/-! ### (C5) -/

/-- **(C5)**: `[u_s] = −Res(λ(s)) [F_s]` in `L²(Γ\X)` for `Re s > 2`
(`u_s = E_Ψ(·, s) − h_s`; D1 as the named hypothesis `EisEigen Ψ s`). -/
theorem uL2_eq_resPart (hG : Good 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) {s : ℂ} (hs : 2 < s.re) (hD : EisEigen Ψ s) :
    uL2 Γ Ψ s = resPart Γ Ψ s := by
  have h𝔪 := hG.ne_bot
  have hu2 := l2Rep_upart hG Γ hΓ hs
  have hF2 := l2Rep_src hG Γ hΓ s
  have hf2 : X.L2Rep Γ (fun P => (-1 : ℂ) * src Ψ s P) := hF2.const_mul (-1)
  have heq : ∀ P, X.lap (upart Ψ s) P = lam F s * upart Ψ s P + (-1 : ℂ) * src Ψ s P :=
    fun P => by rw [lap_upart h𝔪 hD]; ring
  obtain ⟨x, hx1, hx2⟩ := RC.exists_isWeakSol_of_lap_eq (RO.sBezout hG) (RO.finiteCusps (RO.SOf 𝔪))
    (smooth_upart h𝔪 hD) hu2 hf2 (lam F s) heq
  have hdom : lam F s ∈ resolventDomain :=
    (lam_mem_resolventDomain_iff s).mpr (mem_Omega_of_two_lt_re hs)
  have h1 := ((X.energy Γ).eq_Res_iff hdom).mpr ⟨x, hx1, hx2⟩
  rw [uL2_eq hu2, h1, X.toL2_const_mul hF2]
  unfold resPart
  rw [srcL2_eq hF2, map_smul, neg_smul, one_smul]

/-! ### Continuation -/

/-! ### The limit (C7) -/

/-! ### `θ` is a weak eigenfunction -/

end

end ArtinKP.C5
end

section
-- module Solutions.Artin.KP.C5_Linear
/-! # WP-C5, file 6: functionals and linearity in `Ψ`

* `differentiableOn_functional_resPart`, `tendsto_ray_functional`: for a bounded functional `ℓ`
  on `L²(Γ\X)` (e.g. `X.coeffFunctional Γ n ψ …`), `s ↦ ℓ(−Res(λ(s))[F_s])` is holomorphic on
  `Omega` and `(s_t − s₀) ℓ(…) → ℓ(θ_Ψ)` along the ray.
* `coeffFunctional_resPart`: for `Re s > 2` the local pairing of the resolvent expression is the
  integral of `u_s = E_Ψ − h_s` over the box.
* linearity: `src_add`, `src_smul`, `hpart_add`, `hpart_smul`, `Inv.add`, `Inv.smul`,
  `srcL2_add`, `srcL2_smul`, `resPart_add`, `resPart_smul`, `theta_add`, `theta_smul`.
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

/-! ### Linearity of the weights -/

variable [IsTotallyComplex F]

/-! ### Linearity of the classes, of the resolvent part and of `θ` -/

/-! ### Functionals -/

/-- For `Re s > 2`: the local pairing of the resolvent expression is the box integral of
`u_s = E_Ψ(·, s) − h_s`. -/
theorem coeffFunctional_resPart (hG : Good 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) {s : ℂ} (hs : 2 < s.re) (hD : EisEigen Ψ s) (n : ℕ)
    (ψ : X F → ℂ) (hψ : Measurable ψ) (C : ℝ) (hC : ∀ P, ‖ψ P‖ ≤ C) :
    X.coeffFunctional Γ n ψ hψ C hC (resPart Γ Ψ s) =
      ∫ P in X.box n, conj (ψ P) * upart Ψ s P ∂X.vol F := by
  have hu2 := l2Rep_upart hG Γ hΓ hs
  rw [← uL2_eq_resPart hG Γ hΓ hs hD, uL2_eq hu2, X.coeffFunctional_apply]
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [X.lift_toL2 hu2] with P hP
  rw [hP]

/-! ### A bound for the cut-off part on compact sets -/

end

end ArtinKP.C5
end

section
-- module Solutions.Artin.KP.N_Shape
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

/-! ### The constant-term functional -/

/-! ### Fubini: a function with vanishing `x`-integrals over `D` is killed by `cf` -/

/-! ### The shape -/

lemma isCompact_box (n : ℕ) : IsCompact (X.box n : Set (X F)) :=
  isCompact_siegelBox (F := F) (m := 1 / ((n : ℝ) + 1)) (M := (n : ℝ) + 1) (B := n)
    (by positivity)

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.N_Cont
attribute [-simp] _root_.ArtinKP.S2.cubicSymbol_sym
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

lemma integrableOn_bdd_mul {n : ℕ} {ψ : X F → ℂ} (hψ : Measurable ψ) {C : ℝ}
    (hC : ∀ P, ‖ψ P‖ ≤ C) {f : X F → ℂ} (hf : IntegrableOn f (X.box n) (X.vol F)) :
    IntegrableOn (fun P => conj (ψ P) * f P) (X.box n) (X.vol F) := by
  refine Integrable.bdd_mul (c := C) hf
    (Complex.continuous_conj.measurable.comp hψ).aestronglyMeasurable ?_
  exact Eventually.of_forall fun P => by rw [RCLike.norm_conj]; exact hC P

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

/-- **Item 5 / MATH2 (C6)–(C7) in functional form.**  Let `ψ` be a bounded measurable test
function on `box n` (e.g. `RF.stripFn D ν φ`).  If `a` is holomorphic on `E.slit`, equals the
`ψ`-coefficient of the series `E_Ψ(·, s)` for `Re s > 2`, and `(s_t − s₀)·a(s_t) → r` along the
ray, then the `ψ`-coefficient of `θ_Ψ` is `r`. -/
theorem integral_box_theta_eq_of_tendsto_ray_oai (hG : Good 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) (hE : ∀ s : ℂ, 2 < s.re → EisEigen Ψ s) (n : ℕ)
    (ψ : X F → ℂ) (hψ : Measurable ψ) (C : ℝ) (hC : ∀ P, ‖ψ P‖ ≤ C) {a : ℂ → ℂ}
    (ha : DifferentiableOn ℂ a E.slit)
    (heq : ∀ s : ℂ, 2 < s.re → a s = ∫ P in X.box n, conj (ψ P) * eis Ψ s P ∂X.vol F) {r : ℂ}
    (hr : Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) * a (ray t)) (𝓝[>] 0) (𝓝 r)) :
    ∫ P in X.box n, conj (ψ P) * X.lift Γ (theta Γ Ψ) P ∂X.vol F = r := by
  set ℓ := X.coeffFunctional Γ n ψ hψ C hC with hℓ
  have hH := differentiable_hInt hG.ne_bot Ψ n hψ hC
  have hb : EqOn (fun s => ℓ (resPart Γ Ψ s) + hInt Ψ n ψ s) a E.slit := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ) (z₀ := (3 : ℂ)) ?_ ?_
      E.isPreconnected_slit ⟨by norm_num, fun _ => by norm_num⟩ ?_
    · have hd1 : DifferentiableOn ℂ (fun s => ℓ (resPart Γ Ψ s) + hInt Ψ n ψ s) E.slit :=
        ((differentiableOn_functional_resPart hG Γ hΓ ℓ).mono slit_subset_Omega).add
          hH.differentiableOn
      exact hd1.analyticOnNhd isOpen_slit
    · exact ha.analyticOnNhd isOpen_slit
    · filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (2 : ℝ) < (3 : ℂ).re by norm_num)] with s hs
      have hs' : 2 < s.re := hs
      have hEc : IntegrableOn (fun P : X F => eis Ψ s P) (X.box n) (X.vol F) :=
        (continuous_eis hG.ne_bot Ψ hs').continuousOn.integrableOn_compact (isCompact_box n)
      have hhc : IntegrableOn (hpart Ψ s) (X.box n) (X.vol F) :=
        (smooth_hpart hG.ne_bot Ψ s).continuous.continuousOn.integrableOn_compact
          (isCompact_box n)
      rw [heq s hs']
      change ℓ (resPart Γ Ψ s) + hInt Ψ n ψ s = _
      rw [hℓ, coeffFunctional_resPart hG Γ hΓ hs' (hE s hs') n ψ hψ C hC]
      unfold hInt
      have hup : IntegrableOn (upart Ψ s) (X.box n) (X.vol F) := hEc.sub hhc
      rw [← integral_add (integrableOn_bdd_mul hψ hC hup) (integrableOn_bdd_mul hψ hC hhc)]
      refine integral_congr_ae (Eventually.of_forall fun P => ?_)
      simp only [upart]
      ring
  have h1 := tendsto_ray_functional_resPart_theta hG Γ hΓ ℓ
  have h2 := tendsto_ray_mul_zero (g := hInt Ψ n ψ) hH.continuous.continuousAt
  have h3 : Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) * a (ray t)) (𝓝[>] 0)
      (𝓝 (ℓ (theta Γ Ψ) + 0)) := by
    refine (h1.add h2).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [← hb (ray_mem_slit ht)]
    simp only [ray]
    ring
  have h4 := tendsto_nhds_unique h3 hr
  rw [← X.coeffFunctional_apply Γ n ψ hψ C hC]
  rw [add_zero] at h4
  exact h4

/-! ### Frequency `0`: the residue of the `ht^{2−s}`-coefficient -/

end

end ArtinKP.N
end

theorem solution.{u_1} : type_of% @ArtinKP.N.integral_box_theta_eq_of_tendsto_ray_oai.{u_1} := @ArtinKP.N.integral_box_theta_eq_of_tendsto_ray_oai.{u_1}
