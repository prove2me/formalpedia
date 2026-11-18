-- Prove2me | solution 1 for ArtinKP.GK.theta_per_gen_of_isExterior
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:12:51.862713+00:00
-- url     : https://prove2.me/submissions/d018a0ca-d6e8-4b87-b741-6b1470f655d8

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
import Theorems.Thm_ArtinKP_C5_exists_single
import Theorems.Thm_ArtinKP_C5_l2Rep_src
import Theorems.Thm_ArtinKP_F_hasCoefT_restrict
import Theorems.Thm_ArtinKP_F_hasCoef_adm
import Theorems.Thm_ArtinKP_F_zPsi_add
import Theorems.Thm_ArtinKP_F_zPsi_restrict_twist
import Theorems.Thm_ArtinKP_F_zPsi_smul
import Theorems.Thm_ArtinKP_F_zPsi_sum
import Theorems.Thm_ArtinKP_F_zPsi_translate_nMat
import Theorems.Thm_ArtinKP_FB_U_eis_primeElt
import Theorems.Thm_ArtinKP_FB_primeElt_gen_of_good
import Theorems.Thm_ArtinKP_N2_theta_eq_zero_iff_forall_zPsi_translate_eq_zero
import Theorems.Thm_ArtinKP_T_HasCoefT_smulFun
import Theorems.Thm_ArtinKP_T_hasCoef_transLat
import Theorems.Thm_ArtinKP_T_hasSeed
import Theorems.Thm_ArtinKP_T_integral_theta_of_hasCoef
import Theorems.Thm_ArtinKP_T_integral_theta_of_hasCoefT
import Theorems.Thm_ArtinKP_T_resSlit_add_of_seed
import Theorems.Thm_ArtinKP_T_resSlit_mul_of_seed
import Theorems.Thm_ArtinKP_T_tau_smulFun
import Theorems.Thm_ArtinKP_X_X_isPOU_pou
import Theorems.Thm_ArtinKP_X_X_tsum_indicator_box_le_boxMult

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

end X

/-! ### Topology and measure -/

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

variable [IsTotallyComplex F]

/-! ### The lattice `𝓞_F ⊂ ℂ^r` -/

lemma isFund : IsAddFundamentalDomain (latSub F) (fundD F) volume :=
  ZSpan.isAddFundamentalDomain' (latE (F := F)) volume

/-! ### Scaling -/

/-! ### Orbits of the translations on the classes `≠ ∞` -/

/-! ### The constant term -/

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

lemma rsum_one (c : R) [Finite (R ⧸ Ideal.span {c})] :
    rsum c (fun _ => 1) = (Nat.card (R ⧸ Ideal.span {c}) : ℂ) := by
  unfold rsum
  have := Fintype.ofFinite (R ⧸ Ideal.span {c})
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
  simp

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
-- module Solutions.Artin.KP.S_Twisted
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.B.Row.inf_c _root_.ArtinKP.RO.rowClassEquiv_mk _root_.ArtinKP.RO.rowPair_c _root_.ArtinKP.RO.rowPair_d _root_.ArtinKP.S.GSection.twist_apply
/-!
# WP-S, part 3: twisted sections on primitive rows

A *twisted section* (`TSection`) is MATH2's `Ψ_s = κ·Φ_s` restricted to primitive pairs of `R`:
a family `Ψ : ℂ → Row 𝔪 → ℂ`, entire in `s`, with

* `hom`: `Ψ_s(εp) = |ε|_{S_f}^{-s} Ψ_s(p)` for `ε ∈ U_S` (**no symbol**: the factor `⟨c, ε⟩` of the
  genuine section is cancelled by `κ(εp) = ⟨c, ε⟩⁻¹ κ(p)`, `kappaRow_smul`);
* `bound`: `|Ψ_s(p)| ≤ B ‖p‖^{-Re s}`, `B` uniform for `|s| ≤ M`;
* `level`: `Ψ_s(pγ) = κ(γ) Ψ_s(p)` for `γ ∈ Γ(𝔫)`, some `𝔫 ≠ 0`.

`SL₂(R)` acts by plain right translation (`TSection.translate`), with no cocycle; the
Eisenstein series `E_Ψ(P, s) = Σ_{p ∈ Row/U_S} Ψ_s(p) I_p(P)^s` then satisfies
`E_Ψ(γP) = E_{γ·Ψ}(P)` by reindexing `p ↦ pγ`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S

open ArtinKP.A

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### Comparison of norms -/

/-! ### Twisted sections -/

/-! ### `Ψ ↦ Ψ · 1[P ∤ c]` for an exterior prime -/

namespace TSection

variable {ι : F →+* ℂ}

theorem restrict_apply_of_val {v : HeightOneSpectrum (𝓞 F)} (hv : ¬ 𝔪 ≤ v.asIdeal)
    (Ψ : TSection ι 𝔪) (s : ℂ) {p : Row 𝔪} (h : v.valuation F (p.c : F) = 1) :
    restrict v hv Ψ s p = Ψ s p := by
  simp [restrict, h]

theorem restrict_apply_of_not_val {v : HeightOneSpectrum (𝓞 F)} (hv : ¬ 𝔪 ≤ v.asIdeal)
    (Ψ : TSection ι 𝔪) (s : ℂ) {p : Row 𝔪} (h : v.valuation F (p.c : F) ≠ 1) :
    restrict v hv Ψ s p = 0 := by
  simp [restrict, h]

end TSection

end ArtinKP.S
end
end

section
-- module Solutions.Artin.KP.B_Def
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-! ### The product formula for `S`-units -/

theorem Ninf_pos {x : F} (hx : x ≠ 0) : 0 < Ninf x :=
  Finset.prod_pos fun _ _ => Complex.normSq_pos.mpr ((map_ne_zero _).mpr hx)

/-! ### Rows modulo `S`-units -/

/-! ### Convergence of the height series over row classes (from WP-B1) -/

/-! ### The summand and the series -/

/-! ### Height form (MATH2 §0.2) -/

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.B_Def2
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-! ### Automorphy by reindexing -/

theorem _root_.ArtinKP.S.TSection.mem_stab {Ψ : TSection ι 𝔪} {γ : SL(2, SInt 𝔪)} :
    γ ∈ Ψ.stab ↔ ∀ (s : ℂ) (p : Row 𝔪), Ψ s (p.act γ) = Ψ s p := Iff.rfl

/-! ### The term at the class of `(0, 1)` -/

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.K_Jacquet
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

theorem archChar_zero : archChar 0 = 1 := by simp [archChar]

theorem continuous_archChar : Continuous archChar := by
  unfold archChar; fun_prop

/-! ## Radial integrals on `ℂ` (copied from OpenAI) -/

lemma integral_radial_sq (f : ℝ → ℂ) :
    (∫ z : ℂ, f (‖z‖ ^ 2)) = (Real.pi : ℂ) * ∫ t : ℝ in Set.Ioi 0, f t := by
  have hball : (volume : Measure ℂ).real (Metric.ball 0 1) = Real.pi := by
    simp [Measure.real, Complex.volume_ball]
  have hpolar := integral_fun_norm_addHaar (volume : Measure ℂ) (fun r : ℝ => f (r^2))
  have hsub := integral_comp_rpow_Ioi (E := ℂ) f (p := 2) (by norm_num)
  norm_num [Real.rpow_two, Real.rpow_one] at hsub
  simp only [Complex.finrank_real_complex, hball, Nat.reduceSub, pow_one,
    nsmul_eq_mul, Complex.real_smul, ] at hpolar hsub
  rw [hpolar]
  rw [← hsub]
  rw [show (fun x : ℝ => (2:ℂ)*x*f (x^2)) =
      (fun x : ℝ => (2:ℂ)*(x*f (x^2))) by funext x; ring, integral_const_mul]
  ring

lemma integrable_radial_sq_iff (f : ℝ → ℂ) :
    Integrable (fun z : ℂ => f (‖z‖ ^ 2)) ↔ IntegrableOn f (Set.Ioi 0) := by
  rw [integrable_fun_norm_addHaar (volume : Measure ℂ) (f := fun r : ℝ => f (r^2))]
  have h := integrableOn_Ioi_comp_rpow_iff' (E := ℂ) f (p := 2) (by norm_num)
  simpa only [Complex.finrank_real_complex, Nat.reduceSub, pow_one,
    show (2:ℝ)-1=1 by norm_num, Real.rpow_one, Real.rpow_two] using h

lemma add_one_image_Ioi : (fun x : ℝ => x+1) '' Set.Ioi 0 = Set.Ioi 1 := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    simp only [Set.mem_Ioi] at *
    linarith
  · intro hy
    refine ⟨y-1, ?_, by ring⟩
    simp only [Set.mem_Ioi] at *
    linarith

lemma integrable_add_one_Ioi_iff (f : ℝ → ℂ) :
    IntegrableOn (fun x : ℝ => f (x+1)) (Set.Ioi 0) ↔ IntegrableOn f (Set.Ioi 1) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi
    (fun x (hx : x ∈ Set.Ioi (0:ℝ)) => (hasDerivAt_id x |>.add_const 1).hasDerivWithinAt)
    (fun x hx y hy hxy => by dsimp at hxy; linarith : InjOn (fun x : ℝ => x+1) (Set.Ioi 0)) f
  simp only [id_eq] at h
  rw [add_one_image_Ioi] at h
  simpa only [abs_one, one_smul] using h.symm

lemma integral_add_one_Ioi (f : ℝ → ℂ) :
    (∫ x : ℝ in Set.Ioi 0, f (x+1)) = ∫ x : ℝ in Set.Ioi 1, f x := by
  have h := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi
    (fun x (hx : x ∈ Set.Ioi (0:ℝ)) => (hasDerivAt_id x |>.add_const 1).hasDerivWithinAt)
    (fun x hx y hy hxy => by dsimp at hxy; linarith : InjOn (fun x : ℝ => x+1) (Set.Ioi 0)) f
  simp only [id_eq] at h
  rw [add_one_image_Ioi] at h
  simpa only [abs_one, one_smul] using h.symm

lemma hyperbolicKernel_integrable (s : ℂ) (hs : 1 < s.re) :
    Integrable (hyperbolicKernel s) := by
  unfold hyperbolicKernel
  rw [integrable_radial_sq_iff (fun t : ℝ => ((1+t : ℝ) : ℂ)^(-s))]
  have h := (integrable_add_one_Ioi_iff (fun x : ℝ => (x : ℂ)^(-s))).mpr
    (integrableOn_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs) (by norm_num : (0:ℝ)<1))
  simpa only [add_comm] using h

theorem integral_hyperbolicKernel (s : ℂ) (hs : 1 < s.re) :
    (∫ z : ℂ, hyperbolicKernel s z) = (Real.pi : ℂ) / (s-1) := by
  unfold hyperbolicKernel
  rw [integral_radial_sq (fun t : ℝ => ((1+t : ℝ) : ℂ)^(-s))]
  simp_rw [add_comm (1:ℝ)]
  rw [integral_add_one_Ioi (fun t : ℝ => (t : ℂ)^(-s))]
  rw [integral_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs) (by norm_num : (0:ℝ)<1)]
  simp only [Complex.ofReal_one, Complex.one_cpow]
  have hn : (-s+1)⁻¹ = -(s-1)⁻¹ := by
    rw [show -s+1=-(s-1) by ring, inv_neg]
  simp only [div_eq_mul_inv, hn]
  ring

lemma continuous_hyperbolicKernel (s : ℂ) : Continuous (hyperbolicKernel s) := by
  unfold hyperbolicKernel
  apply Continuous.cpow
  · fun_prop
  · exact continuous_const
  · intro z
    exact Complex.ofReal_mem_slitPlane.mpr (by positivity)

lemma sourceFourierKernel_zero (s : ℂ) (hs : 1 < s.re) :
    sourceFourierKernel s 0 = (Real.pi : ℂ)/(s-1) := by
  simpa only [sourceFourierKernel, neg_zero, zero_mul, archChar_zero, mul_one]
    using integral_hyperbolicKernel s hs

/-! ## The Bessel form (ours, for `besselK`) -/

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

/-! ## Holomorphy in `s` -/

end

end ArtinKP.K
end

section
-- module Solutions.Artin.KP.S_Ops
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.S.GSection.instAddCommMonoid _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.G1.scal_apply _root_.ArtinKP.S2.cubicSymbol_sym
/-!
# WP-S, part 5: operations on genuine sections

* `GSection.nT t`: `(n(t)Φ)_s(c, d) = Φ_s(c, d + ct)`, `t ∈ F` (no symbol).
* `wFun`: `(wΦ)_s(c, d) = ⟨c, d⟩ Φ_s(d, -c)`; `twist_wFun`: its twist is the `w`-translate of the
  twist of `Φ` (MATH §5.2; the symbol is `σ_S((c,d), w)⁻¹·κ(w) = ⟨c, d⟩`).
* `GSection.torus β`: `(A(β)Φ)_s(c, d) = ⟨c, β⟩² Φ_s(β²c, βd)` for `c ≠ 0`, and
  `⟨d, β⟩ Φ_s(0, βd)` on the cell `c = 0` (MATH2 §6.1, with the `c = 0` factor decided by proof);
  `GSection.torusT β = |β|^{2s-1} A(β)` is `Ã(β)`.
  `torus_torus`: `A(β) A(β') = ⟨β, β'⟩ A(β β')`.
* `GSection.sharp π`: `Φ♯_s(c, d) = Φ_s(c, d/π³)`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S

open ArtinKP.A

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### The Weyl element -/

/-! ### The formal torus action `A(β)` -/

namespace GSection

variable {ι : F →+* ℂ} {P : CubicPkg F}

theorem cpow_sq_cancel {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x : ℂ) ^ (6 * s) * ((x ^ 2 : ℝ) : ℂ) ^ (-(3 * s)) = 1 := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hx2 : ((x ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (pow_pos hx 2).ne'
  rw [Complex.cpow_def_of_ne_zero hx0, Complex.cpow_def_of_ne_zero hx2, ← Complex.exp_add,
    ← Complex.ofReal_log hx.le, ← Complex.ofReal_log (pow_pos hx 2).le, Real.log_pow]
  push_cast
  ring_nf
  exact Complex.exp_zero

theorem sharp_apply (hG : Good 𝔪) (π : F) (hπ : π ≠ 0) (Φ : GSection ι P 𝔪) (s : ℂ) (c d : F) :
    Φ.sharp hG π hπ s c d = Φ s c (d / π ^ 3) := by
  have htf : tf ι P 𝔪 (π ^ 3) c d = 1 := by
    unfold tf
    split_ifs
    · exact brk_pow_three_right _ _
    · rw [brk_pow_three_right, one_pow]
  have e1 : (π ^ 3) ^ 2 * c = (π ^ 2) ^ 3 * c := by ring
  have e2 : π ^ 3 * d = (π ^ 2) ^ 3 * (d / π ^ 3) := by field_simp
  change ((absS 𝔪 π : ℝ) : ℂ) ^ (6 * s) * (tf ι P 𝔪 (π ^ 3) c d
    * Φ s ((π ^ 3) ^ 2 * c) (π ^ 3 * d)) = _
  rw [htf, one_mul, e1, e2, Φ.cube s (π ^ 2) (pow_ne_zero 2 hπ), absS_pow, ← mul_assoc,
    cpow_sq_cancel (absS_pos hπ), one_mul]

end GSection

end ArtinKP.S
end
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

/-! ### The archimedean kernel -/

theorem norm_chiInf (ν : F) (x : InfinitePlace F → ℂ) : ‖chiInf ν x‖ = 1 := by
  rw [chiInf, RCLike.norm_conj, norm_eInf]

theorem chiInf_add (ν : F) (x y : InfinitePlace F → ℂ) :
    chiInf ν (x + y) = chiInf ν x * chiInf ν y := by
  rw [chiInf, mul_add, eInf_add, map_mul]
  rfl

theorem chiInf_emb (ν a : F) : chiInf ν (emb a) = conj (eInf (emb (ν * a))) := by
  rw [chiInf, emb_mul]

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
-- module Solutions.Artin.KP.E_Link
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # E_Link: Theorem E over `R = SInt 𝔪` in the shape of the frozen statement

* `primeDatum_gen`: at a good exterior prime `P`, `π = g.gen P` satisfies `PrimeDatum` with
  `g₁ = tau P 2`, `g₂ = tau P 4` (B7's table).
* `wloc_eq`: at `s₀ = 4/3`, `w_P(e) = (N P)^{e/3} · Wv P e` (`Wv` of the frozen statement).
* `theoremE_SInt`: `τ_Φ(ν) = N(𝔷)^{1/3} · ∏_{P ∣ 𝔷} Wsph P (v_P 𝔷) (ν / gen(P)^{v_P 𝔷}) · τ_{Ã(ν)Φ}(1)`
  for `νR = 𝔷R`, `𝔷` exterior.
* `exists_cutoff_theoremE`: the same as one cutoff statement with the `let`s of the frozen goal
  copied verbatim.

Of `AllowedGen` only `span_gen` is used (through B7 and `L3V`): `gen_mul` and `reciprocity` are
not needed.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinKP.E

open ArtinPrimitiveRoots ArtinKP.B7

lemma hx_of_nat (q : ℕ) (hq : 0 < q) :
    (q : ℂ) ^ 4 * ((q : ℂ) ^ (-(4 / 3 : ℂ))) ^ 3 = 1 := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [← Complex.cpow_nat_mul,
    show ((3 : ℕ) : ℂ) * -(4 / 3 : ℂ) = -((4 : ℕ) : ℂ) by push_cast; ring, Complex.cpow_neg,
    Complex.cpow_natCast]
  exact mul_inv_cancel₀ (pow_ne_zero _ hq0)

/-! ### The global statement -/

end ArtinKP.E
end

section
-- module Solutions.Artin.KP.B_FourThm
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.B_Kub
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-B, part 9: the Kubota series — convergence, holomorphy, the `E.Kubota` instance

* `kTerm`, `aCoeff`: `𝔞_Φ(ν, s) = ∑_{c ∈ (R∖0)/Rˣ} g(ν, c) · Lam Φ c ν s · N(c)^{-s}`, for every
  `ν ∈ R` (`ν = 0` gives the Dirichlet series of the constant term), with
  `Lam = S2.LamR ψ_{S_f}` (WP-S2's normalized finite Jacquet functional at a valid depth).
* `exists_majorant_kTerm`: locally uniform absolute convergence on `Re s > 2`
  (`|g(ν,c)| ≤ N(c)`, `S2.norm_Lam_le`, S-1, `∑ N(c)^{1-σ} < ∞`).
* `differentiableOn_aCoeff`: holomorphy on `Re s > 2`.
* `kubota hG hz6 : E.Kubota (S2.cubicSymbol …) (B7.sAdd 𝔪 _) (GSection ι P 𝔪)` — no hypothesis left.
* `fourier_coeff_aSer`, `const_term_aCoeff`: the Fourier coefficients in this normalization.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E ArtinKP.K ArtinKP.B7

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

variable [IsTotallyComplex F] (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  (Φ : GSection ι P 𝔪) (ν : SInt 𝔪)

theorem kubota_act (β : SInt 𝔪) : (kubota hG hz6).act β Φ = S2.actR hG β Φ := rfl

/-- A valid depth exists for every section and frequency. -/
theorem exists_validDepth (ν : F) : ∃ M : ℤ, ValidDepth hG Φ ν M := by
  obtain ⟨M, h1, h2⟩ := S2.exists_valid hG (psiS hG.ne_bot) Φ ν
  exact ⟨M, h1, h2⟩

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.BZ_Vol
attribute [-instance] _root_.ArtinKP.N.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinKP.X.instSigmaFiniteE1Mu1 _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-BZ, part 4: stub B-2 — the covolume of the translation lattice `Λ_M`

* `exists_fund_sublattice`, `measure_fund_sublattice` (Mathlib only): for countable subgroups
  `L' ≤ L` of finite index of a measurable additive group with an invariant measure, a
  fundamental domain of `L'` has measure `[L : L'] ·` that of a fundamental domain of `L`.
* `card_transLat_quot`: `[Λ_M : Λ_{M'}] = ∏_{v ∣ 𝔪} q_v^{M' - M}` for `M ≤ M'`
  (`S2.card_latD_quot` transported by strong approximation `F = R + 𝔩_{M'}`).
* `transLat_zero`: `Λ_0 = emb(𝓞_F)`.
* **`volume_cell`** (B-2): `vol(D) · vol(𝔩_M) = vol(B1.fundD F)` for every fundamental cell `D`
  of `Λ_M`, every `M : ℤ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Pointwise
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.BZ

/-! ### Fundamental domains of a sublattice -/

section abstract

variable {E : Type*} [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd E]
  (μ : Measure E) [μ.IsAddLeftInvariant]

/-- From a fundamental domain of `L` to one of a subgroup `L' ≤ L` of finite index. -/
theorem exists_fund_sublattice {L' L : AddSubgroup E} [Countable L] (hle : L' ≤ L)
    [Finite (L ⧸ L'.addSubgroupOf L)] {D : Set E} (hD : IsAddFundamentalDomain L D μ) :
    ∃ D' : Set E, IsAddFundamentalDomain L' D' μ ∧
      μ D' = (Nat.card (L ⧸ L'.addSubgroupOf L) : ENNReal) * μ D := by
  classical
  set K := L'.addSubgroupOf L with hK
  let σ : L ⧸ K → L := fun q => Quotient.out q
  have hσ : ∀ q, (QuotientAddGroup.mk (σ q) : L ⧸ K) = q := fun q => Quotient.out_eq q
  have hσinj : ∀ q₁ q₂ : L ⧸ K, ((σ q₁ : L) : E) - ((σ q₂ : L) : E) ∈ L' → q₁ = q₂ := by
    intro q₁ q₂ h
    rw [← hσ q₁, ← hσ q₂, QuotientAddGroup.eq, hK, AddSubgroup.mem_addSubgroupOf]
    have : ((-(σ q₁) + σ q₂ : L) : E) = -(((σ q₁ : L) : E) - ((σ q₂ : L) : E)) := by
      push_cast
      abel
    rw [this]
    exact L'.neg_mem h
  let f : L ⧸ K → Set E := fun q => (σ q : L) +ᵥ D
  have hfm : ∀ q, NullMeasurableSet (f q) μ := fun q => hD.nullMeasurableSet_vadd (σ q)
  have hfd : Pairwise (Function.onFun (AEDisjoint μ) f) := by
    intro q₁ q₂ hq
    refine hD.aedisjoint fun h => hq (hσinj q₁ q₂ ?_)
    rw [h, sub_self]
    exact L'.zero_mem
  refine ⟨⋃ q, f q, ⟨NullMeasurableSet.iUnion hfm, ?_, ?_⟩, ?_⟩
  · -- covering
    filter_upwards [hD.ae_covers] with x hx
    obtain ⟨g, hg⟩ := hx
    set q : L ⧸ K := QuotientAddGroup.mk (-g) with hq
    have hmem : ((σ q : L) : E) + (g : E) ∈ L' := by
      have h1 : (QuotientAddGroup.mk (σ q) : L ⧸ K) = QuotientAddGroup.mk (-g) := hσ q
      rw [QuotientAddGroup.eq, hK, AddSubgroup.mem_addSubgroupOf] at h1
      have h2 : ((σ q : L) : E) + (g : E) = -((-(σ q) + -g : L) : E) := by
        push_cast
        abel
      rw [h2]
      exact L'.neg_mem h1
    refine ⟨⟨_, hmem⟩, Set.mem_iUnion.2 ⟨q, ?_⟩⟩
    refine ⟨g +ᵥ x, hg, ?_⟩
    change ((σ q : L) : E) + ((g : E) + x) = (((σ q : L) : E) + (g : E)) + x
    rw [add_assoc]
  · -- disjointness
    intro g₁ g₂ hg
    change AEDisjoint μ (g₁ +ᵥ ⋃ q, f q) (g₂ +ᵥ ⋃ q, f q)
    rw [Set.vadd_set_iUnion, Set.vadd_set_iUnion, AEDisjoint.iUnion_left_iff]
    intro q₁
    rw [AEDisjoint.iUnion_right_iff]
    intro q₂
    have e : ∀ (g : L') (q : L ⧸ K),
        g +ᵥ f q = ((⟨(g : E), hle g.2⟩ + σ q : L)) +ᵥ D := by
      intro g q
      ext y
      constructor
      · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
        exact ⟨w, hw, by
          change ((g : E) + ((σ q : L) : E)) + w = (g : E) + (((σ q : L) : E) + w)
          rw [add_assoc]⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨(σ q : L) +ᵥ w, ⟨w, hw, rfl⟩, by
          change (g : E) + (((σ q : L) : E) + w) = ((g : E) + ((σ q : L) : E)) + w
          rw [add_assoc]⟩
    rw [e, e]
    refine hD.aedisjoint fun h => hg ?_
    have h' : (g₁ : E) + ((σ q₁ : L) : E) = (g₂ : E) + ((σ q₂ : L) : E) :=
      congrArg (fun z : L => (z : E)) h
    have hq : q₁ = q₂ := by
      refine hσinj q₁ q₂ ?_
      have : ((σ q₁ : L) : E) - ((σ q₂ : L) : E) = (g₂ : E) - (g₁ : E) := by
        rw [sub_eq_sub_iff_add_eq_add, add_comm, h', add_comm]
      rw [this]
      exact L'.sub_mem g₂.2 g₁.2
    rw [hq] at h'
    exact Subtype.ext (add_right_cancel h')
  · -- measure
    let _ := Fintype.ofFinite (L ⧸ K)
    rw [measure_iUnion₀ hfd hfm, tsum_fintype]
    have : ∀ q, μ (f q) = μ D := fun q => by
      change μ (((σ q : L) : E) +ᵥ D) = μ D
      exact measure_vadd μ _ D
    rw [Finset.sum_congr rfl fun q _ => this q, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Nat.card_eq_fintype_card]

/-- A fundamental domain of a sublattice `L' ≤ L` of finite index has measure
`[L : L'] · μ(D)`. -/
theorem measure_fund_sublattice {L' L : AddSubgroup E} [Countable L] (hle : L' ≤ L)
    [Finite (L ⧸ L'.addSubgroupOf L)] {D D' : Set E} (hD : IsAddFundamentalDomain L D μ)
    (hD' : IsAddFundamentalDomain L' D' μ) :
    μ D' = (Nat.card (L ⧸ L'.addSubgroupOf L) : ENNReal) * μ D := by
  have : Countable L' := (AddSubgroup.inclusion_injective hle).countable
  obtain ⟨D'', h1, h2⟩ := exists_fund_sublattice μ hle hD
  rw [← h2]
  exact hD'.measure_eq h1

end abstract

/-- Two surjective homomorphisms with the same kernel have equinumerous targets. -/
theorem card_eq_of_ker_eq {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B) (g : A →+ C) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : f.ker = g.ker) : Nat.card B = Nat.card C := by
  rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hf).toEquiv,
    ← Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective g hg).toEquiv, h]

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

theorem transLat_mono {M M' : ℤ} (h : M ≤ M') : transLat 𝔪 M' ≤ transLat 𝔪 M := by
  rintro x ⟨b, hb, rfl⟩
  exact ⟨b, Small.mono (𝔪 := 𝔪) h hb, rfl⟩

theorem embR_mem_transLat {M : ℤ} {b : SInt 𝔪} :
    (embR b : InfinitePlace F → ℂ) ∈ transLat 𝔪 M ↔ b ∈ latR 𝔪 M := by
  constructor
  · rintro ⟨b', hb', h⟩
    rwa [← embR_injective h]
  · intro hb
    exact ⟨b, hb, rfl⟩

/-- `[Λ_M : Λ_{M'}] = ∏_{v ∣ 𝔪} q_v^{M' - M}` for `M ≤ M'`. -/
theorem card_transLat_quot (h𝔪 : 𝔪 ≠ ⊥) {M M' : ℤ} (h : M ≤ M') :
    Nat.card (transLat 𝔪 M ⧸ (transLat 𝔪 M').addSubgroupOf (transLat 𝔪 M))
      = ∏ v ∈ CubicPkg.sFin 𝔪, Ideal.absNorm v.asIdeal ^ (M' - M).toNat := by
  rw [← S2.card_latD_quot h𝔪 (k := fun _ => M) (k' := fun _ => M') fun _ _ => h]
  -- the two maps out of `R ∩ 𝔩_M`
  let f₀ : latR 𝔪 M →+ transLat 𝔪 M := (embR (𝔪 := 𝔪)).addSubgroupMap (latR 𝔪 M)
  have hf₀ : Function.Surjective f₀ := (embR (𝔪 := 𝔪)).addSubgroupMap_surjective (latR 𝔪 M)
  let g₀ : latR 𝔪 M →+ S2.latD 𝔪 (fun _ => M) :=
    { toFun := fun b => ⟨((b : SInt 𝔪) : F), b.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let f : latR 𝔪 M →+ transLat 𝔪 M ⧸ (transLat 𝔪 M').addSubgroupOf (transLat 𝔪 M) :=
    (QuotientAddGroup.mk' _).comp f₀
  let g : latR 𝔪 M →+
      S2.latD 𝔪 (fun _ => M) ⧸ (S2.latD 𝔪 (fun _ => M')).addSubgroupOf (S2.latD 𝔪 (fun _ => M)) :=
    (QuotientAddGroup.mk' _).comp g₀
  have hf : Function.Surjective f := (QuotientAddGroup.mk'_surjective _).comp hf₀
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
    obtain ⟨r, hr⟩ := exists_sInt_sub_small h𝔪 M' (x : F)
    have hrM : Small 𝔪 M ((r : SInt 𝔪) : F) := by
      have h1 : Small 𝔪 M ((x : F) - (r : F)) := Small.mono (𝔪 := 𝔪) h hr
      have h2 : Small 𝔪 M (x : F) := x.2
      have := h2.sub h1
      rwa [sub_sub_cancel] at this
    refine ⟨⟨r, hrM⟩, ?_⟩
    change (QuotientAddGroup.mk (g₀ ⟨r, hrM⟩) : S2.latD 𝔪 (fun _ => M) ⧸ _) = QuotientAddGroup.mk x
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    change Small 𝔪 M' (-((r : SInt 𝔪) : F) + (x : F))
    rwa [neg_add_eq_sub]
  refine card_eq_of_ker_eq f g hf hg ?_
  ext b
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker]
  change (QuotientAddGroup.mk (f₀ b) : transLat 𝔪 M ⧸ _) = 0 ↔
    (QuotientAddGroup.mk (g₀ b) : S2.latD 𝔪 (fun _ => M) ⧸ _) = 0
  rw [QuotientAddGroup.eq_zero_iff, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf,
    AddSubgroup.mem_addSubgroupOf]
  change (embR (b : SInt 𝔪) : InfinitePlace F → ℂ) ∈ transLat 𝔪 M' ↔ _
  rw [embR_mem_transLat]
  rfl

variable [IsTotallyComplex F]

/-- `Λ_0 = emb(𝓞_F)`. -/
theorem transLat_zero (𝔪 : Ideal (𝓞 F)) : transLat 𝔪 0 = latSub F := by
  ext x
  rw [mem_latSub]
  constructor
  · rintro ⟨b, hb, rfl⟩
    have hall : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F ((b : SInt 𝔪) : F) ≤ 1 := by
      intro v
      by_cases hv : 𝔪 ≤ v.asIdeal
      · have := hb v hv
        rwa [neg_zero, WithZero.exp_zero] at this
      · exact sInt_val_le_one b v hv
    obtain ⟨β, hβ⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F _ hall
    exact ⟨β, by rw [embR_apply, ← hβ]⟩
  · rintro ⟨β, rfl⟩
    refine ⟨algebraMap (𝓞 F) (SInt 𝔪) β, fun v _ => ?_, rfl⟩
    rw [neg_zero, WithZero.exp_zero]
    exact v.valuation_le_one β

/-- **Stub B-2, proved** (only `𝔪 ≠ ⊥` is used): `vol(D) · vol(𝔩_M) = covol(𝓞_F)`. -/
theorem volume_cell' (h𝔪 : 𝔪 ≠ ⊥) (M : ℤ) {D : Set (InfinitePlace F → ℂ)}
    (hD : IsAddFundamentalDomain (transLat 𝔪 M) D volume) :
    volume D * ENNReal.ofReal (vol 𝔪 M) = volume (B1.fundD F) := by
  classical
  set M' : ℤ := max M 0 with hM'
  have h1 : M ≤ M' := le_max_left _ _
  have h0 : (0 : ℤ) ≤ M' := le_max_right _ _
  have hq : ∀ v : HeightOneSpectrum (𝓞 F), 0 < Ideal.absNorm v.asIdeal := fun v => by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm v
    omega
  set n₁ : ℕ := ∏ v ∈ CubicPkg.sFin 𝔪, Ideal.absNorm v.asIdeal ^ (M' - M).toNat with hn₁
  set n₀ : ℕ := ∏ v ∈ CubicPkg.sFin 𝔪, Ideal.absNorm v.asIdeal ^ (M' - 0).toNat with hn₀
  have hn₁0 : n₁ ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (hq v).ne'
  have hn₀0 : n₀ ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (hq v).ne'
  have hc₁ := card_transLat_quot h𝔪 h1
  have hc₀ := card_transLat_quot h𝔪 h0
  have hfin₁ : Finite (transLat 𝔪 M ⧸ (transLat 𝔪 M').addSubgroupOf (transLat 𝔪 M)) :=
    Nat.finite_of_card_ne_zero (by rw [hc₁]; exact hn₁0)
  have hfin₀ : Finite (transLat 𝔪 0 ⧸ (transLat 𝔪 M').addSubgroupOf (transLat 𝔪 0)) :=
    Nat.finite_of_card_ne_zero (by rw [hc₀]; exact hn₀0)
  have hF : IsAddFundamentalDomain (transLat 𝔪 0) (B1.fundD F) volume := by
    rw [transLat_zero]
    exact B1.isFund
  obtain ⟨D', hD', hvol₀⟩ := exists_fund_sublattice volume (transLat_mono h0) hF
  have hvol₁ := measure_fund_sublattice volume (transLat_mono h1) hD hD'
  rw [hc₀] at hvol₀
  rw [hc₁] at hvol₁
  -- `vol 𝔪 M = n₁ / n₀`
  have hvolM : vol 𝔪 M = (n₁ : ℝ) / (n₀ : ℝ) := by
    rw [vol, hn₁, hn₀, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    have hqv : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by exact_mod_cast (hq v).ne'
    push_cast
    rw [← zpow_natCast, ← zpow_natCast, Int.toNat_of_nonneg (by omega),
      Int.toNat_of_nonneg (by omega), ← zpow_sub₀ hqv]
    congr 1
    ring
  have hn₀pos : (0 : ℝ) < n₀ := by exact_mod_cast Nat.pos_of_ne_zero hn₀0
  rw [hvolM, ENNReal.ofReal_div_of_pos hn₀pos, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
    ← mul_div_assoc, mul_comm (volume D), ← hvol₁, hvol₀, mul_comm,
    ENNReal.mul_div_cancel_right (by exact_mod_cast hn₀0) (ENNReal.natCast_ne_top n₀)]

end ArtinKP.BZ
end
end

section
-- module Solutions.Artin.KP.B_RO
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
attribute [-instance] _root_.ArtinKP.B.instCountableIdxI _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.B1.instCountablePairClass _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma chart_x (y : Coord F) (w : InfinitePlace F) : (chart F y).x w = (y w).1 := rfl
lemma chart_v (y : Coord F) (w : InfinitePlace F) : (chart F y).v w = Real.exp (y w).2 := rfl

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_L2
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
attribute [-instance] _root_.ArtinKP.B.instCountableIdxI _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.B.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupTransLat _root_.ArtinKP.B1.instCountablePairClass _root_.ArtinKP.B1.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatSub _root_.ArtinKP.N.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
-- module Solutions.Artin.KP.X2_H1
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma X.toL2_congr {f g : X F → ℂ} (hf : X.L2Rep Γ f) (hg : X.L2Rep Γ g) (h : f = g) :
    X.toL2 Γ f hf = X.toL2 Γ g hg := by
  subst h; rfl

/-! ### Local integrability of pull-backs -/

/-! ### The core -/

/-! ### Density of the core -/

/-! ### The symmetric operator and the energy space -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Prod
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
-- module Solutions.Artin.KP.C5_PE
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma pe_lin_weight (a₁ a₂ : PairClass S → ℂ) {g : ℝ → ℂ} (hg : VanishLow g) (c : ℂ) (P : X F) :
    pe S (fun p => c * a₁ p + a₂ p) g P = c * pe S a₁ g P + pe S a₂ g P := by
  obtain ⟨p₁, h⟩ := pe_single S P
  rw [h _ g hg, h a₁ g hg, h a₂ g hg]
  ring

/-! ### Smoothness and the Laplacian -/

/-! ### Support -/

end

end ArtinKP.C5
end

section
-- module Solutions.Artin.KP.C5_Profile
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma rt_low {τ : ℝ} (h : τ < Real.log 2) : rt τ = 0 := by
  unfold rt
  rw [rho_zero ((Real.lt_log_iff_exp_lt (by norm_num)).mp h).le]
  simp

lemma vanishLow_rt : VanishLow rt := fun _ h => rt_low h

lemma vanishLow_rt1 : VanishLow rt1 := vanishLow_rt.deriv

lemma vanishLow_rt2 : VanishLow rt2 := vanishLow_rt1.deriv

/-! ### The profile of `h_s` -/

variable {F : Type*} [Field F] [NumberField F]

/-! ### The eigenvalue and the profile of the source -/

lemma vanishLow_phiS (s : ℂ) : VanishLow (phiS F s) := fun τ h => by
  unfold phiS
  rw [vanishLow_rt1 τ h, vanishLow_rt2 τ h]
  simp

end

end ArtinKP.C5
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

lemma src_eq_pe (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) (s : ℂ) :
    src Ψ s = pe (RO.SOf 𝔪) (wt h𝔪 Ψ s) (phiS F s) :=
  funext fun Q => tsum_eq_pe h𝔪 Ψ s (phiS F s) Q

/-! ### The Eisenstein series on pair classes -/

/-! ### Invariance, regularity -/

/-! ### The source -/

end

end ArtinKP.C5
end

section
-- module Solutions.Artin.KP.C5_Main
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-! ### The classes in `L²(Γ\X)` -/

lemma srcL2_eq {Γ : Subgroup (SL(2, 𝓞 F))} {Ψ : TSection ι 𝔪} {s : ℂ}
    (h : X.L2Rep Γ (src Ψ s)) : srcL2 Γ Ψ s = X.toL2 Γ (src Ψ s) h := dif_pos h

/-! ### (C5) -/

/-! ### Continuation -/

/-! ### The limit (C7) -/

/-! ### `θ` is a weak eigenfunction -/

end

end ArtinKP.C5
end

section
-- module Solutions.Artin.KP.C5_Linear
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap _root_.ArtinKP.S.GSection.twist_apply
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

lemma wt_add (h𝔪 : 𝔪 ≠ ⊥) (Ψ Ψ' : TSection ι 𝔪) (s : ℂ) (p : PairClass (RO.SOf 𝔪)) :
    wt h𝔪 (Ψ + Ψ') s p = wt h𝔪 Ψ s p + wt h𝔪 Ψ' s p := by
  unfold wt tildeC TSection.tilde
  rw [TSection.add_apply]
  ring

lemma wt_smul (h𝔪 : 𝔪 ≠ ⊥) (c : ℂ) (Ψ : TSection ι 𝔪) (s : ℂ) (p : PairClass (RO.SOf 𝔪)) :
    wt h𝔪 (c • Ψ) s p = c * wt h𝔪 Ψ s p := by
  unfold wt tildeC TSection.tilde
  rw [TSection.smul_apply]
  ring

lemma Inv.add {Γ : Subgroup (SL(2, 𝓞 F))} {Ψ Ψ' : TSection ι 𝔪} (h : Inv Γ Ψ) (h' : Inv Γ Ψ') :
    Inv Γ (Ψ + Ψ') := fun γ hγ => TSection.mem_stab.mpr fun s p => by
  rw [TSection.add_apply, TSection.add_apply, TSection.mem_stab.mp (h γ hγ) s p,
    TSection.mem_stab.mp (h' γ hγ) s p]

lemma Inv.smul {Γ : Subgroup (SL(2, 𝓞 F))} {Ψ : TSection ι 𝔪} (h : Inv Γ Ψ) (c : ℂ) :
    Inv Γ (c • Ψ) := fun γ hγ => TSection.mem_stab.mpr fun s p => by
  rw [TSection.smul_apply, TSection.smul_apply, TSection.mem_stab.mp (h γ hγ) s p]

variable [IsTotallyComplex F]

lemma pe_wt_add (h𝔪 : 𝔪 ≠ ⊥) (Ψ Ψ' : TSection ι 𝔪) (s : ℂ) {g : ℝ → ℂ} (hg : VanishLow g)
    (Q : X F) :
    pe (RO.SOf 𝔪) (wt h𝔪 (Ψ + Ψ') s) g Q =
      pe (RO.SOf 𝔪) (wt h𝔪 Ψ s) g Q + pe (RO.SOf 𝔪) (wt h𝔪 Ψ' s) g Q := by
  have e : wt h𝔪 (Ψ + Ψ') s = fun p => 1 * wt h𝔪 Ψ s p + wt h𝔪 Ψ' s p :=
    funext fun p => by rw [wt_add, one_mul]
  rw [e, pe_lin_weight _ _ hg, one_mul]

lemma pe_wt_smul (h𝔪 : 𝔪 ≠ ⊥) (c : ℂ) (Ψ : TSection ι 𝔪) (s : ℂ) {g : ℝ → ℂ} (hg : VanishLow g)
    (Q : X F) :
    pe (RO.SOf 𝔪) (wt h𝔪 (c • Ψ) s) g Q = c * pe (RO.SOf 𝔪) (wt h𝔪 Ψ s) g Q := by
  have e : wt h𝔪 (c • Ψ) s = fun p => c * wt h𝔪 Ψ s p + (fun _ => (0 : ℂ)) p :=
    funext fun p => by rw [wt_smul, add_zero]
  have h0 : pe (RO.SOf 𝔪) (fun _ => (0 : ℂ)) g Q = 0 := by
    unfold pe
    simp
  rw [e, pe_lin_weight _ _ hg, h0, add_zero]

theorem src_add (h𝔪 : 𝔪 ≠ ⊥) (Ψ Ψ' : TSection ι 𝔪) (s : ℂ) (Q : X F) :
    src (Ψ + Ψ') s Q = src Ψ s Q + src Ψ' s Q := by
  rw [src_eq_pe h𝔪, src_eq_pe h𝔪, src_eq_pe h𝔪]
  exact pe_wt_add h𝔪 Ψ Ψ' s (vanishLow_phiS s) Q

theorem src_smul (h𝔪 : 𝔪 ≠ ⊥) (c : ℂ) (Ψ : TSection ι 𝔪) (s : ℂ) (Q : X F) :
    src (c • Ψ) s Q = c * src Ψ s Q := by
  rw [src_eq_pe h𝔪, src_eq_pe h𝔪]
  exact pe_wt_smul h𝔪 c Ψ s (vanishLow_phiS s) Q

/-! ### Linearity of the classes, of the resolvent part and of `θ` -/

theorem srcL2_add (hG : Good 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    {Ψ Ψ' : TSection ι 𝔪} (hΓ : Inv Γ Ψ) (hΓ' : Inv Γ Ψ') (s : ℂ) :
    srcL2 Γ (Ψ + Ψ') s = srcL2 Γ Ψ s + srcL2 Γ Ψ' s := by
  rw [srcL2_eq (l2Rep_src hG Γ (hΓ.add hΓ') s), srcL2_eq (l2Rep_src hG Γ hΓ s),
    srcL2_eq (l2Rep_src hG Γ hΓ' s), ← X.toL2_add]
  exact X.toL2_congr _ _ (funext fun Q => src_add hG.ne_bot Ψ Ψ' s Q)

theorem srcL2_smul (hG : Good 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) (c : ℂ) (s : ℂ) :
    srcL2 Γ (c • Ψ) s = c • srcL2 Γ Ψ s := by
  rw [srcL2_eq (l2Rep_src hG Γ (hΓ.smul c) s), srcL2_eq (l2Rep_src hG Γ hΓ s),
    ← X.toL2_const_mul]
  exact X.toL2_congr _ _ (funext fun Q => src_smul hG.ne_bot c Ψ s Q)

/-- **`Ψ ↦ θ_Ψ` is additive.** -/
theorem theta_add (hG : Good 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    {Ψ Ψ' : TSection ι 𝔪} (hΓ : Inv Γ Ψ) (hΓ' : Inv Γ Ψ') :
    theta Γ (Ψ + Ψ') = theta Γ Ψ + theta Γ Ψ' := by
  unfold theta
  rw [srcL2_add hG Γ hΓ hΓ', map_add, smul_add, neg_add]

/-- **`Ψ ↦ θ_Ψ` is homogeneous.** -/
theorem theta_smul (hG : Good 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) (c : ℂ) : theta Γ (c • Ψ) = c • theta Γ Ψ := by
  unfold theta
  rw [srcL2_smul hG Γ hΓ, map_smul, smul_neg, smul_comm]

/-! ### Functionals -/

/-! ### A bound for the cut-off part on compact sets -/

end

end ArtinKP.C5
end

section
-- module Solutions.Artin.KP.F_Alg_Const
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-FA, part 4: Lemma 5.2 (constant terms) as identities of Dirichlet series, and the scalars

In WP-E's normalization the constant-term series of a section is `D.aSer Φ 0 s`
(`= ∑_{c ∈ (R∖0)/U} g(0,c) · Lam Φ c 0 s · N(c)^{-s}`, `g(0,c) = G₀(c)`; the archimedean factor
`c_∞(s)^r` is common to all series below and is left out).  For a prime datum `π`:

* `const_split`: for weights `w₀` (on `π ∤ c`) and `w₁` (on `π ∣ c`),
  `∑_c w(c) · term(c) = (w₀ + w₁ (L_P - 1)) · m^♭`, `m^♭ = ∑_{π ∤ c}`;
* `lemma52_full` (`m_Φ = L_P m^♭`), `lemma52_infty` (`m_{Φρ_∞} = m^♭`),
  `lemma52_p` (`m_{Φρ_p} = (L_P - q⁻¹) m^♭`);
* `LP q x = (1 - q²x³)/(1 - q³x³)`, `hasSum_lcoef` (it is `∑_j φ(π^j) 1[3 ∣ j] x^j`);
* the scalar identities at `q⁴x³ = 1` (`s₀ = 4/3`): `LP_at`, `kernel_infty`, `kernel_p`,
  `U_eigen`, `cc_absS_cpow`.
-/

set_option autoImplicit false

namespace ArtinKP.FA

open ArtinKP.B7 ArtinKP.E

/-! ### The local factor `L_P` -/

/-! ### The scalar identities at `s₀ = 4/3` (`q⁴ x³ = 1`) -/

section scalars

variable {q x : ℂ}

theorem coef_at (hq : q ≠ 0) (hx : q ^ 4 * x ^ 3 = 1) :
    q ^ 3 * x ^ 3 = q⁻¹ ∧ q ^ 2 * x ^ 3 = (q⁻¹) ^ 2 := by
  have h3 : x ^ 3 = (q ^ 4)⁻¹ := eq_inv_of_mul_eq_one_right hx
  constructor
  · rw [h3]; field_simp
  · rw [h3]; field_simp

theorem U_eigen' (hq : q ≠ 0) (hq2 : q + 1 ≠ 0) :
    q⁻¹ + (1 - (q⁻¹) ^ 2) * (q / (q + 1)) = 1 := by
  field_simp
  ring

/-- The product formula turns `X = cc³ |π|_{S_f}^{-3s}` of `prop54` into `(q^{-s})³`:
if `N_∞(π) · |π|_{S_f} = q` then `(N_∞(π)^{-s})³ · |π|^{-3s} = (q^{-s})³`. -/
theorem cc_absS_cpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s : ℂ) :
    ((a : ℂ) ^ (-s)) ^ 3 * (b : ℂ) ^ (-(3 * s)) = (((a * b : ℝ) : ℂ) ^ (-s)) ^ 3 := by
  have h3 : (b : ℂ) ^ (-(3 * s)) = ((b : ℂ) ^ (-s)) ^ 3 := by
    rw [← Complex.cpow_nat_mul]
    congr 1
    push_cast
    ring
  rw [h3, ← mul_pow, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg ha.le hb.le]

end scalars

/-! ### Lemma 5.2 -/

end ArtinKP.FA
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

end ArtinKP.FA
end

section
-- module Solutions.Artin.KP.F_Alg_Symbol
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-FA, part 2: the strata of Proposition 5.4 and their symbols (MATH2 §5.3)

`π` generates an exterior prime (`PrimeElt`).  For `m ≤ 3` and `t ∈ R` the relation
`Rel π m t p p₁` says `p · [[1, t], [0, π³]] = π^m · p₁` with `m = min(v_P(c), 3)`:

  `p = (π^m c₁, d)`,  `p₁ = (c₁, c₁ t + π^(3-m) d)`,  and `π ∤ c₁` if `m < 3`.

* bijection part: `rel_smul`, `rel_fun`, `rel_inj`, `rel_dom_iff`, `rel_cod_iff`;
* symbol part: `kappa_rel` (`π ∤ c₁`), `kappa_rel_three` (`m = 3`, all cells, incl. the lower
  cells `π ∣ c₁`), `Phi_rel` (the `S_f`-part for a `t` that is deep for `Φ`);
* the phase `Theta` on the strata `m = 1, 2` and its vanishing sum `rsum_Theta`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.FA

open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

section basic

variable {ι : F →+* ℂ} {v : HeightOneSpectrum (𝓞 F)} {π : SInt 𝔪}

theorem PrimeElt.coprime_iff (H : PrimeElt ι 𝔪 v π) (d : SInt 𝔪) : IsCoprime d π ↔ ¬ π ∣ d :=
  isCoprime_iff_not_dvd H.isMax d

/-- `v(c) = 1 ↔ π ∤ c`: the condition of `TSection.restrict` in terms of `π`. -/
theorem PrimeElt.val_iff (H : PrimeElt ι 𝔪 v π) (hv : ¬ 𝔪 ≤ v.asIdeal) (c : SInt 𝔪) :
    v.valuation F (c : F) = 1 ↔ ¬ π ∣ c := by
  constructor
  · rintro h ⟨r, rfl⟩
    have h1 : v.valuation F (((π * r : SInt 𝔪)) : F) < 1 := by
      push_cast
      rw [map_mul]
      exact mul_lt_one_of_lt_of_le H.val_lt (sInt_val_le_one r v hv)
    rw [h] at h1
    exact lt_irrefl _ h1
  · intro h
    rcases val_of_isCoprime ((H.coprime_iff c).2 h) v hv with h1 | h1
    · exact h1
    · exact absurd h1 H.val_lt.ne

end basic

/-! ### The relation -/

/-! ### Powers in the cubic symbol -/

/-! ### The phase on the strata `m = 1, 2` -/

end ArtinKP.FA
end
end

section
-- module Solutions.Artin.KP.F_Eis_Reps
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-FB, part 1: deep complete sets of representatives (MATH2 §5.1, WP-FA §6 item 1)

For an exterior prime `P` (coprime to `𝔪`) with generator `π` of `P·R`, `R = SInt 𝔪`, and any
depth `N`, there is a complete set of representatives `T` of `R/πⁿR` all of whose elements `t`
have `t` and `t/πⁿ` in the `S_f`-adic ball `Small 𝔪 N` (`exists_deep_reps`).  This is the
strong-approximation statement "`R/πⁿR` has representatives in any `S_f`-adic ball"; the proof
is CRT in `𝓞`: `𝔪^K + Pⁿ = 𝓞` gives `e ∈ 𝔪^K` with `e ≡ 1 mod Pⁿ`, and `e·T₀` is deep for any
complete set of representatives `T₀` once `K` is large.

* `exists_isReps`, `isReps_mul_left`: generalities on `FA.IsReps`;
* `exists_deep_one`: the element `e`;
* `exists_deep_reps`, `exists_deep_reps_gen`: the deep `T`;
* `exists_reps_deep`, `exists_reps_deep_gen`: `T` in exactly the form `FA.prop54` takes
  (`hdeep`, uniform in `s`), for one genuine section; `exists_reps_deep₂` for two.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.FB

open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E ArtinKP.FA

section reps

variable {R : Type*} [CommRing R]

/-- A finite quotient `R ⧸ (c)` has a complete set of representatives. -/
theorem exists_isReps (c : R) [Finite (R ⧸ Ideal.span {c})] : ∃ T : Finset R, IsReps c T := by
  classical
  have := Fintype.ofFinite (R ⧸ Ideal.span {c})
  refine ⟨Finset.univ.image (fun x : R ⧸ Ideal.span {c} => x.out), fun x => ?_⟩
  have key : ∀ y : R ⧸ Ideal.span {c}, c ∣ x - y.out ↔ Ideal.Quotient.mk _ x = y := by
    intro y
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
    constructor
    · intro h; rw [h]; exact Quotient.out_eq y
    · intro h; rw [h]; exact (Quotient.out_eq y).symm
  refine ⟨(Ideal.Quotient.mk (Ideal.span {c}) x).out,
    ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (key _).2 rfl⟩, ?_⟩
  rintro t ⟨ht, hdvd⟩
  obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 ht
  rw [(key y).1 hdvd]

/-- Multiplying a complete set of representatives by `e ≡ 1 mod c` gives another one. -/
theorem isReps_mul_left [DecidableEq R] {c : R} {T : Finset R} (hT : IsReps c T) {e : R}
    (he : c ∣ e - 1) : IsReps c (T.image fun t => e * t) := by
  intro x
  obtain ⟨t, ⟨ht, hd⟩, huniq⟩ := hT x
  refine ⟨e * t, ⟨Finset.mem_image_of_mem _ ht, ?_⟩, ?_⟩
  · have e1 : x - e * t = (x - t) - (e - 1) * t := by ring
    rw [e1]
    exact dvd_sub hd (he.mul_right t)
  · rintro t' ⟨ht', hd'⟩
    obtain ⟨t₁, ht₁, rfl⟩ := Finset.mem_image.1 ht'
    have e1 : x - t₁ = (x - e * t₁) + (e - 1) * t₁ := by ring
    have : t₁ = t := huniq t₁ ⟨ht₁, by rw [e1]; exact dvd_add hd' (he.mul_right t₁)⟩
    rw [this]

end reps

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
  {v : HeightOneSpectrum (𝓞 F)} {ι : F →+* ℂ}

/-- CRT between the exterior prime `P` and `𝔪`: an element of `R` that is `S_f`-adically
`K`-deep and `≡ 1 mod πⁿ`. -/
theorem exists_deep_one (hcop : v.asIdeal ⊔ 𝔪 = ⊤) {π : SInt 𝔪}
    (hspan : Ideal.span {π} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) (n K : ℕ) :
    ∃ e : SInt 𝔪, Small 𝔪 K (e : F) ∧ π ^ n ∣ e - 1 := by
  have hc : IsCoprime (v.asIdeal ^ n) (𝔪 ^ K) :=
    IsCoprime.pow (Ideal.isCoprime_iff_sup_eq.2 hcop)
  obtain ⟨b, hb, a, ha, hab⟩ := Ideal.isCoprime_iff_exists.1 hc
  refine ⟨algebraMap (𝓞 F) (SInt 𝔪) a, ?_, ?_⟩
  · intro w hw
    have hmem : a ∈ w.asIdeal ^ K := Ideal.pow_right_mono hw _ ha
    have h1 := (w.intValuation_le_pow_iff_mem _ K).mpr hmem
    rw [← w.valuation_of_algebraMap (K := F)] at h1
    exact h1
  · have e1 : algebraMap (𝓞 F) (SInt 𝔪) a - 1 = -algebraMap (𝓞 F) (SInt 𝔪) b := by
      rw [← map_one (algebraMap (𝓞 F) (SInt 𝔪)), ← hab, map_add]; ring
    rw [e1, dvd_neg, ← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow, hspan,
      ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hb

/-- **A deep complete set of representatives** (strong approximation): for every depth `N`
there is a complete set of representatives `T` of `R/πⁿR` with `t` and `t/πⁿ` in the
`S_f`-adic ball of depth `N` for all `t ∈ T`. -/
theorem exists_deep_reps (h𝔪 : 𝔪 ≠ ⊥) (hcop : v.asIdeal ⊔ 𝔪 = ⊤) {π : SInt 𝔪}
    (hspan : Ideal.span {π} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) (n : ℕ)
    [Finite (SInt 𝔪 ⧸ Ideal.span {π ^ n})] (N : ℤ) :
    ∃ T : Finset (SInt 𝔪), IsReps (π ^ n) T ∧
      ∀ t ∈ T, Small 𝔪 N (t : F) ∧ Small 𝔪 N ((t : F) / (π : F) ^ n) := by
  classical
  obtain ⟨T₀, hT₀⟩ := exists_isReps (π ^ n)
  choose B₁ hB₁ using fun t : SInt 𝔪 => exists_small_neg h𝔪 (t : F)
  choose B₂ hB₂ using fun t : SInt 𝔪 => exists_small_neg h𝔪 ((t : F) / (π : F) ^ n)
  set B : ℕ := T₀.sup fun t => B₁ t + B₂ t with hB
  obtain ⟨e, he, hdvd⟩ := exists_deep_one hcop hspan n (N + B).toNat
  refine ⟨T₀.image fun t => e * t, isReps_mul_left hT₀ hdvd, fun t ht => ?_⟩
  obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.1 ht
  have hle : B₁ t₀ + B₂ t₀ ≤ B := Finset.le_sup (f := fun t => B₁ t + B₂ t) ht₀
  have hK : N + B ≤ ((N + B).toNat : ℤ) := Int.self_le_toNat _
  constructor
  · have := he.mul (hB₁ t₀)
    rw [Subalgebra.coe_mul]
    exact this.mono (by omega)
  · have := he.mul (hB₂ t₀)
    rw [Subalgebra.coe_mul, mul_div_assoc]
    exact this.mono (by omega)

/-- The deep set of representatives in the form `FA.prop54` takes: `hdeep` for the genuine
section `Φ`, uniformly in `s`. -/
theorem exists_reps_deep (P : CubicPkg F) (h𝔪 : 𝔪 ≠ ⊥) (hcop : v.asIdeal ⊔ 𝔪 = ⊤) {π : SInt 𝔪}
    (hspan : Ideal.span {π} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) (n : ℕ)
    [Finite (SInt 𝔪 ⧸ Ideal.span {π ^ n})] (Φ : GSection ι P 𝔪) (N₀ : ℤ) :
    ∃ T : Finset (SInt 𝔪), IsReps (π ^ n) T ∧
      (∀ t ∈ T, Small 𝔪 N₀ (t : F) ∧ Small 𝔪 N₀ ((t : F) / (π : F) ^ n)) ∧
      ∀ t ∈ T, ∀ (s : ℂ) (c d : F), Φ s c (d + c * ((t : F) / (π : F) ^ n)) = Φ s c d := by
  obtain ⟨N, hN⟩ := Φ.exists_unip
  obtain ⟨T, hT, hsmall⟩ := exists_deep_reps h𝔪 hcop hspan n (max N₀ (N : ℤ))
  exact ⟨T, hT, fun t ht => ⟨(hsmall t ht).1.mono (le_max_left _ _),
    (hsmall t ht).2.mono (le_max_left _ _)⟩,
    fun t ht => hN _ ((hsmall t ht).2.mono (le_max_right _ _))⟩

/-! ### At an allowed generator of a good exterior prime -/

section gen

variable (h : C3I.Good 𝔪 v) (g : AllowedGen ι 𝔪) (h𝔪 : 𝔪 ≠ ⊥)

include h h𝔪 in
theorem exists_deep_reps_gen (n : ℕ) (N : ℤ) :
    ∃ T : Finset (SInt 𝔪), IsReps (g.gen v.asIdeal ^ n) T ∧
      ∀ t ∈ T, Small 𝔪 N (t : F) ∧ Small 𝔪 N ((t : F) / (g.gen v.asIdeal : F) ^ n) := by
  have := finite_quot_gen_pow h g h𝔪 n
  exact exists_deep_reps h𝔪 h.cop (span_gen h g) n N

include h h𝔪 in
theorem exists_reps_deep_gen (P : CubicPkg F) (n : ℕ) (Φ : GSection ι P 𝔪) (N₀ : ℤ) :
    ∃ T : Finset (SInt 𝔪), IsReps (g.gen v.asIdeal ^ n) T ∧
      (∀ t ∈ T, Small 𝔪 N₀ (t : F) ∧ Small 𝔪 N₀ ((t : F) / (g.gen v.asIdeal : F) ^ n)) ∧
      ∀ t ∈ T, ∀ (s : ℂ) (c d : F),
        Φ s c (d + c * ((t : F) / (g.gen v.asIdeal : F) ^ n)) = Φ s c d := by
  have := finite_quot_gen_pow h g h𝔪 n
  exact exists_reps_deep P h𝔪 h.cop (span_gen h g) n Φ N₀

end gen

end ArtinKP.FB
end
end

section
-- module Solutions.Artin.KP.F_Eis_Op
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.G1.scal_apply
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

open NumberField.HeightOneSpectrum in
theorem adicAbv_eq_inv_of_val {v : HeightOneSpectrum (𝓞 F)} {x : F}
    (h : v.valuation F x = WithZero.exp (-1 : ℤ)) :
    adicAbv F v x = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at h
    exact WithZero.exp_ne_zero h.symm
  have hq : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
    have h' : 1 < Ideal.absNorm v.asIdeal := by exact_mod_cast this
    exact_mod_cast (zero_lt_one.trans h')
  have h1 := abv_le_of_val_le v (x := x) (n := 1) h.le
  have h2 := abv_le_of_val_le v (x := x⁻¹) (n := -1)
    (by rw [map_inv₀, h, ← WithZero.exp_neg])
  rw [zpow_neg_one] at h1
  rw [neg_neg, zpow_one, map_inv₀] at h2
  have hpos : 0 < adicAbv F v x := (adicAbv F v).pos hx0
  refine le_antisymm h1 ?_
  rw [inv_le_comm₀ hq hpos]
  exact h2

/-- **`N_∞(π) · |π|_{S_f} = N P`** for a generator `π` of `P·R`, `P` an exterior prime. -/
theorem Ninf_mul_absS_of_span [IsTotallyComplex F] (h𝔪 : 𝔪 ≠ ⊥) {v : HeightOneSpectrum (𝓞 F)}
    (hv : ¬ 𝔪 ≤ v.asIdeal) {π : SInt 𝔪} (hπ : π ≠ 0)
    (hspan : Ideal.span {π} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    Ninf (π : F) * absS 𝔪 (π : F) = Ideal.absNorm v.asIdeal := by
  classical
  obtain ⟨hvv, hw⟩ := val_generator v hv π hspan
  have hπF : (π : F) ≠ 0 := fun h => hπ (Subtype.ext h)
  have hnot : FinitePlace.mk v ∉ sPl 𝔪 := by
    intro hmem
    obtain ⟨v', hv', he⟩ := Finset.mem_image.mp hmem
    rw [FinitePlace.mk_eq_iff] at he
    exact hv ((CubicPkg.mem_sFin h𝔪 v).mp (he ▸ hv'))
  have h2 : ∏ᶠ w : FinitePlace F, w (π : F)
      = ∏ w ∈ insert (FinitePlace.mk v) (sPl 𝔪), w (π : F) := by
    refine finprod_eq_prod_of_mulSupport_subset _ fun w hw' => ?_
    by_contra hwS
    rw [Finset.mem_coe, Finset.mem_insert, not_or] at hwS
    apply hw'
    have e : w (π : F) = NumberField.HeightOneSpectrum.adicAbv F w.maximalIdeal (π : F) := by
      conv_lhs => rw [← FinitePlace.mk_maximalIdeal w]
      exact mk_apply_eq _ _
    change w (π : F) = 1
    rw [e]
    refine abv_eq_one_of_val_eq_one _ (hw _ (fun hle => hwS.2 ?_) (fun he => hwS.1 ?_))
    · rw [← FinitePlace.mk_maximalIdeal w]
      exact Finset.mem_image_of_mem _ ((CubicPkg.mem_sFin h𝔪 _).mpr hle)
    · rw [← FinitePlace.mk_maximalIdeal w, he]
  rw [Finset.prod_insert hnot, prod_sPl_eq_absS, mk_apply_eq, adicAbv_eq_inv_of_val hvv,
    X.finprod_finitePlace hπF] at h2
  have hN : 0 < Ninf (π : F) := Ninf_pos hπF
  have hq : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
    have h' : 1 < Ideal.absNorm v.asIdeal := by exact_mod_cast this
    exact_mod_cast (zero_lt_one.trans h')
  change (Ninf (π : F))⁻¹ = _ at h2
  field_simp at h2
  linarith

/-- The product formula at an allowed generator of a good exterior prime, with FA's `q`. -/
theorem Ninf_mul_absS_gen [IsTotallyComplex F] {ι : F →+* ℂ} {v : HeightOneSpectrum (𝓞 F)}
    (h : C3I.Good 𝔪 v) (g : AllowedGen ι 𝔪) (h𝔪 : 𝔪 ≠ ⊥) :
    Ninf (g.gen v.asIdeal : F) * absS 𝔪 (g.gen v.asIdeal : F)
      = (Nat.card (SInt 𝔪 ⧸ Ideal.span {g.gen v.asIdeal}) : ℝ) := by
  rw [card_quot_gen h g]
  exact Ninf_mul_absS_of_span h𝔪 (not_le_of_good h) (gen_ne_zero h g) (span_gen h g)

end ArtinKP.FB
end
end

section
-- module Solutions.Artin.KP.F_Eis_Main
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.G1.scal_apply _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
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

section main

variable (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  {π : SInt 𝔪} (H : PrimeElt ι 𝔪 v π) (Φ : GSection ι P 𝔪)

variable [IsTotallyComplex F]

include H in
/-- **Proposition 5.4 for `B.eis`** (MATH2 §5.3), `Re s > 2`, pointwise on `X`:
`U E_Ψ(·, s) = Nh(π³)^s [ q³(q^{-s})³ E_{Ψ♯} + (1 − q²(q^{-s})³) E_{Ψ♯ρ_∞} ]`,
under the product formula `N_∞(π)|π|_{S_f} = q`. -/
theorem U_eis (hv : ¬ 𝔪 ≤ v.asIdeal) {T : Finset (SInt 𝔪)} (hT : IsReps (π ^ 3) T)
    (hdeep : ∀ t ∈ T, ∀ (s : ℂ) (c d : F), Φ s c (d + c * ((t : F) / (π : F) ^ 3)) = Φ s c d)
    {q : ℕ} (hq : Nat.card (SInt 𝔪 ⧸ Ideal.span {π}) = q)
    (hprod : Ninf (π : F) * absS 𝔪 (π : F) = q)
    {s : ℂ} (hs : 2 < s.re) (Q : X F) :
    U ((π : F) ^ 3) (pow_ne_zero 3 H.coe_ne_zero) T (eis (Φ.twist hG hz6) s) Q
      = ((Nh ((π : F) ^ 3) : ℝ) : ℂ) ^ s *
        ((q : ℂ) ^ 3 * ((q : ℂ) ^ (-s)) ^ 3
            * eis ((Φ.sharp hG (π : F) H.coe_ne_zero).twist hG hz6) s Q
          + (1 - (q : ℂ) ^ 2 * ((q : ℂ) ^ (-s)) ^ 3)
            * eis (TSection.restrict v hv ((Φ.sharp hG (π : F) H.coe_ne_zero).twist hG hz6))
                s Q) := by
  have h := U_eis_primeElt P hG hz6 H Φ hv hT hdeep hs Q
  rw [cc_absS_cpow (Ninf_pos H.coe_ne_zero) (absS_pos H.coe_ne_zero) s, hprod, hq] at h
  simpa using h

end main

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

section gen

variable [IsTotallyComplex F] (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F}
  (hz6 : IsPrimitiveRoot z6 6) (h : C3I.Good 𝔪 v) (g : AllowedGen ι 𝔪) (Φ : GSection ι P 𝔪)

/-- **Proposition 5.4** at `π = g.gen P`, `q = N P`, in MATH2's normalization:
`U E_Ψ(·,s) = N_∞(π)^{3s/2}·[q^{3−3s}·E_{Ψ♯}(·,s) + (1 − q^{2−3s})·E_{Ψ♯ρ_∞}(·,s)]`
for `Re s > 2`, pointwise on `X`, for every complete set of representatives `T` of `R/π³R`
that is deep for `Φ`. -/
theorem U_eis_gen {T : Finset (SInt 𝔪)} (hT : IsReps (g.gen v.asIdeal ^ 3) T)
    (hdeep : ∀ t ∈ T, ∀ (s : ℂ) (c d : F),
      Φ s c (d + c * ((t : F) / (g.gen v.asIdeal : F) ^ 3)) = Φ s c d)
    {s : ℂ} (hs : 2 < s.re) (Q : X F) :
    U ((g.gen v.asIdeal : F) ^ 3) (pow_ne_zero 3 (primeElt_gen_of_good P hG hz6 h g).coe_ne_zero) T
        (eis (Φ.twist hG hz6) s) Q
      = ((Ninf (g.gen v.asIdeal : F) : ℝ) : ℂ) ^ (3 * s / 2) *
        ((Ideal.absNorm v.asIdeal : ℂ) ^ (3 - 3 * s)
            * eis ((Φ.sharp hG (g.gen v.asIdeal : F)
                (primeElt_gen_of_good P hG hz6 h g).coe_ne_zero).twist hG hz6) s Q
          + (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (2 - 3 * s))
            * eis (TSection.restrict v (not_le_of_good h) ((Φ.sharp hG (g.gen v.asIdeal : F)
                (primeElt_gen_of_good P hG hz6 h g).coe_ne_zero).twist hG hz6)) s Q) := by
  have H := primeElt_gen_of_good P hG hz6 h g
  have hq0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
    have h' : 1 < Ideal.absNorm v.asIdeal := by exact_mod_cast this
    omega
  have key := U_eis P hG hz6 H Φ (not_le_of_good h) hT hdeep (card_quot_gen h g)
    (Ninf_mul_absS_of_span hG.ne_bot (not_le_of_good h) (gen_ne_zero h g) (span_gen h g)) hs Q
  rw [key, Nh_pi_cube_cpow H.coe_ne_zero, q_cpow_three hq0, q_cpow_two hq0]

/-- **Proposition 5.4 with its deep `T`**: there is one finite `T ⊂ R` (independent of `s`),
a complete set of representatives of `R/π³R` in the `S_f`-adic ball of any prescribed depth
`N₀`, such that the identity of `U_eis_gen` holds for all `s` with `Re s > 2` and all `Q`. -/
theorem exists_U_eis_gen (N₀ : ℤ) :
    ∃ T : Finset (SInt 𝔪), IsReps (g.gen v.asIdeal ^ 3) T ∧
      (∀ t ∈ T, Small 𝔪 N₀ (t : F) ∧ Small 𝔪 N₀ ((t : F) / (g.gen v.asIdeal : F) ^ 3)) ∧
      ∀ s : ℂ, 2 < s.re → ∀ Q : X F,
        U ((g.gen v.asIdeal : F) ^ 3) (pow_ne_zero 3 (primeElt_gen_of_good P hG hz6 h g).coe_ne_zero) T
            (eis (Φ.twist hG hz6) s) Q
          = ((Ninf (g.gen v.asIdeal : F) : ℝ) : ℂ) ^ (3 * s / 2) *
            ((Ideal.absNorm v.asIdeal : ℂ) ^ (3 - 3 * s)
                * eis ((Φ.sharp hG (g.gen v.asIdeal : F)
                    (primeElt_gen_of_good P hG hz6 h g).coe_ne_zero).twist hG hz6) s Q
              + (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (2 - 3 * s))
                * eis (TSection.restrict v (not_le_of_good h) ((Φ.sharp hG (g.gen v.asIdeal : F)
                    (primeElt_gen_of_good P hG hz6 h g).coe_ne_zero).twist hG hz6)) s Q) := by
  obtain ⟨T, hT, hsmall, hdeep⟩ := exists_reps_deep_gen h g hG.ne_bot P 3 Φ N₀
  exact ⟨T, hT, hsmall, fun s hs Q => U_eis_gen P hG hz6 h g Φ hT hdeep hs Q⟩

end gen

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
-- module Solutions.Artin.KP.RF_Strip
attribute [-instance] _root_.ArtinKP.B.instCountableIdxI _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.B1.instCountablePairClass _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma measurable_ofXV : Measurable (ofXV : XV F → X F) := by
  refine (chart F).continuous.measurable.comp (measurable_pi_lambda _ fun w => ?_)
  exact ((measurable_pi_apply w).comp measurable_fst).prodMk
    (Real.measurable_log.comp ((measurable_pi_apply w).comp measurable_snd))

/-! ### Boxes in `v` -/

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
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-! ### The constant-term functional -/

lemma eChar_zero (x : InfinitePlace F → ℂ) : eChar 0 x = 1 := by
  simp [eChar, pair]

lemma stripFn_zero (D : Set (InfinitePlace F → ℂ)) (φ : (InfinitePlace F → ℝ) → ℂ) (P : X F) :
    stripFn D 0 φ P = D.indicator (fun _ => (1 : ℂ)) P.x * φ P.v := by
  rw [stripFn, eChar_zero, one_mul]

section lin

variable {D : Set (InfinitePlace F → ℂ)} {n : ℕ} {φ : (InfinitePlace F → ℝ) → ℂ}

lemma cf_integrable (hD : MeasurableSet D) (hφ : Measurable φ) (hφ1 : ∀ v, ‖φ v‖ ≤ 1)
    {f : X F → ℂ} (hf : IntegrableOn f (X.box n) (X.vol F)) :
    IntegrableOn (fun P => conj (stripFn D 0 φ P) * f P) (X.box n) (X.vol F) := by
  refine Integrable.bdd_mul (c := 1) hf
    (Complex.continuous_conj.measurable.comp (measurable_stripFn hD 0 hφ)).aestronglyMeasurable ?_
  exact Eventually.of_forall fun P => by
    rw [RCLike.norm_conj]; exact norm_stripFn_le D 0 hφ1 P

end lin

/-! ### Fubini: a function with vanishing `x`-integrals over `D` is killed by `cf` -/

lemma ofXV_eq_mk (x : InfinitePlace F → ℂ) {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w) :
    ofXV (x, v) = X.mk x v hv := by
  refine X.ext' (funext fun w => ?_) (funext fun w => ?_)
  · simp [ofXV, chart_x]
  · simp [ofXV, chart_v, Real.exp_log (hv w)]

/-! ### The shape -/

lemma isCompact_box (n : ℕ) : IsCompact (X.box n : Set (X F)) :=
  isCompact_siegelBox (F := F) (m := 1 / ((n : ℝ) + 1)) (M := (n : ℝ) + 1) (B := n)
    (by positivity)

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.N_Cont
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-! ### The cut-off part against a bounded test function -/

/-! ### Coefficients of `θ_Ψ` from a continuation (all test functions) -/

/-! ### Frequency `0`: the residue of the `ht^{2−s}`-coefficient -/

end

end ArtinKP.N
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
attribute [-instance] _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma volume_ne_top_of_bdd {D : Set (InfinitePlace F → ℂ)} {n : ℕ}
    (h : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) : volume D ≠ ⊤ := by
  have hsub : D ⊆ Metric.closedBall (0 : InfinitePlace F → ℂ) n := fun x hx => by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)]
    exact h x hx
  exact ((measure_mono hsub).trans_lt measure_closedBall_lt_top).ne


theorem pcell_cellM (h𝔪 : 𝔪 ≠ ⊥) {M : ℤ} (hM : 0 ≤ M) : PCell (transLat 𝔪 M) (cellM 𝔪 M) := by
  unfold cellM
  rw [dif_pos ⟨h𝔪, hM⟩]
  exact (exists_pcell_transLat h𝔪 hM).choose_spec.choose_spec.1

theorem cellM_bdd (h𝔪 : 𝔪 ≠ ⊥) {M : ℤ} (hM : 0 ≤ M) :
    ∀ x ∈ cellM 𝔪 M, ∀ w, ‖x w‖ ≤ cellN 𝔪 M := by
  unfold cellM cellN
  rw [dif_pos ⟨h𝔪, hM⟩, dif_pos ⟨h𝔪, hM⟩]
  exact (exists_pcell_transLat h𝔪 hM).choose_spec.choose_spec.2

lemma vol_pos (𝔪 : Ideal (𝓞 F)) (M : ℤ) : 0 < vol 𝔪 M := by
  unfold vol
  refine Finset.prod_pos fun v _ => zpow_pos ?_ _
  have h : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero h)

lemma volume_toReal_pos {L : AddSubgroup (InfinitePlace F → ℂ)} [Countable L]
    {D : Set (InfinitePlace F → ℂ)} (h : PCell L D) {n : ℕ} (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) :
    0 < (volume D).toReal :=
  ENNReal.toReal_pos ((h.isAddFundamentalDomain volume).measure_ne_zero (NeZero.ne _))
    (volume_ne_top_of_bdd hb)

theorem kap_ne_zero (h𝔪 : 𝔪 ≠ ⊥) {M : ℤ} (hM : 0 ≤ M) : kap 𝔪 M ≠ 0 := by
  unfold kap
  refine inv_ne_zero (Complex.ofReal_ne_zero.mpr (mul_pos ?_ (vol_pos 𝔪 M)).ne')
  exact volume_toReal_pos (pcell_cellM h𝔪 hM) (cellM_bdd h𝔪 hM)

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.T_Kap
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-T, file 9: the constant `kap 𝔪 M` is `covol(𝓞_F)⁻¹`

By WP-BZ's `volume_cell'` (WP-B's stub B-2): `kap 𝔪 M = (volume (B1.fundD F)).toReal⁻¹` for every
`M ≥ 0`; in particular it does not depend on `M`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.T

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}

theorem kap_eq (h𝔪 : 𝔪 ≠ ⊥) {M : ℤ} (hM : 0 ≤ M) :
    kap 𝔪 M = ((((volume (B1.fundD F)).toReal : ℝ)) : ℂ)⁻¹ := by
  have h := BZ.volume_cell' h𝔪 M ((pcell_cellM h𝔪 hM).isAddFundamentalDomain volume)
  have h' := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (vol_pos 𝔪 M).le] at h'
  rw [kap, h']

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.T_Arch
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
/-! # WP-T, file 2: the archimedean Whittaker function as a function on `X`

`WX s ν P = Winf s ν P.v = ∏_w jacquet s (−σ_w ν) v_w`.  For `Re s > 1`:

* `continuous_WX`, `differentiableOn_WX` (in `s`, `ν ≠ 0`), `exists_norm_WX_le` (bounded on
  `ball × box`);
* **`exists_WX_ne_zero`**: for every `s₁` (complex!) there is `δ > 0` with `WX s₁ ν P ≠ 0` whenever
  all `v_w < δ`.  (The Jacquet integral is `v^{2−s}·ĝ_s(νv)` with `ĝ_s` continuous and
  `ĝ_s(0) = π/(s−1) ≠ 0`; no information on zeros of `K_μ` of complex order is needed.)
* `phaseW s₁ ν`, a measurable test function of `v` of modulus `≤ 1` with
  `conj (phaseW s₁ ν P.v) * WX s₁ ν P = ‖WX s₁ ν P‖`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.T

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

/-! ### One place -/

theorem continuous_sFK {s : ℂ} (hs : 1 < s.re) : Continuous (sourceFourierKernel s) := by
  unfold sourceFourierKernel
  refine continuous_of_dominated (bound := fun z => ‖hyperbolicKernel s z‖) (fun ξ => ?_)
    (fun ξ => ?_) (hyperbolicKernel_integrable s hs).norm ?_
  · have hchar : Continuous (fun z : ℂ => archChar (-ξ * z)) :=
      K.continuous_archChar.comp (by fun_prop)
    exact ((continuous_hyperbolicKernel s).mul hchar).aestronglyMeasurable
  · exact Eventually.of_forall fun z => by rw [norm_mul, archChar_norm, mul_one]
  · exact Eventually.of_forall fun z =>
      continuous_const.mul (K.continuous_archChar.comp (by fun_prop))

theorem sFK_zero_ne {s : ℂ} (hs : 1 < s.re) : sourceFourierKernel s 0 ≠ 0 := by
  rw [sourceFourierKernel_zero s hs]
  refine div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) fun h => ?_
  have := congrArg Complex.re h
  simp at this
  linarith

/-- Near frequency `0` the kernel does not vanish. -/
theorem exists_sFK_ne_zero {s : ℂ} (hs : 1 < s.re) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ξ : ℂ, ‖ξ‖ < ε → sourceFourierKernel s ξ ≠ 0 := by
  have h := (continuous_sFK hs).continuousAt.eventually_ne (sFK_zero_ne hs)
  obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff.mp h
  exact ⟨ε, hε, fun ξ hξ => hb (by simpa using hξ)⟩

/-! ### The function on `X` -/

variable {F : Type*} [Field F] [NumberField F]

lemma WX_eq (s : ℂ) (ν : F) (P : X F) :
    WX s ν P = ∏ w : InfinitePlace F, ((P.v w : ℝ) : ℂ) ^ (2 - s) *
      sourceFourierKernel s (-(w.embedding ν) * P.v w) := by
  unfold WX Winf
  exact Finset.prod_congr rfl fun w _ => jacquet_eq_sourceFourierKernel s _ (P.v_pos w)

theorem continuous_WX {s : ℂ} (hs : 1 < s.re) (ν : F) : Continuous (WX s ν : X F → ℂ) := by
  have e : (WX s ν : X F → ℂ) = fun P => ∏ w : InfinitePlace F, ((P.v w : ℝ) : ℂ) ^ (2 - s) *
      sourceFourierKernel s (-(w.embedding ν) * P.v w) := funext fun P => WX_eq s ν P
  rw [e]
  refine continuous_finsetProd _ fun w _ => ?_
  have hv : Continuous fun P : X F => ((P.v w : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (X.continuous_v w)
  refine (hv.cpow continuous_const fun P => Or.inl ?_).mul
    ((continuous_sFK hs).comp (continuous_const.mul hv))
  simpa using P.v_pos w

/-- **Non-vanishing near the cusp**, for every complex `s₁` with `Re s₁ > 1`. -/
theorem exists_WX_ne_zero (ν : F) {s₁ : ℂ} (hs₁ : 1 < s₁.re) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ P : X F, (∀ w, P.v w < δ) → WX s₁ ν P ≠ 0 := by
  obtain ⟨ε, hε, hne⟩ := exists_sFK_ne_zero hs₁
  set m : ℝ := ∑ w : InfinitePlace F, ‖w.embedding ν‖ with hm
  have hm0 : 0 ≤ m := Finset.sum_nonneg fun w _ => norm_nonneg _
  refine ⟨ε / (m + 1), by positivity, fun P hP => ?_⟩
  rw [WX_eq]
  refine Finset.prod_ne_zero_iff.mpr fun w _ => mul_ne_zero ?_ (hne _ ?_)
  · rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (P.v_pos w).ne')]
    exact Complex.exp_ne_zero _
  · rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (P.v_pos w)]
    have h1 : ‖w.embedding ν‖ ≤ m :=
      Finset.single_le_sum (f := fun w : InfinitePlace F => ‖w.embedding ν‖)
        (fun w _ => norm_nonneg _) (Finset.mem_univ w)
    have h2 : P.v w < ε / (m + 1) := hP w
    calc ‖w.embedding ν‖ * P.v w ≤ m * P.v w :=
          mul_le_mul_of_nonneg_right h1 (P.v_pos w).le
      _ ≤ (m + 1) * P.v w := by nlinarith [P.v_pos w]
      _ < (m + 1) * (ε / (m + 1)) := mul_lt_mul_of_pos_left h2 (by positivity)
      _ = ε := by field_simp

/-! ### The phase test function -/

variable [IsTotallyComplex F]

lemma measurable_unitPhase : Measurable unitPhase :=
  measurable_id.div (Complex.measurable_ofReal.comp measurable_norm)

lemma norm_unitPhase_le (z : ℂ) : ‖unitPhase z‖ ≤ 1 := by
  unfold unitPhase
  rw [norm_div, Complex.norm_real, norm_norm]
  exact div_self_le_one _

lemma conj_unitPhase_mul (z : ℂ) : conj (unitPhase z) * z = ((‖z‖ : ℝ) : ℂ) := by
  unfold unitPhase
  by_cases hz : z = 0
  · simp [hz]
  have h0 : ((‖z‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  rw [map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, Complex.conj_mul']
  field_simp

lemma measurable_phaseW {s₁ : ℂ} (hs₁ : 1 < s₁.re) (ν : F) :
    Measurable (phaseW (F := F) s₁ ν) :=
  measurable_unitPhase.comp ((continuous_WX hs₁ ν).measurable.comp
    (measurable_ofXV.comp (measurable_const.prodMk measurable_id)))

lemma norm_phaseW_le (s₁ : ℂ) (ν : F) (v : InfinitePlace F → ℝ) : ‖phaseW s₁ ν v‖ ≤ 1 :=
  norm_unitPhase_le _

lemma phaseW_v (s₁ : ℂ) (ν : F) (P : X F) : phaseW s₁ ν P.v = unitPhase (WX s₁ ν P) := by
  unfold phaseW
  have h : (ofXV ((0 : InfinitePlace F → ℂ), P.v)).v = P.v := by
    rw [ofXV_eq_mk 0 (fun w => P.v_pos w)]
    rfl
  unfold WX
  rw [h]

lemma conj_phaseW_mul (s₁ : ℂ) (ν : F) (P : X F) :
    conj (phaseW s₁ ν P.v) * WX s₁ ν P = ((‖WX s₁ ν P‖ : ℝ) : ℂ) := by
  rw [phaseW_v, conj_unitPhase_mul]

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.T_Coef
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
/-! # WP-T, file 4: the `ν`-th coefficient of `E_Φ` over a cell, for `Re s > 2`

* `freq ν = (−2σ_w ν)_w`: `conj (RF.eChar (freq ν) x) = B.chiInf ν x`, so that
  `X.coeffFunctional Γ n (RF.stripFn D (freq ν) φ) …` is the `ν`-th coefficient against `conj φ`.
* `HasCoefT Ψ ν' a₀ D κ` (twisted section, any coefficient series `a₀`): for `Re s > 2` and all
  `v`, `∫_D E_Ψ(x, v) conj e_∞(ν'x) dx = vol(D)·κ·W_s(ν'; v)·a₀(s)`;
  `HasCoef hG hz6 Φ ν D κ` is the case `Ψ = Φ.twist`, `a₀ = 𝔞_Φ(ν, ·)`.
  - `hasCoef_transLat`: a strict cell of `Λ_M` (`M ≥ 0` valid) has it with `κ = kap 𝔪 M` (WP-B);
  - **`hasCoef_latN`**: so has every bounded strict cell of the translation lattice of any `Γ`
    fixing `Φ.twist`, provided `conj e_∞(ν·)` is `Λ_Γ`-periodic (`T.mean_eq`).
* `Afun Γ Ψ n ψ s = ∫_{box n} conj ψ · lift (resPart Γ Ψ s) + ∫_{box n} conj ψ · h_s`: holomorphic
  on `E.slit`, `= ∫_{box n} conj ψ · E_Ψ` for `Re s > 2`, ray limit `∫ conj ψ · θ`.
* `Wc D n φ ν s = N.cf D n φ (WX s ν)`: holomorphic on `Re s > 1`; `exists_Wc_ne_zero`.
* **`Afun_eq_of_hasCoefT`**: `Afun … (stripFn D (freq ν') φ) s = κ·a₀(s)·Wc D n φ ν' s`, `Re s > 2`.
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
  {ι : F →+* ℂ} {P : CubicPkg F}

/-! ### The frequency of `ν` in WP-RF's parametrization -/

/-! ### Cells that compute the coefficient -/

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (Φ : GSection ι P 𝔪)
  (ν : SInt 𝔪)

theorem validDepth_mono {ν' : F} {M M' : ℤ} (h : ValidDepth hG Φ ν' M) (hMM : M ≤ M') :
    ValidDepth hG Φ ν' M' :=
  ⟨fun b hb => h.unip b (hb.mono hMM), fun x hx => h.char x (hx.mono hMM)⟩

theorem exists_validDepth_nonneg (ν' : F) : ∃ M : ℤ, 0 ≤ M ∧ ValidDepth hG Φ ν' M := by
  obtain ⟨M, hM⟩ := exists_validDepth hG Φ ν'
  exact ⟨max M 0, le_max_right _ _, validDepth_mono hG Φ hM (le_max_left _ _)⟩

variable {hG hz6 Φ ν}

/-! ### The coefficient function of the continuation -/

/-! ### The archimedean factor -/

/-- `nuV` of a small box near `v = 0` is positive. -/
lemma nuV_Icc_ne_zero {n : ℕ} {lo hi : ℝ} (hlo : 1 / ((n : ℝ) + 1) ≤ lo) (hlh : lo < hi)
    (hhi : hi ≤ (n : ℝ) + 1) :
    X.nuV F (Icc (fun _ : InfinitePlace F => lo) (fun _ : InfinitePlace F => hi)) ≠ 0 := by
  have hsub : Icc (fun _ : InfinitePlace F => lo) (fun _ : InfinitePlace F => hi) ⊆ vBox F n := by
    intro v hv w
    exact ⟨hlo.trans (hv.1 w), (hv.2 w).trans hhi⟩
  rw [nuV_eq_withDensity, withDensity_apply _ measurableSet_Icc]
  intro h
  rw [lintegral_eq_zero_iff RF.measurable_dens] at h
  have h1 : ∀ᵐ v ∂(volume : Measure (InfinitePlace F → ℝ)),
      v ∉ Icc (fun _ : InfinitePlace F => lo) (fun _ : InfinitePlace F => hi) := by
    have h2 := (ae_restrict_iff' measurableSet_Icc).mp h
    filter_upwards [h2] with v hv hmem
    exact dens_ne_zero (hsub hmem) (hv hmem)
  have h3 := measure_eq_zero_iff_ae_notMem.mpr h1
  rw [Real.volume_Icc_pi] at h3
  exact (Finset.prod_ne_zero_iff.mpr fun w _ =>
    (ENNReal.ofReal_pos.mpr (by linarith)).ne') h3

/-- **A test function seeing `W_{s₁}(ν; ·)`**, for every complex `s₁` with `Re s₁ > 1`. -/
theorem exists_Wc_ne_zero (ν : F) {s₁ : ℂ} (hs₁ : 1 < s₁.re) {D : Set (InfinitePlace F → ℂ)}
    (hDm : MeasurableSet D) (hD0 : volume D ≠ 0) {n₀ : ℕ} (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n₀) :
    ∃ n : ℕ, n₀ ≤ n ∧ Wc D n (phaseW s₁ ν) ν s₁ ≠ 0 := by
  obtain ⟨δ, hδ, hne⟩ := exists_WX_ne_zero (F := F) ν hs₁
  set δ' : ℝ := min δ 1 with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ one_pos
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / δ')
  set n : ℕ := max n₀ m with hn
  have hnm : (m : ℝ) ≤ n := by exact_mod_cast le_max_right n₀ m
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set lo : ℝ := 1 / ((n : ℝ) + 1) with hlo
  have hlo_lt : lo < δ' := by
    rw [hlo, one_div_lt (by positivity) hδ'0]
    linarith
  set hi : ℝ := (lo + δ') / 2 with hhi
  have hlh : lo < hi := by rw [hhi]; linarith
  have hhiδ : hi < δ := by
    have : δ' ≤ δ := min_le_left _ _
    rw [hhi]; linarith
  have hhin : hi ≤ (n : ℝ) + 1 := by
    have : δ' ≤ 1 := min_le_right _ _
    rw [hhi]; linarith
  refine ⟨n, le_max_left _ _, ?_⟩
  set V' : Set (InfinitePlace F → ℝ) :=
    Icc (fun _ : InfinitePlace F => lo) (fun _ : InfinitePlace F => hi) with hV'
  have hV'sub : V' ⊆ vBox F n := fun v hv w => ⟨hv.1 w, (hv.2 w).trans hhin⟩
  have hbn : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n := fun x hx w =>
    (hb x hx w).trans (by exact_mod_cast le_max_left n₀ m)
  set h : X F → ℝ := (X.x ⁻¹' D : Set (X F)).indicator (fun Q => ‖WX s₁ ν Q‖) with hh
  have hSm : MeasurableSet (X.x ⁻¹' D : Set (X F)) := X.measurable_x hDm
  have e : ∀ Q : X F, conj (stripFn D 0 (phaseW s₁ ν) Q) * WX s₁ ν Q = ((h Q : ℝ) : ℂ) := by
    intro Q
    rw [stripFn_zero, hh]
    by_cases hQ : Q.x ∈ D
    · rw [indicator_of_mem hQ, indicator_of_mem (show Q ∈ X.x ⁻¹' D from hQ), one_mul,
        conj_phaseW_mul]
    · rw [indicator_of_notMem hQ, indicator_of_notMem (show Q ∉ X.x ⁻¹' D from hQ)]
      simp
  have hWint : IntegrableOn (WX s₁ ν : X F → ℂ) (X.box n) (X.vol F) :=
    (continuous_WX hs₁ ν).continuousOn.integrableOn_compact (isCompact_box n)
  have hint0 := cf_integrable (n := n) hDm (measurable_phaseW hs₁ ν) (norm_phaseW_le s₁ ν) hWint
  have hint : IntegrableOn h (X.box n) (X.vol F) := by
    have := hint0.norm
    refine this.congr (Eventually.of_forall fun Q => ?_)
    change ‖conj (stripFn D 0 (phaseW s₁ ν) Q) * WX s₁ ν Q‖ = h Q
    rw [e Q, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    rw [hh]
    exact indicator_nonneg (fun Q _ => norm_nonneg _) Q
  have hnonneg : 0 ≤ᵐ[(X.vol F).restrict (X.box n)] h :=
    Eventually.of_forall fun Q => indicator_nonneg (fun Q _ => norm_nonneg _) Q
  have hWc : Wc D n (phaseW s₁ ν) ν s₁ = ((∫ Q in X.box n, h Q ∂X.vol F : ℝ) : ℂ) := by
    unfold Wc cf
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall e)
  rw [hWc]
  refine Complex.ofReal_ne_zero.mpr (ne_of_gt ?_)
  rw [integral_pos_iff_support_of_nonneg_ae hnonneg hint]
  -- the support contains `{x ∈ D, v ∈ V'}`, of positive measure
  set S' : Set (X F) := X.v ⁻¹' V' ∩ X.x ⁻¹' D with hS'
  have hVm : MeasurableSet (X.v ⁻¹' V' : Set (X F)) := X.measurable_v measurableSet_Icc
  have hS'sub : S' ⊆ Function.support h ∩ X.box n := by
    rintro Q ⟨hQv, hQx⟩
    refine ⟨?_, (mem_box_iff n Q).mpr ⟨hbn _ hQx, hV'sub hQv⟩⟩
    rw [Function.mem_support, hh, indicator_of_mem hQx]
    exact norm_ne_zero_iff.mpr (hne Q fun w => lt_of_le_of_lt (hQv.2 w) hhiδ)
  have hS'pos : X.vol F S' ≠ 0 := by
    have h1 := X.setLIntegral_strip (F := F) hDm
      (f := fun p => V'.indicator (fun _ => (1 : ℝ≥0∞)) p.2)
      ((measurable_const.indicator measurableSet_Icc).comp measurable_snd)
    have h2 : ∫⁻ Q in (X.x ⁻¹' D : Set (X F)), V'.indicator (fun _ => (1 : ℝ≥0∞)) Q.v
        ∂X.vol F = X.vol F S' := by
      have e' : (fun Q : X F => V'.indicator (fun _ => (1 : ℝ≥0∞)) Q.v)
          = (X.v ⁻¹' V' : Set (X F)).indicator 1 := by
        funext Q
        by_cases hQ : Q.v ∈ V'
        · rw [indicator_of_mem hQ, indicator_of_mem (show Q ∈ X.v ⁻¹' V' from hQ)]; rfl
        · rw [indicator_of_notMem hQ, indicator_of_notMem (show Q ∉ X.v ⁻¹' V' from hQ)]
      rw [e', lintegral_indicator_one hVm, Measure.restrict_apply hVm]
    rw [← h2, h1]
    have h3 : ∀ x : InfinitePlace F → ℂ,
        ∫⁻ v, (fun p : (InfinitePlace F → ℂ) × (InfinitePlace F → ℝ) =>
          V'.indicator (fun _ => (1 : ℝ≥0∞)) p.2) (x, v) ∂X.nuV F = X.nuV F V' := fun _ =>
      lintegral_indicator_one measurableSet_Icc
    rw [lintegral_congr h3, lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact mul_ne_zero (nuV_Icc_ne_zero (le_of_eq hlo.symm) hlh hhin) hD0
  rw [Measure.restrict_apply' (X.measurableSet_box n)]
  exact lt_of_lt_of_le (pos_iff_ne_zero.mpr hS'pos) (measure_mono hS'sub)

/-! ### The coefficient of the series over an admissible cell -/

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.T_Cont
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-T, file 5: the continuation of the coefficient series and its residue (generic form)

Function level (`E.slit`, the ray `N.ray t = 4/3 + t(1+i)`):
* `contSlit a₀` — the holomorphic function on `E.slit` agreeing with `a₀` on `Re s > 2`, if there
  is one (`contSlit_spec`, `contSlit_unique`);
* `resSlit a₀ = lim_{t↓0} (s_t − 4/3)·contSlit a₀ (s_t)`.

For a twisted section `Ψ`, a frequency `ν' ≠ 0` and a coefficient series `a₀` with one admissible
cell (`HasSeed Ψ ν' a₀`: some bounded measurable `D₀` of positive volume with
`HasCoefT Ψ ν' a₀ D₀ κ₀`, `κ₀ ≠ 0`):
* `differentiableOn_contSlit`, `contSlit_eq` — MATH2 (C6) for `ν' ≠ 0`;
* **`Afun_eq_contSlit`**: for every `Γ` fixing `Ψ`, every admissible cell `(D, κ)`, every box
  `n ⊇ D` and test function `φ`, on all of `E.slit`
  `∫_{box n} conj (stripFn D (freq ν') φ) · E^{ext} = κ · contSlit a₀ s · Wc D n φ ν' s`;
* `tendsto_resSlit` — MATH2 (C7); `hasResOn` (the `E.HasResOn` statement);
* **`integral_theta_of_hasCoefT`**:
  `∫_{box n} conj (stripFn D (freq ν') φ) · θ_Ψ = κ · resSlit a₀ · Wc D n φ ν' (4/3)`.

The genuine sections `Φ` (`Ψ = Φ.twist`, `a₀ = 𝔞_Φ(ν, ·)`) are in `T_Theta`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.T

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

lemma eqOn_slit {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f E.slit)
    (hg : DifferentiableOn ℂ g E.slit) (h : ∀ s : ℂ, 2 < s.re → f s = g s) :
    EqOn f g E.slit := by
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ) (z₀ := (3 : ℂ))
    (hf.analyticOnNhd isOpen_slit) (hg.analyticOnNhd isOpen_slit)
    E.isPreconnected_slit ⟨by norm_num, fun _ => by norm_num⟩ ?_
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show (2 : ℝ) < (3 : ℂ).re by norm_num)] with s hs
  exact h s hs

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ}

/-! ### Function level -/

theorem contSlit_spec {a₀ : ℂ → ℂ}
    (h : ∃ a : ℂ → ℂ, DifferentiableOn ℂ a E.slit ∧ ∀ s : ℂ, 2 < s.re → a s = a₀ s) :
    DifferentiableOn ℂ (contSlit a₀) E.slit ∧ ∀ s : ℂ, 2 < s.re → contSlit a₀ s = a₀ s := by
  unfold contSlit; rw [dif_pos h]
  exact h.choose_spec

/-- Uniqueness: any holomorphic function on `E.slit` agreeing with `a₀` is `contSlit a₀`. -/
theorem contSlit_unique {a₀ a : ℂ → ℂ} (ha : DifferentiableOn ℂ a E.slit)
    (h : ∀ s : ℂ, 2 < s.re → a s = a₀ s) : EqOn a (contSlit a₀) E.slit := by
  have hs := contSlit_spec ⟨a, ha, h⟩
  exact eqOn_slit ha hs.1 fun s hs' => (h s hs').trans (hs.2 s hs').symm

/-! ### Twisted sections with a coefficient series -/

/-! ### The residue -/

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.T_Linear
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-T, file 7: linearity

Twisted level (for the linear combinations of WP-F, which are not genuine sections):
* `eis_add`, `eis_smulFun` (`Re s > 2`); `HasCoefT.add`, `HasCoefT.smulFun`, `HasCoefT.unique`;
* `resSlit_congr`, `resSlit_add`, `resSlit_mul` (function level) and their forms with seeds
  `resSlit_add_of_seed`, `resSlit_mul_of_seed`: `Res(a₀ + b₀) = Res a₀ + Res b₀`,
  `Res(f·a₀) = f(4/3)·Res a₀` for entire `f`.

Genuine level:
* `aSer_add`, `aSer_smulFun`: the Kubota series is linear in `Φ` (`Re s > 2`), read off the
  Fourier coefficients;
* **`tau_add`, `tau_smulFun`, `tau_smul`**.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.T

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

/-! ### Function level -/

theorem contSlit_congr {a₀ b₀ : ℂ → ℂ} (h : ∀ s : ℂ, 2 < s.re → a₀ s = b₀ s) :
    EqOn (contSlit a₀) (contSlit b₀) E.slit := by
  by_cases hex : ∃ a : ℂ → ℂ, DifferentiableOn ℂ a E.slit ∧ ∀ s : ℂ, 2 < s.re → a s = a₀ s
  · have hs := contSlit_spec hex
    exact contSlit_unique hs.1 fun s hs' => (hs.2 s hs').trans (h s hs')
  · have hex' : ¬ ∃ a : ℂ → ℂ, DifferentiableOn ℂ a E.slit ∧ ∀ s : ℂ, 2 < s.re → a s = b₀ s := by
      rintro ⟨a, ha, hab⟩
      exact hex ⟨a, ha, fun s hs => (hab s hs).trans (h s hs).symm⟩
    unfold contSlit
    rw [dif_neg hex, dif_neg hex']
    exact fun _ _ => rfl

lemma eventually_ray_mem_slit : ∀ᶠ t : ℝ in 𝓝[>] 0, ray t ∈ E.slit := by
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact ray_mem_slit ht

theorem resSlit_congr {a₀ b₀ : ℂ → ℂ} (h : ∀ s : ℂ, 2 < s.re → a₀ s = b₀ s) :
    resSlit a₀ = resSlit b₀ := by
  have heq : (fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) * contSlit a₀ (ray t)) =ᶠ[𝓝[>] 0]
      fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) * contSlit b₀ (ray t) := by
    filter_upwards [eventually_ray_mem_slit] with t ht
    rw [contSlit_congr h ht]
  unfold resSlit limUnder
  rw [Filter.map_congr heq]

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ}

/-! ### Twisted sections -/

/-! ### Genuine sections -/

section genuine

variable {P : CubicPkg F} (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  (Φ Φ' : GSection ι P 𝔪) {ν : SInt 𝔪}

theorem tau_smul (hν : ν ≠ 0) (c : ℂ) : tau hG hz6 (c • Φ) ν = c * tau hG hz6 Φ ν :=
  tau_smulFun hG hz6 Φ hν (fun _ => c) (differentiable_const c)

end genuine

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

/-! ### Genuine sections: the stabilizer contains `n(Λ_M)` -/

section genuine

variable {P : CubicPkg F} (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  (Φ : GSection ι P 𝔪)

lemma inv_stabGroup (Ψ : TSection ι 𝔪) : Inv (stabGroup Ψ) Ψ := fun _ hγ => hγ

lemma le_stabGroup {Γ : Subgroup (SL(2, 𝓞 F))} {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) :
    Γ ≤ stabGroup Ψ := fun γ hγ => hΓ γ hγ

include hG hz6 in
theorem finiteIndex_stabGroup (Pk : CubicPkg F) (Ψ : TSection ι 𝔪) :
    (stabGroup Ψ).FiniteIndex := by
  obtain ⟨Γ₀, hfi, hΓ₀⟩ := exists_finiteIndex_inv Pk hG hz6 Ψ
  exact Subgroup.finiteIndex_of_le (le_stabGroup hΓ₀)

lemma intMat_nInt (β : 𝓞 F) :
    RO.intMat 𝔪 (nInt β) = S.nMat (algebraMap (𝓞 F) (SInt 𝔪) β) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [RO.intMat, nInt_coe, S.nMat]

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

lemma countable_latO : Countable (latO F) :=
  haveI _iCO := ArtinKP.X.instCountableRingOfIntegers (F := F)
  ((Set.to_countable ((⊤ : AddSubgroup (𝓞 F)) : Set (𝓞 F))).image embO).to_subtype

lemma Adm.countable {A : AddSubgroup (InfinitePlace F → ℂ)} (h : Adm A) : Countable A := by
  have := countable_latO (F := F)
  exact (AddSubgroup.inclusion_injective h.le).countable

/-! ### Scaled lattices and cells -/

lemma emb_one : emb (1 : F) = 1 := by
  ext w; simp

lemma emb_inv_mul {a : F} (ha : a ≠ 0) (x : InfinitePlace F → ℂ) :
    emb a⁻¹ * (emb a * x) = x := by
  rw [← mul_assoc, ← emb_mul, inv_mul_cancel₀ ha, emb_one, one_mul]

lemma emb_mul_inv {a : F} (ha : a ≠ 0) (x : InfinitePlace F → ℂ) :
    emb a * (emb a⁻¹ * x) = x := by
  rw [← mul_assoc, ← emb_mul, mul_inv_cancel₀ ha, emb_one, one_mul]

lemma mem_scaleSet {a : F} (ha : a ≠ 0) {D : Set (InfinitePlace F → ℂ)}
    {x : InfinitePlace F → ℂ} : x ∈ scaleSet a D ↔ emb a⁻¹ * x ∈ D := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [emb_inv_mul ha]
  · intro h
    exact ⟨_, h, emb_mul_inv ha x⟩

lemma measurableSet_scaleSet {a : F} (ha : a ≠ 0) {D : Set (InfinitePlace F → ℂ)}
    (hD : MeasurableSet D) : MeasurableSet (scaleSet a D) := by
  have e : scaleSet a D = (fun x : InfinitePlace F → ℂ => emb a⁻¹ * x) ⁻¹' D := by
    ext x; exact mem_scaleSet ha
  rw [e]
  exact (continuous_const.mul continuous_id).measurable hD

lemma pcell_scale {a : F} (ha : a ≠ 0) {L : AddSubgroup (InfinitePlace F → ℂ)}
    {D : Set (InfinitePlace F → ℂ)} (hD : PCell L D) : PCell (scaleLat a L) (scaleSet a D) := by
  refine ⟨measurableSet_scaleSet ha hD.meas, fun x => ?_⟩
  obtain ⟨g₀, hg₀, huniq⟩ := hD.fund (emb a⁻¹ * x)
  refine ⟨⟨emb a * (g₀ : InfinitePlace F → ℂ), ⟨g₀, g₀.2, rfl⟩⟩, ?_, ?_⟩
  · change emb a * (g₀ : InfinitePlace F → ℂ) + x ∈ scaleSet a D
    rw [mem_scaleSet ha, mul_add, emb_inv_mul ha]
    exact hg₀
  · rintro ⟨g, y, hy, rfl⟩ hg
    have hg' : emb a * y + x ∈ scaleSet a D := hg
    rw [mem_scaleSet ha, mul_add, emb_inv_mul ha] at hg'
    have := huniq ⟨y, hy⟩ hg'
    apply Subtype.ext
    change emb a * y = emb a * (g₀ : InfinitePlace F → ℂ)
    rw [← this]

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

/-- `a·Λ_M ⊆ Λ_{M−K}` for `a ∈ R` with `|a|_v ≤ q_v^K` on `S_f`. -/
lemma scaleLat_transLat_le (r : SInt 𝔪) {K M : ℤ} (hK : Small 𝔪 (-K) (r : F)) :
    scaleLat (r : F) (transLat 𝔪 M) ≤ transLat 𝔪 (M - K) := by
  rintro x ⟨y, ⟨b, hb, rfl⟩, rfl⟩
  refine ⟨r * b, ?_, ?_⟩
  · have h1 : Small 𝔪 (-K + M) ((r : F) * (b : F)) := hK.mul hb
    have e : -K + M = M - K := by ring
    rw [e] at h1
    exact h1
  · change emb (((r * b : SInt 𝔪) : F)) = emb (r : F) * emb (b : F)
    rw [← emb_mul]
    rfl

/-- `a·Λ_M` contains the image of a nonzero ideal. -/
lemma exists_idealLat_le_scaleLat (h𝔪 : 𝔪 ≠ ⊥) {a : F} (ha : a ≠ 0) (M : ℤ) :
    ∃ I : Ideal (𝓞 F), I ≠ ⊥ ∧ idealLat I ≤ scaleLat a (transLat 𝔪 M) := by
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 F) (K := F) a
  have hy0 : (algebraMap (𝓞 F) F y) ≠ 0 :=
    RingOfIntegers.coe_ne_zero_iff.mpr (nonZeroDivisors.ne_zero hy)
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hxy
    exact ha hxy.symm
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔪
  refine ⟨Ideal.span {x * b ^ M.toNat}, by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact mul_ne_zero hx0 (pow_ne_zero _ hb0), ?_⟩
  rintro z ⟨β, hβ, rfl⟩
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hβ
  have e : ((algebraMap (𝓞 F) (SInt 𝔪) (c * y * b ^ M.toNat) : SInt 𝔪) : F)
      = ((c : 𝓞 F) : F) * ((y : 𝓞 F) : F) * ((b : 𝓞 F) : F) ^ M.toNat := by
    change (((c * y * b ^ M.toNat : 𝓞 F)) : F) = _
    push_cast; rfl
  refine ⟨embR (algebraMap (𝓞 F) (SInt 𝔪) (c * y * b ^ M.toNat)), ⟨_, ?_, rfl⟩, ?_⟩
  · have h1 : Small 𝔪 0 ((c * y : 𝓞 F) : F) := fun v _ => by
      simpa using v.valuation_le_one (K := F) (c * y)
    have h2 := h1.mul (small_pow_of_mem hb M.toNat)
    have h3 : Small 𝔪 M ((((c * y : 𝓞 F)) : F) * ((b : 𝓞 F) : F) ^ M.toNat) :=
      h2.mono (by rw [zero_add]; exact Int.self_le_toNat M)
    change Small 𝔪 M (((algebraMap (𝓞 F) (SInt 𝔪) (c * y * b ^ M.toNat) : SInt 𝔪) : F))
    rw [e]
    push_cast at h3
    exact h3
  · change emb a * emb (((algebraMap (𝓞 F) (SInt 𝔪) (c * y * b ^ M.toNat) : SInt 𝔪) : F))
      = emb (((c * (x * b ^ M.toNat) : 𝓞 F)) : F)
    rw [← emb_mul, e]
    congr 1
    have hxy' : a = ((x : 𝓞 F) : F) / ((y : 𝓞 F) : F) := hxy.symm
    have hy0' : ((y : 𝓞 F) : F) ≠ 0 := hy0
    rw [hxy']
    push_cast
    field_simp

/-- **`a·Λ_M` is admissible** for `a ∈ R ∖ 0` and `M` beyond the `S_f`-size of `a`. -/
lemma adm_scaleLat (h𝔪 : 𝔪 ≠ ⊥) (r : SInt 𝔪) (hr : (r : F) ≠ 0) {K M : ℤ}
    (hK : Small 𝔪 (-K) (r : F)) (hKM : K ≤ M) : Adm (scaleLat (r : F) (transLat 𝔪 M)) :=
  ⟨(scaleLat_transLat_le r hK).trans (transLat_le_latO (by omega)),
    exists_idealLat_le_scaleLat h𝔪 hr M⟩

/-! ### Coefficients over cells of admissible lattices -/

/-- `kap 𝔪 M` does not depend on `M ≥ 0`. -/
lemma kap_eq_zero' (h𝔪 : 𝔪 ≠ ⊥) {M : ℤ} (hM : 0 ≤ M) : kap 𝔪 M = kap 𝔪 0 := by
  rw [kap_eq h𝔪 hM, kap_eq h𝔪 le_rfl]

end

end ArtinKP.F
end

section
-- module Solutions.Artin.KP.S2_Translate
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-S2, part 3: genuine sections are stable under `SL₂(F)`, in particular under `SL₂(R)`

* `GSection.translateF α β γ δ` (`αδ - βγ = 1`, entries in `F`):
  `(σ·Φ)_s(p) = σ_S(p, σ)⁻¹ Φ_s(pσ)`.  It is a genuine section: (S1), (S1³) by `sig_smul`, the
  level condition by Kubota's cocycle identity (`sig_cocycle`, twice) and `sig_conj`.
* `GSection.translate σ` for `σ ∈ SL₂(R)`: `κ(σ) · translateF σ`, and
  `twist_translate : twist (translate σ Φ) = TSection.translate σ (twist Φ)` — MATH2 §5.2's `Φ^σ`.
* `translate_mul`: `translate (σ₁ σ₂) Φ = translate σ₁ (translate σ₂ Φ)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S2

open ArtinKP.A ArtinKP.S

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

namespace GSection

theorem translate_apply (hG : Good 𝔪) (σ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪))
    (Φ : GSection ι P 𝔪) (s : ℂ) (c d : F) :
    translate hG σ Φ s c d = kappa ι 𝔪 σ *
      ((sig ι P 𝔪 c d ((σ.1 0 0 : SInt 𝔪) : F) ((σ.1 0 1 : SInt 𝔪) : F)
        ((σ.1 1 0 : SInt 𝔪) : F) ((σ.1 1 1 : SInt 𝔪) : F))⁻¹ *
      Φ s (c * ((σ.1 0 0 : SInt 𝔪) : F) + d * ((σ.1 1 0 : SInt 𝔪) : F))
        (c * ((σ.1 0 1 : SInt 𝔪) : F) + d * ((σ.1 1 1 : SInt 𝔪) : F))) := rfl

/-- **Genuine sections are stable under `SL₂(R)`**: the twist of the genuine translate is the
right translate of the twist. -/
theorem twist_translate (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
    (σ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)) (Φ : GSection ι P 𝔪) :
    (translate hG σ Φ).twist hG hz6 = TSection.translate P hG hz6 σ (Φ.twist hG hz6) := by
  ext s p
  rw [GSection.twist_apply, TSection.translate_apply, GSection.twist_apply, translate_apply,
    kappaRow_act ι P hG hz6]
  have hc : (((p.act σ).c : SInt 𝔪) : F) = (p.c : F) * ((σ.1 0 0 : SInt 𝔪) : F)
      + (p.d : F) * ((σ.1 1 0 : SInt 𝔪) : F) := by
    rw [Row.act_c]; push_cast; rfl
  have hd : (((p.act σ).d : SInt 𝔪) : F) = (p.c : F) * ((σ.1 0 1 : SInt 𝔪) : F)
      + (p.d : F) * ((σ.1 1 1 : SInt 𝔪) : F) := by
    rw [Row.act_d]; push_cast; rfl
  rw [hc, hd]
  ring

end GSection

end ArtinKP.S2
end
end

section
-- module Solutions.Artin.KP.F_Per_Sharp
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-- The three symbol factors of `A(β)³` multiply to `1`. -/
lemma tf_three (β : F) (hβ : β ≠ 0) (c d : F) :
    tf ι P 𝔪 β c d * (tf ι P 𝔪 β (β ^ 2 * c) (β * d)
      * tf ι P 𝔪 β (β ^ 2 * (β ^ 2 * c)) (β * (β * d))) = 1 := by
  by_cases hc : c = 0
  · subst hc
    simp only [mul_zero, tf, if_true]
    by_cases hd : d = 0
    · subst hd; simp
    · rw [brk_mul_left _ hβ (mul_ne_zero hβ hd), brk_mul_left _ hβ hd, brk_self]
      have h3 := brk_pow_three (ι := ι) (P := P) (𝔪 := 𝔪) d β
      linear_combination h3
  · have h2 : β ^ 2 * c ≠ 0 := mul_ne_zero (pow_ne_zero 2 hβ) hc
    have h4 : β ^ 2 * (β ^ 2 * c) ≠ 0 := mul_ne_zero (pow_ne_zero 2 hβ) h2
    rw [tf, if_neg hc, tf, if_neg h2, tf, if_neg h4,
      brk_mul_left _ (pow_ne_zero 2 hβ) h2, brk_mul_left _ (pow_ne_zero 2 hβ) hc, pow_two β,
      brk_mul_left _ hβ hβ, brk_self]
    have h3 := brk_pow_three (ι := ι) (P := P) (𝔪 := 𝔪) c β
    linear_combination (brk ι P 𝔪 c β ^ 3 + 1) * h3

include hz6 in
/-- **`Ã(π)³ Φ = |π|_{S_f}^{-3} Φ♯`.** -/
theorem iterate_act {π : SInt 𝔪} (hπ : (π : F) ≠ 0) :
    ((kubota (ι := ι) (P := P) hG hz6).act π)^[3] Φ
      = (((absS 𝔪 (π : F) : ℝ) : ℂ)⁻¹ ^ 3) • Φ.sharp hG (π : F) hπ := by
  have hact : ∀ Ψ : GSection ι P 𝔪, (kubota (ι := ι) (P := P) hG hz6).act π Ψ
      = Ψ.torusT hG (π : F) hπ := fun Ψ => by
    rw [kubota_act, S2.actR, dif_neg hπ]
  have ha0 : ((absS 𝔪 (π : F) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (absS_pos hπ).ne'
  ext s c d
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id, hact]
  rw [GSection.smul_apply, GSection.sharp_apply, GSection.torusT_apply, GSection.torusT_apply,
    GSection.torusT_apply]
  have e1 : (π : F) ^ 2 * ((π : F) ^ 2 * ((π : F) ^ 2 * c)) = ((π : F) ^ 2) ^ 3 * c := by ring
  have e2 : (π : F) * ((π : F) * ((π : F) * d)) = ((π : F) ^ 2) ^ 3 * (d / (π : F) ^ 3) := by
    field_simp
  rw [e1, e2, Φ.cube s ((π : F) ^ 2) (pow_ne_zero 2 hπ), absS_pow]
  have key := tf_three (ι := ι) (P := P) (𝔪 := 𝔪) (π : F) hπ c d
  have hA : ((absS 𝔪 (π : F) : ℝ) : ℂ) ^ (2 * s - 1) * (((absS 𝔪 (π : F) : ℝ) : ℂ) ^ (2 * s - 1)
      * (((absS 𝔪 (π : F) : ℝ) : ℂ) ^ (2 * s - 1)
        * (((absS 𝔪 (π : F) ^ 2 : ℝ) : ℂ)) ^ (-(3 * s))))
      = ((absS 𝔪 (π : F) : ℝ) : ℂ)⁻¹ ^ 3 := by
    have hpos := absS_pos (𝔪 := 𝔪) hπ
    have hx2 : (0 : ℝ) < absS 𝔪 (π : F) ^ 2 := by positivity
    have e3 : ((absS 𝔪 (π : F) : ℝ) : ℂ)⁻¹ ^ 3
        = Complex.exp ((Real.log (absS 𝔪 (π : F)) : ℂ) * (-3)) := by
      rw [← cpow_pos_eq hpos, show (-3 : ℂ) = -((3 : ℕ) : ℂ) by norm_num, Complex.cpow_neg,
        Complex.cpow_natCast, inv_pow]
    rw [e3, cpow_pos_eq hpos, cpow_pos_eq hx2, Real.log_pow, ← Complex.exp_add,
      ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination
    (((absS 𝔪 (π : F) : ℝ) : ℂ) ^ (2 * s - 1) * (((absS 𝔪 (π : F) : ℝ) : ℂ) ^ (2 * s - 1)
      * (((absS 𝔪 (π : F) : ℝ) : ℂ) ^ (2 * s - 1)
        * (((absS 𝔪 (π : F) ^ 2 : ℝ) : ℂ)) ^ (-(3 * s)))) * Φ s c (d / (π : F) ^ 3)) * key
      + Φ s c (d / (π : F) ^ 3) * hA

end

end ArtinKP.F
end

section
-- module Solutions.Artin.KP.F_Per_U
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-- Deep `T` exist (`FB.exists_U_eis_gen`). -/
theorem exists_isU (N₀ : ℤ) : ∃ T : Finset (SInt 𝔪), IsU hG hz6 h g Φ T ∧
    ∀ t ∈ T, Small 𝔪 N₀ (t : F) ∧ Small 𝔪 N₀ ((t : F) / (g.gen v.asIdeal : F) ^ 3) := by
  obtain ⟨T, hT, hsm, hU⟩ := FB.exists_U_eis_gen P hG hz6 h g Φ N₀
  exact ⟨T, ⟨hT, fun s hs Q => hU s hs Q⟩, hsm⟩

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

end

end ArtinKP.F
end

section
-- module Solutions.Artin.KP.F_Per_Const
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

section general

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-- Translations by `r` with `Φ_s(c, d + c r) = Φ_s(c, d)` lie in the lattice of the stabilizer. -/
lemma mem_latN_stabGroup_of_unip (Φ : GSection ι P 𝔪) {x : InfinitePlace F → ℂ}
    (hx : x ∈ latO F) {r : F} (hxr : x = emb r)
    (hunip : ∀ (s : ℂ) (c d : F), Φ s c (d + c * r) = Φ s c d) :
    x ∈ latN (stabGroup (Φ.twist hG hz6)) := by
  obtain ⟨β, -, hβ⟩ := hx
  have hβr : ((β : 𝓞 F) : F) = r := by
    have h0 : emb (((β : 𝓞 F) : F) - r) = 0 := by
      rw [map_sub, sub_eq_zero, ← hxr]
      exact hβ
    exact sub_eq_zero.mp (emb_eq_zero h0)
  refine ⟨β, ?_, hβ⟩
  change RO.intMat 𝔪 (nInt β) ∈ (Φ.twist hG hz6).stab
  rw [intMat_nInt, TSection.mem_stab]
  intro s p
  rw [GSection.twist_apply, GSection.twist_apply, kappaRow_n ι P hG hz6, act_nMat_c,
    act_nMat_d]
  have h3 := hunip s (p.c : F) (p.d : F)
  push_cast
  rw [add_comm]
  rw [show (algebraMap (𝓞 F) F) β = r from hβr, h3]

end general

/-! ### Powers of positive reals -/

/-! ### The constant term of `E_{Φ♯ρ_∞}` over scaled cells -/

section gen

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (h : C3I.Good 𝔪 v)
  (g : AllowedGen ι 𝔪) (Φ : GSection ι P 𝔪)

include h in
lemma absNorm_eq_mul (h𝔪 : 𝔪 ≠ ⊥) :
    (Ideal.absNorm v.asIdeal : ℂ)
      = ((Ninf (g.gen v.asIdeal : F) * absS 𝔪 (g.gen v.asIdeal : F) : ℝ) : ℂ) := by
  rw [FB.Ninf_mul_absS_gen h g h𝔪, card_quot_gen h g, Complex.ofReal_natCast]

include h in
lemma one_lt_absNorm : 1 < Ideal.absNorm v.asIdeal := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
  exact_mod_cast this

include hG hz6 in
/-- `a·Λ_M` consists of periods of `Φ♯` (`a = π³`, `M` a depth of unipotent invariance of `Φ`). -/
lemma scaleLat_le_stab_sharp {π : F} (hπ : π ≠ 0) {M : ℤ}
    (hunip : ∀ b : F, Small 𝔪 M b → ∀ (s : ℂ) (c d : F), Φ s c (d + c * b) = Φ s c d)
    (hA : scaleLat (π ^ 3) (transLat 𝔪 M) ≤ latO F) :
    scaleLat (π ^ 3) (transLat 𝔪 M) ≤ latN (stabGroup ((Φ.sharp hG π hπ).twist hG hz6)) := by
  intro x hx
  obtain ⟨y, ⟨b, hb, rfl⟩, rfl⟩ := hx
  refine mem_latN_stabGroup_of_unip hG hz6 _ (hA ⟨_, ⟨b, hb, rfl⟩, rfl⟩) (r := π ^ 3 * (b : F))
    (by rw [emb_mul]; rfl) fun s c d => ?_
  rw [GSection.sharp_apply, GSection.sharp_apply]
  have e : (d + c * (π ^ 3 * (b : F))) / π ^ 3 = d / π ^ 3 + c * (b : F) := by
    field_simp
  rw [e, hunip _ hb]

end gen

end

end ArtinKP.F
end

section
-- module Solutions.Artin.KP.F_Per_Z
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-F, file 5: the residue `z_Ψ` — linearity, translations, `ρ_∞`

* `zPsi_of_mD`: `z_Ψ` from a continuation of `mD D Ψ` over a strict cell.
* `zPsi_add`, `zPsi_smul`, `zPsi_sum`: `Ψ ↦ z_Ψ` is linear.
* `zPsi_translate_nMat`: `z_{n(t)·Ψ} = z_Ψ` for `t ∈ R`.
* **`zPsi_restrict`**: `z_{Φρ_∞} = q/(q+1) · z_Φ` for every genuine section `Φ`.
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

/-! ### Finite sums of twisted sections -/

lemma sum_apply {α : Type*} (Tf : Finset α) (Ψ : α → TSection ι 𝔪) (s : ℂ) (p : Row 𝔪) :
    (∑ t ∈ Tf, Ψ t) s p = ∑ t ∈ Tf, Ψ t s p := by
  classical
  induction Tf using Finset.induction_on with
  | empty => simp
  | insert a Tf ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, TSection.add_apply, ih]

section z

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

include hG hz6 in
/-- A finite-index group fixing two sections, with a strict cell. -/
lemma exists_common (P : CubicPkg F) (Ψ Ψ' : TSection ι 𝔪) : ∃ (Γ : Subgroup (SL(2, 𝓞 F))) (_ : Γ.FiniteIndex)
    (D : Set (InfinitePlace F → ℂ)) (n : ℕ), Inv Γ Ψ ∧ Inv Γ Ψ' ∧ PCell (latN Γ) D ∧
      (∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) ∧ 1 ≤ n := by
  have h1 := finiteIndex_stabGroup hG hz6 P Ψ
  have h2 := finiteIndex_stabGroup hG hz6 P Ψ'
  have h3 : (stabGroup Ψ ⊓ stabGroup Ψ').FiniteIndex := inferInstance
  obtain ⟨D, n, hD, hb⟩ := exists_pcell_latN (stabGroup Ψ ⊓ stabGroup Ψ')
  refine ⟨_, h3, D, max n 1, fun γ hγ => inv_stabGroup Ψ γ hγ.1,
    fun γ hγ => inv_stabGroup Ψ' γ hγ.2, hD, fun x hx w => (hb x hx w).trans ?_, le_max_right _ _⟩
  exact_mod_cast le_max_left n 1

/-! ### Translations -/

/-! ### `ρ_∞` -/

end z

end

end ArtinKP.F
end

section
-- module Solutions.Artin.KP.F_Per_Kernel
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-F, file 6: the Kernel Lemma 5.3

* `translate_restrict_of_dvd`: for `σ ∈ SL₂(R)` with `π ∣ σ₁₀`, `σ·(Ψρ_∞) = (σ·Ψ)ρ_∞`.
* `sum_translate_restrict`: for `π ∤ σ₁₀` and `T₁` representatives of `R/π` fixing `σ·Ψ`,
  `∑_{t ∈ T₁} n(t)·σ·(Ψρ_∞) + (σ·Ψ)ρ_∞ = q • σ·Ψ` (the `q + 1` points of `ℙ¹(R/P)`).
* `zPsi_translate_restrict`: `z_{σ·(Φρ_∞)} = (q/(q+1)) z_{σ·Φ}` for **every** `σ ∈ SL₂(R)`
  (MATH2 §5.2: "the finite identities among the `z_η`").
* **`kernel`**: `θ_{Φρ_∞} = (q/(q+1)) θ_Φ` (Corollary N, `N2.theta_eq_zero_iff`).

MATH2 obtains the finite cusps from an unfolding with the lattice `Λ ∩ πR`; here they follow from
the cusp `∞` (`zPsi_restrict`), linearity of `z`, and `z_{n(t)·Ψ} = z_Ψ`.
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

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (h : C3I.Good 𝔪 v)
  (g : AllowedGen ι 𝔪)

include h in
lemma prime_gen : Prime (g.gen v.asIdeal) :=
  (Ideal.span_singleton_prime (gen_ne_zero h g)).mp (isMaximal_span_gen h g).isPrime

include hG hz6 h in
lemma val_iff_gen (P : CubicPkg F) (c : SInt 𝔪) :
    v.valuation F (c : F) = 1 ↔ ¬ g.gen v.asIdeal ∣ c :=
  (FB.primeElt_gen_of_good P hG hz6 h g).val_iff (not_le_of_good h) c

include h in
/-- A complete set of representatives of `R/π` has `q` elements. -/
lemma card_reps (h𝔪 : 𝔪 ≠ ⊥) {T₁ : Finset (SInt 𝔪)} (hT₁ : IsReps (g.gen v.asIdeal) T₁) :
    (T₁.card : ℂ) = (Ideal.absNorm v.asIdeal : ℂ) := by
  have h1 := sum_reps hT₁ (f := fun _ => (1 : ℂ)) (fun _ _ _ => rfl)
  have h2 := rsum_pow_one (gen_ne_zero h g) (finite_quot_gen_pow h g h𝔪) 1
  rw [pow_one, pow_one] at h2
  rw [h2, card_quot_gen h g] at h1
  rw [← h1]
  simp

include hG hz6 h in
/-- **`σ·(Ψρ_∞) = (σ·Ψ)ρ_∞`** when the lower left entry of `σ` is divisible by `π`. -/
theorem translate_restrict_of_dvd (Ψ : TSection ι 𝔪) (σ : SL(2, SInt 𝔪))
    (hσ : g.gen v.asIdeal ∣ σ.1 1 0) :
    TSection.translate P hG hz6 σ (TSection.restrict v (not_le_of_good h) Ψ)
      = TSection.restrict v (not_le_of_good h) (TSection.translate P hG hz6 σ Ψ) := by
  have hp := prime_gen h g
  have hdet := σ.2
  rw [Matrix.det_fin_two] at hdet
  have ha : ¬ g.gen v.asIdeal ∣ σ.1 0 0 := by
    intro hd
    have : g.gen v.asIdeal ∣ σ.1 0 0 * σ.1 1 1 - σ.1 0 1 * σ.1 1 0 :=
      dvd_sub (Dvd.dvd.mul_right hd _) (Dvd.dvd.mul_left hσ _)
    rw [hdet] at this
    exact hp.not_isUnit (isUnit_of_dvd_one this)
  have key : ∀ p : Row 𝔪, v.valuation F ((p.act σ).c : F) = 1 ↔ v.valuation F (p.c : F) = 1 := by
    intro p
    rw [val_iff_gen hG hz6 h g P, val_iff_gen hG hz6 h g P, not_iff_not, Row.act_c]
    constructor
    · intro hd
      have h1 : g.gen v.asIdeal ∣ p.c * σ.1 0 0 :=
        (dvd_add_left (Dvd.dvd.mul_left hσ _)).mp hd
      exact (hp.dvd_or_dvd h1).resolve_right ha
    · intro hd
      exact dvd_add (Dvd.dvd.mul_right hd _) (Dvd.dvd.mul_left hσ _)
  ext s p
  rw [TSection.translate_apply]
  by_cases hv : v.valuation F (p.c : F) = 1
  · rw [TSection.restrict_apply_of_val _ _ s ((key p).mpr hv),
      TSection.restrict_apply_of_val _ _ s hv, TSection.translate_apply]
  · rw [TSection.restrict_apply_of_not_val _ _ s (fun h' => hv ((key p).mp h')),
      TSection.restrict_apply_of_not_val _ _ s hv]

open Classical in
include hG hz6 h in
/-- **The `q` finite points of `ℙ¹(R/P)`**: for `π ∤ σ₁₀`,
`∑_{t ∈ T₁} n(t)·σ·(Ψρ_∞) + (σ·Ψ)ρ_∞ = q • σ·Ψ`. -/
theorem sum_translate_restrict (Ψ : TSection ι 𝔪) (σ : SL(2, SInt 𝔪))
    (hσ : ¬ g.gen v.asIdeal ∣ σ.1 1 0) {T₁ : Finset (SInt 𝔪)}
    (hT₁ : IsReps (g.gen v.asIdeal) T₁)
    (hinv : ∀ t ∈ T₁, ∀ (s : ℂ) (p : Row 𝔪),
      TSection.translate P hG hz6 σ Ψ s (p.act (_root_.ArtinKP.S.nMat t)) = TSection.translate P hG hz6 σ Ψ s p) :
    (∑ t ∈ T₁, TSection.translate P hG hz6 (_root_.ArtinKP.S.nMat t)
        (TSection.translate P hG hz6 σ (TSection.restrict v (not_le_of_good h) Ψ)))
      + TSection.restrict v (not_le_of_good h) (TSection.translate P hG hz6 σ Ψ)
      = (Ideal.absNorm v.asIdeal : ℂ) • TSection.translate P hG hz6 σ Ψ := by
  have h𝔪 := hG.ne_bot
  have hp := prime_gen h g
  have hH := FB.primeElt_gen_of_good P hG hz6 h g
  ext s p
  rw [TSection.add_apply, sum_apply, TSection.smul_apply]
  set A : ℂ := TSection.translate P hG hz6 σ Ψ s p with hA
  set e : SInt 𝔪 → SInt 𝔪 := fun t => p.c * σ.1 0 0 + (p.c * t + p.d) * σ.1 1 0 with he
  have hterm : ∀ t ∈ T₁, TSection.translate P hG hz6 (_root_.ArtinKP.S.nMat t)
      (TSection.translate P hG hz6 σ (TSection.restrict v (not_le_of_good h) Ψ)) s p
      = if g.gen v.asIdeal ∣ e t then 0 else A := by
    intro t ht
    rw [TSection.translate_apply, TSection.translate_apply]
    have hc : ((p.act (_root_.ArtinKP.S.nMat t)).act σ).c = e t := by
      rw [Row.act_c, act_nMat_c, act_nMat_d]
    by_cases hd : g.gen v.asIdeal ∣ e t
    · rw [if_pos hd, TSection.restrict_apply_of_not_val _ _ s
        (fun h' => (val_iff_gen hG hz6 h g P _).mp h' (by rw [hc]; exact hd))]
    · rw [if_neg hd, TSection.restrict_apply_of_val _ _ s
        ((val_iff_gen hG hz6 h g P _).mpr (by rw [hc]; exact hd)), hA, ← hinv t ht s p,
        TSection.translate_apply]
  rw [Finset.sum_congr rfl hterm]
  have hsplit : ∑ t ∈ T₁, (if g.gen v.asIdeal ∣ e t then 0 else A)
      = (Ideal.absNorm v.asIdeal : ℂ) * A - ∑ t ∈ T₁, (if g.gen v.asIdeal ∣ e t then A else 0) := by
    rw [← card_reps h g h𝔪 hT₁, eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (g := fun _ => A) (fun t _ => by split_ifs <;> simp)]
    simp
  rw [hsplit]
  by_cases hpc : g.gen v.asIdeal ∣ p.c
  · -- `p ≡ ∞`: no `t` is excluded
    have hpd : ¬ g.gen v.asIdeal ∣ p.d := by
      intro hd
      obtain ⟨a, b, hab⟩ := p.coprime
      have : g.gen v.asIdeal ∣ a * p.c + b * p.d :=
        dvd_add (Dvd.dvd.mul_left hpc _) (Dvd.dvd.mul_left hd _)
      rw [hab] at this
      exact hp.not_isUnit (isUnit_of_dvd_one this)
    have hno : ∀ t ∈ T₁, ¬ g.gen v.asIdeal ∣ e t := by
      intro t _ hd
      have e1 : e t = p.c * (σ.1 0 0 + t * σ.1 1 0) + p.d * σ.1 1 0 := by simp only [he]; ring
      rw [e1] at hd
      have h1 : g.gen v.asIdeal ∣ p.d * σ.1 1 0 :=
        (dvd_add_right (Dvd.dvd.mul_right hpc _)).mp hd
      exact (hp.dvd_or_dvd h1).elim hpd hσ
    rw [Finset.sum_congr rfl (g := fun _ => (0 : ℂ)) (fun t ht => if_neg (hno t ht)),
      TSection.restrict_apply_of_not_val _ _ s
        (fun h' => (val_iff_gen hG hz6 h g P _).mp h' hpc)]
    simp
  · -- a finite point: exactly one `t` is excluded
    have hu : ¬ g.gen v.asIdeal ∣ p.c * σ.1 1 0 := fun hd => (hp.dvd_or_dvd hd).elim hpc hσ
    obtain ⟨a, b, hab⟩ := (hH.coprime_iff _).mpr hu
    have hna : ¬ g.gen v.asIdeal ∣ a := by
      intro hd
      have : g.gen v.asIdeal ∣ a * (p.c * σ.1 1 0) + b * g.gen v.asIdeal :=
        dvd_add (Dvd.dvd.mul_right hd _) (Dvd.dvd.mul_left dvd_rfl _)
      rw [hab] at this
      exact hp.not_isUnit (isUnit_of_dvd_one this)
    set x : SInt 𝔪 := -(a * (p.c * σ.1 0 0 + p.d * σ.1 1 0)) with hx
    have hiff : ∀ t : SInt 𝔪, g.gen v.asIdeal ∣ e t ↔ g.gen v.asIdeal ∣ x - t := by
      intro t
      have e1 : a * e t = -(x - t) - b * g.gen v.asIdeal * t := by
        simp only [he, hx]
        linear_combination t * hab
      constructor
      · intro hd
        have h1 : g.gen v.asIdeal ∣ a * e t + b * g.gen v.asIdeal * t :=
          dvd_add (Dvd.dvd.mul_left hd _) (Dvd.dvd.mul_right (Dvd.dvd.mul_left dvd_rfl _) _)
        rw [e1, sub_add_cancel] at h1
        exact (dvd_neg.mp h1)
      · intro hd
        have h1 : g.gen v.asIdeal ∣ a * e t := by
          rw [e1]
          exact dvd_sub (dvd_neg.mpr hd) (Dvd.dvd.mul_right (Dvd.dvd.mul_left dvd_rfl _) _)
        exact (hp.dvd_or_dvd h1).resolve_left hna
    obtain ⟨t₀, ⟨ht₀, hd₀⟩, huniq⟩ := hT₁ x
    have hone : ∑ t ∈ T₁, (if g.gen v.asIdeal ∣ e t then A else 0) = A := by
      rw [Finset.sum_eq_single t₀ (fun t ht hne => if_neg fun hd =>
        hne (huniq t ⟨ht, (hiff t).mp hd⟩)) (fun hnot => (hnot ht₀).elim),
        if_pos ((hiff t₀).mpr hd₀)]
    rw [hone, TSection.restrict_apply_of_val _ _ s ((val_iff_gen hG hz6 h g P _).mpr hpc)]
    ring

include hG hz6 h g in
/-- **The finite identities among the `z_η`** (MATH2 §5.2): for every genuine section `Φ` and
every `σ ∈ SL₂(R)`, `z_{σ·(Φρ_∞)} = (q/(q+1)) · z_{σ·Φ}`. -/
theorem zPsi_translate_restrict (Φ : GSection ι P 𝔪) (σ : SL(2, SInt 𝔪)) :
    zPsi P hG hz6 (TSection.translate P hG hz6 σ
        (TSection.restrict v (not_le_of_good h) (Φ.twist hG hz6)))
      = cq v * zPsi P hG hz6 (TSection.translate P hG hz6 σ (Φ.twist hG hz6)) := by
  have h𝔪 := hG.ne_bot
  have htw := S2.GSection.twist_translate hG hz6 σ Φ
  by_cases hσ : g.gen v.asIdeal ∣ σ.1 1 0
  · rw [translate_restrict_of_dvd hG hz6 h g _ σ hσ, ← htw]
    exact zPsi_restrict_twist hG hz6 h g _
  · obtain ⟨M, hV⟩ := exists_validDepth hG (S2.GSection.translate hG σ Φ) (0 : F)
    obtain ⟨T₁, hT₁, hsm⟩ := FB.exists_deep_reps_gen h g h𝔪 1 M
    rw [pow_one] at hT₁
    have hinv : ∀ t ∈ T₁, ∀ (s : ℂ) (p : Row 𝔪),
        TSection.translate P hG hz6 σ (Φ.twist hG hz6) s (p.act (_root_.ArtinKP.S.nMat t))
          = TSection.translate P hG hz6 σ (Φ.twist hG hz6) s p := by
      intro t ht s p
      rw [← htw, GSection.twist_apply, GSection.twist_apply, kappaRow_n ι P hG hz6, act_nMat_c,
        act_nMat_d]
      have h3 := hV.unip _ (hsm t ht).1 s (p.c : F) (p.d : F)
      push_cast
      rw [add_comm, h3]
    have hsum := congrArg (zPsi P hG hz6)
      (sum_translate_restrict hG hz6 h g (Φ.twist hG hz6) σ hσ hT₁ hinv)
    rw [zPsi_add, zPsi_sum, zPsi_smul,
      Finset.sum_congr rfl (fun t _ => zPsi_translate_nMat hG hz6 t _), Finset.sum_const,
      nsmul_eq_mul, card_reps h g h𝔪 hT₁, ← htw, zPsi_restrict_twist hG hz6 h g, htw] at hsum
    have hq := one_lt_absNorm h
    have hq0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by exact_mod_cast (by omega : _ ≠ 0)
    have hq1 : (Ideal.absNorm v.asIdeal : ℂ) + 1 ≠ 0 := by
      exact_mod_cast (by omega : Ideal.absNorm v.asIdeal + 1 ≠ 0)
    apply mul_left_cancel₀ hq0
    unfold cq
    field_simp
    field_simp at hsum
    linear_combination hsum

include hG hz6 h g in
/-- **Kernel Lemma 5.3**: `θ_{Φρ_∞} = (q/(q+1)) · θ_Φ` for every genuine section `Φ`. -/
theorem kernel (Φ : GSection ι P 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    (hΓ : Inv Γ (Φ.twist hG hz6))
    (hΓR : Inv Γ (TSection.restrict v (not_le_of_good h) (Φ.twist hG hz6))) :
    theta Γ (TSection.restrict v (not_le_of_good h) (Φ.twist hG hz6))
      = cq v • theta Γ (Φ.twist hG hz6) := by
  have hΞ : Inv Γ (TSection.restrict v (not_le_of_good h) (Φ.twist hG hz6)
      + (-cq v) • Φ.twist hG hz6) := hΓR.add (hΓ.smul _)
  have h0 : theta Γ (TSection.restrict v (not_le_of_good h) (Φ.twist hG hz6)
      + (-cq v) • Φ.twist hG hz6) = 0 := by
    refine (theta_eq_zero_iff_forall_zPsi_translate_eq_zero P hG hz6 hΞ).mpr fun σ => ?_
    have e : TSection.translate P hG hz6 σ
        (TSection.restrict v (not_le_of_good h) (Φ.twist hG hz6) + (-cq v) • Φ.twist hG hz6)
        = TSection.translate P hG hz6 σ (TSection.restrict v (not_le_of_good h) (Φ.twist hG hz6))
          + (-cq v) • TSection.translate P hG hz6 σ (Φ.twist hG hz6) := by
      ext s p; simp
    rw [e, zPsi_add, zPsi_smul, zPsi_translate_restrict hG hz6 h g]
    ring
  rw [theta_add hG Γ hΓR (hΓ.smul _), theta_smul hG Γ hΓ] at h0
  rw [neg_smul, add_neg_eq_zero] at h0
  exact h0

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

/-! ### Algebra -/

section gen

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (h : C3I.Good 𝔪 v)
  (g : AllowedGen ι 𝔪) (Φ : GSection ι P 𝔪)

include hG hz6 h g in
/-- **Theorem F1** (MATH2 §5.4): `τ_{Φ♯}(ν) = |π|_{S_f}³ · τ_Φ(νπ³)`, i.e.
`τ_Φ(νπ³) = |π|_{S_f}^{-3} τ_{Φ^{(3)}}(ν)`, for every genuine section `Φ` and `ν ∈ R ∖ 0`. -/
theorem tau_sharp {ν : SInt 𝔪} (hν : ν ≠ 0) :
    T.tau hG hz6 (Φ.sharp hG (g.gen v.asIdeal : F) (gen_coe_ne_zero h g)) ν
      = ((absS 𝔪 (g.gen v.asIdeal : F) : ℝ) : ℂ) ^ 3
        * T.tau hG hz6 Φ (ν * g.gen v.asIdeal ^ 3) := by
  have h𝔪 := hG.ne_bot
  have hπ : (g.gen v.asIdeal : F) ≠ 0 := gen_coe_ne_zero h g
  have hπ3 : (g.gen v.asIdeal : F) ^ 3 ≠ 0 := pow_ne_zero 3 hπ
  have hnpos : 0 < Ninf (g.gen v.asIdeal : F) := Ninf_pos hπ
  have hppos : 0 < absS 𝔪 (g.gen v.asIdeal : F) := absS_pos hπ
  have hq := one_lt_absNorm h
  have hνF : (ν : F) ≠ 0 := T.coe_ne_zero hν
  have hμ : ν * g.gen v.asIdeal ^ 3 ≠ 0 := mul_ne_zero hν (pow_ne_zero 3 (gen_ne_zero h g))
  have hμF : ((ν * g.gen v.asIdeal ^ 3 : SInt 𝔪) : F) ≠ 0 := T.coe_ne_zero hμ
  have eμ : ((ν * g.gen v.asIdeal ^ 3 : SInt 𝔪) : F) = (ν : F) * (g.gen v.asIdeal : F) ^ 3 := rfl
  -- depths, representatives, cells
  obtain ⟨M₀, hM₀, hV₀⟩ := exists_validDepth_nonneg hG Φ ((ν * g.gen v.asIdeal ^ 3 : SInt 𝔪) : F)
  obtain ⟨B, hB⟩ := exists_small_neg h𝔪 ((g.gen v.asIdeal : F) ^ 3)
  set M : ℤ := max M₀ B with hMdef
  have hM : 0 ≤ M := hM₀.trans (le_max_left _ _)
  have hV : ValidDepth hG Φ ((ν * g.gen v.asIdeal ^ 3 : SInt 𝔪) : F) M :=
    validDepth_mono hG Φ hV₀ (le_max_left _ _)
  have hKM : (B : ℤ) ≤ M := le_max_right _ _
  obtain ⟨Bν, hBν⟩ := exists_small_neg h𝔪 (ν : F)
  obtain ⟨Tr, hT, hTsm⟩ := exists_isU hG hz6 h g Φ (Bν : ℤ)
  have hdeep : ∀ t ∈ Tr, Small 𝔪 0
      (((ν * g.gen v.asIdeal ^ 3 : SInt 𝔪) : F) * (t : F) / (g.gen v.asIdeal : F) ^ 3) := by
    intro t ht
    have e : ((ν * g.gen v.asIdeal ^ 3 : SInt 𝔪) : F) * (t : F) / (g.gen v.asIdeal : F) ^ 3
        = (ν : F) * (t : F) := by rw [eμ]; field_simp
    rw [e]
    have := hBν.mul (hTsm t ht).1
    rwa [neg_add_cancel] at this
  have hD := pcell_cellM h𝔪 hM
  have hb := cellM_bdd h𝔪 hM
  have hAdm : Adm (scaleLat ((g.gen v.asIdeal : F) ^ 3) (transLat 𝔪 M)) := by
    have ecast : (((g.gen v.asIdeal ^ 3 : SInt 𝔪)) : F) = (g.gen v.asIdeal : F) ^ 3 := rfl
    have := adm_scaleLat h𝔪 (g.gen v.asIdeal ^ 3) (by rw [ecast]; exact hπ3) (K := B) (M := M)
      (by rw [ecast]; exact hB) hKM
    rwa [ecast] at this
  have := hAdm.countable
  obtain ⟨n', hn'⟩ := exists_bdd_scaleSet ((g.gen v.asIdeal : F) ^ 3) hb
  have hD' := pcell_scale hπ3 hD
  have hD'0 : volume (scaleSet ((g.gen v.asIdeal : F) ^ 3) (cellM 𝔪 M)) ≠ 0 :=
    (hD'.isAddFundamentalDomain volume).measure_ne_zero (NeZero.ne _)
  -- coefficients of `E_Φ` at `νπ³` over `D` and of `E_{Φ♯}` at `ν` over `π³D`
  have hc1 : HasCoef hG hz6 Φ (ν * g.gen v.asIdeal ^ 3) (cellM 𝔪 M) (T.kap 𝔪 0) := by
    have := hasCoef_transLat (hG := hG) (hz6 := hz6) (Φ := Φ) hμ hM hV hD hb
    rwa [kap_eq_zero' h𝔪 hM] at this
  obtain ⟨M', hM', hV'⟩ := exists_validDepth_nonneg hG
    (Φ.sharp hG (g.gen v.asIdeal : F) hπ) (ν : F)
  have hχ : ∀ g' ∈ scaleLat ((g.gen v.asIdeal : F) ^ 3) (transLat 𝔪 M),
      chiInf (ν : F) g' = 1 := by
    rintro _ ⟨y, ⟨b, hb', rfl⟩, rfl⟩
    have h1 := chiInf_transLat_one hG Φ hV (b := embR b) ⟨b, hb', rfl⟩
    rw [embR_apply, chiInf_emb, eμ] at h1
    change chiInf (ν : F) (emb ((g.gen v.asIdeal : F) ^ 3) * emb (b : F)) = 1
    rw [← emb_mul, chiInf_emb, ← h1]
    congr 3
    ring
  have hc2 : HasCoef hG hz6 (Φ.sharp hG (g.gen v.asIdeal : F) hπ) ν
      (scaleSet ((g.gen v.asIdeal : F) ^ 3) (cellM 𝔪 M)) (T.kap 𝔪 0) :=
    hasCoef_adm hG hz6 _ hν hM' hV' hAdm hD' hn' (inv_stabGroup _)
      (scaleLat_le_stab_sharp hG hz6 Φ hπ hV.unip hAdm.le) hχ
  have hc3 := hasCoefT_restrict hG hz6 h g Φ hν hT hdeep hM hV hD hb hc1 hc2
  -- residues
  have hκ := kap_ne_zero h𝔪 (le_refl (0 : ℤ))
  have hseedR : HasSeed (TSection.restrict v (not_le_of_good h)
      ((Φ.sharp hG (g.gen v.asIdeal : F) hπ).twist hG hz6)) (ν : F) (bR hG hz6 h g Φ ν) :=
    ⟨_, _, n', hc3, hκ, hD'.meas, hD'0, hn'⟩
  set q : ℂ := (Ideal.absNorm v.asIdeal : ℂ) with hqdef
  set f1 : ℂ → ℂ := fun s => 1 - q ^ 2 * (q ^ (-s)) ^ 3 with hf1def
  set f2 : ℂ → ℂ := fun s => -(q ^ 3 * (q ^ (-s)) ^ 3) with hf2def
  set c1 : ℂ := q ^ 3 * ((Ninf (g.gen v.asIdeal : F) : ℝ) : ℂ)⁻¹ ^ 3 with hc1def
  have hq0 : q ≠ 0 := by rw [hqdef]; exact_mod_cast (by omega : Ideal.absNorm v.asIdeal ≠ 0)
  have hx : Differentiable ℂ fun s : ℂ => q ^ (-s) :=
    (differentiable_id.neg).const_cpow (Or.inl hq0)
  have hf1 : Differentiable ℂ f1 :=
    (differentiable_const _).sub ((differentiable_const _).mul (hx.pow 3))
  have hf2 : Differentiable ℂ f2 := ((differentiable_const _).mul (hx.pow 3)).neg
  have r1 := resSlit_mul_of_seed P hG hz6 hνF hseedR hf1
  have r2 : resSlit (fun s => f1 s * bR hG hz6 h g Φ ν s)
      = resSlit (fun s => c1 * (kubota hG hz6).aSer Φ (ν * g.gen v.asIdeal ^ 3) s
        + f2 s * (kubota hG hz6).aSer (Φ.sharp hG (g.gen v.asIdeal : F) hπ) ν s) :=
    resSlit_congr fun s hs => by
      have hd := ratio_den_ne_zero hq (s := s) (by linarith)
      simp only [bR, hf1def, hf2def, hc1def, hqdef]
      rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  obtain ⟨D₁, κ₁, n₁, hcΦ, hκ₁, hm₁, hv₁, hb₁⟩ := T.hasSeed hG hz6 Φ hμ
  obtain ⟨D₂, κ₂, n₂, hcS, hκ₂, hm₂, hv₂, hb₂⟩ :=
    T.hasSeed hG hz6 (Φ.sharp hG (g.gen v.asIdeal : F) hπ) hν
  have r3 := resSlit_add_of_seed P hG hz6 hμF
    (⟨D₁, κ₁, n₁, hcΦ.smulFun h𝔪 (fun _ => c1) (differentiable_const c1), hκ₁, hm₁, hv₁, hb₁⟩ :
      HasSeed _ _ (fun s => c1 * (kubota hG hz6).aSer Φ (ν * g.gen v.asIdeal ^ 3) s)) hνF
    (⟨D₂, κ₂, n₂, hcS.smulFun h𝔪 f2 hf2, hκ₂, hm₂, hv₂, hb₂⟩ :
      HasSeed _ _ (fun s => f2 s
        * (kubota hG hz6).aSer (Φ.sharp hG (g.gen v.asIdeal : F) hπ) ν s))
  have r4 := resSlit_mul_of_seed P hG hz6 hμF (T.hasSeed hG hz6 Φ hμ)
    (differentiable_const c1)
  have r5 := resSlit_mul_of_seed P hG hz6 hνF
    (T.hasSeed hG hz6 (Φ.sharp hG (g.gen v.asIdeal : F) hπ) hν) hf2
  have hres : f1 (4 / 3) * resSlit (bR hG hz6 h g Φ ν)
      = c1 * T.tau hG hz6 Φ (ν * g.gen v.asIdeal ^ 3)
        + f2 (4 / 3) * T.tau hG hz6 (Φ.sharp hG (g.gen v.asIdeal : F) hπ) ν := by
    rw [← r1, r2, r3, r4, r5]
    rfl
  -- a test function seeing `W_{4/3}(ν; ·)`
  obtain ⟨n, hn, hW⟩ := exists_Wc_ne_zero (ν : F) (s₁ := (4 / 3 : ℂ))
    (by change (1 : ℝ) < (4 / 3 : ℂ).re; norm_num) hD'.meas hD'0 hn'
  have hbn : ∀ x ∈ scaleSet ((g.gen v.asIdeal : F) ^ 3) (cellM 𝔪 M), ∀ w, ‖x w‖ ≤ n :=
    fun x hx w => (hn' x hx w).trans (by exact_mod_cast hn)
  have hφ := measurable_phaseW (F := F) (s₁ := (4 / 3 : ℂ))
    (by change (1 : ℝ) < (4 / 3 : ℂ).re; norm_num) (ν : F)
  have hφ1 := norm_phaseW_le (F := F) (4 / 3 : ℂ) (ν : F)
  -- a group fixing `Ψ♯` and `Ψ♯ρ_∞`
  obtain ⟨Γ, hfi, -, -, hΓ, hΓR, -, -, -⟩ := exists_common hG hz6 P
    ((Φ.sharp hG (g.gen v.asIdeal : F) hπ).twist hG hz6)
    (TSection.restrict v (not_le_of_good h)
      ((Φ.sharp hG (g.gen v.asIdeal : F) hπ).twist hG hz6))
  have i1 := integral_theta_of_hasCoefT P hG hz6 hνF hseedR hΓR hc3 hD'.meas hbn hφ hφ1
  have i2 := integral_theta_of_hasCoef hG hz6 (Φ.sharp hG (g.gen v.asIdeal : F) hπ) hν hΓ hc2
    hD'.meas hbn hφ hφ1
  have hk := kernel hG hz6 h g (Φ.sharp hG (g.gen v.asIdeal : F) hπ) Γ hΓ hΓR
  rw [← X.coeffFunctional_apply Γ n _ (measurable_stripFn hD'.meas _ hφ) 1
    (norm_stripFn_le _ _ hφ1), hk, map_smul, smul_eq_mul,
    X.coeffFunctional_apply, i2] at i1
  -- `Res b = cq · τ_{Φ♯}(ν)`
  have hRes : resSlit (bR hG hz6 h g Φ ν)
      = cq v * T.tau hG hz6 (Φ.sharp hG (g.gen v.asIdeal : F) hπ) ν := by
    apply mul_left_cancel₀ hκ
    apply mul_right_cancel₀ hW
    linear_combination -i1
  rw [hRes] at hres
  -- the scalars at `s₀ = 4/3`
  obtain ⟨h3, h2⟩ := FA.coef_at hq0 (E.hx_of_nat _ (by omega : 0 < Ideal.absNorm v.asIdeal))
  have hq1 : q + 1 ≠ 0 := by
    rw [hqdef]; exact_mod_cast (by omega : Ideal.absNorm v.asIdeal + 1 ≠ 0)
  have hf1v : f1 (4 / 3) = 1 - (q⁻¹) ^ 2 := by simp only [hf1def]; rw [h2]
  have hf2v : f2 (4 / 3) = -q⁻¹ := by simp only [hf2def]; rw [h3]
  have hc1v : c1 = ((absS 𝔪 (g.gen v.asIdeal : F) : ℝ) : ℂ) ^ 3 := by
    have hn0 : ((Ninf (g.gen v.asIdeal : F) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hnpos.ne'
    rw [hc1def, hqdef, absNorm_eq_mul h g h𝔪]
    push_cast
    field_simp
  have hU := FA.U_eigen' hq0 hq1
  rw [hf1v, hf2v, hc1v] at hres
  unfold cq at hres
  linear_combination
    (-T.tau hG hz6 (Φ.sharp hG (g.gen v.asIdeal : F) hπ) ν) * hU + hres

include hG hz6 h g in
/-- **Cube periodicity (PER)** at `π = g.gen P` for the theta functional of WP-T. -/
theorem theta_per_gen_of_good : (T.theta (ι := ι) (P := P) hG hz6).PER (g.gen v.asIdeal) := by
  intro Φ ν hν
  have hπ : (g.gen v.asIdeal : F) ≠ 0 := gen_coe_ne_zero h g
  have ha0 : ((absS 𝔪 (g.gen v.asIdeal : F) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (absS_pos hπ).ne'
  rw [iterate_act hG hz6 Φ hπ]
  change T.tau hG hz6 Φ (ν * g.gen v.asIdeal ^ 3) = T.tau hG hz6 _ ν
  rw [T.tau_smul hG hz6 _ hν, tau_sharp hG hz6 h g Φ hν, ← mul_assoc, ← mul_pow,
    inv_mul_cancel₀ ha0, one_pow, one_mul]

end gen

end

end ArtinKP.F
end

section
-- module Solutions.Artin.KP.GK_E
/-! # WP-GK, file 1: Theorem E without hypotheses, `hsm`, `hne`, Lemma KW

Setting of the cut: `hG : Good 𝔪`, `hz6`, `g : AllowedGen ι 𝔪`, `hgood` (every exterior prime is
`C3I.Good`), `hd : DD.DiffInS 𝔪`.  The theta functional is WP-T's `T.theta hG hz6`.

* `hsm`: the scalar law `SmulOn {Re s > 1}` of `T.theta` (G1's hypothesis `hsm`).
* `per_all`: cube periodicity at every exterior prime (from `F.per`).
* **`tau_eq_coefF'`** (Theorem E): `τ_Φ(ν) = N(νR)^{1/3} · coefF' g ⊤ (rowOf ν) · τ_{Ã(ν)Φ}(1)`;
  `tau_eq_Kir`: the same with G1's Kirillov function.
* **`hne`**: some Kirillov value is nonzero (G1's hypothesis `hne`).
* `tau_eq_zero_of_theta`: `θ_Φ = 0 ⇒ τ_Φ(ν) = 0` for every `ν ∈ R ∖ 0` (converse of (C10′)).
* `theta_wSec_eq_zero`: `θ_Φ = 0 ⇒ θ_{wΦ} = 0` (Corollary N, `N2.theta_eq_zero_iff`).
* **`KW`**: MATH3's Lemma KW in G1's form `G1.KW hG hz6 (T.theta hG hz6)`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.GK

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N
  ArtinKP.B7

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

section E

variable (g : AllowedGen ι 𝔪)
  (hgood : ∀ (Q : Ideal (𝓞 F)) (hQ : Q.IsPrime) (hext : IsExterior 𝔪 Q),
    C3I.Good 𝔪 (⟨Q, hQ, hext.1⟩ : HeightOneSpectrum (𝓞 F)))

include hgood in
/-- Cube periodicity at every exterior prime. -/
theorem theta_per_gen_of_isExterior_oai : ∀ Q : Ideal (𝓞 F), Q.IsPrime → IsExterior 𝔪 Q →
    (T.theta (ι := ι) (P := P) hG hz6).PER (g.gen Q) :=
  fun Q hQ hext => _root_.ArtinKP.F.theta_per_gen_of_good hG hz6 (hgood Q hQ hext) g

end E

/-! ### `θ = 0 ⇒ τ ≡ 0`, and `θ_Φ = 0 ⇒ θ_{wΦ} = 0` -/

/-! ### Lemma KW -/

end

end ArtinKP.GK
end

theorem solution.{u_1} : type_of% @ArtinKP.GK.theta_per_gen_of_isExterior_oai.{u_1} := @ArtinKP.GK.theta_per_gen_of_isExterior_oai.{u_1}
