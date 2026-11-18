-- Prove2me | solution 1 for ArtinKP.N2.theta_eq_zero_iff_forall_zPsi_translate_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:13:41.774991+00:00
-- url     : https://prove2.me/submissions/9aa19d3b-56a1-4685-adae-456c4599868f

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
import Theorems.Thm_ArtinKP_C5_l2Rep_src
import Theorems.Thm_ArtinKP_GL_eisEigen_of_two_lt_re
import Theorems.Thm_ArtinKP_N_cf_theta_translate
import Theorems.Thm_ArtinKP_N_lift_theta_translate
import Theorems.Thm_ArtinKP_N2_integrable_orbit
import Theorems.Thm_ArtinKP_N2_orbit_integral_eq_zero
import Theorems.Thm_ArtinKP_X_X_isPOU_pou
import Theorems.Thm_ArtinKP_X_X_tsum_indicator_box_le_boxMult

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
-- module Solutions.Artin.KP.B_Def
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-! ### The product formula for `S`-units -/

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

lemma unit_coe_ne_zero (ε : (SInt 𝔪)ˣ) : ((ε : SInt 𝔪) : F) ≠ 0 := by
  have h3 : ((ε : SInt 𝔪) : F) * (((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = 1 := by
    rw [← MulMemClass.coe_mul, ε.mul_inv]
    rfl
  exact left_ne_zero_of_mul_eq_one h3

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
-- module Solutions.Artin.KP.RO_Cusps
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-- (O) as a finite set of representatives. -/
theorem finite_orbits_SL2 (S : Finset (FinitePlace F)) :
    ∃ T : Finset (PairClass S), ∀ p : PairClass S, ∃ q ∈ T, ∃ γ : SL(2, 𝓞 F), p = q.act γ := by
  classical
  obtain ⟨n, τ, hτ, h⟩ := finiteCusps S
  refine ⟨Finset.univ.image fun i => (PairClass.inf S).actR (τ i) (hτ i), fun p => ?_⟩
  obtain ⟨i, γ, hp⟩ := h p
  exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ i), γ, hp⟩

end

end ArtinKP.RO
end

section
-- module Solutions.Artin.KP.RO_Bridge
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
-- module Solutions.Artin.KP.X_QuotC
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.CAbs_Residue
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-- `P₀` is a self-adjoint idempotent: `⟪P x, P y⟫ = ⟪P x, y⟫` (MATH (C8)). -/
lemma inner_eigenProj_eigenProj (T : H →L[ℂ] H) (t : ℂ) (x y : H) :
    ⟪eigenProj T t x, eigenProj T t y⟫_ℂ = ⟪eigenProj T t x, y⟫_ℂ := by
  unfold eigenProj
  rw [← Submodule.inner_starProjection_left_eq_right]
  congr 1
  exact Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)

end

end ArtinKP.CAbs
end

section
-- module Solutions.Artin.KP.X2_H1
attribute [-instance] _root_.ArtinKP.B1.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatSub _root_.ArtinKP.N.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
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

lemma X.integral_quotVol {h : Quotient (MulAction.orbitRel Γ (X F)) → ℂ} (hh : Measurable h) :
    ∫ q, h q ∂X.quotVol Γ =
      ∫ P, (((X.pou Γ P).toReal : ℝ) : ℂ) * h (Quotient.mk _ P) ∂X.vol F := by
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  unfold X.quotVol quotMeasure
  rw [integral_map measurable_mk.aemeasurable hh.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (X.isPOU_pou Γ).measurable
      (Filter.Eventually.of_forall fun P => ((X.isPOU_pou Γ).ne_top P).lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun P => ?_)
  simp only [Complex.real_smul]

/-- Inner products with a class are integrals against the partition of unity. -/
theorem X.inner_toL2 {f : X F → ℂ} (h : X.L2Rep Γ f) (v : X.L2 Γ) :
    ⟪X.toL2 Γ f h, v⟫_ℂ =
      ∫ P, (((X.pou Γ P).toReal : ℝ) : ℂ) * (conj (f P) * X.lift Γ v P) ∂X.vol F := by
  rw [MeasureTheory.L2.inner_def]
  have h1 : (fun q => ⟪(X.toL2 Γ f h : Quotient (MulAction.orbitRel Γ (X F)) → ℂ) q, v q⟫_ℂ)
      =ᵐ[X.quotVol Γ] fun q => conj (X.desc Γ f q) * v q := by
    filter_upwards [MemLp.coeFn_toLp h.memLp] with q hq
    rw [show (X.toL2 Γ f h : Quotient (MulAction.orbitRel Γ (X F)) → ℂ) q = X.desc Γ f q from hq]
    simp [mul_comm]
  have hm : Measurable fun q : Quotient (MulAction.orbitRel Γ (X F)) =>
      conj (X.desc Γ f q) * v q :=
    (Complex.continuous_conj.measurable.comp (X.measurable_desc h.meas h.inv)).mul
      (Lp.stronglyMeasurable v).measurable
  rw [integral_congr_ae h1, X.integral_quotVol hm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun P => ?_)
  simp only [X.desc_mk h.inv]
  rfl

/-! ### Local integrability of pull-backs -/

/-! ### The core -/

/-! ### Density of the core -/

/-! ### The symmetric operator and the energy space -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Eigen
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-! ### Functions of the height on `X` -/

/-! ### Invariance: pair heights -/

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

lemma VanishLow.deriv {g : ℝ → ℂ} (hg : VanishLow g) : VanishLow (deriv g) := by
  intro τ hτ
  have h : g =ᶠ[𝓝 τ] fun _ => (0 : ℂ) := by
    filter_upwards [Iio_mem_nhds hτ] with t ht using hg t ht
  rw [h.deriv_eq]
  simp

lemma VanishHigh.deriv {g : ℝ → ℂ} (hg : VanishHigh g) : VanishHigh (deriv g) := by
  intro τ hτ
  have h : g =ᶠ[𝓝 τ] fun _ => (0 : ℂ) := by
    filter_upwards [Ioi_mem_nhds hτ] with t ht using hg t ht
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

/-! ### Smoothness and the Laplacian -/

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

lemma rho_one {h : ℝ} (hh : 3 ≤ h) : rho h = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma contDiff_rho : ContDiff ℝ (⊤ : ℕ∞) rho :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

lemma contDiff_rt : ContDiff ℝ (⊤ : ℕ∞) rt :=
  Complex.ofRealCLM.contDiff.comp (contDiff_rho.comp Real.contDiff_exp)

lemma rt_low {τ : ℝ} (h : τ < Real.log 2) : rt τ = 0 := by
  unfold rt
  rw [rho_zero ((Real.lt_log_iff_exp_lt (by norm_num)).mp h).le]
  simp

lemma rt_high {τ : ℝ} (h : Real.log 3 < τ) : rt τ = 1 := by
  unfold rt
  rw [rho_one ((Real.log_lt_iff_lt_exp (by norm_num)).mp h).le]
  simp

lemma contDiff_rt1 : ContDiff ℝ (⊤ : ℕ∞) rt1 := by
  have h : ContDiff ℝ ((⊤ : ℕ∞) + 1) rt := contDiff_rt
  exact (contDiff_succ_iff_deriv.1 h).2.2

lemma contDiff_rt2 : ContDiff ℝ (⊤ : ℕ∞) rt2 := by
  have h : ContDiff ℝ ((⊤ : ℕ∞) + 1) rt1 := contDiff_rt1
  exact (contDiff_succ_iff_deriv.1 h).2.2

lemma vanishLow_rt : VanishLow rt := fun _ h => rt_low h

lemma vanishLow_rt1 : VanishLow rt1 := vanishLow_rt.deriv

lemma vanishLow_rt2 : VanishLow rt2 := vanishLow_rt1.deriv

lemma vanishHigh_rt1 : VanishHigh rt1 := by
  intro τ hτ
  have h : rt =ᶠ[𝓝 τ] fun _ => (1 : ℂ) := by
    filter_upwards [Ioi_mem_nhds hτ] with t ht using rt_high ht
  unfold rt1
  rw [h.deriv_eq]
  simp

lemma vanishHigh_rt2 : VanishHigh rt2 := vanishHigh_rt1.deriv

lemma log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

lemma log_three_le : Real.log 3 ≤ 2 := by
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
  linarith

/-- A smooth function vanishing outside `[log 2, log 3]` is bounded. -/
lemma exists_bound_of_vanish {g : ℝ → ℂ} (hc : Continuous g) (hl : VanishLow g)
    (hh : VanishHigh g) : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ, ‖g τ‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := Real.log 2) (b := Real.log 3)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun τ => ?_⟩
  by_cases h1 : τ < Real.log 2
  · rw [hl τ h1]; simp
  by_cases h2 : Real.log 3 < τ
  · rw [hh τ h2]; simp
  · exact (hC τ ⟨not_lt.mp h1, not_lt.mp h2⟩).trans (le_max_left _ _)

lemma exists_rt_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ, ‖rt1 τ‖ ≤ C ∧ ‖rt2 τ‖ ≤ C := by
  obtain ⟨C₁, h₁, hC₁⟩ := exists_bound_of_vanish contDiff_rt1.continuous vanishLow_rt1
    vanishHigh_rt1
  obtain ⟨C₂, h₂, hC₂⟩ := exists_bound_of_vanish contDiff_rt2.continuous vanishLow_rt2
    vanishHigh_rt2
  exact ⟨max C₁ C₂, h₁.trans (le_max_left _ _), fun τ =>
    ⟨(hC₁ τ).trans (le_max_left _ _), (hC₂ τ).trans (le_max_right _ _)⟩⟩

/-! ### The profile of `h_s` -/

variable {F : Type*} [Field F] [NumberField F]

/-! ### The eigenvalue and the profile of the source -/

lemma contDiff_phiS (s : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (phiS F s) :=
  contDiff_const.mul ((X.contDiff_cexp_mul s).mul
    (contDiff_rt2.neg.add (contDiff_const.mul contDiff_rt1)))

lemma vanishLow_phiS (s : ℂ) : VanishLow (phiS F s) := fun τ h => by
  unfold phiS
  rw [vanishLow_rt1 τ h, vanishLow_rt2 τ h]
  simp

lemma vanishHigh_phiS (s : ℂ) : VanishHigh (phiS F s) := fun τ h => by
  unfold phiS
  rw [vanishHigh_rt1 τ h, vanishHigh_rt2 τ h]
  simp

/-- `φ_s` is bounded on `{‖s‖ ≤ M} × ℝ`. -/
lemma exists_norm_phiS_le (F : Type*) [Field F] [NumberField F] (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, ‖s‖ ≤ M → ∀ τ : ℝ, ‖phiS F s τ‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_rt_bound
  set r : ℝ := (Fintype.card (InfinitePlace F) : ℝ) with hr
  refine ⟨r * (Real.exp (2 * |M|) * (C + (2 + 2 * |M|) * C)), by positivity, fun s hs τ => ?_⟩
  have hsM : ‖s‖ ≤ |M| := hs.trans (le_abs_self M)
  by_cases h1 : τ < Real.log 2
  · rw [vanishLow_phiS s τ h1, norm_zero]; positivity
  by_cases h2 : Real.log 3 < τ
  · rw [vanishHigh_phiS s τ h2, norm_zero]; positivity
  have hτ0 : 0 ≤ τ := log_two_pos.le.trans (not_lt.mp h1)
  have hτ2 : τ ≤ 2 := (not_lt.mp h2).trans log_three_le
  unfold phiS
  rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_exp]
  have he : Real.exp (s * (τ : ℂ)).re ≤ Real.exp (2 * |M|) := by
    refine Real.exp_le_exp.mpr ?_
    have : (s * (τ : ℂ)).re = s.re * τ := by simp
    rw [this]
    calc s.re * τ ≤ |s.re| * τ := mul_le_mul_of_nonneg_right (le_abs_self _) hτ0
      _ ≤ |M| * 2 := mul_le_mul ((Complex.abs_re_le_norm s).trans hsM) hτ2 hτ0 (abs_nonneg M)
      _ = 2 * |M| := mul_comm _ _
  have h3 : ‖-rt2 τ + (2 - 2 * s) * rt1 τ‖ ≤ C + (2 + 2 * |M|) * C := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_neg]; exact (hC τ).2
    · rw [norm_mul]
      refine mul_le_mul ?_ (hC τ).1 (norm_nonneg _) (by positivity)
      calc ‖(2 : ℂ) - 2 * s‖ ≤ ‖(2 : ℂ)‖ + ‖2 * s‖ := norm_sub_le _ _
        _ = 2 + 2 * ‖s‖ := by simp
        _ ≤ 2 + 2 * |M| := by linarith
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul he h3 (norm_nonneg _) (Real.exp_pos _).le) (Nat.cast_nonneg _)

end

end ArtinKP.C5
end

section
-- module Solutions.Artin.KP.RO_Orbits
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-RO, file 4: finitely many `Γ`-orbits of pair classes (stub S-2 of WP-S)

* `finite_orbits_of_finiteIndex`: for a subgroup `Γ ≤ SL₂(𝓞)` of finite index, `𝒫/Γ` is finite
  (`𝒫 = B1.PairClass S`, any `S`).
* `princCong 𝔫`, the principal congruence subgroup of `SL₂(𝓞)`; it has finite index for `𝔫 ≠ ⊥`
  (`princCong_finiteIndex`), and `Gamma 𝔪 𝔫 = (princCong 𝔫).map (intMat 𝔪)` (`Gamma_eq_map`).
* `finite_orbits_row`: the same on `S.Row 𝔪` modulo `U_S`; **`finite_orbits`**: the statement of
  `S_Stubs.finite_orbits`, proved.
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

/-- **`𝒫/Γ` is finite** for `Γ` of finite index in `SL₂(𝓞_F)`. -/
theorem finite_orbits_of_finiteIndex (S : Finset (FinitePlace F)) (Γ : Subgroup (SL(2, 𝓞 F)))
    [Γ.FiniteIndex] :
    ∃ T : Finset (PairClass S), ∀ p : PairClass S, ∃ q ∈ T, ∃ γ ∈ Γ, p = q.act γ := by
  classical
  obtain ⟨T₀, hT₀⟩ := finite_orbits_SL2 S
  have : Finite (SL(2, 𝓞 F) ⧸ Γ) := Subgroup.finite_quotient_of_finiteIndex
  have := Fintype.ofFinite (SL(2, 𝓞 F) ⧸ Γ)
  refine ⟨(T₀ ×ˢ Finset.univ).image fun x : PairClass S × (SL(2, 𝓞 F) ⧸ Γ) => x.1.act x.2.out,
    fun p => ?_⟩
  obtain ⟨q, hq, γ, rfl⟩ := hT₀ p
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul Γ γ
  refine ⟨q.act (QuotientGroup.mk γ : SL(2, 𝓞 F) ⧸ Γ).out,
    Finset.mem_image.mpr ⟨(q, QuotientGroup.mk γ), by simp [hq], rfl⟩, ((h⁻¹ : Γ) : SL(2, 𝓞 F)),
    (h⁻¹).2, ?_⟩
  rw [← PairClass.act_mul, hh]
  simp

/-! ### WP-B1's conditional statements, unconditionally for a good modulus -/

end

end ArtinKP.RO
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

lemma wt_rowClass (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) (s : ℂ) (r : Row 𝔪) :
    wt h𝔪 Ψ s (RO.rowClass h𝔪 r) = Ψ.tilde s r := by
  unfold wt
  have : (RO.rowClassEquiv h𝔪).symm (RO.rowClass h𝔪 r) = B.RowClass.mk r := by
    rw [Equiv.symm_apply_eq]
    rfl
  rw [this, tildeC_mk]

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
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
-- module Solutions.Artin.KP.N_Shape
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma Cell.mono {D : Set (InfinitePlace F → ℂ)} {n₀ n : ℕ} (h : Cell Γ D n₀) (hn : n₀ ≤ n) :
    Cell Γ D n :=
  ⟨h.meas, h.fund, fun x hx w => (h.bdd x hx w).trans (by exact_mod_cast hn)⟩

/-! ### The constant-term functional -/

section lin

variable {D : Set (InfinitePlace F → ℂ)} {n : ℕ} {φ : (InfinitePlace F → ℝ) → ℂ}

lemma cf_congr_ae {f g : X F → ℂ} (h : f =ᵐ[X.vol F] g) : cf D n φ f = cf D n φ g := by
  unfold cf
  refine integral_congr_ae ((ae_restrict_of_ae h).mono fun P hP => ?_)
  simp only [hP]

end lin

/-! ### Fubini: a function with vanishing `x`-integrals over `D` is killed by `cf` -/

/-! ### The shape -/

lemma isCompact_box (n : ℕ) : IsCompact (X.box n : Set (X F)) :=
  isCompact_siegelBox (F := F) (m := 1 / ((n : ℝ) + 1)) (M := (n : ℝ) + 1) (B := n)
    (by positivity)

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.N_Res
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-! ### The coefficient function `Acoef` and the cross identity -/

/-! ### `‖θ‖² = −c₀⟪F, θ⟫` -/

lemma c0_ne_zero : c0 F ≠ 0 := by
  unfold c0
  have : (Fintype.card (InfinitePlace F) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) this)

/-- **First step of Theorem N**: `θ_Ψ = −c₀ P₀ F_{s₀}` vanishes as soon as it is orthogonal to the
source `F_{s₀}` (`⟪F, θ⟫ = −c₀‖P₀F‖²`). -/
theorem theta_eq_zero_of_inner (Γ : Subgroup (SL(2, 𝓞 F))) (Ψ : TSection ι 𝔪)
    (h : ⟪srcL2 Γ Ψ (4 / 3), theta Γ Ψ⟫_ℂ = 0) : theta Γ Ψ = 0 := by
  set f := srcL2 Γ Ψ (4 / 3) with hf
  set Pf := (X.energy Γ).proj ((lam0 F : ℝ) : ℂ) f with hPf
  have hθ : theta Γ Ψ = -(c0 F • Pf) := rfl
  have h1 : ⟪Pf, f⟫_ℂ = ⟪Pf, Pf⟫_ℂ := (CAbs.inner_eigenProj_eigenProj _ _ f f).symm
  have h2 : ⟪f, Pf⟫_ℂ = ⟪Pf, Pf⟫_ℂ := by
    rw [← inner_conj_symm, h1, inner_conj_symm]
  rw [hθ, inner_neg_right, inner_smul_right, h2, neg_eq_zero, mul_eq_zero] at h
  rcases h with h | h
  · exact absurd h c0_ne_zero
  · rw [hθ, inner_self_eq_zero.mp h, smul_zero, neg_zero]

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.N_Level
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
/-! # WP-N, file 5: `θ_Ψ` under change of `Γ` and under `SL₂(R)` (C5's open item 3; MATH2 §2.1 end)

* `ae_eq_zero_of_box_tests`: a locally integrable function killed by all bounded test functions on
  all boxes vanishes almost everywhere.
* **`lift_theta_of_eis_smul`**: if `E_{Ψ'}(Q, s) = E_Ψ(τQ, s)` for `Re s > 2` (`τ ∈ SL₂(F)`), then
  `θ_{Γ'}(Ψ') = θ_Γ(Ψ) ∘ τ` almost everywhere, for any finite-index `Γ`, `Γ'` fixing `Ψ`, `Ψ'`.
* `lift_theta_congr`: `θ_Γ(Ψ)` does not depend on `Γ` (as a function on `X`, a.e.).
* `lift_theta_translate`: `θ(σ·Ψ)(Q) = θ(Ψ)(σ⁻¹Q)` for `σ ∈ SL₂(R)`.
* `cf_theta_translate`: the constant term of `θ_Ψ` at the cusp `σ⁻¹∞`, i.e. of `Q ↦ θ_Ψ(σ⁻¹Q)` at
  `∞`, is `zRes(σ·Ψ)·ht^{2/3}`.
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
  {ι : F →+* ℂ}

/-! ### Test functions on boxes -/

/-! ### Transport of a box integral by `τ ∈ SL₂(F)` -/

lemma measurable_psiT (τ : SL(2, F)) (n : ℕ) {ψ : X F → ℂ} (hψ : Measurable ψ) :
    Measurable (psiT τ n ψ) :=
  (hψ.indicator (X.measurableSet_box n)).comp (measurable_const_smul τ⁻¹)

lemma norm_psiT_le (τ : SL(2, F)) (n : ℕ) {ψ : X F → ℂ} (hψ1 : ∀ P, ‖ψ P‖ ≤ 1) (P : X F) :
    ‖psiT τ n ψ P‖ ≤ 1 := by
  unfold psiT
  by_cases h : τ⁻¹ • P ∈ (X.box n : Set (X F))
  · rw [indicator_of_mem h]; exact hψ1 _
  · rw [indicator_of_notMem h, norm_zero]; exact zero_le_one

theorem exists_setIntegral_box_smul (τ : SL(2, F)) (n : ℕ) (ψ : X F → ℂ) :
    ∃ n' : ℕ, ∀ f : X F → ℂ,
      ∫ Q in X.box n, conj (ψ Q) * f (τ • Q) ∂X.vol F
        = ∫ P in X.box n', conj (psiT τ n ψ P) * f P ∂X.vol F := by
  obtain ⟨n', hn'⟩ := X.exists_box_of_isCompact
    ((isCompact_box (F := F) n).image (continuous_const_smul τ))
  refine ⟨n', fun f => ?_⟩
  have h1 : ∀ Q : X F, (X.box n : Set (X F)).indicator (fun Q => conj (ψ Q) * f (τ • Q)) Q
      = (fun P => conj (psiT τ n ψ P) * f P) (τ • Q) := by
    intro Q
    simp only [psiT, inv_smul_smul]
    by_cases hQ : Q ∈ (X.box n : Set (X F))
    · rw [indicator_of_mem hQ, indicator_of_mem hQ]
    · rw [indicator_of_notMem hQ, indicator_of_notMem hQ]; simp
  rw [← integral_indicator (X.measurableSet_box n), integral_congr_ae (Eventually.of_forall h1)]
  refine ((measurePreserving_smul τ).integral_comp (MeasurableEquiv.smul τ).measurableEmbedding
    (fun P => conj (psiT τ n ψ P) * f P)).trans ?_
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun P hP => ?_).symm
  have h2 : τ⁻¹ • P ∉ (X.box n : Set (X F)) := fun hmem =>
    hP (hn' ⟨τ⁻¹ • P, hmem, smul_inv_smul τ P⟩)
  simp [psiT, indicator_of_notMem h2]

/-! ### `θ` under a transformation of the series -/

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.N_Main
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-N, file 6: Corollary N (MATH2 §2.2), modulo the unfolding over the cusps

`theta_eq_zero_of_inner` (file 4) reduces `θ_Ψ = 0` to `⟪[F_{4/3}], θ_Ψ⟫ = 0`.  The remaining step
of Theorem N — a function on `Γ\X` all of whose constant terms vanish is orthogonal to the
pseudo-Eisenstein series `F_{4/3}` — is the **named hypothesis `CuspOrth`** (stated in
`N_Stubs.lean`, route in `WP-N.md`).  Everything else of Corollary N is proved here:

* `CuspVanish`: the constant terms of `θ_Γ(Ψ)` vanish at the cusp `σ⁻¹∞`, tested on a cell of some
  finite-index group fixing `σ·Ψ`.
* `corollaryN`: if `zRes(σ·Ψ) = 0` for all `σ ∈ SL₂(R)` then `θ_Ψ = 0`.
* `corollaryN_of_continuation`: the same with the residues read off arbitrary continuations.
* `zRes_translate_eq_zero_of_theta`: conversely `θ_Ψ = 0` forces every `zRes(σ·Ψ) = 0`.
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
  {ι : F →+* ℂ}

section

variable (Pk : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  {Γ : Subgroup (SL(2, 𝓞 F))} [Γ.FiniteIndex] {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ)
  (hE : ∀ (Ψ' : TSection ι 𝔪) (s : ℂ), 2 < s.re → EisEigen Ψ' s)

include hΓ hE in
/-- `zRes(σ·Ψ) = 0` gives the vanishing of the constant term of `θ_Ψ` at `σ⁻¹∞`. -/
theorem cuspVanish_of_zRes (σ : SL(2, SInt 𝔪)) {Γ' : Subgroup (SL(2, 𝓞 F))} [Γ'.FiniteIndex]
    (hΓ' : Inv Γ' (TSection.translate Pk hG hz6 σ Ψ)) {D : Set (InfinitePlace F → ℂ)} {n : ℕ}
    (hD : Cell Γ' D n) (hn : 1 ≤ n)
    (hz : zRes Γ' (TSection.translate Pk hG hz6 σ Ψ) D n = 0) : CuspVanish Pk hG hz6 Γ Ψ σ :=
  ⟨Γ', D, n, inferInstance, hΓ', hD, fun n' hn' φ hφ hφ1 => by
    rw [cf_theta_translate Pk hG hz6 σ hΓ hΓ' (hE Ψ) (hE _) hD hn (hD.mono hn') hφ hφ1, hz,
      zero_mul]⟩

include hΓ hE in
/-- **Corollary N** (MATH2 §2.2), modulo `CuspOrth`: if for every `σ ∈ SL₂(R)` the residue
`zRes(σ·Ψ)` of the `ht^{2−s}`-coefficient of the constant term at `∞` of `E_{σ·Ψ}` vanishes (for
some finite-index group fixing `σ·Ψ`, some cell of it and some box index `n ≥ 1`), then
`θ_Ψ = 0`. -/
theorem corollaryN (hO : CuspOrth Pk hG hz6 Γ Ψ)
    (hz : ∀ σ : SL(2, SInt 𝔪), ∃ (Γ' : Subgroup (SL(2, 𝓞 F))) (D : Set (InfinitePlace F → ℂ))
      (n : ℕ), Γ'.FiniteIndex ∧ Inv Γ' (TSection.translate Pk hG hz6 σ Ψ) ∧ Cell Γ' D n ∧ 1 ≤ n ∧
        zRes Γ' (TSection.translate Pk hG hz6 σ Ψ) D n = 0) : theta Γ Ψ = 0 := by
  refine theta_eq_zero_of_inner Γ Ψ (hO fun σ => ?_)
  obtain ⟨Γ', D, n, hfi, hinv, hcell, hn, hzero⟩ := hz σ
  exact cuspVanish_of_zRes Pk hG hz6 hΓ hE σ hinv hcell hn hzero

include hΓ hE in
/-- **Converse of Corollary N**: if `θ_Ψ = 0` then every `zRes(σ·Ψ)` vanishes. -/
theorem zRes_translate_eq_zero_of_theta (h : theta Γ Ψ = 0) (σ : SL(2, SInt 𝔪))
    {Γ' : Subgroup (SL(2, 𝓞 F))} [Γ'.FiniteIndex]
    (hΓ' : Inv Γ' (TSection.translate Pk hG hz6 σ Ψ)) {D : Set (InfinitePlace F → ℂ)} {n : ℕ}
    (hD : Cell Γ' D n) : zRes Γ' (TSection.translate Pk hG hz6 σ Ψ) D n = 0 := by
  have h1 := cf_congr_ae (D := D) (n := n) (φ := phase (2 / 3))
    (lift_theta_translate Pk hG hz6 σ hΓ hΓ' (hE Ψ) (hE _))
  obtain ⟨n', hn'⟩ := exists_setIntegral_box_smul (toF 𝔪 σ⁻¹) n (stripFn D 0 (phase (2 / 3)))
  have h2 : cf D n (phase (2 / 3)) (fun Q => X.lift Γ (theta Γ Ψ) (toF 𝔪 σ⁻¹ • Q)) = 0 := by
    have hm := measurable_psiT (toF 𝔪 σ⁻¹) n
      (measurable_stripFn hD.meas 0 (measurable_phase (F := F) (2 / 3)))
    have hb := norm_psiT_le (toF 𝔪 σ⁻¹) n
      (norm_stripFn_le D 0 (norm_phase_le (F := F) (2 / 3)))
    unfold cf
    rw [hn', ← X.coeffFunctional_apply Γ n' _ hm 1 hb, h, map_zero]
  unfold zRes
  rw [h1, h2, zero_div]

end

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.N2_Main
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma orbOf_out {Γ : Subgroup (SL(2, 𝓞 F))} {S : Finset (FinitePlace F)} (o : Orb Γ S) :
    orbOf Γ o.out = o := Quotient.out_eq o

instance finite_orb (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex] (S : Finset (FinitePlace F)) :
    Finite (Orb Γ S) := by
  obtain ⟨T, hT⟩ := RO.finite_orbits_of_finiteIndex S Γ
  refine Finite.of_surjective (fun q : T => orbOf Γ (q : PairClass S)) fun o => ?_
  obtain ⟨q, hq, γ, hγ, hp⟩ := hT o.out
  exact ⟨⟨q, hq⟩, by rw [← orbOf_out o, hp, orbOf_act Γ q hγ]⟩

/-! ### The pseudo-Eisenstein series by orbits -/

/-- The orbit piece of a pseudo-Eisenstein series is a sum over `stab \ Γ`. -/
lemma pe_aOrb (Γ : Subgroup (SL(2, 𝓞 F))) {S : Finset (FinitePlace F)} (p₀ : PairClass S)
    (g : ℝ → ℂ) (P : X F) :
    pe S (aOrb (orbOf Γ p₀)) g P
      = automC (stab Γ p₀) (fun P => g (Real.log (p₀.ht P))) P := by
  unfold pe automC
  have h1 : ∀ q : Γ ⧸ stab Γ p₀, g (Real.log (p₀.ht ((q.out)⁻¹ • P)))
      = (fun p : {p : PairClass S // orbOf Γ p = orbOf Γ p₀} =>
          g (Real.log ((p : PairClass S).ht P))) (orbEquiv Γ p₀ q) := by
    intro q
    change _ = g (Real.log ((p₀.act (((q.out)⁻¹ : Γ) : SL(2, 𝓞 F))).ht P))
    rw [PairClass.ht_act]
    rfl
  rw [tsum_congr h1, (orbEquiv Γ p₀).tsum_eq
    (fun p : {p : PairClass S // orbOf Γ p = orbOf Γ p₀} => g (Real.log ((p : PairClass S).ht P)))]
  have h2 := tsum_subtype {p : PairClass S | orbOf Γ p = orbOf Γ p₀}
      (fun p => g (Real.log (p.ht P)))
  refine Eq.trans (tsum_congr fun p => ?_) h2.symm
  unfold aOrb
  by_cases hp : orbOf Γ p = orbOf Γ p₀
  · rw [if_pos hp, one_mul, indicator_of_mem (by exact hp)]
  · rw [if_neg hp, zero_mul, indicator_of_notMem (by exact hp)]

/-- Decomposition of a pseudo-Eisenstein series with `Γ`-invariant weights into orbit pieces. -/
lemma pe_decomp {Γ : Subgroup (SL(2, 𝓞 F))} {S : Finset (FinitePlace F)} [Fintype (Orb Γ S)]
    {a : PairClass S → ℂ} (ha : ∀ γ ∈ Γ, ∀ p : PairClass S, a (p.act γ) = a p) {g : ℝ → ℂ}
    (hg : VanishLow g) (P : X F) :
    pe S a g P = ∑ o : Orb Γ S, a o.out * pe S (aOrb o) g P := by
  classical
  obtain ⟨p₁, h⟩ := pe_single S P
  rw [h a g hg]
  simp only [h _ g hg]
  rw [Finset.sum_eq_single (orbOf Γ p₁)]
  · have h1 : aOrb (orbOf Γ p₁) p₁ = 1 := by unfold aOrb; rw [if_pos rfl]
    obtain ⟨γ, hγ, hp⟩ := exists_of_orbOf_eq (orbOf_out (orbOf Γ p₁))
    have h2 : a (orbOf Γ p₁).out = a p₁ := ((congrArg a hp).trans (ha γ hγ _)).symm
    rw [h1, h2, one_mul]
  · intro o _ ho
    have h1 : aOrb o p₁ = 0 := by unfold aOrb; rw [if_neg (fun hc => ho hc.symm)]
    rw [h1, zero_mul, mul_zero]
  · intro hc
    exact absurd (Finset.mem_univ _) hc

/-! ### `L¹` bounds -/

/-! ### One orbit -/

/-! ### Cusp representatives -/

lemma rowClass_cuspMat (h𝔪 : 𝔪 ≠ ⊥) (Γ : Subgroup (SL(2, 𝓞 F))) (o : Orb Γ (RO.SOf 𝔪)) :
    RO.rowClass h𝔪 (Row.bot (cuspMat h𝔪 Γ o)) = o.out :=
  (exists_bot_rowClass h𝔪 o.out).choose_spec

/-! ### Stub N-1 -/

section main

variable (Pk : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  {Γ : Subgroup (SL(2, 𝓞 F))} [Γ.FiniteIndex] {Ψ : TSection ι 𝔪}

/-- **Theorem N's unfolding, with finitely many cusps**: if the constant term of `θ_Γ(Ψ)`
vanishes at the cusp `(cuspMat o)⁻¹∞` for every `Γ`-orbit `o` on which the weights of `Ψ` at
`s₀ = 4/3` do not vanish, then `θ_Γ(Ψ)` is orthogonal to the source `[F_{4/3}]`. -/
theorem inner_src_theta_eq_zero (hΓ : Inv Γ Ψ)
    (hv : ∀ o : Orb Γ (RO.SOf 𝔪), wt hG.ne_bot Ψ (4 / 3) o.out ≠ 0 →
      CuspVanish Pk hG hz6 Γ Ψ (cuspMat hG.ne_bot Γ o)) :
    ⟪srcL2 Γ Ψ (4 / 3), theta Γ Ψ⟫_ℂ = 0 := by
  classical
  have : Fintype (Orb Γ (RO.SOf 𝔪)) := Fintype.ofFinite _
  have h𝔪 := hG.ne_bot
  set a : PairClass (RO.SOf 𝔪) → ℂ := wt h𝔪 Ψ (4 / 3) with ha
  set g : ℝ → ℂ := fun τ => conj (phiS F (4 / 3) τ) with hg
  set u := X.lift Γ (theta Γ Ψ) with hu
  have hgs : ContDiff ℝ (⊤ : ℕ∞) g :=
    Complex.conjCLE.contDiff.comp (contDiff_phiS (F := F) (4 / 3))
  have hgl : VanishLow g := fun τ hτ => by
    simp only [hg]; rw [vanishLow_phiS (F := F) (4 / 3) τ hτ, map_zero]
  obtain ⟨C, hC0, hC⟩ := exists_norm_phiS_le F ‖(4 / 3 : ℂ)‖
  have hgC : ∀ τ, ‖g τ‖ ≤ C := fun τ => by
    simp only [hg]; rw [RCLike.norm_conj]; exact hC _ le_rfl τ
  have hainv : ∀ γ ∈ Γ, ∀ p : PairClass (RO.SOf 𝔪),
      (fun p => conj (a p)) (p.act γ) = (fun p => conj (a p)) p := fun γ hγ p => by
    simp only [ha]; rw [wt_act h𝔪 hΓ hγ]
  -- the conjugate of the source, by orbits
  have hsrc : ∀ P : X F, conj (src Ψ (4 / 3) P)
      = ∑ o : Orb Γ (RO.SOf 𝔪), conj (a o.out)
          * automC (stab Γ o.out) (fun P => g (Real.log (o.out.ht P))) P := by
    intro P
    have h1 : conj (src Ψ (4 / 3) P) = pe (RO.SOf 𝔪) (fun p => conj (a p)) g P := by
      rw [src_eq_pe h𝔪]
      obtain ⟨p₁, h⟩ := pe_single (RO.SOf 𝔪) P
      rw [h _ _ (vanishLow_phiS (4 / 3)), h _ _ hgl, map_mul]
    rw [h1, pe_decomp hainv hgl P]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [← pe_aOrb, orbOf_out]
  rw [srcL2_eq (l2Rep_src hG Γ hΓ (4 / 3)), X.inner_toL2]
  have hint : ∀ P : X F, (((X.pou Γ P).toReal : ℝ) : ℂ) * (conj (src Ψ (4 / 3) P) * u P)
      = ∑ o : Orb Γ (RO.SOf 𝔪), conj (a o.out)
          * (automC (stab Γ o.out) (fun P => g (Real.log (o.out.ht P))) P
            * (u P * (((X.pou Γ P).toReal : ℝ) : ℂ))) := by
    intro P
    rw [hsrc P, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun o _ => ?_
    ring
  rw [integral_congr_ae (Eventually.of_forall hint),
    integral_finsetSum _ (fun o _ => (integrable_orbit hG o.out hgs hgl hgC _).const_mul _)]
  refine Finset.sum_eq_zero fun o _ => ?_
  rw [integral_const_mul]
  by_cases hao : a o.out = 0
  · rw [hao, map_zero, zero_mul]
  · have h1 := orbit_integral_eq_zero Pk hG hz6 hΓ (cuspMat h𝔪 Γ o) (hv o hao)
      (rowClass_cuspMat h𝔪 Γ o) hgs.continuous.measurable hgl hgC
    have h2 : ∀ P : X F, automC (stab Γ o.out) (fun P => g (Real.log (o.out.ht P))) P
        * (u P * (((X.pou Γ P).toReal : ℝ) : ℂ))
        = automC (stab Γ o.out) (fun P => g (Real.log (o.out.ht P))) P * u P
          * (((X.pou Γ P).toReal : ℝ) : ℂ) := fun P => by ring
    rw [integral_congr_ae (Eventually.of_forall h2), h1, mul_zero]

/-- **Stub N-1** (`N_Stubs.cuspOrth`), without `EisEigen`. -/
theorem cuspOrth (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex] {Ψ : TSection ι 𝔪}
    (hΓ : Inv Γ Ψ) : CuspOrth Pk hG hz6 Γ Ψ :=
  fun h => inner_src_theta_eq_zero Pk hG hz6 hΓ fun _ _ => h _

end main

end

end ArtinKP.N2
end

section
-- module Solutions.Artin.KP.N2_Cor
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-N2, file 5: Corollary N without hypotheses; the intrinsic residue `z_Ψ`

* **`corollaryN`**, **`corollaryN_of_continuation`**: `N.corollaryN`, `N.corollaryN_of_continuation`
  with both named hypotheses discharged (`CuspOrth` by `N2.cuspOrth`, `EisEigen` by `GL.eisEigen`).
* `corollaryN_reps`, `corollaryN_of_continuation_reps`: the same, testing only the finitely many
  cusps `cuspMat Γ o` (`o` a `Γ`-orbit of pair classes on which the weights of `Ψ` at `4/3` do not
  vanish).
* `zPsi Ψ`: the residue `z_Ψ` of the `ht^{2−s}`-coefficient of the constant term at `∞`, defined
  with a chosen level group and cell; **`zRes_eq_zPsi`**: every `zRes Γ Ψ D n` (`n ≥ 1`) equals it.
* `cf_theta_translate_zPsi`: the constant term of `θ_Ψ` at the cusp `σ⁻¹∞` is `z_{σ·Ψ}·ht^{2/3}`.
* **`theta_eq_zero_iff`**, **`theta_eq_zero_iff_reps`**: `θ_Ψ = 0` iff `z_{σ·Ψ} = 0` for all
  `σ ∈ SL₂(R)`, iff for the finitely many representatives.
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

/-- `GL.eisEigen` in the form taken by `N_Main`. -/
theorem eisE (hG : Good 𝔪) : ∀ (Ψ' : TSection ι 𝔪) (s : ℂ), 2 < s.re → EisEigen Ψ' s :=
  fun Ψ' _ hs => GL.eisEigen_of_two_lt_re hG.ne_bot Ψ' hs

section

variable (Pk : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  {Γ : Subgroup (SL(2, 𝓞 F))} [Γ.FiniteIndex] {Ψ : TSection ι 𝔪}

/-! ### Corollary N -/

/-- **Corollary N** (MATH2 §2.2), unconditional: if for every `σ ∈ SL₂(R)` the residue
`zRes(σ·Ψ)` vanishes (for some finite-index group fixing `σ·Ψ`, some cell and some `n ≥ 1`), then
`θ_Ψ = 0`. -/
theorem corollaryN (hΓ : Inv Γ Ψ)
    (hz : ∀ σ : SL(2, SInt 𝔪), ∃ (Γ' : Subgroup (SL(2, 𝓞 F))) (D : Set (InfinitePlace F → ℂ))
      (n : ℕ), Γ'.FiniteIndex ∧ Inv Γ' (TSection.translate Pk hG hz6 σ Ψ) ∧ Cell Γ' D n ∧ 1 ≤ n ∧
        zRes Γ' (TSection.translate Pk hG hz6 σ Ψ) D n = 0) : theta Γ Ψ = 0 :=
  N.corollaryN Pk hG hz6 hΓ (eisE hG) (cuspOrth Pk hG hz6 Γ hΓ) hz

/-! ### The intrinsic residue -/

lemma inv_levelGroup (Ψ : TSection ι 𝔪) : Inv (levelGroup Pk hG hz6 Ψ) Ψ :=
  (exists_finiteIndex_inv Pk hG hz6 Ψ).choose_spec.2

lemma cell_level (Ψ : TSection ι 𝔪) :
    Cell (levelGroup Pk hG hz6 Ψ) (levelCell Pk hG hz6 Ψ) (levelN Pk hG hz6 Ψ) :=
  (exists_strict_cell (levelGroup Pk hG hz6 Ψ)).choose_spec.choose_spec.2.2.2.2

lemma one_le_levelN (Ψ : TSection ι 𝔪) : 1 ≤ levelN Pk hG hz6 Ψ :=
  (exists_strict_cell (levelGroup Pk hG hz6 Ψ)).choose_spec.choose_spec.2.2.2.1

/-- **Corollary N as an equivalence**: `θ_Ψ = 0` iff `z_{σ·Ψ} = 0` for every `σ ∈ SL₂(R)`. -/
theorem theta_eq_zero_iff_forall_zPsi_translate_eq_zero_oai (hΓ : Inv Γ Ψ) :
    theta Γ Ψ = 0 ↔ ∀ σ : SL(2, SInt 𝔪), zPsi Pk hG hz6 (TSection.translate Pk hG hz6 σ Ψ) = 0 := by
  constructor
  · intro h σ
    exact zRes_translate_eq_zero_of_theta Pk hG hz6 hΓ (eisE hG) h σ
      (inv_levelGroup Pk hG hz6 _) (cell_level Pk hG hz6 _)
  · intro h
    exact corollaryN Pk hG hz6 hΓ fun σ => ⟨_, _, _, inferInstance, inv_levelGroup Pk hG hz6 _,
      cell_level Pk hG hz6 _, one_le_levelN Pk hG hz6 _, h σ⟩

end

end

end ArtinKP.N2
end

theorem solution.{u_1} : type_of% @ArtinKP.N2.theta_eq_zero_iff_forall_zPsi_translate_eq_zero_oai.{u_1} := @ArtinKP.N2.theta_eq_zero_iff_forall_zPsi_translate_eq_zero_oai.{u_1}
