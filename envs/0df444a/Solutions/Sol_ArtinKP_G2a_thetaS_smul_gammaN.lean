-- Prove2me | solution 1 for ArtinKP.G2a.thetaS_smul_gammaN
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:07:26.96869+00:00
-- url     : https://prove2.me/submissions/79603929-27d4-4647-b780-de9f68067845

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
import Theorems.Thm_ArtinKP_B_continuous_eis
import Theorems.Thm_ArtinKP_GL_eisEigen_of_two_lt_re
import Theorems.Thm_ArtinKP_N_coeff_resPart_add_hInt
import Theorems.Thm_ArtinKP_T_coeffFunctional_theta_twist_eq
import Theorems.Thm_ArtinKP_T_differentiableOn_Afun
import Theorems.Thm_ArtinKP_T_tendsto_ray_Afun
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

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.B_Def2
attribute [-instance] _root_.ArtinKP.B1.instCountablePairClass _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
-- module Solutions.Artin.KP.B_FourArch
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

theorem archChar_neg (z : ℂ) : archChar (-z) = conj (archChar z) := by
  rw [archChar_eq_re, archChar_eq_re, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.neg_re, map_ofNat]
  push_cast
  ring

/-! ### The `S_f`-character -/

/-! ### The archimedean kernel -/

theorem chiInf_eq_prod (ν : F) (x : InfinitePlace F → ℂ) :
    chiInf ν x = ∏ w, archChar (-(-(w.embedding ν)) * x w) := by
  rw [chiInf, eInf, map_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← archChar_neg, Pi.mul_apply, emb_apply]
  congr 1
  ring

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
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-- A valid depth exists for every section and frequency. -/
theorem exists_validDepth (ν : F) : ∃ M : ℤ, ValidDepth hG Φ ν M := by
  obtain ⟨M, h1, h2⟩ := S2.exists_valid hG (psiS hG.ne_bot) Φ ν
  exact ⟨M, h1, h2⟩

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

lemma ofXV_toXV (P : X F) : ofXV (toXV P) = P := (chart F).apply_symm_apply P

lemma measurable_ofXV : Measurable (ofXV : XV F → X F) := by
  refine (chart F).continuous.measurable.comp (measurable_pi_lambda _ fun w => ?_)
  exact ((measurable_pi_apply w).comp measurable_fst).prodMk
    (Real.measurable_log.comp ((measurable_pi_apply w).comp measurable_snd))

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
-- module Solutions.Artin.KP.X_Cusp
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
/-! # WP-X, file 12: the translation subgroup of the cusp and unfolding to a strip

`GammaN Γ ≤ Γ` is the group of translations `[[1, β], [0, 1]]` in `Γ`; it acts on `X` by
`x ↦ x + β` (through the embeddings) and fixes `v`.  If `D ⊂ ℂ^r` is a strict fundamental set for
the translation lattice, `P ↦ 1_D(x(P))` is a partition of unity for `GammaN Γ`, and the
unfolding theorem reads
`∫_{Γ\X} (Σ_{γ ∈ N\Γ} f(γP)) u(P) = ∫_{x ∈ D} f u dμ` (`X.lintegral_unfold_N`).
Fourier analysis along `x` (frequencies in the dual lattice) takes place on the strip `{x ∈ D}`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- `GammaN Γ` acts by translations. -/
theorem GammaN.smul_eq {Γ : Subgroup (SL(2, 𝓞 F))} (γ : GammaN Γ) (P : X F) :
    γ • P = X.trans (GammaN.shift γ) P := by
  have h := smul_of_upper (γ := ((γ : Γ) : SL(2, 𝓞 F))) γ.2.1 P
  have h2 : (((γ : Γ) : SL(2, 𝓞 F)) 0 0 : 𝓞 F) = 1 := γ.2.2
  refine X.ext' (funext fun w => ?_) (funext fun w => ?_)
  · change (((γ : Γ) : SL(2, 𝓞 F)) • P).x w = P.x w + GammaN.shift γ w
    rw [(h w).1, h2]
    simp [GammaN.shift]
  · change (((γ : Γ) : SL(2, 𝓞 F)) • P).v w = P.v w
    rw [(h w).2, h2]
    simp

end

end ArtinKP.X
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

lemma eChar_add_of_int {ν y : InfinitePlace F → ℂ} (h : ∃ m : ℤ, pair ν y = m)
    (x : InfinitePlace F → ℂ) : eChar ν (x + y) = eChar ν x := by
  obtain ⟨m, hm⟩ := h
  rw [eChar, eChar, pair_add, hm]
  have e : 2 * Real.pi * Complex.I * ((pair ν x + (m : ℝ) : ℝ) : ℂ)
      = 2 * Real.pi * Complex.I * (pair ν x : ℂ) + (m : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

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

theorem cf_eq_zero_of_fibers {D : Set (InfinitePlace F → ℂ)} (hD : MeasurableSet D) {n : ℕ}
    (hn : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) {φ : (InfinitePlace F → ℝ) → ℂ} (hφ : Measurable φ)
    (hφ1 : ∀ v, ‖φ v‖ ≤ 1) {R : X F → ℂ} (hR : Measurable R)
    (hint : IntegrableOn R (X.box n) (X.vol F))
    (h0 : ∀ (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w), ∫ x in D, R (X.mk x v hv) = 0) :
    cf D n φ R = 0 := by
  classical
  set G : X F → ℂ := (X.box n : Set (X F)).indicator
    (fun P => conj (stripFn D 0 φ P) * R P) with hG
  have hGm : Measurable G :=
    ((Complex.continuous_conj.measurable.comp (measurable_stripFn hD 0 hφ)).mul hR).indicator
      (X.measurableSet_box n)
  have hGint : Integrable G (X.vol F) :=
    (cf_integrable hD hφ hφ1 hint).integrable_indicator (X.measurableSet_box n)
  set H : XV F → ℂ := fun p => if p.2 ∈ vBox F n then G (ofXV p) else 0 with hH
  have hHm : Measurable H :=
    Measurable.ite (measurable_snd (measurableSet_vBox n)) (hGm.comp measurable_ofXV)
      measurable_const
  have hmp := X.measurePreserving_xv (F := F)
  have hGH : ∀ P : X F, H (P.x, P.v) = G P := by
    intro P
    have hP : ofXV (P.x, P.v) = P := ofXV_toXV P
    simp only [hH, hP]
    split_ifs with hv
    · rfl
    · rw [hG, indicator_of_notMem]
      intro hbox
      exact hv ((mem_box_iff n P).mp hbox).2
  have e1 : cf D n φ R = ∫ p, H p ∂((volume : Measure (InfinitePlace F → ℂ)).prod (X.nuV F)) := by
    unfold cf
    rw [← integral_indicator (X.measurableSet_box n), ← hmp.map_eq,
      integral_map hmp.aemeasurable hHm.aestronglyMeasurable]
    exact integral_congr_ae (Eventually.of_forall fun P => (hGH P).symm)
  have hHint : Integrable H ((volume : Measure (InfinitePlace F → ℂ)).prod (X.nuV F)) := by
    rw [← hmp.integrable_comp hHm.aestronglyMeasurable]
    exact hGint.congr (Eventually.of_forall fun P => (hGH P).symm)
  rw [e1, integral_prod_symm H hHint]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun v => ?_)
  change ∫ x, H (x, v) = 0
  by_cases hv : v ∈ vBox F n
  · have hpos : ∀ w, 0 < v w := fun w => vBox_subset_posSet n hv w (mem_univ _)
    have h1 : ∀ x : InfinitePlace F → ℂ,
        H (x, v) = D.indicator (fun x => conj (φ v) * R (X.mk x v hpos)) x := by
      intro x
      simp only [hH, if_pos hv, ofXV_eq_mk x hpos, hG]
      by_cases hx : x ∈ D
      · have hb : X.mk x v hpos ∈ (X.box n : Set (X F)) := by
          rw [mem_box_iff]
          exact ⟨by simpa using hn x hx, by simpa using hv⟩
        rw [indicator_of_mem hb, indicator_of_mem hx, stripFn_zero]
        simp [indicator_of_mem hx]
      · rw [indicator_of_notMem hx]
        by_cases hb : X.mk x v hpos ∈ (X.box n : Set (X F))
        · rw [indicator_of_mem hb, stripFn_zero]
          simp [indicator_of_notMem hx]
        · rw [indicator_of_notMem hb]
    simp only [h1]
    rw [integral_indicator hD, integral_const_mul, h0 v hpos, mul_zero]
  · simp [hH, if_neg hv]

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

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {Γ : Subgroup (SL(2, 𝓞 F))}

/-! ### The cut-off part against a bounded test function -/

lemma integrableOn_bdd_mul {n : ℕ} {ψ : X F → ℂ} (hψ : Measurable ψ) {C : ℝ}
    (hC : ∀ P, ‖ψ P‖ ≤ C) {f : X F → ℂ} (hf : IntegrableOn f (X.box n) (X.vol F)) :
    IntegrableOn (fun P => conj (ψ P) * f P) (X.box n) (X.vol F) := by
  refine Integrable.bdd_mul (c := C) hf
    (Complex.continuous_conj.measurable.comp hψ).aestronglyMeasurable ?_
  exact Eventually.of_forall fun P => by rw [RCLike.norm_conj]; exact hC P

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

theorem PCell.shift (h : PCell L D) (t : E) : PCell L (shiftSet t D) := by
  refine ⟨measurableSet_shiftSet t h.meas, fun x => ?_⟩
  obtain ⟨g, hg, hu⟩ := h.fund (x - t)
  refine ⟨g, ?_, fun g' hg' => hu g' ?_⟩
  · change (g : E) + x - t ∈ D
    rwa [add_sub_assoc]
  · have : (g' : E) + x - t ∈ D := hg'
    rwa [add_sub_assoc] at this

lemma IsReps.injective {κ : Type*} {rep : κ → E} (h : IsReps L L₁ rep) :
    Function.Injective rep := by
  intro k k' hkk
  obtain ⟨k₀, _, hu⟩ := h.uniq (rep k) (h.mem k)
  have h1 : k = k₀ := hu k (by simp)
  have h2 : k' = k₀ := hu k' (by rw [hkk]; simp)
  rw [h1, h2]

lemma IsReps.nonempty {κ : Type*} {rep : κ → E} (h : IsReps L L₁ rep) : Nonempty κ := by
  obtain ⟨k, _, _⟩ := h.uniq 0 L₁.zero_mem
  exact ⟨k⟩

section union

variable {κ : Type*} [Fintype κ] {rep : κ → E}

/-- The translates `rep k + D` are pairwise disjoint. -/
lemma disjoint_shiftSet (hrep : IsReps L L₁ rep) (h : PCell L₁ D) {k k' : κ} (hk : k ≠ k') :
    Disjoint (shiftSet (rep k) D) (shiftSet (rep k') D) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨g, _, hu⟩ := h.fund x
  have h1 := hu ⟨-rep k, L₁.neg_mem (hrep.mem k)⟩ (by
    change -rep k + x ∈ D
    rw [neg_add_eq_sub]; exact hx)
  have h2 := hu ⟨-rep k', L₁.neg_mem (hrep.mem k')⟩ (by
    change -rep k' + x ∈ D
    rw [neg_add_eq_sub]; exact hx')
  have h3 : -rep k = -rep k' := congrArg Subtype.val (h1.trans h2.symm)
  exact hk (hrep.injective (neg_injective h3))

variable {μ : Measure E}

theorem integral_unionSet (hrep : IsReps L L₁ rep) (h : PCell L₁ D) {f : E → ℂ}
    (hf : ∀ k, IntegrableOn f (shiftSet (rep k) D) μ) :
    ∫ x in unionSet rep D, f x ∂μ = ∑ k, ∫ x in shiftSet (rep k) D, f x ∂μ := by
  have e : unionSet rep D = ⋃ k ∈ (Finset.univ : Finset κ), shiftSet (rep k) D := by
    rw [unionSet_eq]; simp
  rw [e]
  exact integral_biUnion_finset _ (fun k _ => measurableSet_shiftSet _ h.meas)
    (fun k _ k' _ hkk => disjoint_shiftSet hrep h hkk) (fun k _ => hf k)

end union

section shift

variable {μ : Measure E} [μ.IsAddRightInvariant]

theorem integral_shiftSet (t : E) {D : Set E} (hD : MeasurableSet D) (f : E → ℂ) :
    ∫ x in shiftSet t D, f x ∂μ = ∫ y in D, f (y + t) ∂μ := by
  have h := (measurePreserving_sub_right μ t).setIntegral_preimage_emb
    (MeasurableEquiv.subRight t).measurableEmbedding (fun y => f (y + t)) D
  rw [← h]
  refine setIntegral_congr_fun (measurableSet_shiftSet t hD) fun x _ => ?_
  simp

theorem integrableOn_shiftSet (t : E) {D : Set E} {f : E → ℂ}
    (hf : IntegrableOn (fun y => f (y + t)) D μ) : IntegrableOn f (shiftSet t D) μ := by
  have h := (measurePreserving_sub_right μ t).integrableOn_comp_preimage
    (MeasurableEquiv.subRight t).measurableEmbedding (f := fun y => f (y + t)) (s := D)
  have e : ((fun y => f (y + t)) ∘ fun x => x - t) = f := by
    funext x; simp
  rw [e] at h
  exact h.mpr hf

end shift

/-- An `L₁`-periodic function integrates over the union cell to `[L₁ : L]` times its integral
over `D`. -/
theorem integral_unionSet_periodic {μ : Measure E} [μ.IsAddRightInvariant] {κ : Type*}
    [Fintype κ] {rep : κ → E} (hrep : IsReps L L₁ rep) (h : PCell L₁ D) {f : E → ℂ}
    (hper : ∀ g ∈ L₁, ∀ x, f (x + g) = f x) (hint : IntegrableOn f D μ) :
    ∫ x in unionSet rep D, f x ∂μ = (Fintype.card κ : ℂ) * ∫ x in D, f x ∂μ := by
  have hint' : ∀ k, IntegrableOn f (shiftSet (rep k) D) μ := fun k =>
    integrableOn_shiftSet _ (by simpa only [hper _ (hrep.mem k)] using hint)
  rw [integral_unionSet hrep h hint']
  have : ∀ k, ∫ x in shiftSet (rep k) D, f x ∂μ = ∫ x in D, f x ∂μ := fun k => by
    rw [integral_shiftSet _ h.meas]
    simp only [hper _ (hrep.mem k)]
  simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

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

lemma latN_le_latO (Γ : Subgroup (SL(2, 𝓞 F))) : latN Γ ≤ latO F :=
  AddSubgroup.map_mono le_top

/-- Two lattices between `emb(ideal)` and `emb(𝓞)` are commensurable. -/
theorem relIndex_inf_left {A B : AddSubgroup (InfinitePlace F → ℂ)} {I J : Ideal (𝓞 F)}
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (hIA : idealLat I ≤ A) (hJB : idealLat J ≤ B)
    (hA : A ≤ latO F) : (A ⊓ B).relIndex A ≠ 0 := by
  have hIJ : I * J ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot]
    exact not_or.mpr ⟨hI, hJ⟩
  have h0 := relIndex_idealLat hIJ
  have h1 : idealLat (I * J) ≤ idealLat I :=
    AddSubgroup.map_mono (Submodule.toAddSubgroup_mono Ideal.mul_le_left)
  have h2 : idealLat (I * J) ≤ idealLat J :=
    AddSubgroup.map_mono (Submodule.toAddSubgroup_mono Ideal.mul_le_right)
  have hle : idealLat (I * J) ≤ A ⊓ B := le_inf (h1.trans hIA) (h2.trans hJB)
  intro h
  exact h0 (AddSubgroup.relIndex_eq_zero_of_le_right hA
    (AddSubgroup.relIndex_eq_zero_of_le_left hle h))

/-! ### The two families of lattices -/

theorem exists_idealLat_le_latN (Γ : Subgroup (SL(2, 𝓞 F)))
    [Γ.FiniteIndex] : ∃ 𝔫 : Ideal (𝓞 F), 𝔫 ≠ ⊥ ∧ idealLat 𝔫 ≤ latN Γ := by
  obtain ⟨𝔫, h𝔫, h⟩ := exists_ideal_translations Γ
  refine ⟨𝔫, h𝔫, ?_⟩
  rintro x ⟨β, hβ, rfl⟩
  obtain ⟨γ, hγ⟩ := h β hβ
  refine ⟨β, ?_, rfl⟩
  change nInt β ∈ Γ
  rw [← hγ, nInt_eq_of_GammaN]
  exact (γ : Γ).2

/-! ### Cells -/

lemma volume_ne_top_of_bdd {D : Set (InfinitePlace F → ℂ)} {n : ℕ}
    (h : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) : volume D ≠ ⊤ := by
  have hsub : D ⊆ Metric.closedBall (0 : InfinitePlace F → ℂ) n := fun x hx => by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)]
    exact h x hx
  exact ((measure_mono hsub).trans_lt measure_closedBall_lt_top).ne

lemma integrableOn_of_bdd {D : Set (InfinitePlace F → ℂ)} {n : ℕ}
    (h : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) {f : (InfinitePlace F → ℂ) → ℂ} (hf : Continuous f) :
    IntegrableOn f D volume := by
  have hsub : D ⊆ Metric.closedBall (0 : InfinitePlace F → ℂ) n := fun x hx => by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)]
    exact h x hx
  exact (hf.continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set hsub


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
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

theorem conj_eChar_freq (ν : F) (x : InfinitePlace F → ℂ) :
    conj (eChar (freq ν) x) = chiInf ν x := by
  have h1 : chiInf ν x = Complex.exp (2 * Real.pi * Complex.I *
      ((∑ w : InfinitePlace F, 2 * (w.embedding ν * x w).re : ℝ) : ℂ)) := by
    rw [chiInf_eq_prod]
    simp only [archChar_eq_re, neg_neg]
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum]
  have h2 : pair (freq ν) x = -∑ w : InfinitePlace F, 2 * (w.embedding ν * x w).re := by
    unfold pair freq
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    have e : -2 * w.embedding ν * x w = ((-2 : ℝ) : ℂ) * (w.embedding ν * x w) := by
      push_cast; ring
    rw [e, Complex.re_ofReal_mul]
    ring
  rw [h1, eChar, h2, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

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

section Afun

variable (hG) {Γ : Subgroup (SL(2, 𝓞 F))} [Γ.FiniteIndex] {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ)
  (n : ℕ) {ψ : X F → ℂ} (hψ : Measurable ψ) {C : ℝ} (hC : ∀ Q, ‖ψ Q‖ ≤ C)

lemma Afun_eq_functional (s : ℂ) :
    Afun Γ Ψ n ψ s = X.coeffFunctional Γ n ψ hψ C hC (resPart Γ Ψ s) + hInt Ψ n ψ s := by
  rw [Afun, X.coeffFunctional_apply]

include hG hΓ hψ hC in
theorem Afun_eq_eis {s : ℂ} (hs : 2 < s.re) :
    Afun Γ Ψ n ψ s = ∫ Q in X.box n, conj (ψ Q) * eis Ψ s Q ∂X.vol F := by
  rw [Afun_eq_functional n hψ hC]
  exact coeff_resPart_add_hInt hG Γ hΓ hs (GL.eisEigen_of_two_lt_re hG.ne_bot Ψ hs) n ψ hψ C hC

end Afun

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

/-! ### Function level -/

/-! ### Twisted sections with a coefficient series -/

/-! ### The residue -/

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.T_Theta
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-T, file 6: genuine sections — `aCont`, `tau`, the instance `E.Theta`, coefficients of `θ`

For `ν ∈ R ∖ 0` and a genuine section `Φ` (`Ψ = Φ.twist hG hz6`, `a₀ = (B.kubota hG hz6).aSer Φ ν`):

* `aCont hG hz6 Φ ν = contSlit a₀` — holomorphic on `E.slit` (`differentiableOn_aCont`), equal to
  the series on `Re s > 2` (`aCont_eq`), unique (`aCont_unique`);
* `tau hG hz6 Φ ν = resSlit a₀ = lim_{t↓0} (s_t − 4/3)·aCont(s_t)` (`tendsto_tau`);
* **`theta hG hz6 : E.Theta (B.kubota hG hz6) (4/3)`** with `toResFun = E.resFunSlit`;
* **`coeff_theta`** (item 3): the Fourier coefficients of `C5.theta Γ (Φ.twist)` for the cells of
  any `Γ`; `coeff_cont`: the same for the continuation on `E.slit`.
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

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (Φ : GSection ι P 𝔪)
  (ν : SInt 𝔪)

variable {ν}

/-! ### The archimedean factor as an integral over `v` -/


/-! ### Fourier coefficients of `θ` for the cells of `Γ` -/

/-- `freq ν` in WP-RF's dual lattice gives the periodicity hypothesis. -/
lemma chiInf_of_mem_dualLat {Γ : Subgroup (SL(2, 𝓞 F))} {ν' : F} (h : freq ν' ∈ dualLat Γ)
    (β : 𝓞 F) (hβ : β ∈ lamN Γ) : chiInf ν' (emb (β : F)) = 1 := by
  obtain ⟨m, hm⟩ := h (ofLam ⟨β, hβ⟩)
  rw [shift_ofLam] at hm
  rw [← conj_eChar_freq, eChar]
  have e : (emb (β : F) : InfinitePlace F → ℂ) = embO β := rfl
  rw [e, hm]
  have : Complex.exp (2 * Real.pi * Complex.I * ((m : ℝ) : ℂ)) = 1 := by
    have := Complex.exp_int_mul_two_pi_mul_I m
    rw [← this]; congr 1; push_cast; ring
  rw [this, map_one]

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.C9_Dual
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-C9, part 5: trace duality — the frequencies of `Λ_Γ^⊥` are `T.freq ν`, `ν ∈ R`

`DualCover 𝔪 Γ` (the named hypothesis of `C9_Tau`) is proved for every finite-index `Γ` whose
translations contain `emb(𝔪^N)` (`TransLevel 𝔪 Γ`), **under the hypothesis that the different of
`F` is supported in the primes of `𝔪`**:

  `hdiff : ∀ v, v ∉ placesOf 𝔪 → ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal`.

(Without it the statement is false: a prime `v ∤ 𝔪` dividing the different gives frequencies
`ν ∈ 𝔡⁻¹ ∖ R` in the dual lattice of `emb(𝓞)`.)

* `pair_freq_emb`: `pair (T.freq (-μ)) (emb x) = Tr_{F/ℚ}(μ x)`.
* **`dualCover_of_transLevel`**.
* `exists_tau_sumBig_ne_zero'`, `exists_tau_bigCell_ne_zero'`: the statements for package G with
  `hdiff` in place of `DualCover`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology nonZeroDivisors
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C9

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

/-- The pairing with `T.freq (-μ)` on `emb(F)` is the trace form. -/
lemma pair_freq_emb (μ x : F) :
    pair (T.freq (-μ)) (emb x) = ((Algebra.trace ℚ F (μ * x) : ℚ) : ℝ) := by
  have h := congrArg Complex.re
    (K.trace_eq_sum_places (fun w => IsTotallyComplex.isComplex w) (μ * x))
  rw [Complex.ratCast_re, Complex.re_sum] at h
  rw [h]
  unfold pair
  refine Finset.sum_congr rfl fun w _ => ?_
  have e : T.freq (-μ) w * emb x w = ((2 : ℝ) : ℂ) * w.embedding (μ * x) := by
    change -2 * w.embedding (-μ) * w.embedding x = _
    rw [map_neg, map_mul]
    push_cast
    ring
  rw [e, Complex.re_ofReal_mul, Complex.add_re, Complex.conj_re]
  ring

/-! ### The statements for package G, with `hdiff` -/

end

end ArtinKP.C9
end

section
-- module Solutions.Artin.KP.T_Vanish
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
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

lemma continuous_eChar (ν' : InfinitePlace F → ℂ) : Continuous (eChar ν') := by
  unfold eChar pair
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
  exact continuous_finset_sum _ fun w _ =>
    Complex.continuous_re.comp (continuous_const.mul (continuous_apply w))

lemma eChar_add (ν' x y : InfinitePlace F → ℂ) : eChar ν' (x + y) = eChar ν' x * eChar ν' y := by
  rw [eChar, eChar, eChar, RF.pair_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma conj_stripFn' (D : Set (InfinitePlace F → ℂ)) (ν' : InfinitePlace F → ℂ)
    (φ : (InfinitePlace F → ℝ) → ℂ) (Q : X F) :
    conj (stripFn D ν' φ Q) = conj (stripFn D 0 φ Q) * conj (eChar ν' Q.x) := by
  rw [stripFn_zero, stripFn, map_mul, map_mul, map_mul]
  ring

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

section vanish

variable (hG : Good 𝔪) {Γ Γ' : Subgroup (SL(2, 𝓞 F))} [Γ.FiniteIndex] [Γ'.FiniteIndex]
  {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) (hΓ' : Inv Γ' Ψ) {D : Set (InfinitePlace F → ℂ)} {n : ℕ}
  {ν' : InfinitePlace F → ℂ} {g : InfinitePlace F → ℂ}

include hG hΓ hΓ' in
/-- The coefficient of the series at a character not trivial on `Λ_{Γ'}` vanishes. -/
theorem integral_eis_eChar_eq_zero (hD : PCell (latN Γ) D) (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n)
    (hν' : ν' ∈ dualLat Γ) (hg : g ∈ latN Γ') (hne : eChar ν' g ≠ 1) {s : ℂ} (hs : 2 < s.re)
    (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) :
    ∫ x in D, conj (eChar ν' x) * eis Ψ s (X.mk x v hv) = 0 := by
  have h𝔪 := hG.ne_bot
  set f : (InfinitePlace F → ℂ) → ℂ :=
    fun x => conj (eChar ν' x) * eis Ψ s (X.mk x v hv) with hf
  have hfc : Continuous f :=
    (Complex.continuous_conj.comp (continuous_eChar ν')).mul
      ((continuous_eis h𝔪 Ψ hs).comp (continuous_mk_x v hv))
  have hper : ∀ y ∈ latN Γ, ∀ x, f (x + y) = f x := by
    intro y hy x
    simp only [hf]
    rw [eis_add_latN h𝔪 hΓ s hy]
    obtain ⟨β, hβ, rfl⟩ := hy
    have h1 := hν' (ofLam ⟨β, hβ⟩)
    rw [shift_ofLam] at h1
    rw [eChar_add_of_int h1]
  have hshift : ∀ x, f (x + g) = conj (eChar ν' g) * f x := by
    intro x
    simp only [hf]
    rw [eis_add_latN h𝔪 hΓ' s hg, eChar_add, map_mul]
    ring
  obtain ⟨I₁, hI₁, hle₁⟩ := exists_idealLat_le_latN Γ
  obtain ⟨I₂, hI₂, hle₂⟩ := exists_idealLat_le_latN Γ'
  obtain ⟨κ₁, _, rep₁, hrep₁⟩ :=
    exists_reps (relIndex_inf_left hI₁ hI₂ hle₁ hle₂ (latN_le_latO Γ))
  have hD' : PCell (latN Γ ⊓ latN Γ') (unionSet rep₁ D) := hD.union inf_le_left hrep₁
  have hJ := integral_unionSet_periodic (μ := (volume : Measure (InfinitePlace F → ℂ))) hrep₁ hD
    hper (integrableOn_of_bdd hb hfc)
  have hinv : ∀ (l : ↥(latN Γ ⊓ latN Γ')) (x : InfinitePlace F → ℂ), f (l +ᵥ x) = f x :=
    fun l x => by
      change f ((l : InfinitePlace F → ℂ) + x) = f x
      rw [add_comm]
      exact hper _ (inf_le_left (a := latN Γ) l.2) x
  have h1 : ∫ x in shiftSet g (unionSet rep₁ D), f x = ∫ x in unionSet rep₁ D, f x :=
    ((hD'.shift g).isAddFundamentalDomain volume).setIntegral_eq
      (hD'.isAddFundamentalDomain volume) hinv
  rw [integral_shiftSet g hD'.meas] at h1
  simp only [hshift] at h1
  rw [integral_const_mul] at h1
  have hc1 : conj (eChar ν' g) ≠ 1 := fun h => hne (by
    have := congrArg (starRingEnd ℂ) h
    simpa using this)
  have hJ0 : ∫ x in unionSet rep₁ D, f x = 0 := by
    have h2 : (conj (eChar ν' g) - 1) * ∫ x in unionSet rep₁ D, f x = 0 := by
      rw [sub_mul, h1, one_mul, sub_self]
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hc1)
  rw [hJ0] at hJ
  have hcard : (Fintype.card κ₁ : ℂ) ≠ 0 := by
    have := hrep₁.nonempty
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact (mul_eq_zero.mp hJ.symm).resolve_left hcard

include hG hΓ hΓ' in
/-- The coefficient of the continuation vanishes on `E.slit`. -/
theorem Afun_eChar_eq_zero (hD : PCell (latN Γ) D) (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n)
    (hν' : ν' ∈ dualLat Γ) (hg : g ∈ latN Γ') (hne : eChar ν' g ≠ 1)
    {φ : (InfinitePlace F → ℝ) → ℂ} (hφ : Measurable φ) (hφ1 : ∀ v, ‖φ v‖ ≤ 1) {s : ℂ}
    (hs : s ∈ E.slit) : Afun Γ Ψ n (stripFn D ν' φ) s = 0 := by
  have h𝔪 := hG.ne_bot
  refine eqOn_slit (g := fun _ => (0 : ℂ)) (differentiableOn_Afun hG hΓ n
    (measurable_stripFn hD.meas ν' hφ) (norm_stripFn_le D ν' hφ1)) (differentiableOn_const 0)
    (fun s hs => ?_) hs
  rw [Afun_eq_eis hG hΓ n (measurable_stripFn hD.meas ν' hφ) (norm_stripFn_le D ν' hφ1) hs]
  have hEint : IntegrableOn (fun Q : X F => eis Ψ s Q) (X.box n) (X.vol F) :=
    (continuous_eis h𝔪 Ψ hs).continuousOn.integrableOn_compact (isCompact_box n)
  have hχm : Measurable fun Q : X F => eChar ν' Q.x :=
    (measurable_eChar ν').comp X.measurable_x
  have hzero : cf D n φ (fun Q => conj (eChar ν' Q.x) * eis Ψ s Q) = 0 := by
    refine cf_eq_zero_of_fibers hD.meas hb hφ hφ1
      ((Complex.continuous_conj.measurable.comp hχm).mul (measurable_eis h𝔪 Ψ hs))
      (integrableOn_bdd_mul hχm (C := 1) (fun Q => (norm_eChar ν' Q.x).le) hEint) fun v hv => ?_
    exact integral_eis_eChar_eq_zero hG hΓ hΓ' hD hb hν' hg hne hs v hv
  rw [← hzero]
  unfold cf
  refine integral_congr_ae (Eventually.of_forall fun Q => ?_)
  change conj (stripFn D ν' φ Q) * eis Ψ s Q = _
  rw [conj_stripFn']
  ring

include hG hΓ hΓ' in
/-- **The coefficient of `θ_Ψ` at a character not trivial on `Λ_{Γ'}` vanishes.** -/
theorem coeff_theta_eq_zero (hD : MeasurableSet D)
    (hfund : ∀ x : InfinitePlace F → ℂ,
      ∃! γ : GammaN Γ, (fun w => x w + GammaN.shift γ w) ∈ D)
    (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) (hν' : ν' ∈ dualLat Γ) (hg : g ∈ latN Γ')
    (hne : eChar ν' g ≠ 1) {φ : (InfinitePlace F → ℝ) → ℂ} (hφ : Measurable φ)
    (hφ1 : ∀ v, ‖φ v‖ ≤ 1) :
    X.coeffFunctional Γ n (stripFn D ν' φ) (measurable_stripFn hD ν' hφ) 1
      (norm_stripFn_le D ν' hφ1) (C5.theta Γ Ψ) = 0 := by
  rw [X.coeffFunctional_apply]
  have h1 := tendsto_ray_Afun hG hΓ n (measurable_stripFn hD ν' hφ) (norm_stripFn_le D ν' hφ1)
  refine tendsto_nhds_unique h1 (tendsto_const_nhds.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [Afun_eChar_eq_zero hG hΓ hΓ' (pcell_of_hfund hD hfund) hb hν' hg hne hφ hφ1
    (ray_mem_slit ht), mul_zero]

end vanish

/-! ### Genuine sections: the stabilizer contains `n(Λ_M)` -/

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.G2a_Per
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
/-! # WP-G2a, file 4: only frequencies of the dual lattice occur; periodicity of `thetaS`

* `eChar_freq`: `RF.eChar (T.freq ν) x = e_∞(νx)`.
* **`freq_mem_dualLat`**: if `τ_Φ(ν) ≠ 0` then `T.freq ν ∈ RF.dualLat Γ` for *every* finite-index
  `Γ` fixing `Φ.twist` (pass to `Γ ⊓ Γ(a)`, `aν ∈ 𝓞`, where `T.coeff_theta` applies, and use
  `T.coeff_theta_eq_zero`).
* `term_smul`, `thetaS_smul_GammaN`: invariance of every term, hence of `thetaS Φ`, under the
  translations of `Γ`.
-/

open scoped ComplexConjugate Topology MatrixGroups
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}
variable [IsTotallyComplex F]

lemma eChar_freq (ν : F) (x : InfinitePlace F → ℂ) :
    eChar (T.freq ν) x = eInf (emb ν * x) := by
  have h := T.conj_eChar_freq ν x
  rw [chiInf] at h
  exact (starRingEnd ℂ).injective h

lemma eChar_eq_one_iff (ν x : InfinitePlace F → ℂ) :
    eChar ν x = 1 ↔ ∃ m : ℤ, pair ν x = m := by
  rw [eChar, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : ((pair ν x : ℝ) : ℂ) = ((m : ℝ) : ℂ) := by
      have h3 : 2 * Real.pi * Complex.I * ((pair ν x : ℝ) : ℂ)
          = 2 * Real.pi * Complex.I * ((m : ℝ) : ℂ) := by rw [hm]; push_cast; ring
      exact mul_left_cancel₀ h2 h3
    exact_mod_cast this
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [hm]; push_cast; ring⟩

/-- `Tr(μβ) ∈ ℤ` gives integrality of the pairing. -/
lemma pair_freq_int {μ : F} {b : 𝓞 F} (h : ∃ c : 𝓞 F, μ * (b : F) = (c : F)) :
    ∃ m : ℤ, pair (T.freq μ) (emb (b : F)) = m := by
  obtain ⟨c, hc⟩ := h
  have h1 := C9.pair_freq_emb (-μ) (b : F)
  rw [neg_neg] at h1
  rw [h1, neg_mul, hc, map_neg]
  refine ⟨-(Algebra.trace ℤ (𝓞 F) c), ?_⟩
  have := Algebra.coe_trace_int (K := F) c
  push_cast
  rw [← this]
  norm_cast

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-- **Only frequencies of the dual lattice carry a nonzero `τ`.** -/
theorem freq_mem_dualLat (Φ : GSection ι P 𝔪) {ν : SInt 𝔪} (hν : ν ≠ 0)
    (hτ : T.tau hG hz6 Φ ν ≠ 0) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    (hΓ : Inv Γ (Φ.twist hG hz6)) : T.freq ((ν : SInt 𝔪) : F) ∈ dualLat Γ := by
  by_contra hnot
  simp only [dualLat, mem_ofPred_eq, not_forall] at hnot
  obtain ⟨γ, hγ⟩ := hnot
  have hne : eChar (T.freq ((ν : SInt 𝔪) : F)) (GammaN.shift γ) ≠ 1 := fun h =>
    hγ ((eChar_eq_one_iff _ _).mp h)
  -- a denominator of `ν`
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 F) ((ν : SInt 𝔪) : F)
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hyF : (algebraMap (𝓞 F) F y) ≠ 0 := by
    simpa using hy0
  have hνy : ((ν : SInt 𝔪) : F) * (y : F) = (x : F) := by
    rw [← hxy]; field_simp
  set 𝔫 : Ideal (𝓞 F) := Ideal.span {y} with h𝔫
  have h𝔫0 : 𝔫 ≠ ⊥ := by
    rw [h𝔫, ne_eq, Ideal.span_singleton_eq_bot]; exact hy0
  have hfi := RO.princCong_finiteIndex h𝔫0
  set Γ₁ : Subgroup (SL(2, 𝓞 F)) := Γ ⊓ RO.princCong 𝔫 with hΓ₁def
  have hΓ₁ : Inv Γ₁ (Φ.twist hG hz6) := fun δ hδ => hΓ δ hδ.1
  have hdual : T.freq ((ν : SInt 𝔪) : F) ∈ dualLat Γ₁ := by
    intro δ
    set β : 𝓞 F := ((δ : Γ₁) : SL(2, 𝓞 F)) 0 1 with hβ
    have hmem : β ∈ 𝔫 := by
      have h1 : ((δ : Γ₁) : SL(2, 𝓞 F)) ∈ RO.princCong 𝔫 := (δ : Γ₁).2.2
      have h2 := congrArg (fun M : SL(2, 𝓞 F ⧸ 𝔫) => M 0 1) (MonoidHom.mem_ker.mp h1)
      simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
        Matrix.map_apply, Matrix.SpecialLinearGroup.coe_one, ne_eq, zero_ne_one,
        not_false_eq_true, Matrix.one_apply_ne] at h2
      exact Ideal.Quotient.eq_zero_iff_mem.mp h2
    obtain ⟨b', hb'⟩ := Ideal.mem_span_singleton'.mp hmem
    have hs : (GammaN.shift δ : InfinitePlace F → ℂ) = emb ((β : 𝓞 F) : F) := rfl
    rw [hs]
    refine pair_freq_int ⟨b' * x, ?_⟩
    rw [← hb']
    push_cast
    linear_combination ((b' : 𝓞 F) : F) * hνy
  obtain ⟨D, hD, hbdd, hfund⟩ :=
    exists_fundamental_translations Γ₁ (exists_ideal_translations Γ₁)
  obtain ⟨R, hR⟩ := hbdd.exists_norm_le
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge R
  have hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ (n₀ : ℝ) := fun x hx w =>
    (norm_le_pi_norm x w).trans ((hR x hx).trans hn₀)
  have hvol : volume D ≠ 0 :=
    ((T.pcell_of_hfund hD hfund).isAddFundamentalDomain volume).measure_ne_zero (NeZero.ne _)
  obtain ⟨n, hn, hW⟩ := T.exists_Wc_ne_zero ((ν : SInt 𝔪) : F) (s₁ := 4 / 3) (by norm_num)
    hD hvol hb
  have hbn : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ (n : ℝ) := fun x hx w =>
    (hb x hx w).trans (by exact_mod_cast hn)
  obtain ⟨M, hM, hV⟩ := T.exists_validDepth_nonneg hG Φ ((ν : SInt 𝔪) : F)
  have hφ := T.measurable_phaseW (F := F) (s₁ := 4 / 3) (by norm_num) ((ν : SInt 𝔪) : F)
  have hφ1 := T.norm_phaseW_le (F := F) (4 / 3) ((ν : SInt 𝔪) : F)
  have h1 := T.coeffFunctional_theta_twist_eq hG hz6 Φ hν hM hV Γ₁ hΓ₁ hD hfund hbn
    (T.chiInf_of_mem_dualLat hdual) hφ hφ1
  have h2 := T.coeff_theta_eq_zero hG hΓ₁ hΓ hD hfund hbn hdual (shift_mem_latN γ) hne hφ hφ1
  rw [h2] at h1
  have h3 := T.kap_ne_zero hG.ne_bot hM
  exact mul_ne_zero (mul_ne_zero h3 hτ) hW h1.symm

/-- Each term with `τ ≠ 0` is invariant under the translations of `Γ`. -/
theorem term_smul (Φ : GSection ι P 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    (hΓ : Inv Γ (Φ.twist hG hz6)) (ν : {ν : SInt 𝔪 // ν ≠ 0}) (γ : GammaN Γ) (Q : X F) :
    term hG hz6 Φ ν (γ • Q) = term hG hz6 Φ ν Q := by
  by_cases hτ : T.tau hG hz6 Φ (ν : SInt 𝔪) = 0
  · simp [term, hτ]
  have hd := freq_mem_dualLat hG hz6 Φ ν.2 hτ Γ hΓ γ
  rw [GammaN.smul_eq]
  have hx : (X.trans (GammaN.shift γ) Q).x = Q.x + GammaN.shift γ := by
    funext w; rfl
  have hW : T.WX (4 / 3) ((ν : SInt 𝔪) : F) (X.trans (GammaN.shift γ) Q)
      = T.WX (4 / 3) ((ν : SInt 𝔪) : F) Q := rfl
  simp only [term]
  rw [hW, hx, ← eChar_freq, ← eChar_freq, eChar_add_of_int hd]

theorem thetaS_smul_gammaN_oai (Φ : GSection ι P 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    (hΓ : Inv Γ (Φ.twist hG hz6)) (γ : GammaN Γ) (Q : X F) :
    thetaS hG hz6 Φ (γ • Q) = thetaS hG hz6 Φ Q :=
  tsum_congr fun ν => term_smul hG hz6 Φ Γ hΓ ν γ Q

end

end ArtinKP.G2a
end

theorem solution.{u_1} : type_of% @ArtinKP.G2a.thetaS_smul_gammaN_oai.{u_1} := @ArtinKP.G2a.thetaS_smul_gammaN_oai.{u_1}
