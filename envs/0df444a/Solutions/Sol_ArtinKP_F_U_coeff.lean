-- Prove2me | solution 1 for ArtinKP.F.U_coeff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:06:32.207305+00:00
-- url     : https://prove2.me/submissions/0b5e3542-fd3d-43f4-bd2e-93511290d357

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
import Theorems.Thm_ArtinKP_FB_sum_eInf_reps

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
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-! ### The archimedean kernel -/

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

/-! ### Coefficients over cells of admissible lattices -/

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
theorem U_coeff_oai {T : Finset (SInt 𝔪)} (hT : IsU hG hz6 h g Φ T) {M : ℤ} (hM : 0 ≤ M)
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

theorem solution.{u_1} : type_of% @ArtinKP.F.U_coeff_oai.{u_1} := @ArtinKP.F.U_coeff_oai.{u_1}
