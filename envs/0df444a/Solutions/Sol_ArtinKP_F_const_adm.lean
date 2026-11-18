-- Prove2me | solution 1 for ArtinKP.F.const_adm
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:04:02.92127+00:00
-- url     : https://prove2.me/submissions/1b8dc311-f0f0-4160-8ad7-c8a8406d2b5c

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
import Theorems.Thm_ArtinKP_B_fourier_coeff

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

lemma integral_add_one_Ioi (f : ℝ → ℂ) :
    (∫ x : ℝ in Set.Ioi 0, f (x+1)) = ∫ x : ℝ in Set.Ioi 1, f x := by
  have h := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi
    (fun x (hx : x ∈ Set.Ioi (0:ℝ)) => (hasDerivAt_id x |>.add_const 1).hasDerivWithinAt)
    (fun x hx y hy hxy => by dsimp at hxy; linarith : InjOn (fun x : ℝ => x+1) (Set.Ioi 0)) f
  simp only [id_eq] at h
  rw [add_one_image_Ioi] at h
  simpa only [abs_one, one_smul] using h.symm

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

/-- The constant term: `∫_ℂ (v/(|x|²+v²))^s dx = π/(s−1) · v^{2−s}`. -/
theorem jacquet_zero (s : ℂ) (hs : 1 < s.re) {v : ℝ} (hv : 0 < v) :
    jacquet s 0 v = (Real.pi : ℂ) / (s - 1) * (v : ℂ) ^ (2 - s) := by
  rw [jacquet_eq_sourceFourierKernel s 0 hv, zero_mul, sourceFourierKernel_zero s hs, mul_comm]

/-! ## Holomorphy in `s` -/

end

end ArtinKP.K
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

/-! ### The `S_f`-character -/

/-! ### The archimedean kernel -/

theorem cpow_prod_nonneg {α : Type*} (t : Finset α) (f : α → ℝ) (hf : ∀ i, 0 ≤ f i) (s : ℂ) :
    (((∏ i ∈ t, f i : ℝ)) : ℂ) ^ s = ∏ i ∈ t, ((f i : ℝ) : ℂ) ^ s := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf a) (Finset.prod_nonneg fun i _ => hf i), ih]

theorem chiInf_zero (x : InfinitePlace F → ℂ) : chiInf (0 : F) x = 1 := by
  simp [chiInf, eInf, archChar]

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

theorem Winf_zero {s : ℂ} (hs : 1 < s.re) {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w) :
    Winf s (0 : F) v = ((Real.pi : ℂ) / (s - 1)) ^ Fintype.card (InfinitePlace F)
      * ((∏ w, v w : ℝ) : ℂ) ^ (2 - s) := by
  rw [Winf, cpow_prod_nonneg _ _ (fun w => (hv w).le)]
  simp only [map_zero, neg_zero]
  rw [Finset.prod_congr rfl fun w _ => jacquet_zero s hs (hv w), Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ]

include hz6 in
/-- **The constant term** (MATH2 §0.2 (B6)):
`∫_D E = vol(D) Φ_s(0,1) ht^s + vol(𝔩_M)⁻¹ (π/(s-1))^r ht^{2-s} ∑_c g(0,c) λ(c;0,s) N(c)^{-s}`. -/
theorem const_term (hV : ValidDepth hG Φ ((0 : SInt 𝔪) : F) M) (hs : 2 < s.re)
    {D : Set (InfinitePlace F → ℂ)} (hD : IsAddFundamentalDomain (transLat 𝔪 M) D volume)
    (hDfin : volume D ≠ ⊤) :
    ∫ x in D, eis (Φ.twist hG hz6) s (X.mk x v hv)
      = ((volume D).toReal : ℂ) * (Φ s 0 1 * ((∏ w, v w : ℝ) : ℂ) ^ s)
        + ((vol 𝔪 M : ℝ) : ℂ)⁻¹
          * (((Real.pi : ℂ) / (s - 1)) ^ Fintype.card (InfinitePlace F)
            * ((∏ w, v w : ℝ) : ℂ) ^ (2 - s))
          * ∑' a : Cls (SInt 𝔪),
              B7.gauss (S2.cubicSymbol ι P hG hz6) (B7.sAdd 𝔪 hG.ne_bot) 0 (rp a.1)
                * lam (psiS hG.ne_bot) M Φ ((rp a.1 : SInt 𝔪) : F) 0 s * nrm (rp a.1) ^ (-s) := by
  have h := fourier_coeff hG hz6 Φ s v hv M (0 : SInt 𝔪) hV hs hD hDfin
  have h0 : ((0 : SInt 𝔪) : F) = 0 := rfl
  rw [h0] at h
  simp only [chiInf_zero, mul_one] at h
  rw [setIntegral_const, Measure.real, Complex.real_smul, mul_one] at h
  rw [h, Winf_zero (by linarith) hv]
  ring

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.S2_Kubota
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-S2, part 8: the normalized finite Jacquet functional `Lam` and the laws of `E.Kubota`

`Lam ψ hG Φ c ν s := |c|_{S_f}^s · J_Φ(c; ν, s)`, the functional of WP-S (`S.lam`) taken at a
valid depth; by `jacD_eq_of_le` it does not depend on the valid depth (`Lam_eq_lamD`).

* `Lam_unit` (J1), `Lam_cube` (S1³), `Lam_act` (MATH2 Lemma 6.1 (iii), any frequency),
  `torusT_torusT_inv` and `Lam_act_surj`: the laws required by the interface `E.Kubota`.
* `kubota`: the instance `E.Kubota (cubicSymbol …) (B7.sAdd 𝔪 h𝔪) (GSection ι P 𝔪)` with
  `act β = Ã(β)`, **given** its field `summable` as a hypothesis.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S2

open ArtinKP.A ArtinKP.S

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

theorem Lam_eq_lam (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) {ν : F} {M : ℤ}
    (h : Valid ψ Φ ν (fun _ => M)) (c : F) (s : ℂ) :
    Lam ψ hG Φ c ν s = lam ψ M Φ c ν s :=
  Lam_eq_lamD ψ hG Φ h c s

/-! ### The interface `E.Kubota` -/

end ArtinKP.S2
end
end

section
-- module Solutions.Artin.KP.B_Kub
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-- `Lam` is `S.lam` at any valid depth. -/
theorem LamR_eq_lam {M : ℤ} (hV : ValidDepth hG Φ (ν : F) M) (c : SInt 𝔪) (s : ℂ) :
    S2.LamR (psiS hG.ne_bot) hG Φ c ν s = lam (psiS hG.ne_bot) M Φ (c : F) (ν : F) s :=
  S2.Lam_eq_lam (psiS hG.ne_bot) hG Φ ⟨hV.unip, hV.char⟩ (c : F) s

theorem aCoeff_eq {M : ℤ} (hV : ValidDepth hG Φ (ν : F) M) (s : ℂ) :
    aCoeff hG hz6 Φ ν s = ∑' a : Cls (SInt 𝔪),
      gauss (S2.cubicSymbol ι P hG hz6) (sAdd 𝔪 hG.ne_bot) ν (rp a.1)
        * lam (psiS hG.ne_bot) M Φ ((rp a.1 : SInt 𝔪) : F) (ν : F) s * nrm (rp a.1) ^ (-s) :=
  tsum_congr fun a => by rw [kTerm, LamR_eq_lam hG Φ ν hV]

/-- **The constant term of `E_Φ` at `∞`**:
`∫_D E(x, v) dx = vol(D) Φ_s(0,1) ht^s + vol(𝔩_M)⁻¹ m_Φ(s) ht^{2-s}`. -/
theorem const_term_mCoeff {M : ℤ} (hV : ValidDepth hG Φ ((0 : SInt 𝔪) : F) M) {s : ℂ}
    (hs : 2 < s.re) (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w)
    {D : Set (InfinitePlace F → ℂ)} (hD : IsAddFundamentalDomain (transLat 𝔪 M) D volume)
    (hDfin : volume D ≠ ⊤) :
    ∫ x in D, eis (Φ.twist hG hz6) s (X.mk x v hv)
      = ((volume D).toReal : ℂ) * (Φ s 0 1 * ((∏ w, v w : ℝ) : ℂ) ^ s)
        + ((vol 𝔪 M : ℝ) : ℂ)⁻¹ * (mCoeff hG hz6 Φ s * ((∏ w, v w : ℝ) : ℂ) ^ (2 - s)) := by
  rw [const_term hG hz6 Φ s v hv M hV hs hD hDfin, mCoeff, aCoeff_eq hG hz6 Φ 0 hV]
  have h0 : ((0 : SInt 𝔪) : F) = 0 := rfl
  rw [h0]
  ring

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

theorem measure_unionSet (hrep : IsReps L L₁ rep) (h : PCell L₁ D) :
    μ (unionSet rep D) = ∑ k, μ (shiftSet (rep k) D) := by
  have e : unionSet rep D = ⋃ k ∈ (Finset.univ : Finset κ), shiftSet (rep k) D := by
    rw [unionSet_eq]; simp
  rw [e]
  exact measure_biUnion_finset (fun k _ k' _ hkk => disjoint_shiftSet hrep h hkk)
    (fun k _ => measurableSet_shiftSet _ h.meas)

end union

section shift

variable {μ : Measure E} [μ.IsAddRightInvariant]

theorem measure_shiftSet (t : E) (D : Set E) (hD : MeasurableSet D) :
    μ (shiftSet t D) = μ D :=
  (measurePreserving_sub_right μ t).measure_preimage hD.nullMeasurableSet

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

/-- **Mean values over cells of commensurable lattices.** -/
theorem mean_eq {μ : Measure E} [μ.IsAddRightInvariant] [μ.IsAddLeftInvariant] [Countable L]
    (hL₁ : L ≤ L₁) (hL₂ : L ≤ L₂)
    {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂] {rep₁ : κ₁ → E} {rep₂ : κ₂ → E}
    (hrep₁ : IsReps L L₁ rep₁) (hrep₂ : IsReps L L₂ rep₂) (h₁ : PCell L₁ D₁) (h₂ : PCell L₂ D₂)
    {f : E → ℂ} (hper : ∀ g ∈ L₁, ∀ x, f (x + g) = f x)
    (hint₁ : IntegrableOn f D₁ μ) (hint₂ : ∀ k, IntegrableOn f (shiftSet (rep₂ k) D₂) μ) {I : ℂ}
    (hI : ∀ k, ∫ x in shiftSet (rep₂ k) D₂, f x ∂μ = I) :
    ((μ.real D₂ : ℝ) : ℂ) * ∫ x in D₁, f x ∂μ = ((μ.real D₁ : ℝ) : ℂ) * I := by
  have hU₁ := (h₁.union hL₁ hrep₁).isAddFundamentalDomain μ
  have hU₂ := (h₂.union hL₂ hrep₂).isAddFundamentalDomain μ
  have hinv : ∀ (g : L) (x : E), f (g +ᵥ x) = f x := fun g x => by
    change f ((g : E) + x) = f x
    rw [add_comm]; exact hper _ (hL₁ g.2) x
  have hint₁' : ∀ k, IntegrableOn f (shiftSet (rep₁ k) D₁) μ := fun k =>
    integrableOn_shiftSet _ (by simpa only [hper _ (hrep₁.mem k)] using hint₁)
  have e1 : ∫ x in unionSet rep₁ D₁, f x ∂μ = (Fintype.card κ₁ : ℂ) * ∫ x in D₁, f x ∂μ := by
    rw [integral_unionSet hrep₁ h₁ hint₁']
    have : ∀ k, ∫ x in shiftSet (rep₁ k) D₁, f x ∂μ = ∫ x in D₁, f x ∂μ := fun k => by
      rw [integral_shiftSet _ h₁.meas]
      simp only [hper _ (hrep₁.mem k)]
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have e2 : ∫ x in unionSet rep₂ D₂, f x ∂μ = (Fintype.card κ₂ : ℂ) * I := by
    rw [integral_unionSet hrep₂ h₂ hint₂]
    simp only [hI, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have e3 : ∫ x in unionSet rep₁ D₁, f x ∂μ = ∫ x in unionSet rep₂ D₂, f x ∂μ :=
    hU₁.setIntegral_eq hU₂ hinv
  have m1 : μ (unionSet rep₁ D₁) = Fintype.card κ₁ * μ D₁ := by
    rw [measure_unionSet hrep₁ h₁]
    simp only [measure_shiftSet _ _ h₁.meas, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have m2 : μ (unionSet rep₂ D₂) = Fintype.card κ₂ * μ D₂ := by
    rw [measure_unionSet hrep₂ h₂]
    simp only [measure_shiftSet _ _ h₂.meas, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have m3 : (Fintype.card κ₁ : ℝ) * μ.real D₁ = (Fintype.card κ₂ : ℝ) * μ.real D₂ := by
    have := hU₁.measure_eq hU₂
    rw [m1, m2] at this
    have h' := congrArg ENNReal.toReal this
    simpa [measureReal_def, ENNReal.toReal_mul] using h'
  have hc : (Fintype.card κ₁ : ℂ) ≠ 0 := by
    have := hrep₁.nonempty
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have m3' : (Fintype.card κ₁ : ℂ) * ((μ.real D₁ : ℝ) : ℂ)
      = (Fintype.card κ₂ : ℂ) * ((μ.real D₂ : ℝ) : ℂ) := by exact_mod_cast m3
  have e4 : (Fintype.card κ₁ : ℂ) * ∫ x in D₁, f x ∂μ = (Fintype.card κ₂ : ℂ) * I := by
    rw [← e1, ← e2, e3]
  apply mul_left_cancel₀ hc
  linear_combination ((μ.real D₂ : ℝ) : ℂ) * e4 - I * m3'

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

theorem relIndex_inf_right {A B : AddSubgroup (InfinitePlace F → ℂ)} {I J : Ideal (𝓞 F)}
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (hIA : idealLat I ≤ A) (hJB : idealLat J ≤ B)
    (hB : B ≤ latO F) : (A ⊓ B).relIndex B ≠ 0 := by
  rw [inf_comm]
  exact relIndex_inf_left hJ hI hJB hIA hB

/-! ### The two families of lattices -/

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

/-- A translate of a bounded set is bounded. -/
lemma exists_bdd_shiftSet {D : Set (InfinitePlace F → ℂ)} {n : ℕ}
    (h : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) (t : InfinitePlace F → ℂ) :
    ∃ n' : ℕ, ∀ x ∈ shiftSet t D, ∀ w, ‖x w‖ ≤ n' := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖t‖
  refine ⟨n + N, fun x hx w => ?_⟩
  have h1 := h _ hx w
  have h2 : ‖t w‖ ≤ N := (norm_le_pi_norm t w).trans hN
  have e : x w = (x - t) w + t w := by simp
  rw [e]
  push_cast
  exact (norm_add_le _ _).trans (add_le_add h1 h2)


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

/-- All cells of `Λ_M` have the volume of `cellM`. -/
theorem volume_eq_cellM (h𝔪 : 𝔪 ≠ ⊥) {M : ℤ} (hM : 0 ≤ M) {D : Set (InfinitePlace F → ℂ)}
    (hD : IsAddFundamentalDomain (transLat 𝔪 M) D volume) : volume D = volume (cellM 𝔪 M) :=
  hD.measure_eq ((pcell_cellM h𝔪 hM).isAddFundamentalDomain volume)

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

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.F_Per_Mean
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.G1.scal_apply
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

lemma adm_transLat (h𝔪 : 𝔪 ≠ ⊥) {M : ℤ} (hM : 0 ≤ M) : Adm (transLat 𝔪 M) :=
  ⟨transLat_le_latO hM, exists_idealLat_le_transLat h𝔪 M⟩

/-- **Means over cells of two admissible lattices.** -/
theorem mean_adm {A₁ A₂ : AddSubgroup (InfinitePlace F → ℂ)} (h₁ : Adm A₁) (h₂ : Adm A₂)
    {D₁ D₂ : Set (InfinitePlace F → ℂ)} {n₁ n₂ : ℕ} (hD₁ : PCell A₁ D₁)
    (hb₁ : ∀ x ∈ D₁, ∀ w, ‖x w‖ ≤ n₁) (hD₂ : PCell A₂ D₂) (hb₂ : ∀ x ∈ D₂, ∀ w, ‖x w‖ ≤ n₂)
    {f : (InfinitePlace F → ℂ) → ℂ} (hfc : Continuous f)
    (hper : ∀ g ∈ A₁, ∀ x, f (x + g) = f x) {I : ℂ}
    (hI : ∀ t, ∫ x in shiftSet t D₂, f x = (((volume D₂).toReal : ℝ) : ℂ) * I) :
    ∫ x in D₁, f x = (((volume D₁).toReal : ℝ) : ℂ) * I := by
  obtain ⟨I₁, hI₁, hle₁⟩ := h₁.ideal
  obtain ⟨I₂, hI₂, hle₂⟩ := h₂.ideal
  have := h₁.countable
  have := h₂.countable
  have : Countable ↥(A₁ ⊓ A₂) :=
    (AddSubgroup.inclusion_injective (inf_le_left : A₁ ⊓ A₂ ≤ A₁)).countable
  obtain ⟨κ₁, _, rep₁, hrep₁⟩ := exists_reps (relIndex_inf_left hI₁ hI₂ hle₁ hle₂ h₁.le)
  obtain ⟨κ₂, _, rep₂, hrep₂⟩ := exists_reps (relIndex_inf_right hI₁ hI₂ hle₁ hle₂ h₂.le)
  have key := mean_eq (μ := (volume : Measure (InfinitePlace F → ℂ)))
    (L := A₁ ⊓ A₂) inf_le_left inf_le_right hrep₁ hrep₂ hD₁ hD₂ hper
    (integrableOn_of_bdd hb₁ hfc)
    (fun k => by
      obtain ⟨n', hn'⟩ := exists_bdd_shiftSet hb₂ (rep₂ k)
      exact integrableOn_of_bdd hn' hfc)
    (fun k => hI (rep₂ k))
  have hc0 : (((volume D₂).toReal : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (volume_toReal_pos hD₂ hb₂).ne'
  simp only [measureReal_def] at key
  apply mul_left_cancel₀ hc0
  rw [key]
  ring

/-! ### Scaled lattices and cells -/

/-! ### Coefficients over cells of admissible lattices -/

/-- `kap 𝔪 M` does not depend on `M ≥ 0`. -/
lemma kap_eq_zero' (h𝔪 : 𝔪 ≠ ⊥) {M : ℤ} (hM : 0 ≤ M) : kap 𝔪 M = kap 𝔪 0 := by
  rw [kap_eq h𝔪 hM, kap_eq h𝔪 le_rfl]

section coef

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (Φ : GSection ι P 𝔪)

include hG hz6 in
/-- **The constant term over a cell of an admissible lattice of periods.** -/
theorem const_adm_oai {M : ℤ} (hM : 0 ≤ M) (hV : ValidDepth hG Φ ((0 : SInt 𝔪) : F) M)
    {A : AddSubgroup (InfinitePlace F → ℂ)} (hA : Adm A)
    {D : Set (InfinitePlace F → ℂ)} (hD : PCell A D) {n : ℕ} (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n)
    {Γ : Subgroup (SL(2, 𝓞 F))} (hΓ : Inv Γ (Φ.twist hG hz6)) (hAΓ : A ≤ latN Γ)
    {s : ℂ} (hs : 2 < s.re) (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) :
    ∫ x in D, eis (Φ.twist hG hz6) s (X.mk x v hv)
      = (((volume D).toReal : ℝ) : ℂ) * (Φ s 0 1 * ((∏ w, v w : ℝ) : ℂ) ^ s
          + kap 𝔪 0 * mCoeff hG hz6 Φ s * ((∏ w, v w : ℝ) : ℂ) ^ (2 - s)) := by
  have h𝔪 := hG.ne_bot
  set f : (InfinitePlace F → ℂ) → ℂ := fun x => eis (Φ.twist hG hz6) s (X.mk x v hv) with hf
  have hfc : Continuous f := (continuous_eis h𝔪 _ hs).comp (continuous_mk_x v hv)
  have hperf : ∀ g ∈ A, ∀ x, f (x + g) = f x := fun g hg x =>
    eis_add_latN h𝔪 hΓ s (hAΓ hg) x v hv
  have hc := pcell_cellM h𝔪 hM
  have hcb := cellM_bdd h𝔪 hM
  have hV0 : ((vol 𝔪 M : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (vol_pos 𝔪 M).ne'
  have hc0 : (((volume (cellM 𝔪 M)).toReal : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (volume_toReal_pos hc hcb).ne'
  refine mean_adm hA (adm_transLat h𝔪 hM) hD hb hc hcb hfc hperf (fun t => ?_)
  obtain ⟨n', hn'⟩ := exists_bdd_shiftSet hcb t
  have h1 := const_term_mCoeff hG hz6 Φ hV hs v hv
    ((hc.shift t).isAddFundamentalDomain volume) (volume_ne_top_of_bdd hn')
  rw [h1, volume_eq_cellM h𝔪 hM ((hc.shift t).isAddFundamentalDomain volume),
    ← kap_eq_zero' h𝔪 hM, T.kap]
  push_cast
  field_simp

end coef

end

end ArtinKP.F
end

theorem solution.{u_1} : type_of% @ArtinKP.F.const_adm_oai.{u_1} := @ArtinKP.F.const_adm_oai.{u_1}
