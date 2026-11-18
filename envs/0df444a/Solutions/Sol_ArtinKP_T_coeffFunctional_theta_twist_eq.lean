-- Prove2me | solution 1 for ArtinKP.T.coeffFunctional_theta_twist_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:01:07.377697+00:00
-- url     : https://prove2.me/submissions/2a12c6e4-dd18-48d8-a5af-6e3398bdd5ba

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
import Theorems.Thm_ArtinKP_T_integral_theta_of_hasCoef
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

theorem archChar_neg (z : ℂ) : archChar (-z) = conj (archChar z) := by
  rw [archChar_eq_re, archChar_eq_re, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.neg_re, map_ofNat]
  push_cast
  ring

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

theorem chiInf_add (ν : F) (x y : InfinitePlace F → ℂ) :
    chiInf ν (x + y) = chiInf ν x * chiInf ν y := by
  rw [chiInf, mul_add, eInf_add, map_mul]
  rfl

theorem chiInf_emb (ν a : F) : chiInf ν (emb a) = conj (eInf (emb (ν * a))) := by
  rw [chiInf, emb_mul]

theorem continuous_chiInf (ν : F) : Continuous (chiInf ν) :=
  Complex.continuous_conj.comp (continuous_eInf.comp (continuous_const.mul continuous_id))

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
attribute [-instance] _root_.ArtinKP.N.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatN _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instSigmaFiniteE1Mu1 _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

theorem archChar_zero : archChar 0 = 1 := by simp [archChar]

theorem exists_chiInf_ne_one {ν : F} (hν : ν ≠ 0) :
    ∃ y : InfinitePlace F → ℂ, chiInf ν y ≠ 1 := by
  classical
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have ha : w₀.embedding ν ≠ 0 := (map_ne_zero _).mpr hν
  refine ⟨Pi.single w₀ (1 / (4 * w₀.embedding ν)), ?_⟩
  rw [chiInf_eq_prod, Finset.prod_eq_single w₀ (fun w _ hw => by
    rw [Pi.single_eq_of_ne hw, mul_zero, archChar_zero]) (fun h => absurd (Finset.mem_univ _) h),
    Pi.single_eq_same]
  have e : -(-(w₀.embedding ν)) * (1 / (4 * w₀.embedding ν)) = ((1 / 4 : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [e, archChar_eq_re, Complex.ofReal_re]
  have e2 : 2 * (Real.pi : ℂ) * Complex.I * ((2 * (1 / 4 : ℝ) : ℝ) : ℂ)
      = (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [e2, Complex.exp_pi_mul_I]
  norm_num

/-- A non-trivial character integrates to `0` over a fundamental cell of a group of periods. -/
theorem setIntegral_chiInf_eq_zero {ν : F} (hν : ν ≠ 0)
    (L : AddSubgroup (InfinitePlace F → ℂ)) [Countable L]
    {D : Set (InfinitePlace F → ℂ)} (hD : IsAddFundamentalDomain L D volume)
    (hper : ∀ (b : L) (x : InfinitePlace F → ℂ),
      chiInf ν ((b : InfinitePlace F → ℂ) + x) = chiInf ν x) :
    ∫ x in D, chiInf ν x = 0 := by
  obtain ⟨y, hy⟩ := exists_chiInf_ne_one hν
  have : VAddCommClass (InfinitePlace F → ℂ) L (InfinitePlace F → ℂ) :=
    ⟨fun a b c => by
      change a + ((b : InfinitePlace F → ℂ) + c) = (b : InfinitePlace F → ℂ) + (a + c)
      abel⟩
  have hD' : IsAddFundamentalDomain L (y +ᵥ D) volume := hD.vadd_of_comm y
  have h1 : ∫ x in D, chiInf ν x = ∫ x in y +ᵥ D, chiInf ν x :=
    hD.setIntegral_eq hD' (fun g x => hper g x)
  have h2 : ∫ x in y +ᵥ D, chiInf ν x = ∫ x in D, chiInf ν (y + x) := by
    have := (measurePreserving_add_left (volume : Measure (InfinitePlace F → ℂ))
      y).setIntegral_image_emb (MeasurableEquiv.addLeft y).measurableEmbedding (chiInf ν) D
    exact this
  simp only [chiInf_add] at h2
  rw [integral_const_mul] at h2
  have h3 : (1 - chiInf ν y) * ∫ x in D, chiInf ν x = 0 := by
    rw [sub_mul, one_mul, ← h2, ← h1, sub_self]
  exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr (Ne.symm hy))

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

include hz6 in
/-- **The `ν`-th Fourier coefficient, `ν ≠ 0`**: `vol(𝔩_M)⁻¹ · W_s(ν; v) · 𝔞_Φ(ν, s)`. -/
theorem fourier_coeff_ne_zero (ν : SInt 𝔪) (hν : ν ≠ 0) (hV : ValidDepth hG Φ (ν : F) M)
    (hs : 2 < s.re) {D : Set (InfinitePlace F → ℂ)}
    (hD : IsAddFundamentalDomain (transLat 𝔪 M) D volume) (hDfin : volume D ≠ ⊤) :
    ∫ x in D, eis (Φ.twist hG hz6) s (X.mk x v hv) * chiInf (ν : F) x
      = ((vol 𝔪 M : ℝ) : ℂ)⁻¹ * Winf s (ν : F) v
          * ∑' a : Cls (SInt 𝔪),
              B7.gauss (S2.cubicSymbol ι P hG hz6) (B7.sAdd 𝔪 hG.ne_bot) ν (rp a.1)
                * lam (psiS hG.ne_bot) M Φ ((rp a.1 : SInt 𝔪) : F) (ν : F) s * nrm (rp a.1) ^ (-s) := by
  have hνF : (ν : F) ≠ 0 := fun h => hν (Subtype.ext h)
  rw [fourier_coeff hG hz6 Φ s v hv M ν hV hs hD hDfin,
    setIntegral_chiInf_eq_zero hνF (transLat 𝔪 M) hD (chiInf_transLat hG Φ M hV), mul_zero,
    zero_add]

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

theorem kubota_aSer (s : ℂ) : (kubota hG hz6).aSer Φ ν s = aCoeff hG hz6 Φ ν s := rfl

/-- `Lam` is `S.lam` at any valid depth. -/
theorem LamR_eq_lam {M : ℤ} (hV : ValidDepth hG Φ (ν : F) M) (c : SInt 𝔪) (s : ℂ) :
    S2.LamR (psiS hG.ne_bot) hG Φ c ν s = lam (psiS hG.ne_bot) M Φ (c : F) (ν : F) s :=
  S2.Lam_eq_lam (psiS hG.ne_bot) hG Φ ⟨hV.unip, hV.char⟩ (c : F) s

theorem aCoeff_eq {M : ℤ} (hV : ValidDepth hG Φ (ν : F) M) (s : ℂ) :
    aCoeff hG hz6 Φ ν s = ∑' a : Cls (SInt 𝔪),
      gauss (S2.cubicSymbol ι P hG hz6) (sAdd 𝔪 hG.ne_bot) ν (rp a.1)
        * lam (psiS hG.ne_bot) M Φ ((rp a.1 : SInt 𝔪) : F) (ν : F) s * nrm (rp a.1) ^ (-s) :=
  tsum_congr fun a => by rw [kTerm, LamR_eq_lam hG Φ ν hV]

/-- **The `ν`-th Fourier coefficient of `E_Φ` at `∞`** (`ν ≠ 0`):
`∫_D E(x, v) conj e_∞(νx) dx = vol(𝔩_M)⁻¹ · W_s(ν; v) · D.aSer Φ ν s`. -/
theorem fourier_coeff_aSer (hν : ν ≠ 0) {M : ℤ} (hV : ValidDepth hG Φ (ν : F) M) {s : ℂ}
    (hs : 2 < s.re) (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w)
    {D : Set (InfinitePlace F → ℂ)} (hD : IsAddFundamentalDomain (transLat 𝔪 M) D volume)
    (hDfin : volume D ≠ ⊤) :
    ∫ x in D, eis (Φ.twist hG hz6) s (X.mk x v hv) * chiInf (ν : F) x
      = ((vol 𝔪 M : ℝ) : ℂ)⁻¹ * Winf s (ν : F) v * (kubota hG hz6).aSer Φ ν s := by
  rw [kubota_aSer, aCoeff_eq hG hz6 Φ ν hV]
  exact fourier_coeff_ne_zero hG hz6 Φ s v hv M ν hν hV hs hD hDfin

end ArtinKP.B
end
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

theorem relIndex_inf_right {A B : AddSubgroup (InfinitePlace F → ℂ)} {I J : Ideal (𝓞 F)}
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (hIA : idealLat I ≤ A) (hJB : idealLat J ≤ B)
    (hB : B ≤ latO F) : (A ⊓ B).relIndex B ≠ 0 := by
  rw [inf_comm]
  exact relIndex_inf_left hJ hI hJB hIA hB

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

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.T_Coef
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap _root_.ArtinKP.G1.scal_apply
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

variable {hG hz6 Φ ν}

/-- **Cells of an arbitrary invariance group compute the coefficient, with the same constant.** -/
theorem hasCoef_latN (hν : ν ≠ 0) {M : ℤ} (hM : 0 ≤ M) (hV : ValidDepth hG Φ (ν : F) M)
    {Γ : Subgroup (SL(2, 𝓞 F))} [Γ.FiniteIndex] (hΓ : Inv Γ (Φ.twist hG hz6))
    {D : Set (InfinitePlace F → ℂ)} (hD : PCell (latN Γ) D) {n : ℕ}
    (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n)
    (hper : ∀ β : 𝓞 F, β ∈ lamN Γ → chiInf (ν : F) (emb (β : F)) = 1) :
    HasCoef hG hz6 Φ ν D (kap 𝔪 M) := by
  intro s hs v hv
  have h𝔪 := hG.ne_bot
  set f : (InfinitePlace F → ℂ) → ℂ :=
    fun x => eis (Φ.twist hG hz6) s (X.mk x v hv) * chiInf (ν : F) x with hf
  have hfc : Continuous f :=
    ((continuous_eis h𝔪 _ hs).comp (continuous_mk_x v hv)).mul (continuous_chiInf _)
  obtain ⟨I₁, hI₁, hle₁⟩ := exists_idealLat_le_latN Γ
  obtain ⟨I₂, hI₂, hle₂⟩ := exists_idealLat_le_transLat h𝔪 M
  obtain ⟨κ₁, _, rep₁, hrep₁⟩ :=
    exists_reps (relIndex_inf_left hI₁ hI₂ hle₁ hle₂ (latN_le_latO Γ))
  obtain ⟨κ₂, _, rep₂, hrep₂⟩ :=
    exists_reps (relIndex_inf_right hI₁ hI₂ hle₁ hle₂ (transLat_le_latO hM))
  have hc := pcell_cellM h𝔪 hM
  have hcb := cellM_bdd h𝔪 hM
  have hperf : ∀ g ∈ latN Γ, ∀ x, f (x + g) = f x := by
    rintro g ⟨β, hβ, rfl⟩ x
    simp only [hf]
    have h1 : eis (Φ.twist hG hz6) s (nInt β • X.mk x v hv)
        = eis (Φ.twist hG hz6) s (X.mk x v hv) :=
      isInv_eis h𝔪 hΓ s ⟨nInt β, hβ⟩ (X.mk x v hv)
    rw [nInt_smul_mk] at h1
    rw [chiInf_add, embO_apply, hper β hβ, mul_one, h1]
  have key := mean_eq (μ := (volume : Measure (InfinitePlace F → ℂ)))
    (L := latN Γ ⊓ transLat 𝔪 M) inf_le_left inf_le_right hrep₁ hrep₂ hD hc hperf
    (integrableOn_of_bdd hb hfc)
    (fun k => by
      obtain ⟨n', hn'⟩ := exists_bdd_shiftSet hcb (rep₂ k)
      exact integrableOn_of_bdd hn' hfc)
    (I := ((vol 𝔪 M : ℝ) : ℂ)⁻¹ * Winf s (ν : F) v * (kubota hG hz6).aSer Φ ν s)
    (fun k => by
      obtain ⟨n', hn'⟩ := exists_bdd_shiftSet hcb (rep₂ k)
      exact fourier_coeff_aSer hG hz6 Φ ν hν hV hs v hv
        ((hc.shift _).isAddFundamentalDomain volume) (volume_ne_top_of_bdd hn'))
  have hc0 : (((volume (cellM 𝔪 M)).toReal : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (volume_toReal_pos hc hcb).ne'
  have hV0 : ((vol 𝔪 M : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (vol_pos 𝔪 M).ne'
  simp only [measureReal_def] at key
  apply mul_left_cancel₀ hc0
  rw [key, kap]
  push_cast
  field_simp

/-! ### The coefficient function of the continuation -/

/-! ### The archimedean factor -/

/-! ### The coefficient of the series over an admissible cell -/

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.T_Theta
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-- **Item 3: the Fourier coefficients of `θ_{Φ.twist}`.**  For every `Γ` of finite index fixing
`Φ.twist`, every bounded strict cell `D` of its translation lattice (`hfund`, as in
`RF.eq_zero_of_coeff`), every box `n ⊇ D`, every `ν ∈ R ∖ 0` with `conj e_∞(ν·)` periodic under
`Λ_Γ`, every valid depth `M ≥ 0` and every test function `φ`:
`ℓ_{ν,φ}(θ) = kap 𝔪 M · τ_Φ(ν) · ∫_{box n} 1_D(x) conj φ(v) W_{4/3}(ν; v)`. -/
theorem coeffFunctional_theta_twist_eq_oai (hν : ν ≠ 0) {M : ℤ} (hM : 0 ≤ M) (hV : ValidDepth hG Φ (ν : F) M)
    (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex] (hΓ : Inv Γ (Φ.twist hG hz6))
    {D : Set (InfinitePlace F → ℂ)} (hD : MeasurableSet D)
    (hfund : ∀ x : InfinitePlace F → ℂ,
      ∃! γ : GammaN Γ, (fun w => x w + GammaN.shift γ w) ∈ D)
    {n : ℕ} (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n)
    (hper : ∀ β : 𝓞 F, β ∈ lamN Γ → chiInf (ν : F) (emb (β : F)) = 1)
    {φ : (InfinitePlace F → ℝ) → ℂ} (hφ : Measurable φ) (hφ1 : ∀ v, ‖φ v‖ ≤ 1) :
    X.coeffFunctional Γ n (stripFn D (freq (ν : F)) φ) (measurable_stripFn hD _ hφ) 1
        (norm_stripFn_le D _ hφ1) (C5.theta Γ (Φ.twist hG hz6))
      = kap 𝔪 M * tau hG hz6 Φ ν * Wc D n φ (ν : F) (4 / 3) := by
  rw [X.coeffFunctional_apply]
  exact integral_theta_of_hasCoef hG hz6 Φ hν hΓ
    (hasCoef_latN hν hM hV hΓ (pcell_of_hfund hD hfund) hb hper) hD hb hφ hφ1

end

end ArtinKP.T
end

theorem solution.{u_1} : type_of% @ArtinKP.T.coeffFunctional_theta_twist_eq_oai.{u_1} := @ArtinKP.T.coeffFunctional_theta_twist_eq_oai.{u_1}
