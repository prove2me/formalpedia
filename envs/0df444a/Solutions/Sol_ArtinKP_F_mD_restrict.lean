-- Prove2me | solution 1 for ArtinKP.F.mD_restrict
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:06:08.001408+00:00
-- url     : https://prove2.me/submissions/764dfd49-9358-4f63-887b-09dbbc3c20aa

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
import Theorems.Thm_ArtinKP_F_integral_restrict_scale
import Theorems.Thm_ArtinKP_FB_U_eis_primeElt
import Theorems.Thm_ArtinKP_FB_primeElt_gen_of_good

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

theorem Ninf_mul (x y : F) : Ninf (x * y) = Ninf x * Ninf y := by
  simp only [Ninf, map_mul, Finset.prod_mul_distrib]

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
-- module Solutions.Artin.KP.E_Series
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.S2.cubicSymbol_sym
/-! # E_Series: the Kubota coefficient series and its splitting at a prime (corrected (4.1))

Abstract setting (`R` a domain; in the application `R = SInt 𝔪`):

* `Cls R` = nonzero classes of `R` modulo units (`(R∖0)/U_S`), `ClsP π` = those prime to `π`;
  `tsum_split`: a unit-invariant absolutely summable family over `Cls R` is the iterated sum over
  `c = π^j c'`, `π ∤ c'`.
* `Pairing S`: the pairing `⟨c, d⟩` (in the application `ι (c, d)_S`, WP-A's `HS`).
* `Kubota S A Sec`: the **interface** to the analytic packages.  A section `Φ : Sec` is seen only
  through its normalized finite Jacquet functional `Lam Φ c ν s = |c|_{S_f}^s · J_Φ(c; ν, s)`, and
  `act β = Ã(β)` (MATH2 §6.1).  The coefficient series is
  `aSer Φ ν s = ∑_{c ∈ (R∖0)/U} g(ν, c) · Lam Φ c ν s · N(c)^{-s}`.
* `aSer_split` — **(4.1′)**: for `π ∤ ν₀`, `Re s > 2`,
  `aSer Φ (ν₀ π^k) s = Cform q G G' x (m ↦ Y_m(Ã(π)^k Φ)) k`, with B7's `Cform` verbatim, `x = q^{-s}`,
  and the three `π`-coprime twisted series `Y_m(Ψ) = ∑_{π ∤ c'} g(ν₀,c') ((π/c')(c'/π))^{-m}
  Lam Ψ (π^m c') ν₀ s N(c')^{-s}`.
* `aSer_unit` (MATH2 Lemma 6.2), `Lam_act_act` (`Ã(β)Ã(β') = ⟨β,β'⟩ Ã(ββ')` on `Lam`),
  `Lam_iter_eq_pow`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ArtinKP.E

open ArtinKP.B7

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]

/-! ### Classes modulo units -/

/-! ### The norm `N(c) = #(R/cR)` -/

/-! ### Symbols -/

namespace Pairing

variable {S : CubicSymbol R} (B : Pairing S)

lemma br_ne_zero {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) : B.br a b ≠ 0 := by
  intro h
  have := B.br_pow_three a b ha hb
  rw [h] at this
  norm_num at this

lemma br_one_left {b : R} (hb : b ≠ 0) : B.br 1 b = 1 := by
  have h := B.br_mul_left 1 1 b one_ne_zero one_ne_zero hb
  rw [one_mul] at h
  exact (mul_eq_left₀ (B.br_ne_zero one_ne_zero hb)).1 h.symm

lemma br_pow_left {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) (n : ℕ) :
    B.br (a ^ n) b = B.br a b ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, B.br_one_left hb]
  | succ n ih => rw [pow_succ, B.br_mul_left _ _ _ (pow_ne_zero _ ha) ha hb, ih, pow_succ]

/-- `⟨π^n c, π⟩ = ⟨c, π⟩`. -/
lemma br_pow_mul_self {π c : R} (hπ : π ≠ 0) (hc : c ≠ 0) (n : ℕ) :
    B.br (π ^ n * c) π = B.br c π := by
  rw [B.br_mul_left _ _ _ (pow_ne_zero _ hπ) hc hπ, B.br_pow_left hπ hπ, B.br_self π hπ, one_pow,
    one_mul]

end Pairing

/-! ### Gauss sums: units and the splitting `c = π^j c'` -/

/-! ### The interface -/

namespace Kubota

variable {S : CubicSymbol R} {A : AddData R K} {Sec : Type*} (D : Kubota S A Sec)
  (hfin : ∀ c : R, c ≠ 0 → Finite (R ⧸ Ideal.span {c}))

/-- `Ã(π)^k` on `Lam`: `Lam (Ã(π)^k Φ) c ν = ⟨c,π⟩^{2k} Lam Φ (π^{2k} c) (π^k ν)`. -/
theorem Lam_iter (Φ : Sec) {π : R} (hπ : π ≠ 0) (k : ℕ) (c ν : R) {s : ℂ} (hc : c ≠ 0)
    (hs : 2 < s.re) :
    D.Lam ((D.act π)^[k] Φ) c ν s =
      D.br c π ^ (2 * k) * D.Lam Φ (π ^ (2 * k) * c) (π ^ k * ν) s := by
  induction k generalizing c ν with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', D.Lam_act _ π c ν s hπ hc hs,
      ih _ _ (mul_ne_zero (pow_ne_zero _ hπ) hc), D.toPairing.br_pow_mul_self hπ hc,
      show π ^ (2 * k) * (π ^ 2 * c) = π ^ (2 * (k + 1)) * c by ring,
      show π ^ k * (π * ν) = π ^ (k + 1) * ν by ring]
    ring

/-- `Ã(π)³` translates the frequency by `π³` and does nothing else (MATH2 Lemma 6.1(ii):
`Ã(π)³Φ = |π|^{-3} Φ(c, d/π³)`). -/
theorem Lam_iter_three (Φ : Sec) {π : R} (hπ : π ≠ 0) (c ν : R) {s : ℂ} (hc : c ≠ 0)
    (hs : 2 < s.re) : D.Lam ((D.act π)^[3] Φ) c ν s = D.Lam Φ c (π ^ 3 * ν) s := by
  have h3 := D.br_pow_three c π hc hπ
  rw [D.Lam_iter Φ hπ 3 c ν hc hs, show π ^ (2 * 3) * c = (π ^ 2) ^ 3 * c by ring,
    D.Lam_cube Φ (π ^ 2) c _ s (pow_ne_zero _ hπ) hc hs, show 2 * 3 = 3 * 2 by norm_num, pow_mul,
    h3, one_pow, one_mul]

end Kubota

/-! ### The prime datum and the splitting (4.1′) -/

end ArtinKP.E
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

theorem kubota_Lam (c : SInt 𝔪) (s : ℂ) :
    (kubota hG hz6).Lam Φ c ν s = S2.LamR (psiS hG.ne_bot) hG Φ c ν s := rfl

theorem kubota_act (β : SInt 𝔪) : (kubota hG hz6).act β Φ = S2.actR hG β Φ := rfl

/-- A valid depth exists for every section and frequency. -/
theorem exists_validDepth (ν : F) : ∃ M : ℤ, ValidDepth hG Φ ν M := by
  obtain ⟨M, h1, h2⟩ := S2.exists_valid hG (psiS hG.ne_bot) Φ ν
  exact ⟨M, h1, h2⟩

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

end ArtinKP.FB
end
end

section
-- module Solutions.Artin.KP.F_Eis_Fourier
attribute [-instance] _root_.ArtinKP.B.instCountableIdxI _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.B1.instCountablePairClass _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instSigmaFiniteE1Mu1 _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
-- module Solutions.Artin.KP.N_Orbit
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-N, file 1: the `x`-integral of the tail of `E_Ψ` over a cell of the translations of `Γ`

For `Γ ≤ SL₂(𝓞_F)` fixing the twisted section `Ψ`, `Λ_Γ = {β : n(β) ∈ Γ}` (`lamN Γ`, embedded in
`ℂ^r` as `latN Γ`) and `D` a fundamental domain of `latN Γ`:

* `tail Ψ s Q = E_Ψ(Q, s) − Ψ_s(0,1)·ht(Q)^s` (no hypotheses in the definition);
* `exists_integral_tail`: for `Re s > 2` there is a constant `C` with
  `∫_D tail Ψ s (x, v) dx = C · ∏_w v_w^{2−s}` for **all** `v`
  (the classes `≠ ∞` are unfolded along the free action of `Λ_Γ`, `orbN`; each full-space integral
  is a Jacquet integral at frequency `0`, WP-B's `integral_hKer` and WP-K's `jacquet_zero`);
* `integrableOn_tail`: the tail is integrable over `D`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ}

/-! ### The translation lattice of `Γ` -/

/-! ### Orbits of `Λ_Γ` on the classes `≠ ∞` -/

variable {S : Finset (FinitePlace F)}

/-! ### The terms as shifted kernels -/

variable {Γ : Subgroup (SL(2, 𝓞 F))}

/-! ### The tail -/

/-! ### Finiteness of the unfolded `L¹` norm -/

lemma ht_mk (x : InfinitePlace F → ℂ) {v : InfinitePlace F → ℝ} (hv : ∀ w, 0 < v w) :
    X.ht (X.mk x v hv) = ∏ w, v w := by
  simp [X.ht]

/-! ### The integral over a cell -/

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

lemma mem_shiftSet {t : E} {D : Set E} {x : E} : x ∈ shiftSet t D ↔ x - t ∈ D := Iff.rfl

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
-- module Solutions.Artin.KP.T_Coef
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-! ### The coefficient function of the continuation -/

/-! ### The archimedean factor -/

/-! ### The coefficient of the series over an admissible cell -/

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

lemma adm_latN (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex] : Adm (latN Γ) :=
  ⟨latN_le_latO Γ, exists_idealLat_le_latN Γ⟩

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

lemma shiftSet_scaleSet {a : F} (ha : a ≠ 0) (t : InfinitePlace F → ℂ)
    (D : Set (InfinitePlace F → ℂ)) :
    shiftSet t (scaleSet a D) = scaleSet a (shiftSet (emb a⁻¹ * t) D) := by
  ext x
  rw [mem_shiftSet, mem_scaleSet ha, mem_scaleSet ha, mem_shiftSet, mul_sub]

/-- `vol(a·D) = N_∞(a)·vol(D)`. -/
lemma volume_scaleSet {a : F} (ha : a ≠ 0) {D : Set (InfinitePlace F → ℂ)}
    (hD : MeasurableSet D) :
    (((volume (scaleSet a D)).toReal : ℝ) : ℂ)
      = ((Ninf a : ℝ) : ℂ) * (((volume D).toReal : ℝ) : ℂ) := by
  have hA : ∀ w : InfinitePlace F, emb a w ≠ 0 := fun w => by
    rw [emb_apply]; exact (map_ne_zero _).2 ha
  have h := FB.setIntegral_image_mulE hA hD (fun _ => (1 : ℂ))
  rw [setIntegral_const, setIntegral_const] at h
  simp only [Complex.real_smul, mul_one, measureReal_def] at h
  rw [scaleSet, h]
  rfl

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

section coef

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (Φ : GSection ι P 𝔪)

include hG hz6 in
/-- **The constant term over a cell of an admissible lattice of periods.** -/
theorem const_adm {M : ℤ} (hM : 0 ≤ M) (hV : ValidDepth hG Φ ((0 : SInt 𝔪) : F) M)
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

section
-- module Solutions.Artin.KP.G1_Lam
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-G1, part 2: linearity of `Lam`, and the cusp change for `Lam` and for the Kirillov term

* `Lam_smulFun`, `Lam_smul`, `Lam_scal`, `Lam_nT` (all `s`); `Lam_add`, `Lam_sum`, `Lam_addProj`
  (`Re s > 1`, where the defining series converges: `summable_jacTerm`).
* `torusT_torusT`, `torusT_smulFun`, `torusT_smul`.
* `Kt ψ hG Φ β η s := Lam (Ã(β)Φ) η 1 s`, the `η`-term of the Kirillov function (`= S.kir` at a
  valid depth, `Kt_eq_kir`), with the rules (K4):
  `Kt_torusT`, `Kt_nT`, `Kt_smulFun`, `Kt_add`, `Kt_addProj`.
* `Lam_cusp`: `Lam Ψ c' μ s = κ(γ)|c|^{s-2} ψ(μa/c) ⟨c',c⟩⁻¹ Lam (wΦ) (c'/c) (μ/c²) s`,
  `Ψ = translate γ (n(-d/c)Φ)`;
  `cusp_torusT`: `Ã(μ)Ψ = κ(γ)⟨μ,c⟩ |c|^{s-2} n(μa/c) Ã(μ/c²)(wΦ)`;
  `Kt_cusp`, and `xiT_cusp` (MATH3 (2.2)): with `ξ^η_Φ(β) := |β|^{1/3} Kt Φ β η (4/3)`,
  `ξ^η_Ψ(μ) = κ(γ) ψ(μa/c) ⟨μ,c⟩ ξ^η_{wΦ}(μ/c²)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.G1

open ArtinKP.A ArtinKP.S ArtinKP.S2

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

/-! ### Convergence of the defining series, linearity -/

theorem valid_smulFun {ψ : SfChar 𝔪} {Φ : GSection ι P 𝔪} {ν : F}
    {k : HeightOneSpectrum (𝓞 F) → ℤ} (h : Valid ψ Φ ν k) (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    Valid ψ (GSection.smulFun f hf Φ) ν k :=
  ⟨fun b hb s c d => by rw [GSection.smulFun_apply, GSection.smulFun_apply, h.1 b hb], h.2⟩

/-- `Lam` commutes with multiplication by a function of `s` (all `s`). -/
theorem Lam_smulFun (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (c ν : F) (s : ℂ) :
    Lam ψ hG (GSection.smulFun f hf Φ) c ν s = f s * Lam ψ hG Φ c ν s := by
  have h := valid_depth ψ hG Φ ν
  rw [Lam_eq_lam ψ hG _ (valid_smulFun h f hf), Lam_eq_lam ψ hG _ h, lam, lam]
  simp only [GSection.smulFun_apply]
  rw [jac_const_mul]
  ring

theorem Lam_smul (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) (a : ℂ) (c ν : F) (s : ℂ) :
    Lam ψ hG (a • Φ) c ν s = a * Lam ψ hG Φ c ν s :=
  Lam_smulFun ψ hG Φ (fun _ => a) (differentiable_const a) c ν s

/-! ### `Ã(β)` against the other operations -/

/-! ### The Kirillov term -/

/-! ### The cusp change for `Lam` and for the Kirillov term -/

/-! ### The normalized term `ξ^η = |β|^{1/3} Kt(·, 4/3)` -/

end ArtinKP.G1
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

theorem sharp_sharp_inv {π : F} (hπ : π ≠ 0) :
    (Φ.sharp hG π⁻¹ (inv_ne_zero hπ)).sharp hG π hπ = Φ := by
  ext s c d
  rw [GSection.sharp_apply, GSection.sharp_apply]
  congr 1
  field_simp

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

include hz6 in
/-- **`Lam Φ♯ c μ = |π|³ · Lam Φ c (π³ μ)`** (MATH2 (J2)). -/
theorem Lam_sharp {π : SInt 𝔪} (hπ : (π : F) ≠ 0) {c : SInt 𝔪} (hc : c ≠ 0) (μ : SInt 𝔪)
    {s : ℂ} (hs : 2 < s.re) :
    (kubota hG hz6).Lam (Φ.sharp hG (π : F) hπ) c μ s
      = ((absS 𝔪 (π : F) : ℝ) : ℂ) ^ 3 * (kubota hG hz6).Lam Φ c (π ^ 3 * μ) s := by
  have hπ' : π ≠ 0 := fun h => hπ (by rw [h]; rfl)
  have h1 := (kubota (ι := ι) (P := P) hG hz6).Lam_iter_three Φ hπ' c μ hc hs
  rw [iterate_act hG hz6 Φ hπ, kubota_Lam, S2.LamR, G1.Lam_smul] at h1
  have ha0 : ((absS 𝔪 (π : F) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (absS_pos hπ).ne'
  rw [← h1, kubota_Lam, S2.LamR, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ ha0, one_pow, one_mul]

include hz6 in
/-- `m_{Φ♯} = |π|³ · m_Φ`. -/
theorem mCoeff_sharp {π : SInt 𝔪} (hπ : (π : F) ≠ 0) {s : ℂ} (hs : 2 < s.re) :
    mCoeff hG hz6 (Φ.sharp hG (π : F) hπ) s
      = ((absS 𝔪 (π : F) : ℝ) : ℂ) ^ 3 * mCoeff hG hz6 Φ s := by
  have key : ∀ a : Cls (SInt 𝔪), kTerm hG hz6 (Φ.sharp hG (π : F) hπ) 0 a s
      = ((absS 𝔪 (π : F) : ℝ) : ℂ) ^ 3 * kTerm hG hz6 Φ 0 a s := fun a => by
    have h := Lam_sharp hG hz6 Φ hπ (rp_ne_zero a.2) 0 hs
    rw [kubota_Lam, kubota_Lam, mul_zero] at h
    rw [kTerm, kTerm, h]
    ring
  rw [mCoeff, mCoeff, aCoeff, aCoeff, tsum_congr key, tsum_mul_left]
  ring

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

lemma twist_inf (Φ : GSection ι P 𝔪) (s : ℂ) :
    Φ.twist hG hz6 s (Row.inf 𝔪) = Φ s 0 1 := by
  rw [GSection.twist_apply, kappaRow, if_pos (Row.inf_c)]
  simp

lemma restrict_inf (hv : ¬ 𝔪 ≤ v.asIdeal) (Ψ : TSection ι 𝔪) (s : ℂ) :
    TSection.restrict v hv Ψ s (Row.inf 𝔪) = 0 := by
  refine TSection.restrict_apply_of_not_val hv Ψ s ?_
  rw [Row.inf_c]
  simp

/-- `mD` in terms of the integral of the series (`Re s > 2`). -/
lemma mD_eq_integral (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) {s : ℂ} (hs : 2 < s.re)
    {D : Set (InfinitePlace F → ℂ)} {n : ℕ} (_hDm : MeasurableSet D)
    (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) (hD0 : (((volume D).toReal : ℝ) : ℂ) ≠ 0) :
    mD D Ψ s = (((volume D).toReal : ℝ) : ℂ)⁻¹
        * (∫ x in D, eis Ψ s (X.mk x (fun _ => 1) (fun _ => one_pos))) - Ψ s (Row.inf 𝔪) := by
  have hfin := volume_ne_top_of_bdd hb
  have hi : IntegrableOn (fun x : InfinitePlace F → ℂ =>
      eis Ψ s (X.mk x (fun _ => 1) (fun _ => one_pos))) D volume := integrableOn_of_bdd hb
    ((continuous_eis h𝔪 Ψ hs).comp (continuous_mk_x (fun _ => (1 : ℝ)) (fun _ => one_pos)))
  have hc : IntegrableOn (fun _ : InfinitePlace F → ℂ => Ψ s (Row.inf 𝔪)) D volume :=
    integrableOn_const hfin
  have e : ∀ x : InfinitePlace F → ℂ, tail Ψ s (X.mk x (fun _ => 1) (fun _ => one_pos))
      = eis Ψ s (X.mk x (fun _ => 1) (fun _ => one_pos)) - Ψ s (Row.inf 𝔪) := fun x => by
    rw [tail, ht_mk]
    simp
  rw [mD]
  simp only [e]
  rw [integral_sub hi hc, setIntegral_const, measureReal_def, Complex.real_smul, mul_sub,
    ← mul_assoc, inv_mul_cancel₀ hD0, one_mul]

end general

/-! ### Powers of positive reals -/

/-! ### The constant term of `E_{Φ♯ρ_∞}` over scaled cells -/

section gen

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (h : C3I.Good 𝔪 v)
  (g : AllowedGen ι 𝔪) (Φ : GSection ι P 𝔪)

include h in
lemma one_lt_absNorm : 1 < Ideal.absNorm v.asIdeal := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
  exact_mod_cast this

lemma Ninf_pow_three (a : F) :
    ((Ninf (a ^ 3) : ℝ) : ℂ) = ((Ninf a : ℝ) : ℂ) ^ 3 := by
  rw [pow_succ, pow_succ, pow_one, Ninf_mul, Ninf_mul]
  push_cast
  ring

include hG hz6 h g in
/-- **Lemma 5.2 for `ρ_∞`**: `m_{Φ₁ρ_∞}(s) = m_{Φ₁}(s)/L_P(s)` for every genuine section `Φ₁`,
`Re s > 2`, in terms of `N.mD` over a strict cell of a group fixing both sections. -/
theorem mD_restrict_oai (Φ₁ : GSection ι P 𝔪) {Γ' : Subgroup (SL(2, 𝓞 F))} [Γ'.FiniteIndex]
    (hΓ₁ : Inv Γ' (Φ₁.twist hG hz6))
    (hΓR : Inv Γ' (TSection.restrict v (not_le_of_good h) (Φ₁.twist hG hz6)))
    {D₁ : Set (InfinitePlace F → ℂ)} (hD₁ : PCell (latN Γ') D₁) {n₁ : ℕ}
    (hb₁ : ∀ x ∈ D₁, ∀ w, ‖x w‖ ≤ n₁) {s : ℂ} (hs : 2 < s.re) :
    mD D₁ (TSection.restrict v (not_le_of_good h) (Φ₁.twist hG hz6)) s
      = ratio (Ideal.absNorm v.asIdeal : ℂ) s * mD D₁ (Φ₁.twist hG hz6) s := by
  have h𝔪 := hG.ne_bot
  have hπ : (g.gen v.asIdeal : F) ≠ 0 := gen_coe_ne_zero h g
  have hπ3 : (g.gen v.asIdeal : F) ^ 3 ≠ 0 := pow_ne_zero 3 hπ
  have hd := ratio_den_ne_zero (one_lt_absNorm h) (s := s) (by linarith)
  have hsh := sharp_sharp_inv hG Φ₁ hπ
  set Φ : GSection ι P 𝔪 := Φ₁.sharp hG (g.gen v.asIdeal : F)⁻¹ (inv_ne_zero hπ) with hΦ
  obtain ⟨Tr, hT, -⟩ := exists_isU hG hz6 h g Φ 0
  obtain ⟨M₀, hM₀, hV₀⟩ := exists_validDepth_nonneg hG Φ (((0 : SInt 𝔪)) : F)
  obtain ⟨B, hB⟩ := exists_small_neg h𝔪 ((g.gen v.asIdeal : F) ^ 3)
  set M : ℤ := max M₀ B with hMdef
  have hM : 0 ≤ M := hM₀.trans (le_max_left _ _)
  have hV : ValidDepth hG Φ (((0 : SInt 𝔪)) : F) M := validDepth_mono hG Φ hV₀ (le_max_left _ _)
  have hKM : (B : ℤ) ≤ M := le_max_right _ _
  have one_pos' : ∀ w : InfinitePlace F, (0 : ℝ) < (fun _ => 1 : InfinitePlace F → ℝ) w :=
    fun _ => one_pos
  have hprod : (((∏ _w : InfinitePlace F, (1 : ℝ)) : ℝ) : ℂ) = 1 := by simp
  -- the value over all scaled cells
  have hC : ∀ (D : Set (InfinitePlace F → ℂ)) (n : ℕ), PCell (transLat 𝔪 M) D →
      (∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) →
      ∫ x in scaleSet ((g.gen v.asIdeal : F) ^ 3) D,
        eis (TSection.restrict v (not_le_of_good h) (Φ₁.twist hG hz6)) s
          (X.mk x (fun _ => 1) (fun _ => one_pos))
      = ((Ninf (g.gen v.asIdeal : F) : ℝ) : ℂ) ^ 3 * (((volume D).toReal : ℝ) : ℂ)
        * (T.kap 𝔪 0 * mCoeff hG hz6 Φ₁ s * ratio (Ideal.absNorm v.asIdeal : ℂ) s) := by
    intro D n hD hb
    have key := integral_restrict_scale hG hz6 h g Φ hT hM hV hB hKM hD hb hs hd
      (fun _ => 1) (fun _ => one_pos)
    have hm := mCoeff_sharp hG hz6 Φ hπ hs
    simp only [hsh] at key hm
    rw [key, hprod, Complex.one_cpow, hm, ratio]
    ring
  have hAdm : Adm (scaleLat ((g.gen v.asIdeal : F) ^ 3) (transLat 𝔪 M)) := by
    have ecast : (((g.gen v.asIdeal ^ 3 : SInt 𝔪)) : F) = (g.gen v.asIdeal : F) ^ 3 := rfl
    have := adm_scaleLat h𝔪 (g.gen v.asIdeal ^ 3) (by rw [ecast]; exact hπ3) (K := B) (M := M)
      (by rw [ecast]; exact hB) hKM
    rwa [ecast] at this
  have hc := pcell_cellM h𝔪 hM
  have hcb := cellM_bdd h𝔪 hM
  obtain ⟨nc, hnc⟩ := exists_bdd_scaleSet ((g.gen v.asIdeal : F) ^ 3) hcb
  have hfc : Continuous fun x : InfinitePlace F → ℂ =>
      eis (TSection.restrict v (not_le_of_good h) (Φ₁.twist hG hz6)) s
        (X.mk x (fun _ => 1) (fun _ => one_pos)) :=
    (continuous_eis h𝔪 _ hs).comp (continuous_mk_x _ _)
  have hR := mean_adm (adm_latN Γ') hAdm hD₁ hb₁ (pcell_scale hπ3 hc) hnc hfc
    (fun g' hg' x => eis_add_latN h𝔪 hΓR s hg' x _ _)
    (I := T.kap 𝔪 0 * mCoeff hG hz6 Φ₁ s * ratio (Ideal.absNorm v.asIdeal : ℂ) s)
    (fun t => by
      obtain ⟨n', hn'⟩ := exists_bdd_shiftSet hcb (emb ((g.gen v.asIdeal : F) ^ 3)⁻¹ * t)
      rw [shiftSet_scaleSet hπ3, hC _ n' (hc.shift _) hn', measure_shiftSet _ _ hc.meas,
        volume_scaleSet hπ3 hc.meas, Ninf_pow_three])
  have := (adm_latN Γ').countable
  have hD0 : (((volume D₁).toReal : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (volume_toReal_pos hD₁ hb₁).ne'
  obtain ⟨M₁, hM₁, hV₁⟩ := exists_validDepth_nonneg hG Φ₁ (((0 : SInt 𝔪)) : F)
  have h1 := const_adm hG hz6 Φ₁ hM₁ hV₁ (adm_latN Γ') hD₁ hb₁ hΓ₁ le_rfl hs
    (fun _ => 1) (fun _ => one_pos)
  rw [mD_eq_integral h𝔪 _ hs hD₁.meas hb₁ hD0, mD_eq_integral h𝔪 _ hs hD₁.meas hb₁ hD0, hR, h1,
    restrict_inf, twist_inf, hprod, Complex.one_cpow, Complex.one_cpow]
  field_simp
  ring

end gen

end

end ArtinKP.F
end

theorem solution.{u_1} : type_of% @ArtinKP.F.mD_restrict_oai.{u_1} := @ArtinKP.F.mD_restrict_oai.{u_1}
