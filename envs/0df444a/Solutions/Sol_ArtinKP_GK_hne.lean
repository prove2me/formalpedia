-- Prove2me | solution 1 for ArtinKP.GK.hne
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:10:40.426929+00:00
-- url     : https://prove2.me/submissions/8c2b05c1-c60b-4768-a1f3-a63bc70776c2

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
import Theorems.Thm_ArtinKP_C9_ae_eq_htC_of_coeff
import Theorems.Thm_ArtinKP_C9_exists_theta_bigCell_ne_zero
import Theorems.Thm_ArtinKP_GK_tau_eq_rpow_mul_coefF_mul_kir
import Theorems.Thm_ArtinKP_GL_eisEigen_of_two_lt_re
import Theorems.Thm_ArtinKP_N_cf_theta
import Theorems.Thm_ArtinKP_T_coeffFunctional_theta_twist_eq
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

lemma rowDen_nonneg (c d : ℂ) (P : H3) : 0 ≤ rowDen c d P :=
  add_nonneg (Complex.normSq_nonneg _) (mul_nonneg (Complex.normSq_nonneg _) (sq_nonneg _))

end H3

open H3

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

variable {F}

namespace X

lemma ht_pos (P : X F) : 0 < ht P := Finset.prod_pos fun w _ => P.v_pos w

lemma pairHt_eq_prod (c d : F) (P : X F) :
    pairHt c d P = ∏ w, P.v w / H3.rowDen (w.embedding c) (w.embedding d) (P w) := by
  unfold pairHt ht pairDen
  rw [Finset.prod_div_distrib]

lemma pairHt_zero_one (P : X F) : pairHt 0 1 P = ht P := by
  simp [pairHt, pairDen, H3.rowDen]

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
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap _root_.ArtinKP.X.chart1_symm_snd _root_.ArtinKP.X.chart1_v _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
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

/-- The local inequality: `|c d' - c' d|² v² ≤ (|cx+d|² + |c|²v²)(|c'x+d'|² + |c'|²v²)`. -/
lemma H3.normSq_det_mul_sq_le (c d c' d' : ℂ) (P : H3) :
    Complex.normSq (c * d' - c' * d) * P.v ^ 2 ≤ H3.rowDen c d P * H3.rowDen c' d' P := by
  have hv := P.v_pos
  set A := c * P.x + d with hA
  set A' := c' * P.x + d' with hA'
  have hΔ : c * d' - c' * d = c * A' - c' * A := by rw [hA, hA']; ring
  have h1 : ‖c * d' - c' * d‖ ≤ ‖c‖ * ‖A'‖ + ‖c'‖ * ‖A‖ := by
    rw [hΔ]
    calc ‖c * A' - c' * A‖ ≤ ‖c * A'‖ + ‖c' * A‖ := norm_sub_le _ _
      _ = _ := by rw [norm_mul, norm_mul]
  unfold H3.rowDen
  rw [← hA, ← hA']
  simp only [Complex.normSq_eq_norm_sq]
  have h0 := norm_nonneg (c * d' - c' * d)
  have hc := norm_nonneg c
  have hc' := norm_nonneg c'
  have hAn := norm_nonneg A
  have hAn' := norm_nonneg A'
  have h2 : ‖c * d' - c' * d‖ * P.v ≤ ‖c‖ * P.v * ‖A'‖ + ‖c'‖ * P.v * ‖A‖ := by
    nlinarith
  have h3 : (‖c * d' - c' * d‖ * P.v) ^ 2 ≤ (‖c‖ * P.v * ‖A'‖ + ‖c'‖ * P.v * ‖A‖) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2 2
  nlinarith [sq_nonneg (‖c‖ * P.v * (‖c'‖ * P.v) - ‖A‖ * ‖A'‖)]

variable {F : Type*} [Field F] [NumberField F]

namespace X

/-- **Product of two pair heights** (complex-normalized):
`I_{(c,d)}(P) · I_{(c',d')}(P) ≤ 1 / ∏_w |Δ_w|²`, `Δ = c d' - c' d ≠ 0`. -/
theorem pairHt_mul_pairHt_le {c d c' d' : F} (hΔ : c * d' - c' * d ≠ 0) (P : X F) :
    pairHt c d P * pairHt c' d' P ≤
      (∏ w : InfinitePlace F, Complex.normSq (w.embedding (c * d' - c' * d)))⁻¹ := by
  have h1 : c ≠ 0 ∨ d ≠ 0 := by
    by_contra h; push Not at h; exact hΔ (by rw [h.1, h.2]; ring)
  have h2 : c' ≠ 0 ∨ d' ≠ 0 := by
    by_contra h; push Not at h; exact hΔ (by rw [h.1, h.2]; ring)
  rw [pairHt_eq_prod, pairHt_eq_prod, ← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib]
  refine Finset.prod_le_prod (fun w _ => ?_) (fun w _ => ?_)
  · exact mul_nonneg (div_nonneg (P.v_pos w).le (H3.rowDen_nonneg _ _ _))
      (div_nonneg (P.v_pos w).le (H3.rowDen_nonneg _ _ _))
  · have hD := H3.rowDen_pos (c := w.embedding c) (d := w.embedding d) (by simpa using h1) (P w)
    have hD' := H3.rowDen_pos (c := w.embedding c') (d := w.embedding d') (by simpa using h2) (P w)
    have hN : 0 < Complex.normSq (w.embedding (c * d' - c' * d)) :=
      Complex.normSq_pos.mpr ((map_ne_zero _).mpr hΔ)
    have key := H3.normSq_det_mul_sq_le (w.embedding c) (w.embedding d) (w.embedding c')
      (w.embedding d') (P w)
    rw [← map_mul, ← map_mul, ← map_sub] at key
    change (P w).v / _ * ((P w).v / _) ≤ _
    rw [div_mul_div_comm, div_le_iff₀ (mul_pos hD hD'), inv_mul_eq_div, le_div_iff₀ hN]
    nlinarith

end X

end

end ArtinKP.X
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
-- module Solutions.Artin.KP.X2_Chart
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.X.e1_one _root_.ArtinKP.X.e1_two _root_.ArtinKP.X.e1_zero
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

lemma map_exp_withDensity :
    Measure.map Real.exp
        ((volume : Measure ℝ).withDensity fun t => ENNReal.ofReal (Real.exp (-2 * t))) =
      ((volume : Measure ℝ).restrict (Ioi 0)).withDensity fun v => ENNReal.ofReal ((v ^ 3)⁻¹) := by
  ext s hs
  rw [Measure.map_apply Real.measurable_exp hs, withDensity_apply _ (Real.measurable_exp hs),
    withDensity_apply _ hs, Measure.restrict_restrict hs]
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := Real.exp ⁻¹' s) (f := Real.exp)
    (f' := Real.exp) (Real.measurable_exp hs)
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun v => ENNReal.ofReal ((v ^ 3)⁻¹))
  rw [image_preimage_eq_inter_range, Real.range_exp] at h
  rw [h]
  refine setLIntegral_congr_fun (Real.measurable_exp hs) fun t _ => ?_
  rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (Real.exp_pos t), ← Real.exp_nat_mul,
    ← Real.exp_neg, ← Real.exp_add]
  congr 2
  push_cast
  ring

lemma map_coe_chart1 : Measure.map (fun p : E1 => (p.1, Real.exp p.2)) mu1 = amb := by
  have h0 : mu1 = (volume : Measure ℂ).prod
      ((volume : Measure ℝ).withDensity fun t => ENNReal.ofReal (Real.exp (-2 * t))) := by
    rw [prod_withDensity_right (by fun_prop)]
    rfl
  have h2 : (volume : Measure ℂ).prod ((volume : Measure ℝ).restrict (Ioi 0)) =
      (volume : Measure (ℂ × ℝ)).restrict upper := by
    have hu : upper = (univ : Set ℂ) ×ˢ Ioi (0 : ℝ) := by
      ext p; simp [upper]
    rw [hu, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have h3 : (fun p : E1 => (p.1, Real.exp p.2)) = Prod.map id Real.exp := rfl
  rw [h0, h3, ← Measure.map_prod_map _ _ measurable_id Real.measurable_exp, Measure.map_id,
    map_exp_withDensity, prod_withDensity_right (by fun_prop), h2]
  rfl

/-- `H3.vol` is the image of `exp (-2t) dx dt` under the chart. -/
theorem map_chart1 : Measure.map chart1 mu1 = H3.vol := by
  have h := map_coe_chart1
  have hc : (fun p : E1 => (p.1, Real.exp p.2)) = H3.coe ∘ chart1 := rfl
  rw [hc, ← Measure.map_map H3.measurableEmbedding_coe.measurable chart1.continuous.measurable] at h
  unfold H3.vol
  rw [← h, H3.measurableEmbedding_coe.comap_map]

/-! ### The product -/

variable (F : Type*) [Field F] [NumberField F]

variable {F}

lemma rho_pos (y : Coord F) : 0 < rho y := Real.exp_pos _

lemma rho_eq_prod (y : Coord F) : rho y = ∏ w, rho1 (y w) := by
  unfold rho rho1
  rw [Finset.mul_sum, Real.exp_sum]

lemma continuous_rho : Continuous (rho : Coord F → ℝ) := by
  unfold rho; fun_prop

variable (F)

lemma muE_eq_pi : muE F = Measure.pi fun _ : InfinitePlace F => mu1 := by
  unfold mu1
  rw [pi_withDensity _ _ (fun _ => by unfold rho1; fun_prop)]
  unfold muE
  congr 1
  funext y
  rw [rho_eq_prod]
  exact ENNReal.ofReal_prod_of_nonneg fun w _ => (Real.exp_pos (-2 * (y w).2)).le

/-- **The chart carries `exp (-2 ∑ t_w) dy` to the invariant measure.** -/
theorem measurePreserving_chart : MeasurePreserving (chart F) (muE F) (X.vol F) := by
  rw [muE_eq_pi]
  exact measurePreserving_pi (fun _ => mu1) (fun _ => H3.vol)
    (fun _ => ⟨chart1.continuous.measurable, map_chart1⟩)

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

lemma liftQ_smul (u : Lp ℂ 2 (quotMeasure G η μ)) (g : G) (a : α) :
    liftQ u (g • a) = liftQ u a := by
  unfold liftQ; rw [mk_smul]

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

lemma X.lift_smul (Γ : Subgroup (SL(2, 𝓞 F))) (u : X.L2 Γ) (γ : Γ) (P : X F) :
    X.lift Γ u (γ • P) = X.lift Γ u P :=
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  liftQ_smul u γ P

lemma X.stronglyMeasurable_lift (Γ : Subgroup (SL(2, 𝓞 F))) (u : X.L2 Γ) :
    StronglyMeasurable (X.lift Γ u) :=
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  stronglyMeasurable_liftQ u

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
attribute [-instance] _root_.ArtinKP.B1.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatSub _root_.ArtinKP.N.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-- An element of `L²(Γ\X)` whose pull-back vanishes almost everywhere is zero. -/
lemma X.eq_zero_of_lift_ae_eq_zero (v : X.L2 Γ) (h : X.lift Γ v =ᵐ[X.vol F] 0) : v = 0 := by
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have hm : MeasurableSet {q : Quotient (MulAction.orbitRel Γ (X F)) | v q = (0 : ℂ)} :=
    (Lp.stronglyMeasurable v).measurable (measurableSet_singleton 0)
  have key : ∀ᵐ q ∂(Measure.map (Quotient.mk (MulAction.orbitRel Γ (X F)))
      ((X.vol F).withDensity (X.pou Γ))),
      q ∈ {q : Quotient (MulAction.orbitRel Γ (X F)) | v q = (0 : ℂ)} :=
    (ae_map_iff measurable_mk.aemeasurable hm).2
      ((withDensity_absolutelyContinuous _ _).ae_le h)
  exact key

/-! ### Local integrability of pull-backs -/

/-! ### The core -/

/-! ### Density of the core -/

/-! ### The symmetric operator and the energy space -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.N_Orbit
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
-- module Solutions.Artin.KP.RF_Fourier
attribute [-instance] _root_.ArtinKP.B1.instDiscreteTopologySubtypeE₂MemSubmoduleIntPairLattice _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma toMixed_shift [IsTotallyComplex F] {Γ : Subgroup (SL(2, 𝓞 F))} (γ : GammaN Γ) :
    toMixed F (GammaN.shift γ) = GammaN.mixed Γ (Additive.ofMul γ) := by
  have h := toMixed_add_shift (Γ := Γ) (0 : InfinitePlace F → ℂ) γ
  simp only [Pi.zero_apply, zero_add, map_zero, add_zero] at h
  exact h

open Classical in
theorem exists_latBasis [IsTotallyComplex F] (Γ : Subgroup (SL(2, 𝓞 F)))
    (h𝔫 : ∃ 𝔫 : Ideal (𝓞 F), 𝔫 ≠ ⊥ ∧
      ∀ β ∈ 𝔫, ∃ γ : GammaN Γ, ((γ : Γ) : SL(2, 𝓞 F)) 0 1 = β) :
    ∃ (d : ℕ) (bV : Module.Basis (Fin d) ℝ (InfinitePlace F → ℂ)), IsLatBasis Γ bV := by
  have := GammaN.isZLattice h𝔫
  set e : (InfinitePlace F → ℂ) ≃L[ℝ] mixedEmbedding.mixedSpace F :=
    (toMixed F).toContinuousLinearEquiv with he
  set L : Submodule ℤ (InfinitePlace F → ℂ) :=
    ZLattice.comap ℝ (E := mixedEmbedding.mixedSpace F) (GammaN.lattice Γ) e.toLinearMap with hL
  have hmem : ∀ x, x ∈ L ↔ ∃ γ : GammaN Γ, x = GammaN.shift γ := by
    intro x
    have h1 : x ∈ L ↔ toMixed F x ∈ GammaN.lattice Γ := Iff.rfl
    rw [h1, GammaN.mem_lattice]
    constructor
    · rintro ⟨γa, hγ⟩
      refine ⟨Additive.toMul γa, (toMixed F).injective ?_⟩
      rw [toMixed_shift, ofMul_toMul, hγ]
    · rintro ⟨γ, rfl⟩
      exact ⟨Additive.ofMul γ, (toMixed_shift γ).symm⟩
  have : Module.Free ℤ L := ZLattice.module_free ℝ L
  have : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  let b0 := (Module.Free.chooseBasis ℤ L).reindex (Fintype.equivFin _)
  refine ⟨_, b0.ofZLatticeBasis ℝ L, fun x => ?_⟩
  rw [b0.ofZLatticeBasis_span ℝ, hmem]

end

end ArtinKP.RF
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

/-! ### Fubini: a function with vanishing `x`-integrals over `D` is killed by `cf` -/

/-! ### The shape -/

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.N_Level
attribute [-instance] _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma integrableOn_lift (Γ : Subgroup (SL(2, 𝓞 F))) (n : ℕ) (u : X.L2 Γ) :
    IntegrableOn (X.lift Γ u) (X.box n) (X.vol F) :=
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  (memLp_liftQ_restrict (X.isPOU_pou Γ) (X.measurableSet_box n) (ENNReal.natCast_ne_top _)
    (X.tsum_indicator_box_le_boxMult Γ n) u).integrable one_le_two

/-! ### Transport of a box integral by `τ ∈ SL₂(F)` -/

/-! ### `θ` under a transformation of the series -/

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.C9_Const
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
/-!
# WP-C9, part 2: a `Γ`-invariant function with the constant-term shape is zero

Analytic core of (C10′) (MATH3 §5.1), independent of sections and of θ.

* `integral_conj_eChar_eq_zero`: orthogonality of a nonzero character of the dual lattice over a
  strict cell of `Λ_Γ`.
* **`ae_eq_htC_of_coeff`**: let `f` be measurable, `GammaN Γ`-invariant, `L²` on boxes.  If the
  frequency-`0` functionals of `f` are those of `z·ht^{s₁}` and all functionals at nonzero
  frequencies `ν ∈ Λ_Γ^⊥` vanish, then `f = z·ht^{s₁}` a.e.  (This contains WP-RF's optional
  lemma "nonzero frequencies vanish ⇒ independent of `x`", and its Fubini step, in one
  application of `RF.ae_eq_zero_of_strip` to `f − z·ht^{s₁}`.)
* `isOpenPosMeasure_vol`: `X.vol` is positive on nonempty open sets (chart + positive density).
* `lowInt`, `exists_lower_mem`: a finite-index `Γ` contains `[[1,0],[k,1]]`, `k ≠ 0`.
* `not_ae_ht_smul`: `ht(γP) = ht(P)` a.e. is impossible when the lower left entry of `γ` is
  nonzero (`X.pairHt_mul_pairHt_le`: then `ht² ≤ 1/|N(c)|²` everywhere).
* **`eq_zero_of_lift_ae_eq_htC`**: `u ∈ L²(Γ\X)` with `lift u = z·ht^{s₁}` a.e., `Re s₁ ≠ 0`, is `0`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C9

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F]
  {Γ : Subgroup (SL(2, 𝓞 F))}

/-! ### Characters -/

/-! ### Strip integrals as box integrals -/

/-! ### The constant-term shape forces the function -/

/-! ### `X.vol` is positive on open sets -/

theorem isOpenPosMeasure_vol : (X.vol F).IsOpenPosMeasure := by
  refine ⟨fun U hU hne h0 => ?_⟩
  have h1 : muE F (chart F ⁻¹' U) = 0 := by
    rw [(measurePreserving_chart F).measure_preimage hU.nullMeasurableSet]
    exact h0
  have hac : (volume : Measure (Coord F)) ≪ muE F := by
    unfold muE
    refine withDensity_absolutelyContinuous' ?_ ?_
    · exact (ENNReal.measurable_ofReal.comp continuous_rho.measurable).aemeasurable
    · exact Eventually.of_forall fun y => by
        simpa using rho_pos y
  have h2 : (volume : Measure (Coord F)) (chart F ⁻¹' U) = 0 := hac h1
  have hopen : IsOpen (chart F ⁻¹' U) := hU.preimage (chart F).continuous
  have hne' : (chart F ⁻¹' U).Nonempty := by
    obtain ⟨P, hP⟩ := hne
    exact ⟨(chart F).symm P, by simpa using hP⟩
  exact (hopen.measure_pos volume hne').ne' h2

/-! ### Lower unipotent elements -/

lemma lowInt_coe (β : 𝓞 F) : (lowInt β : Matrix (Fin 2) (Fin 2) (𝓞 F)) = !![1, 0; β, 1] := rfl

lemma lowInt_add (β β' : 𝓞 F) : lowInt (β + β') = lowInt β * lowInt β' := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowInt_coe, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

lemma lowInt_zero : lowInt (0 : 𝓞 F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowInt_coe]

lemma lowInt_pow (β : 𝓞 F) (n : ℕ) : lowInt β ^ n = lowInt ((n : 𝓞 F) * β) := by
  induction n with
  | zero => simp [lowInt_zero]
  | succ n ih =>
    rw [pow_succ, ih, ← lowInt_add]
    congr 1
    push_cast
    ring

/-- A finite-index subgroup contains a lower unipotent element with nonzero corner. -/
theorem exists_lower_mem (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex] :
    ∃ γ ∈ Γ, (γ 1 0 : 𝓞 F) ≠ 0 := by
  refine ⟨lowInt 1 ^ (Γ.index).factorial, RC.pow_factorial_index_mem Γ _, ?_⟩
  rw [lowInt_pow, mul_one]
  change (((Γ.index).factorial : ℕ) : 𝓞 F) ≠ 0
  exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)

/-- `ht ∘ γ = ht` a.e. is impossible when the lower left entry of `γ` is nonzero. -/
theorem not_ae_ht_smul (γ : SL(2, 𝓞 F)) (hc : (γ 1 0 : 𝓞 F) ≠ 0) :
    ¬ ∀ᵐ P ∂X.vol F, X.ht (γ • P) = X.ht P := by
  intro h
  have := isOpenPosMeasure_vol (F := F)
  have hcont : Continuous fun P : X F => X.ht (γ • P) :=
    X.continuous_ht.comp (continuous_const_smul γ)
  have hall : (fun P : X F => X.ht (γ • P)) = fun P : X F => X.ht P :=
    (hcont.ae_eq_iff_eq (X.vol F) X.continuous_ht).mp h
  set c : F := algebraMap (𝓞 F) F (γ 1 0) with hcdef
  set d : F := algebraMap (𝓞 F) F (γ 1 1) with hddef
  have hc' : c ≠ 0 := by
    rw [hcdef]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr hc
  have hΔ : (0 : F) * d - c * 1 ≠ 0 := by
    rw [zero_mul, zero_sub, mul_one]
    exact neg_ne_zero.mpr hc'
  set B : ℝ := (∏ w : InfinitePlace F, Complex.normSq (w.embedding ((0 : F) * d - c * 1)))⁻¹
    with hB
  have hbound : ∀ P : X F, X.ht P * X.ht P ≤ B := by
    intro P
    have h1 := X.pairHt_mul_pairHt_le hΔ P
    have h2 : X.ht (γ • P) = X.pairHt c d P := by
      rw [intSL_smul, X.ht_smul]
      rfl
    have h3 : X.ht (γ • P) = X.ht P := congrFun hall P
    rw [X.pairHt_zero_one, ← h2, h3] at h1
    exact h1
  set t : ℝ := max 1 (B + 1) with ht
  have ht1 : 1 ≤ t := le_max_left _ _
  have htpos : ∀ w : InfinitePlace F, 0 < (fun _ : InfinitePlace F => t) w :=
    fun _ => lt_of_lt_of_le one_pos ht1
  have hP := hbound (X.mk 0 (fun _ => t) htpos)
  rw [ht_mk, Finset.prod_const] at hP
  have hcard : (Finset.univ : Finset (InfinitePlace F)).card ≠ 0 :=
    Finset.card_ne_zero.mpr Finset.univ_nonempty
  have h4 : t ≤ t ^ (Finset.univ : Finset (InfinitePlace F)).card := le_self_pow₀ ht1 hcard
  have h5 : t * 1 ≤ t ^ (Finset.univ : Finset (InfinitePlace F)).card
      * t ^ (Finset.univ : Finset (InfinitePlace F)).card :=
    mul_le_mul h4 (ht1.trans h4) zero_le_one (le_trans (by positivity) h4)
  have h6 : B + 1 ≤ t := le_max_right _ _
  linarith

/-! ### Step (iii) -/

/-- **`z·ht^{s₁}` is not `Γ`-invariant.**  If `u ∈ L²(Γ\X)` has `lift u = z·ht^{s₁}` a.e. with
`Re s₁ ≠ 0`, then `u = 0`. -/
theorem eq_zero_of_lift_ae_eq_htC (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex] (u : X.L2 Γ)
    (z : ℂ) {s₁ : ℂ} (hs₁ : s₁.re ≠ 0)
    (h : X.lift Γ u =ᵐ[X.vol F] fun P => z * htC s₁ P) : u = 0 := by
  apply X.eq_zero_of_lift_ae_eq_zero
  by_cases hz : z = 0
  · filter_upwards [h] with P hP
    rw [hP, hz, zero_mul]
    rfl
  exfalso
  obtain ⟨γ, hγ, hc⟩ := exists_lower_mem Γ
  refine not_ae_ht_smul γ hc ?_
  have hγae : ∀ᵐ P ∂X.vol F, X.lift Γ u (γ • P) = z * htC s₁ (γ • P) :=
    (X.measurePreserving_smul (intSL F γ)).quasiMeasurePreserving.ae h
  filter_upwards [h, hγae] with P hP hγP
  have hinv : X.lift Γ u (γ • P) = X.lift Γ u P := X.lift_smul Γ u ⟨γ, hγ⟩ P
  rw [hγP, hP] at hinv
  have h1 : htC s₁ (γ • P) = htC s₁ P := mul_left_cancel₀ hz hinv
  have h2 := congrArg norm h1
  unfold htC at h2
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (X.ht_pos _),
    Complex.norm_cpow_eq_rpow_re_of_pos (X.ht_pos _)] at h2
  exact Real.rpow_left_injOn hs₁ (X.ht_pos _).le (X.ht_pos _).le h2

end

end ArtinKP.C9
end

section
-- module Solutions.Artin.KP.C9_Main
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
/-!
# WP-C9, part 3: (C10′) in terms of coefficient functionals; a single big cell with `θ ≠ 0`

* **`eq_zero_of_coeff_shape`**: `u ∈ L²(Γ\X)` whose frequency-`0` functionals are those of
  `z·ht^{s₁}` (`Re s₁ ≠ 0`) and whose functionals at all nonzero frequencies of `Λ_Γ^⊥` vanish
  is `0`.
* **`theta_eq_zero_of_coeff`** — (C10′), the core: if all nonzero-frequency coefficient
  functionals of `θ_Ψ` at `∞` vanish, then `θ_Ψ = 0` (and `zRes_eq_zero_of_coeff`: `z_Ψ = 0`).
  Stated for a twisted section `Ψ` and WP-RF's functionals; no dependence on WP-T.
* `lift_zero_ae`, `theta_eq_zero_congr`: `θ_Ψ = 0` does not depend on the group `Γ`.
* `twist_add`, `twist_zero`, `exists_inv_finset`, `theta_sum_eq_zero`: linearity bookkeeping.
* **`exists_theta_bigCell_ne_zero`**: some single big-cell section `Φ^big_η`, `η ∈ T`, has
  `θ ≠ 0` (for every finite-index `Γ` fixing its twist).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C9

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

/-! ### (C10′), the core -/

/-- **An `L²` class with the constant-term shape and no other frequency is zero.** -/
theorem eq_zero_of_coeff_shape (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    {D : Set (InfinitePlace F → ℂ)} (hD : MeasurableSet D)
    (hfund : ∀ x : InfinitePlace F → ℂ, ∃! γ : GammaN Γ, (fun w => x w + GammaN.shift γ w) ∈ D)
    {n₀ : ℕ} (hn₀ : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n₀) (u : X.L2 Γ) (z : ℂ) {s₁ : ℂ} (hs₁ : s₁.re ≠ 0)
    (h0 : ∀ n : ℕ, n₀ ≤ n → ∀ φ : (InfinitePlace F → ℝ) → ℂ, Measurable φ → (∀ v, ‖φ v‖ ≤ 1) →
      cf D n φ (X.lift Γ u) = z * cf D n φ (htC s₁))
    (h : ∀ ν ∈ dualLat Γ, ν ≠ 0 → ∀ n : ℕ, n₀ ≤ n → ∀ (φ : (InfinitePlace F → ℝ) → ℂ)
      (hφ : Measurable φ) (hφ1 : ∀ v, ‖φ v‖ ≤ 1),
      X.coeffFunctional Γ n (stripFn D ν φ) (measurable_stripFn hD ν hφ) 1
        (norm_stripFn_le D ν hφ1) u = 0) :
    u = 0 := by
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  refine eq_zero_of_lift_ae_eq_htC Γ u z hs₁ ?_
  refine ae_eq_htC_of_coeff Γ (exists_ideal_translations Γ) hD hfund n₀ hn₀ (X.lift Γ u)
    (X.stronglyMeasurable_lift Γ u).measurable (fun γ P => X.lift_smul Γ u (γ : Γ) P)
    (fun n => memLp_liftQ_restrict (X.isPOU_pou Γ) (X.measurableSet_box n)
      (ENNReal.natCast_ne_top _) (X.tsum_indicator_box_le_boxMult Γ n) u)
    (fun n => integrableOn_lift Γ n u) z s₁ h0 ?_
  intro ν hν hν0 n hn φ hφ hφ1
  rw [← X.coeffFunctional_apply Γ n (stripFn D ν φ) (measurable_stripFn hD ν hφ) 1
    (norm_stripFn_le D ν hφ1) u]
  exact h ν hν hν0 n hn φ hφ hφ1

/-- **(C10′), core form.**  Let `Ψ` be a twisted section fixed by the finite-index group `Γ`,
`D` a bounded measurable strict cell of the translations of `Γ`.  If all coefficient functionals
of `θ_Ψ` at the nonzero frequencies `ν ∈ Λ_Γ^⊥` vanish, then `θ_Ψ = 0`. -/
theorem theta_eq_zero_of_coeff (hG : Good 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) {D : Set (InfinitePlace F → ℂ)} (hD : MeasurableSet D)
    (hfund : ∀ x : InfinitePlace F → ℂ, ∃! γ : GammaN Γ, (fun w => x w + GammaN.shift γ w) ∈ D)
    {n₀ : ℕ} (hn₀ : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n₀)
    (h : ∀ ν ∈ dualLat Γ, ν ≠ 0 → ∀ n : ℕ, n₀ ≤ n → ∀ (φ : (InfinitePlace F → ℝ) → ℂ)
      (hφ : Measurable φ) (hφ1 : ∀ v, ‖φ v‖ ≤ 1),
      X.coeffFunctional Γ n (stripFn D ν φ) (measurable_stripFn hD ν hφ) 1
        (norm_stripFn_le D ν hφ1) (theta Γ Ψ) = 0) :
    theta Γ Ψ = 0 := by
  have hcell : Cell Γ D n₀ := Cell.of_hfund hD hfund hn₀
  have hE : ∀ s : ℂ, 2 < s.re → EisEigen Ψ s := fun s hs => GL.eisEigen_of_two_lt_re hG.ne_bot Ψ hs
  refine eq_zero_of_coeff_shape Γ hD hfund hn₀ (theta Γ Ψ) (zRes Γ Ψ D (n₀ + 1))
    (s₁ := 2 / 3) (by norm_num) ?_ h
  intro n hn φ hφ hφ1
  exact cf_theta hG hΓ hE (hcell.mono (Nat.le_succ n₀)) (Nat.succ_le_succ (Nat.zero_le n₀))
    (hcell.mono hn) hφ hφ1

/-! ### Independence of `Γ` -/

/-! ### Linearity bookkeeping -/

/-! ### A single big cell -/

end

end ArtinKP.C9
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

/-! ### The coefficient function of the continuation -/

/-! ### The archimedean factor -/

/-! ### The coefficient of the series over an admissible cell -/

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
-- module Solutions.Artin.KP.C9_Tau
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.G1.scal_apply
/-!
# WP-C9, part 4: (C10′) and (C9) in the vocabulary of WP-T (`T.tau`, `T.theta`)

WP-T's `T.coeff_theta` computes the coefficient functional of `θ_{Φ.twist}` at the frequency
`T.freq ν`, `ν ∈ R ∖ 0` (`R = SInt 𝔪`), as `kap · τ_Φ(ν) · Wc`.  The core lemma
`C9.theta_eq_zero_of_coeff` needs the vanishing at **every** nonzero frequency of WP-RF's dual
lattice `RF.dualLat Γ`.  The bridge is the one named hypothesis of this file:

* `DualCover 𝔪 Γ`: every nonzero `ν' ∈ RF.dualLat Γ` is `T.freq ν` for some `ν ∈ R`.
  (True when `Λ_Γ ⊇ emb(𝔪^N)` — `TransLevel 𝔪 Γ` — and the different of `F` is supported in the
  primes of `𝔪`: trace duality.  Proved in `C9_Dual.lean` / stated in `C9_Stubs.lean`, see
  WP-C9.md.)

Results:

* `stabGroup Ψ` (the full stabilizer of `Ψ` in `SL₂(𝓞)`), finite index, `TransLevel` for twists.
* **`theta_eq_zero_of_tau`** — (C10′) in WP-T's form: `τ_Φ(ν) = 0` for all `ν ∈ R ∖ 0` implies
  `θ_{Φ.twist} = 0`.
* **`exists_tau_sumBig_ne_zero`**, **`exists_tau_bigCell_ne_zero`** — the hypothesis of package
  G (MATH3 §1.2 (G1)): some `τ_{Φ^Σ}(ν₁) ≠ 0`, and some single class `η` with
  `τ_{Φ^big_η}(ν) ≠ 0`.
* `exists_kir_ne_zero_of_theoremE`: given Theorem E in any form `τ_Φ(ν) = c(ν)·𝒦_Φ(ν)`, the
  Kirillov function is not identically zero.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C9

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

/-! ### The full stabilizer -/

theorem inv_stabGroup (Ψ : TSection ι 𝔪) : Inv (stabGroup Ψ) Ψ := fun _ hγ => hγ

theorem le_stabGroup {Γ : Subgroup (SL(2, 𝓞 F))} {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) :
    Γ ≤ stabGroup Ψ := fun γ hγ => hΓ γ hγ

theorem stabGroup_finiteIndex (Pk : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F}
    (hz6 : IsPrimitiveRoot z6 6) (Ψ : TSection ι 𝔪) : (stabGroup Ψ).FiniteIndex := by
  obtain ⟨Γ, hfi, hΓ⟩ := exists_finiteIndex_inv Pk hG hz6 Ψ
  exact Subgroup.finiteIndex_of_le (le_stabGroup hΓ)

section twist

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-- The level of a twist is a power of `𝔪` (the `level` field of `GSection.twist`, with its
ideal made explicit). -/
theorem exists_twist_level (Φ : GSection ι P 𝔪) :
    ∃ N : ℕ, ∀ γ ∈ Gamma 𝔪 (𝔪 ^ N), ∀ (s : ℂ) (p : Row 𝔪),
      Φ.twist hG hz6 s (p.act γ) = kappa ι 𝔪 γ * Φ.twist hG hz6 s p := by
  obtain ⟨N, hN⟩ := Φ.level
  refine ⟨N, fun γ hγ s p => ?_⟩
  have hK := isK_of_mem_Gamma hγ
  have hc : (((p.act γ).c : SInt 𝔪) : F) = (p.c : F) * ((γ.1 0 0 : SInt 𝔪) : F)
      + (p.d : F) * ((γ.1 1 0 : SInt 𝔪) : F) := by
    rw [Row.act_c]; push_cast; rfl
  have hd : (((p.act γ).d : SInt 𝔪) : F) = (p.c : F) * ((γ.1 0 1 : SInt 𝔪) : F)
      + (p.d : F) * ((γ.1 1 1 : SInt 𝔪) : F) := by
    rw [Row.act_d]; push_cast; rfl
  rw [GSection.twist_apply, GSection.twist_apply, hc, hd, hN _ _ _ _ hK,
    kappaRow_act ι P hG hz6]
  have h0 : sig ι P 𝔪 (p.c : F) (p.d : F) ((γ.1 0 0 : SInt 𝔪) : F) ((γ.1 0 1 : SInt 𝔪) : F)
      ((γ.1 1 0 : SInt 𝔪) : F) ((γ.1 1 1 : SInt 𝔪) : F) ≠ 0 := brk_ne_zero _ _
  field_simp

/-- The stabilizer of a twist contains the translations by `𝔪^N`. -/
theorem transLevel_stabGroup (Φ : GSection ι P 𝔪) :
    TransLevel 𝔪 (stabGroup (Φ.twist hG hz6)) := by
  obtain ⟨N, hN⟩ := exists_twist_level hG hz6 Φ
  refine ⟨N, fun β hβ => ?_⟩
  change RO.intMat 𝔪 (nInt β) ∈ (Φ.twist hG hz6).stab
  rw [TSection.mem_stab]
  intro s p
  have hmem : RO.intMat 𝔪 (nInt β) ∈ Gamma 𝔪 (𝔪 ^ N) := by
    rw [mem_Gamma_iff]
    refine ⟨nInt β, fun i j => ?_, rfl⟩
    fin_cases i <;> fin_cases j <;> simp [nInt_coe, hβ]
  have hk : kappa ι 𝔪 (RO.intMat 𝔪 (nInt β)) = 1 := by
    have h10 : (RO.intMat 𝔪 (nInt β)).1 1 0 = 0 := by
      change algebraMap (𝓞 F) (SInt 𝔪) ((nInt β).1 1 0) = 0
      simp [nInt_coe]
    simp [kappa, h10]
  rw [hN _ hmem, hk, one_mul]

end twist

/-! ### The bridge between the two parametrizations of the frequencies -/

lemma freq_zero : T.freq (0 : F) = 0 := by
  funext w
  simp [T.freq]

/-! ### (C10′) in WP-T's form -/

section tau

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-- **(C10′), WP-T's form.**  If `τ_Φ(ν) = 0` for every `ν ∈ R ∖ 0`, then `θ_{Φ.twist} = 0`
(for every finite-index `Γ` fixing the twist whose dual lattice is covered by `R`). -/
theorem theta_eq_zero_of_forall_tau_eq_zero (Φ : GSection ι P 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    (hΓ : Inv Γ (Φ.twist hG hz6)) (hdual : DualCover 𝔪 Γ)
    (h : ∀ ν : SInt 𝔪, ν ≠ 0 → T.tau hG hz6 Φ ν = 0) :
    C5.theta Γ (Φ.twist hG hz6) = 0 := by
  obtain ⟨D, hD, hbdd, hfund⟩ := exists_fundamental_translations Γ (exists_ideal_translations Γ)
  obtain ⟨R, hR⟩ := hbdd.exists_norm_le
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge R
  have hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ (n₀ : ℝ) := fun x hx w =>
    (norm_le_pi_norm x w).trans ((hR x hx).trans hn₀)
  refine theta_eq_zero_of_coeff hG Γ hΓ hD hfund hb ?_
  intro ν' hν' hν'0 n hn φ hφ hφ1
  obtain ⟨ν, rfl⟩ := hdual ν' hν' hν'0
  have hν : ν ≠ 0 := by
    rintro rfl
    exact hν'0 freq_zero
  obtain ⟨M, hM, hV⟩ := T.exists_validDepth_nonneg hG Φ ((ν : SInt 𝔪) : F)
  have hbn : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ (n : ℝ) := fun x hx w =>
    (hb x hx w).trans (by exact_mod_cast hn)
  rw [T.coeffFunctional_theta_twist_eq hG hz6 Φ hν hM hV Γ hΓ hD hfund hbn (T.chiInf_of_mem_dualLat hν') hφ hφ1,
    h ν hν, mul_zero, zero_mul]

/-- Contrapositive: `θ ≠ 0` gives a nonzero residue `τ_Φ(ν)`, `ν ∈ R ∖ 0`. -/
theorem exists_tau_ne_zero_of_theta_ne_zero (Φ : GSection ι P 𝔪) (Γ : Subgroup (SL(2, 𝓞 F)))
    [Γ.FiniteIndex] (hΓ : Inv Γ (Φ.twist hG hz6)) (hdual : DualCover 𝔪 Γ)
    (h : C5.theta Γ (Φ.twist hG hz6) ≠ 0) :
    ∃ ν : SInt 𝔪, ν ≠ 0 ∧ T.tau hG hz6 Φ ν ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact h (theta_eq_zero_of_forall_tau_eq_zero hG hz6 Φ Γ hΓ hdual hcon)

/-- The same on the full stabilizer, where `TransLevel` holds. -/
theorem exists_tau_ne_zero_of_theta' (Φ : GSection ι P 𝔪)
    (hdual : ∀ Γ : Subgroup (SL(2, 𝓞 F)), Γ.FiniteIndex → TransLevel 𝔪 Γ → DualCover 𝔪 Γ)
    (h : ∀ (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex], Inv Γ (Φ.twist hG hz6) →
      C5.theta Γ (Φ.twist hG hz6) ≠ 0) :
    ∃ ν : SInt 𝔪, ν ≠ 0 ∧ T.tau hG hz6 Φ ν ≠ 0 := by
  have hfi := stabGroup_finiteIndex P hG hz6 (Φ.twist hG hz6)
  exact exists_tau_ne_zero_of_theta_ne_zero hG hz6 Φ (stabGroup (Φ.twist hG hz6))
    (inv_stabGroup _) (hdual _ hfi (transLevel_stabGroup hG hz6 Φ))
    (h _ (inv_stabGroup _))

end tau

/-! ### The hypothesis of package G -/

section G

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  {N : ℕ} (hN1 : 1 ≤ N) (hN : P.IsDeepLevel 𝔪 N) (M : ℤ) (Tc : Finset {η : F // η ≠ 0})
  (hdisj : ∀ η ∈ Tc, ∀ η' ∈ Tc, η ≠ η' → ∀ c : F, InClass 𝔪 N η.1 c → ¬ InClass 𝔪 N η'.1 c)
  (hcov : ∀ c : F, c ≠ 0 → ∃ η ∈ Tc, InClass 𝔪 N η.1 c)

include hdisj hcov in
/-- **(C9) + (C10′) for a single class**: there are a class `η ∈ T` and a frequency
`ν ∈ R ∖ 0` with `τ_{Φ^big_η}(ν) ≠ 0`. -/
theorem exists_tau_bigCell_ne_zero (hM : 0 ≤ M)
    (hdual : ∀ Γ : Subgroup (SL(2, 𝓞 F)), Γ.FiniteIndex → TransLevel 𝔪 Γ → DualCover 𝔪 Γ) :
    ∃ η ∈ Tc, ∃ ν : SInt 𝔪, ν ≠ 0 ∧
      T.tau hG hz6 (bigCell ι P hG hN1 hN η.1 η.2 M 0) ν ≠ 0 := by
  obtain ⟨η, hη, hne⟩ := exists_theta_bigCell_ne_zero hG hz6 hN1 hN M Tc hdisj hcov hM
  exact ⟨η, hη, exists_tau_ne_zero_of_theta' hG hz6 _ hdual fun Γ _ hΓ => hne Γ hΓ⟩

end G

end

end ArtinKP.C9
end

section
-- module Solutions.Artin.KP.RF_Parseval
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-RF, part 9: Parseval along `x` in the form of WP-X stub S1 (a)

For `g : (ι → ℂ) → ℂ` measurable, periodic under the translation lattice `Λ` of `Γ` and square
integrable on a strict fundamental set `D` of `Λ`:

`∑_{ν ∈ Λ^⊥} |∫_D conj(e_ν) g|² = vol(D) · ∫_D |g|²`   (`parseval_strip`).

The sum is over the subtype `dualLat Γ`; `dualEquiv` identifies it with `ℤ^J` for a lattice basis
(`nuOf bV m` is the frequency with `e_ν = chi bV m`).
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

lemma pairLin_apply (ν x : InfinitePlace F → ℂ) : pairLin ν x = pair ν x := rfl

lemma pair_sub_left (ν ν' x : InfinitePlace F → ℂ) :
    pair (ν - ν') x = pair ν x - pair ν' x := by
  simp [pair, sub_mul, Finset.sum_sub_distrib]

lemma pair_single [DecidableEq (InfinitePlace F)] (μ : InfinitePlace F → ℂ)
    (w : InfinitePlace F) (z : ℂ) : pair μ (Pi.single w z) = (μ w * z).re := by
  rw [pair, Finset.sum_eq_single w]
  · rw [Pi.single_eq_same]
  · intro w' _ hne
    rw [Pi.single_eq_of_ne hne, mul_zero, Complex.zero_re]
  · intro h; exact absurd (Finset.mem_univ w) h

/-- The pairing is nondegenerate. -/
lemma eq_of_pair_eq {ν ν' : InfinitePlace F → ℂ} (h : ∀ x, pair ν x = pair ν' x) : ν = ν' := by
  classical
  funext w
  have h0 := pair_sub_left ν ν' (Pi.single w (conj ((ν - ν') w)))
  rw [h, sub_self, pair_single, Complex.mul_conj, Complex.ofReal_re] at h0
  have h1 : (ν - ν') w = 0 := Complex.normSq_eq_zero.mp h0
  exact sub_eq_zero.mp h1

end

end ArtinKP.RF
end

section
-- module Solutions.Artin.KP.C9_Dual
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-- **Trace duality.**  If the translations of `Γ` contain `emb(𝔪^N)` and the different is
supported in the primes of `𝔪`, every frequency of `RF.dualLat Γ` is `T.freq ν` with
`ν ∈ R = SInt 𝔪`. -/
theorem dualCover_of_transLevel (h𝔪 : 𝔪 ≠ ⊥)
    (hdiff : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ placesOf 𝔪 →
      ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal)
    (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex] (hΓ : TransLevel 𝔪 Γ) : DualCover 𝔪 Γ := by
  classical
  obtain ⟨N, hN⟩ := hΓ
  intro ν' hν' _
  have hint : ∀ β : 𝓞 F, β ∈ lamN Γ → ∃ m : ℤ, pair ν' (emb (β : F)) = m := by
    intro β hβ
    have h := hν' (ofLam ⟨β, hβ⟩)
    rw [shift_ofLam] at h
    exact h
  -- the `ℚ`-linear functional `x ↦ pair ν' (emb x)`
  let pA : (InfinitePlace F → ℂ) →+ ℝ := AddMonoidHom.mk' (pair ν') (RF.pair_add ν')
  let L : F →ₗ[ℚ] ℝ := (pA.comp (emb (F := F))).toRatLinearMap
  have hL : ∀ x : F, L x = pair ν' (emb x) := fun x => rfl
  -- an integer in `𝔪^N`
  set I : Ideal (𝓞 F) := 𝔪 ^ N with hIdef
  have hI : I ≠ ⊥ := pow_ne_zero N h𝔪
  set c : ℕ := Ideal.absNorm I with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef, Ne, Ideal.absNorm_eq_zero_iff]
    exact hI
  have hcI : ((c : ℕ) : 𝓞 F) ∈ I := Ideal.absNorm_mem I
  -- a `ℚ`-basis of `F` inside `𝔪^N`
  have hu : ∀ _ : Module.Free.ChooseBasisIndex ℤ (𝓞 F), IsUnit ((c : ℚ)) := fun _ =>
    (Nat.cast_ne_zero.mpr hc0 : (c : ℚ) ≠ 0).isUnit
  let b := (integralBasis F).isUnitSMul hu
  have hb : ∀ i, b i = algebraMap (𝓞 F) F (((c : ℕ) : 𝓞 F) * RingOfIntegers.basis F i) := by
    intro i
    change (integralBasis F).isUnitSMul hu i = _
    rw [Module.Basis.isUnitSMul_apply, integralBasis_apply, map_mul, map_natCast]
    rw [Rat.smul_def]
    simp
  have hbm : ∀ i, ∃ m : ℤ, L (b i) = m := fun i => by
    rw [hL, hb]
    exact hint _ (hN _ (I.mul_mem_right _ hcI))
  choose m hm using hbm
  -- the element `μ` with `Tr(μ b_j) = m_j`
  let d := (Algebra.traceForm ℚ F).dualBasis (traceForm_nondegenerate ℚ F) b
  set μ : F := ∑ i, (m i : ℚ) • d i with hμ
  have hμb : ∀ j, Algebra.trace ℚ F (μ * b j) = m j := by
    intro j
    have h1 : ∀ i, Algebra.trace ℚ F (d i * b j) = if j = i then 1 else 0 := fun i =>
      (Algebra.traceForm ℚ F).apply_dualBasis_left (traceForm_nondegenerate ℚ F) b i j
    rw [hμ, Finset.sum_mul, map_sum]
    simp only [smul_mul_assoc, map_smul, h1, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  let L' : F →ₗ[ℚ] ℝ := (Algebra.linearMap ℚ ℝ).comp ((Algebra.traceForm ℚ F) μ)
  have hL' : ∀ x : F, L' x = ((Algebra.trace ℚ F (μ * x) : ℚ) : ℝ) := fun x => rfl
  have hLL : L = L' := b.ext fun j => by
    rw [hm, hL', hμb]
    push_cast
    rfl
  have hpair : ∀ x : F, pair ν' (emb x) = pair (T.freq (-μ)) (emb x) := fun x => by
    rw [pair_freq_emb, ← hL', ← hLL, hL]
  -- `emb(F)` spans
  obtain ⟨dd, bV, hbV⟩ := exists_latBasis Γ (exists_ideal_translations Γ)
  have heq : ν' = T.freq (-μ) := by
    apply eq_of_pair_eq
    have hlin : pairLin ν' = pairLin (T.freq (-μ)) := bV.ext fun j => by
      obtain ⟨γ, hγ⟩ := (hbV (bV j)).mp (Submodule.subset_span (Set.mem_range_self j))
      rw [pairLin_apply, pairLin_apply, hγ]
      exact hpair ((((γ : Γ) : SL(2, 𝓞 F)) 0 1 : 𝓞 F) : F)
    intro x
    exact LinearMap.congr_fun hlin x
  -- integrality of the trace on `𝔪^N`
  have htr : ∀ β ∈ I, ∃ k : ℤ, Algebra.trace ℚ F (μ * (β : F)) = k := by
    intro β hβ
    obtain ⟨k, hk⟩ := hint β (hN β hβ)
    refine ⟨k, ?_⟩
    have h1 : ((Algebra.trace ℚ F (μ * (β : F)) : ℚ) : ℝ) = (k : ℝ) := by
      rw [← hL', ← hLL, hL, hk]
    exact_mod_cast h1
  have hμS : -μ ∈ (placesOf 𝔪).integer F := by
    intro v hv
    rw [Valuation.map_neg]
    have hvI : ¬ I ≤ v.asIdeal := fun hle => hv (v.isPrime.le_of_pow_le hle)
    obtain ⟨c₁, hc₁, hc₁v⟩ := SetLike.not_le_iff_exists.mp hvI
    obtain ⟨p, hp, hpv⟩ := SetLike.not_le_iff_exists.mp (hdiff v hv)
    have hone : (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := one_ne_zero
    have hdual : μ * algebraMap (𝓞 F) F c₁
        ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
      rw [FractionalIdeal.mem_dual hone]
      intro a ha
      obtain ⟨a', rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      obtain ⟨k, hk⟩ := htr (c₁ * a') (I.mul_mem_right _ hc₁)
      refine ⟨k, ?_⟩
      rw [Algebra.traceForm_apply]
      have e : μ * algebraMap (𝓞 F) F c₁ * algebraMap (𝓞 F) F a'
          = μ * ((c₁ * a' : 𝓞 F) : F) := by
        rw [mul_assoc, ← map_mul]
      rw [e, hk]
      simp
    have hp' : algebraMap (𝓞 F) F p ∈
        ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) :=
      (FractionalIdeal.mem_coeIdeal _).2 ⟨p, hp, rfl⟩
    rw [coeIdeal_differentIdeal ℤ ℚ] at hp'
    have h1 := FractionalIdeal.mul_mem_mul hdual hp'
    rw [mul_inv_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ hone)] at h1
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    have hv1 : v.valuation F (algebraMap (𝓞 F) F c₁) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hc₁v
    have hv2 : v.valuation F (algebraMap (𝓞 F) F p) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hpv
    have h2 := v.valuation_le_one (K := F) a
    change v.valuation F (algebraMap (𝓞 F) F a) ≤ 1 at h2
    rw [ha, map_mul, map_mul, hv1, hv2, mul_one, mul_one] at h2
    exact h2
  exact ⟨⟨-μ, hμS⟩, heq.symm⟩

/-! ### The statements for package G, with `hdiff` -/

section G

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  {N : ℕ} (hN1 : 1 ≤ N) (hN : P.IsDeepLevel 𝔪 N) (M : ℤ) (Tc : Finset {η : F // η ≠ 0})
  (hdisj : ∀ η ∈ Tc, ∀ η' ∈ Tc, η ≠ η' → ∀ c : F, InClass 𝔪 N η.1 c → ¬ InClass 𝔪 N η'.1 c)
  (hcov : ∀ c : F, c ≠ 0 → ∃ η ∈ Tc, InClass 𝔪 N η.1 c)
  (hdiff : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ placesOf 𝔪 →
    ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal)

include hdisj hcov hdiff in
/-- **A class and a frequency with nonzero residue**: `τ_{Φ^big_η}(ν) ≠ 0`. -/
theorem exists_tau_bigCell_ne_zero' (hM : 0 ≤ M) :
    ∃ η ∈ Tc, ∃ ν : SInt 𝔪, ν ≠ 0 ∧
      T.tau hG hz6 (bigCell ι P hG hN1 hN η.1 η.2 M 0) ν ≠ 0 :=
  exists_tau_bigCell_ne_zero hG hz6 hN1 hN M Tc hdisj hcov hM
    fun Γ hfi hΓ => @dualCover_of_transLevel _ _ _ _ _ hG.ne_bot hdiff Γ hfi hΓ

end G

end

end ArtinKP.C9
end

section
-- module Solutions.Artin.KP.RO_Classes
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-RO, file 5: finiteness of the class set `𝒞 = F^× / U_S (F^×)³ U_N` (WP-S open issue 6)

Everything is `F : Type*`; no completion, no Hilbert symbol and none of the `F : Type` stubs is used:
already `F^× / U_S U_N` is finite, `U_N = {u : Small 𝔪 N (u - 1)}`.

* `exists_bdd_rescale`: there is `K` such that every `c ≠ 0` has an `S`-unit multiple `c' ∈ 𝓞` with
  `v(c') > exp(-K)` at all `v ∣ 𝔪` (from `B1.exists_unit_rescale`).
* `small_div_sub_one`: two such integers congruent modulo `𝔪^(K+N)` have quotient in `U_N`.
* `exists_finite_cover`: a finite `T ⊂ F^×` with `F^× = ⋃_{η ∈ T} η U_S U_N` (any `N`, `𝔪 ≠ ⊥`).
* `InClass.refl'`, `InClass.symm'`, `InClass.trans'`: `S.InClass 𝔪 N` is an equivalence relation on
  `F^×` for `N ≥ 1`.
* **`exists_classReps`**: for `Good 𝔪`, `N ≥ 1`, a finite complete set of pairwise disjoint classes,
  in exactly the form `S.sum_bigCell_apply` takes (`hdisj`).
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

theorem exists_bdd_rescale (h𝔪 : 𝔪 ≠ ⊥) : ∃ K : ℕ, ∀ a : 𝓞 F, a ≠ 0 →
    ∃ (ε : (SInt 𝔪)ˣ) (c' : 𝓞 F), (c' : F) = ((ε : SInt 𝔪) : F) * (a : F) ∧ Bdd 𝔪 K c' := by
  classical
  obtain ⟨δ, hδ, hres⟩ := exists_unit_rescale (SOf 𝔪)
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨K, fun a ha => ?_⟩
  have haF : (a : F) ≠ 0 := by simpa using ha
  obtain ⟨u, hu0, huS, ⟨c', -, hc', -⟩, hle⟩ := hres (a : F) 0 (Or.inl haF)
    (fun v hv => isSInt_int (S := SOf 𝔪) a v hv) (fun v _ => by simp)
  obtain ⟨ε, hε⟩ := exists_unit_of_isSUnit h𝔪 (u := u) ⟨hu0, huS⟩
  have hc'F : (c' : F) ≠ 0 := by rw [hc']; exact mul_ne_zero hu0 haF
  refine ⟨ε, c', by rw [hε, hc'], fun h0 => hc'F (by rw [h0]; simp), fun v hv => ?_⟩
  by_contra hcon
  rw [not_lt] at hcon
  have h1 := abv_le_of_val_le v hcon
  rw [sNorm_SOf, ← hc'] at hle
  have hvS : v ∈ CubicPkg.sFin 𝔪 := (CubicPkg.mem_sFin h𝔪 v).mpr hv
  set f : HeightOneSpectrum (𝓞 F) → ℝ := fun w =>
    max (NumberField.HeightOneSpectrum.adicAbv F w (c' : F))
      (NumberField.HeightOneSpectrum.adicAbv F w (u * 0)) with hf
  have hf0 : ∀ w, 0 ≤ f w := fun w => le_max_of_le_left ((NumberField.HeightOneSpectrum.adicAbv F w).nonneg _)
  have hf1 : ∀ w, f w ≤ 1 := fun w => by
    have h2 : NumberField.HeightOneSpectrum.adicAbv F w (c' : F) ≤ 1 := by
      have := abv_le_of_val_le w (x := (c' : F)) (n := 0) (by simpa using w.valuation_le_one c')
      simpa using this
    simp only [hf, mul_zero, map_zero]
    exact max_le h2 zero_le_one
  have hfv : f v = NumberField.HeightOneSpectrum.adicAbv F v (c' : F) := by
    simp only [hf, mul_zero, map_zero]
    exact max_eq_left ((NumberField.HeightOneSpectrum.adicAbv F v).nonneg _)
  have h3 : normS 𝔪 (c' : F) (u * 0) ≤ f v := by
    unfold normS
    rw [← Finset.mul_prod_erase _ _ hvS]
    exact mul_le_of_le_one_right (hf0 v) (Finset.prod_le_one (fun w _ => hf0 w) fun w _ => hf1 w)
  have hq : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
    have h' : 1 < Ideal.absNorm v.asIdeal := by exact_mod_cast this
    exact_mod_cast h'
  have h4 : (Ideal.absNorm v.asIdeal : ℝ) ^ (-(K : ℤ)) ≤ (1 / 2 : ℝ) ^ K := by
    rw [zpow_neg, zpow_natCast, one_div, inv_pow]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) hq K)
  linarith [hfv ▸ h3]

/-- Two bounded integers congruent modulo `𝔪^(K+N)` have quotient in `U_N`. -/
theorem small_div_sub_one {K N : ℕ} {a r : 𝓞 F} (hr : Bdd 𝔪 K r) (h : a - r ∈ 𝔪 ^ (K + N)) :
    Small 𝔪 N ((a : F) / (r : F) - 1) := by
  intro v hv
  have hmem : a - r ∈ v.asIdeal ^ (K + N) := Ideal.pow_right_mono hv _ h
  have h1 := (v.intValuation_le_pow_iff_mem _ (K + N)).mpr hmem
  rw [← v.valuation_of_algebraMap (K := F)] at h1
  have hrF : (r : F) ≠ 0 := by simpa using hr.1
  have hpos : 0 < v.valuation F (r : F) := lt_of_le_of_lt zero_le (hr.2 v hv)
  have e : (a : F) / (r : F) - 1 = algebraMap (𝓞 F) F (a - r) / (r : F) := by
    rw [map_sub]; field_simp
  rw [e, map_div₀, div_le_iff₀ hpos]
  refine h1.trans ?_
  have e2 : WithZero.exp (-((K + N : ℕ) : ℤ)) = WithZero.exp (-(N : ℤ)) * WithZero.exp (-(K : ℤ)) := by
    rw [← WithZero.exp_add]; congr 1; push_cast; ring
  rw [e2]
  exact mul_le_mul' le_rfl (hr.2 v hv).le

/-! ### `U_N` is a group for `N ≥ 1` -/

theorem small_mul_sub_one {N : ℕ} (hN1 : 1 ≤ N) {u u' : F} (h : Small 𝔪 N (u - 1))
    (h' : Small 𝔪 N (u' - 1)) : Small 𝔪 N (u * u' - 1) := by
  intro v hv
  have hu' := h'.val_eq_one (by exact_mod_cast hN1) v hv
  have e : u * u' - 1 = (u - 1) * u' + (u' - 1) := by ring
  rw [e]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ (h' v hv))
  rw [map_mul, hu', mul_one]
  exact h v hv

theorem small_inv_sub_one {N : ℕ} (hN1 : 1 ≤ N) {u : F} (h : Small 𝔪 N (u - 1)) :
    Small 𝔪 N (u⁻¹ - 1) := by
  intro v hv
  have hu := h.val_eq_one (by exact_mod_cast hN1) v hv
  have hu0 : u ≠ 0 := by
    intro h0; rw [h0, map_zero] at hu; exact zero_ne_one hu
  have e : u⁻¹ - 1 = -(u - 1) * u⁻¹ := by field_simp; ring
  rw [e, map_mul, map_inv₀, hu, inv_one, mul_one, Valuation.map_neg]
  exact h v hv

/-! ### A finite cover -/

/-- Nonzero integers fall into finitely many classes modulo `U_S U_N`. -/
theorem exists_finite_cover_int (h𝔪 : 𝔪 ≠ ⊥) (N : ℕ) : ∃ T : Finset F, (∀ η ∈ T, η ≠ 0) ∧
    ∀ a : 𝓞 F, a ≠ 0 → ∃ η ∈ T, ∃ (ε : (SInt 𝔪)ˣ) (u : F), Small 𝔪 N (u - 1) ∧
      (a : F) = η * ((ε : SInt 𝔪) : F) * u := by
  classical
  obtain ⟨K, hK⟩ := exists_bdd_rescale h𝔪
  have h𝔑 : 𝔪 ^ (K + N) ≠ ⊥ := pow_ne_zero _ h𝔪
  have := Ideal.finiteQuotientOfFreeOfNeBot _ h𝔑
  have := Fintype.ofFinite (𝓞 F ⧸ 𝔪 ^ (K + N))
  set rep : 𝓞 F ⧸ 𝔪 ^ (K + N) → 𝓞 F := fun x =>
    if h : ∃ r : 𝓞 F, Bdd 𝔪 K r ∧ Ideal.Quotient.mk _ r = x then h.choose else 1 with hrep
  have hrep0 : ∀ x, (rep x : F) ≠ 0 := by
    intro x
    simp only [hrep]
    split_ifs with h
    · simpa using h.choose_spec.1.1
    · simp
  refine ⟨Finset.univ.image fun x => (rep x : F), fun η hη => ?_, fun a ha => ?_⟩
  · obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hη
    exact hrep0 x
  · obtain ⟨ε, c', hc', hb⟩ := hK a ha
    have hex : ∃ r : 𝓞 F, Bdd 𝔪 K r ∧ Ideal.Quotient.mk (𝔪 ^ (K + N)) r = Ideal.Quotient.mk _ c' :=
      ⟨c', hb, rfl⟩
    have hr : rep (Ideal.Quotient.mk _ c') = hex.choose := by simp only [hrep, dif_pos hex]
    obtain ⟨hrb, hrq⟩ := hex.choose_spec
    rw [← hr] at hrb hrq
    set r := rep (Ideal.Quotient.mk _ c') with hrdef
    have hmem : c' - r ∈ 𝔪 ^ (K + N) := Ideal.Quotient.eq.mp hrq.symm
    have hrF : (r : F) ≠ 0 := hrep0 _
    have hε0 : ((ε : SInt 𝔪) : F) ≠ 0 := (isSUnit_coe_unit h𝔪 ε).1
    have hεinv : (((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = (((ε : SInt 𝔪) : F))⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← MulMemClass.coe_mul, ε.inv_mul]; rfl
    refine ⟨(r : F), Finset.mem_image_of_mem _ (Finset.mem_univ _), ε⁻¹, (c' : F) / (r : F),
      small_div_sub_one hrb hmem, ?_⟩
    rw [hεinv, hc']
    field_simp

/-- **`F^× / U_S U_N` is finite**: a finite set of representatives. -/
theorem exists_finite_cover (h𝔪 : 𝔪 ≠ ⊥) (N : ℕ) : ∃ T : Finset F, (∀ η ∈ T, η ≠ 0) ∧
    ∀ c : F, c ≠ 0 → ∃ η ∈ T, ∃ (ε : (SInt 𝔪)ˣ) (u : F), Small 𝔪 N (u - 1) ∧
      c = η * ((ε : SInt 𝔪) : F) * u := by
  classical
  obtain ⟨T, hT0, hT⟩ := exists_finite_cover_int h𝔪 (N + 1)
  refine ⟨Finset.image₂ (fun x y => x / y) T T, fun η hη => ?_, fun c hc => ?_⟩
  · obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_image₂.mp hη
    exact div_ne_zero (hT0 x hx) (hT0 y hy)
  · obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) c
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at hc
    obtain ⟨η₁, hη₁, ε₁, u₁, hu₁, e₁⟩ := hT a ha0
    obtain ⟨η₂, hη₂, ε₂, u₂, hu₂, e₂⟩ := hT b hb0
    have hN1 : 1 ≤ N + 1 := Nat.le_add_left 1 N
    have hbF : algebraMap (𝓞 F) F b ≠ 0 := by simpa using hb0
    have hu₂0 : u₂ ≠ 0 := by
      intro h0
      have e₂' : algebraMap (𝓞 F) F b = η₂ * ((ε₂ : SInt 𝔪) : F) * u₂ := e₂
      rw [e₂', h0, mul_zero] at hbF; exact hbF rfl
    have hε₂0 : ((ε₂ : SInt 𝔪) : F) ≠ 0 := (isSUnit_coe_unit h𝔪 ε₂).1
    have hεinv : (((ε₂⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = (((ε₂ : SInt 𝔪) : F))⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← MulMemClass.coe_mul, ε₂.inv_mul]; rfl
    refine ⟨η₁ / η₂, Finset.mem_image₂_of_mem hη₁ hη₂, ε₁ * ε₂⁻¹, u₁ * u₂⁻¹,
      Small.mono (by omega) (small_mul_sub_one hN1 hu₁ (small_inv_sub_one hN1 hu₂)), ?_⟩
    have hη₂0 := hT0 η₂ hη₂
    have e₁' : algebraMap (𝓞 F) F a = η₁ * ((ε₁ : SInt 𝔪) : F) * u₁ := e₁
    have e₂' : algebraMap (𝓞 F) F b = η₂ * ((ε₂ : SInt 𝔪) : F) * u₂ := e₂
    rw [Units.val_mul, MulMemClass.coe_mul, hεinv, e₁', e₂']
    field_simp

/-! ### `InClass` is an equivalence relation on `F^×`; disjoint representatives -/

theorem InClass.trans' {N : ℕ} (hN1 : 1 ≤ N) {a b c : F} (h : InClass 𝔪 N a b)
    (h' : InClass 𝔪 N b c) : InClass 𝔪 N a c := by
  obtain ⟨ε, t, u, ht, hu, rfl⟩ := h
  obtain ⟨ε', t', u', ht', hu', rfl⟩ := h'
  refine ⟨ε * ε', t * t', u * u', mul_ne_zero ht ht', small_mul_sub_one hN1 hu hu', ?_⟩
  rw [Units.val_mul, MulMemClass.coe_mul]
  ring

theorem InClass.symm' {N : ℕ} (hN1 : 1 ≤ N) {a b : F} (h : InClass 𝔪 N a b) (hb : b ≠ 0) :
    InClass 𝔪 N b a := by
  obtain ⟨ε, t, u, ht, hu, rfl⟩ := h
  have hu0 : u ≠ 0 := right_ne_zero_of_mul hb
  have hε0 : ((ε : SInt 𝔪) : F) ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hb))
  have hεinv : (((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = (((ε : SInt 𝔪) : F))⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← MulMemClass.coe_mul, ε.inv_mul]; rfl
  refine ⟨ε⁻¹, t⁻¹, u⁻¹, inv_ne_zero ht, small_inv_sub_one hN1 hu, ?_⟩
  rw [hεinv]
  field_simp

open scoped Classical in
/-- **Finiteness of `𝒞 = F^× / U_S (F^×)³ U_N`** (WP-S open issue 6): a finite complete set of
pairwise disjoint classes, in the form used by `S.sum_bigCell_apply`. -/
theorem exists_classReps (hG : Good 𝔪) {N : ℕ} (hN1 : 1 ≤ N) :
    ∃ T : Finset {η : F // η ≠ 0},
      (∀ η ∈ T, ∀ η' ∈ T, η ≠ η' → ∀ c, InClass 𝔪 N η.1 c → ¬ InClass 𝔪 N η'.1 c) ∧
      ∀ c : F, c ≠ 0 → ∃ η ∈ T, InClass 𝔪 N η.1 c := by
  obtain ⟨T₀, hT₀0, hT₀⟩ := exists_finite_cover hG.ne_bot N
  have hcov : ∀ c : F, c ≠ 0 → ∃ η ∈ T₀, InClass 𝔪 N η c := by
    intro c hc
    obtain ⟨η, hη, ε, u, hu, rfl⟩ := hT₀ c hc
    exact ⟨η, hη, ε, 1, u, one_ne_zero, hu, by ring⟩
  -- the class of `c`, as a set, and a representative depending only on that set
  set cls : F → Set F := fun c => {η | InClass 𝔪 N η c} with hcls
  have hcls_eq : ∀ {a b : F}, InClass 𝔪 N a b → b ≠ 0 → cls a = cls b := by
    intro a b hab hb
    ext η
    exact ⟨fun h => InClass.trans' hN1 h hab, fun h => InClass.trans' hN1 h (InClass.symm' hN1 hab hb)⟩
  set g : Set F → F := fun A => if h : ∃ η ∈ T₀, η ∈ A then h.choose else 1 with hg
  have hgs : ∀ c : F, c ≠ 0 → g (cls c) ∈ T₀ ∧ InClass 𝔪 N (g (cls c)) c := by
    intro c hc
    have hex : ∃ η ∈ T₀, η ∈ cls c := hcov c hc
    simp only [hg, dif_pos hex]
    exact hex.choose_spec
  refine ⟨(T₀.image fun η => g (cls η)).subtype (· ≠ 0), ?_, ?_⟩
  · intro η hη η' hη' hne c hc hc'
    rw [Finset.mem_subtype] at hη hη'
    obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp hη
    obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp hη'
    have hc0 : c ≠ 0 := InClass.ne_zero hG hN1 η.2 hc
    have h1 : cls a = cls c := by
      rw [← hcls_eq (hgs a (hT₀0 a ha)).2 (hT₀0 a ha), hae]
      exact hcls_eq hc hc0
    have h2 : cls b = cls c := by
      rw [← hcls_eq (hgs b (hT₀0 b hb)).2 (hT₀0 b hb), hbe]
      exact hcls_eq hc' hc0
    exact hne (Subtype.ext (by rw [← hae, ← hbe, h1, h2]))
  · intro c hc
    obtain ⟨η₀, hη₀, hin⟩ := hcov c hc
    obtain ⟨hmem, hin'⟩ := hgs η₀ (hT₀0 η₀ hη₀)
    refine ⟨⟨g (cls η₀), hT₀0 _ hmem⟩, ?_, InClass.trans' hN1 hin' hin⟩
    rw [Finset.mem_subtype]
    exact Finset.mem_image_of_mem _ hη₀

end

end ArtinKP.RO
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

include g hgood in
/-- **G1's hypothesis `hne`**: the Kirillov function of some section is not identically zero
(MATH3 §1.2 (G1): (C9), (C10′), Theorem E). -/
theorem hne_oai (hd : DD.DiffInS 𝔪) :
    ∃ (Φ₁ : GSection ι P 𝔪) (β₁ : F), β₁ ≠ 0 ∧
      G1.Kir hG hz6 (T.theta hG hz6) Φ₁ β₁ ≠ 0 := by
  obtain ⟨N, hN1, hN⟩ := P.exists_isDeepLevel hG.ne_bot
  obtain ⟨Tc, hdisj, hcov⟩ := RO.exists_classReps hG hN1
  obtain ⟨η, -, ν, hν, hτ⟩ := C9.exists_tau_bigCell_ne_zero' (ι := ι) (P := P) hG hz6 hN1 hN 0 Tc
    hdisj hcov hd (le_refl 0)
  refine ⟨bigCell ι P hG hN1 hN η.1 η.2 0 0, (ν : F), T.coe_ne_zero hν, fun h0 => hτ ?_⟩
  have h := tau_eq_rpow_mul_coefF_mul_kir hG hz6 g hgood ⟨ν, hν⟩ (bigCell ι P hG hN1 hN η.1 η.2 0 0)
  rw [h0, mul_zero] at h
  exact h

end E

/-! ### `θ = 0 ⇒ τ ≡ 0`, and `θ_Φ = 0 ⇒ θ_{wΦ} = 0` -/

/-! ### Lemma KW -/

end

end ArtinKP.GK
end

theorem solution.{u_1} : type_of% @ArtinKP.GK.hne_oai.{u_1} := @ArtinKP.GK.hne_oai.{u_1}
