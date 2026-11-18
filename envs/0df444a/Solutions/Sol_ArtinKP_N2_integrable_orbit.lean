-- Prove2me | solution 1 for ArtinKP.N2.integrable_orbit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:13:38.53892+00:00
-- url     : https://prove2.me/submissions/91f4365d-b32e-4dca-bc18-3dba3836f86a

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
import Theorems.Thm_ArtinKP_N2_integrable_lift_pou

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
-- module Solutions.Artin.KP.X2_Chart
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
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
-- module Solutions.Artin.KP.X2_Core
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
-- module Solutions.Artin.KP.X2_Eigen
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma norm_pe_le {a : PairClass S → ℂ} {g : ℝ → ℂ} (hg : VanishLow g) {A B : ℝ}
    (ha : ∀ p, ‖a p‖ ≤ A) (hb : ∀ τ, ‖g τ‖ ≤ B) (P : X F) : ‖pe S a g P‖ ≤ A * B := by
  obtain ⟨p₁, h⟩ := pe_single S P
  rw [h a g hg, norm_mul]
  exact mul_le_mul (ha p₁) (hb _) (norm_nonneg _) ((norm_nonneg _).trans (ha p₁))

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
-- module Solutions.Artin.KP.N2_Main
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-! ### The pseudo-Eisenstein series by orbits -/

lemma norm_aOrb_le {Γ : Subgroup (SL(2, 𝓞 F))} {S : Finset (FinitePlace F)} (o : Orb Γ S)
    (p : PairClass S) : ‖aOrb o p‖ ≤ 1 := by
  unfold aOrb
  split_ifs <;> simp

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

/-! ### `L¹` bounds -/

/-! ### One orbit -/

section orbit

variable (Pk : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  {Γ : Subgroup (SL(2, 𝓞 F))} [Γ.FiniteIndex] {Ψ : TSection ι 𝔪}

include hG in
/-- Integrability of an orbit piece against `θ`. -/
lemma integrable_orbit_oai (p₀ : PairClass (RO.SOf 𝔪)) {g : ℝ → ℂ}
    (hgs : ContDiff ℝ (⊤ : ℕ∞) g) (hgl : VanishLow g) {C : ℝ} (hC : ∀ τ, ‖g τ‖ ≤ C)
    (v : X.L2 Γ) :
    Integrable (fun P => automC (stab Γ p₀) (fun P => g (Real.log (p₀.ht P))) P
      * (X.lift Γ v P * (((X.pou Γ P).toReal : ℝ) : ℂ))) (X.vol F) := by
  have hm : Measurable (automC (stab Γ p₀) (fun P => g (Real.log (p₀.ht P)))) := by
    have : automC (stab Γ p₀) (fun P => g (Real.log (p₀.ht P)))
        = pe (RO.SOf 𝔪) (aOrb (orbOf Γ p₀)) g := funext fun P => (pe_aOrb Γ p₀ g P).symm
    rw [this]
    exact (smooth_pe _ hgs hgl).continuous.measurable
  refine Integrable.bdd_mul (c := 1 * C) (integrable_lift_pou hG Γ v) hm.aestronglyMeasurable
    (Eventually.of_forall fun P => ?_)
  rw [← pe_aOrb]
  exact norm_pe_le hgl (norm_aOrb_le _) hC P

end orbit

/-! ### Cusp representatives -/

/-! ### Stub N-1 -/

end

end ArtinKP.N2
end

theorem solution.{u_1} : type_of% @ArtinKP.N2.integrable_orbit_oai.{u_1} := @ArtinKP.N2.integrable_orbit_oai.{u_1}
