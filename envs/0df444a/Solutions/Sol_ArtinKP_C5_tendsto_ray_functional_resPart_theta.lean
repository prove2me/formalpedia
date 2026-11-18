-- Prove2me | solution 1 for ArtinKP.C5.tendsto_ray_functional_resPart_theta
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:44:53.672004+00:00
-- url     : https://prove2.me/submissions/2e187aca-0735-4ee7-9027-2f1f2e89381a

import Mathlib
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
import Theorems.Thm_ArtinKP_C5_exists_single
import Theorems.Thm_ArtinKP_C5_l2Rep_src
import Theorems.Thm_ArtinKP_C5_quotVol_lt_top
import Theorems.Thm_ArtinKP_C5_smooth_src

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
-- module Solutions.Artin.KP.B_Def
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
-- module Solutions.Artin.KP.CAbs_Residue
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulGinfX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX
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

lemma mem_eigenspace_iff {T : H →L[ℂ] H} {t : ℂ} {x : H} :
    x ∈ eigenspace T t ↔ T x = t • x := by
  simp [eigenspace, sub_eq_zero]

/-- `⟪x, x⟫ = ‖x‖²` with the `Complex.ofReal` cast. -/
lemma inner_self_eq_ofReal (x : H) : ⟪x, x⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  simp [inner_self_eq_norm_sq_to_K]

lemma im_inner_self_eq_zero {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) (x : H) :
    (⟪T x, x⟫_ℂ).im = 0 := by
  have h1 : ⟪T x, x⟫_ℂ = ⟪x, T x⟫_ℂ := by
    have := ContinuousLinearMap.adjoint_inner_left T x x
    rw [ContinuousLinearMap.isSelfAdjoint_iff'.mp hT] at this
    exact this
  have h2 : conj ⟪T x, x⟫_ℂ = ⟪T x, x⟫_ℂ := by
    rw [inner_conj_symm]; exact h1.symm
  exact Complex.conj_eq_iff_im.mp h2

lemma im_inner_sub_smul {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) (z : ℂ) (x : H) :
    (⟪(T - z • (1 : H →L[ℂ] H)) x, x⟫_ℂ).im = z.im * ‖x‖ ^ 2 := by
  have h : ⟪(T - z • (1 : H →L[ℂ] H)) x, x⟫_ℂ = ⟪T x, x⟫_ℂ - conj z * ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    simp [inner_sub_left, inner_smul_left, inner_self_eq_norm_sq_to_K, mul_comm]
  rw [h, Complex.sub_im, im_inner_self_eq_zero hT, Complex.im_mul_ofReal, Complex.conj_im]
  ring

lemma im_mul_sq_le_norm_inner {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) (z : ℂ) (x : H) :
    |z.im| * ‖x‖ ^ 2 ≤ ‖⟪(T - z • (1 : H →L[ℂ] H)) x, x⟫_ℂ‖ := by
  have := Complex.abs_im_le_norm ⟪(T - z • (1 : H →L[ℂ] H)) x, x⟫_ℂ
  rw [im_inner_sub_smul hT, abs_mul, abs_of_nonneg (sq_nonneg ‖x‖)] at this
  exact this

/-- `T - z` is invertible for non-real `z`. -/
lemma isUnit_sub_smul {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) {z : ℂ} (hz : z.im ≠ 0) :
    IsUnit (T - z • (1 : H →L[ℂ] H)) := by
  refine ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map _
    (c := ⟨|z.im|, abs_nonneg _⟩) (by exact_mod_cast abs_pos.mpr hz) fun x => ?_
  have := im_mul_sq_le_norm_inner hT z x
  rw [mul_comm] at this
  exact this

lemma sub_smul_shiftInv_apply {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) {z : ℂ} (hz : z.im ≠ 0)
    (y : H) : (T - z • (1 : H →L[ℂ] H)) (shiftInv T z y) = y := by
  have := Ring.mul_inverse_cancel _ (isUnit_sub_smul hT hz)
  exact congrArg (fun A : H →L[ℂ] H => A y) this

lemma shiftInv_sub_smul_apply {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) {z : ℂ} (hz : z.im ≠ 0)
    (y : H) : shiftInv T z ((T - z • (1 : H →L[ℂ] H)) y) = y := by
  have := Ring.inverse_mul_cancel _ (isUnit_sub_smul hT hz)
  exact congrArg (fun A : H →L[ℂ] H => A y) this

/-- `‖(T - z)⁻¹ y‖ ≤ ‖y‖ / |Im z|`, in multiplied-out form (true also for `Im z = 0`). -/
lemma im_mul_norm_shiftInv_apply_le {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) (z : ℂ) (y : H) :
    |z.im| * ‖shiftInv T z y‖ ≤ ‖y‖ := by
  by_cases hz : z.im = 0
  · simp [hz]
  set x := shiftInv T z y with hx
  have h1 := im_mul_sq_le_norm_inner hT z x
  rw [sub_smul_shiftInv_apply hT hz y] at h1
  have h2 : ‖⟪y, x⟫_ℂ‖ ≤ ‖y‖ * ‖x‖ := norm_inner_le_norm y x
  by_cases hx0 : ‖x‖ = 0
  · rw [hx0]; simp
  have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx0)
  have h3 : (|z.im| * ‖x‖) * ‖x‖ ≤ ‖y‖ * ‖x‖ := by nlinarith
  exact le_of_mul_le_mul_right h3 hxpos

/-- Uniform bound: if `‖z - t₀‖ ≤ M * |Im z|` then `‖(t₀ - z) • (T - z)⁻¹ y‖ ≤ M * ‖y‖`. -/
lemma norm_residue_apply_le {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) (t₀ : ℝ) {z : ℂ} {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ‖z - t₀‖ ≤ M * |z.im|) (y : H) :
    ‖((t₀ : ℂ) - z) • shiftInv T z y‖ ≤ M * ‖y‖ := by
  rw [norm_smul, ← norm_neg, neg_sub]
  have h1 := im_mul_norm_shiftInv_apply_le hT z y
  calc ‖z - t₀‖ * ‖shiftInv T z y‖ ≤ (M * |z.im|) * ‖shiftInv T z y‖ := by gcongr
    _ = M * (|z.im| * ‖shiftInv T z y‖) := by ring
    _ ≤ M * ‖y‖ := by gcongr

/-- On the eigenspace, `(t₀ - z) • (T - z)⁻¹` is the identity. -/
lemma residue_apply_of_mem {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) (t₀ : ℝ) {z : ℂ}
    (hz : z.im ≠ 0) {x : H} (hx : x ∈ eigenspace T t₀) :
    ((t₀ : ℂ) - z) • shiftInv T z x = x := by
  have h1 : (T - z • (1 : H →L[ℂ] H)) x = ((t₀ : ℂ) - z) • x := by
    simp [mem_eigenspace_iff.mp hx, sub_smul]
  have h2 := shiftInv_sub_smul_apply hT hz x
  rw [h1, map_smul] at h2
  exact h2

/-- On the range of `T - t₀`: `(t₀ - z)(T - z)⁻¹(T - t₀) y = (t₀ - z) y - (t₀ - z)² (T - z)⁻¹ y`. -/
lemma residue_apply_range {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) (t₀ : ℝ) {z : ℂ}
    (hz : z.im ≠ 0) (y : H) :
    ((t₀ : ℂ) - z) • shiftInv T z ((T - (t₀ : ℂ) • (1 : H →L[ℂ] H)) y) =
      ((t₀ : ℂ) - z) • y - ((t₀ : ℂ) - z) • (((t₀ : ℂ) - z) • shiftInv T z y) := by
  have h1 : (T - (t₀ : ℂ) • (1 : H →L[ℂ] H)) y =
      (T - z • (1 : H →L[ℂ] H)) y - ((t₀ : ℂ) - z) • y := by
    simp [sub_smul]
  rw [h1, map_sub, shiftInv_sub_smul_apply hT hz, map_smul, smul_sub]

lemma norm_residue_apply_range_le {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) (t₀ : ℝ) {z : ℂ} {M : ℝ}
    (hz : z.im ≠ 0) (hM0 : 0 ≤ M) (hM : ‖z - t₀‖ ≤ M * |z.im|) (y : H) :
    ‖((t₀ : ℂ) - z) • shiftInv T z ((T - (t₀ : ℂ) • (1 : H →L[ℂ] H)) y)‖ ≤
      ‖z - t₀‖ * ((1 + M) * ‖y‖) := by
  rw [residue_apply_range hT t₀ hz]
  have h2 := norm_residue_apply_le hT t₀ hM0 hM y
  have h3 : ‖(t₀ : ℂ) - z‖ = ‖z - t₀‖ := norm_sub_rev _ _
  calc _ ≤ ‖((t₀ : ℂ) - z) • y‖ + ‖((t₀ : ℂ) - z) • (((t₀ : ℂ) - z) • shiftInv T z y)‖ :=
        norm_sub_le _ _
    _ = ‖z - t₀‖ * ‖y‖ + ‖z - t₀‖ * ‖((t₀ : ℂ) - z) • shiftInv T z y‖ := by
        rw [norm_smul, norm_smul ((t₀ : ℂ) - z) (((t₀ : ℂ) - z) • _), h3]
    _ ≤ ‖z - t₀‖ * ‖y‖ + ‖z - t₀‖ * (M * ‖y‖) := by gcongr
    _ = ‖z - t₀‖ * ((1 + M) * ‖y‖) := by ring

/-- The orthogonal complement of the eigenspace is the closure of the range of `T - t₀`. -/
lemma orthogonal_eigenspace {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) (t₀ : ℝ) :
    (eigenspace T t₀)ᗮ =
      (LinearMap.range ((T - (t₀ : ℂ) • (1 : H →L[ℂ] H) : H →L[ℂ] H) : H →ₗ[ℂ] H)).topologicalClosure := by
  have hS : IsSelfAdjoint (T - (t₀ : ℂ) • (1 : H →L[ℂ] H)) := by
    refine hT.sub ?_
    have : IsSelfAdjoint ((t₀ : ℂ) • (1 : H →L[ℂ] H)) := by
      rw [isSelfAdjoint_iff, star_smul, star_one]; simp
    exact this
  have := ContinuousLinearMap.orthogonal_ker (T - (t₀ : ℂ) • (1 : H →L[ℂ] H))
  rw [ContinuousLinearMap.isSelfAdjoint_iff'.mp hS] at this
  exact this

/-- **Lemma C1 (strong residue), pointwise form.** -/
theorem tendsto_residue_apply {ι : Type*} {l : Filter ι} {T : H →L[ℂ] H} (hT : IsSelfAdjoint T)
    (t₀ : ℝ) {z : ι → ℂ} {M : ℝ} (hz : Tendsto z l (𝓝 (t₀ : ℂ)))
    (him : ∀ᶠ i in l, (z i).im ≠ 0) (hcone : ∀ᶠ i in l, ‖z i - t₀‖ ≤ M * |(z i).im|) (x₀ : H) :
    Tendsto (fun i => ((t₀ : ℂ) - z i) • shiftInv T (z i) x₀) l (𝓝 (eigenProj T t₀ x₀)) := by
  set M' : ℝ := |M| with hM'
  have hM'0 : 0 ≤ M' := abs_nonneg M
  have hcone' : ∀ᶠ i in l, ‖z i - t₀‖ ≤ M' * |(z i).im| := by
    filter_upwards [hcone] with i hi
    exact hi.trans (mul_le_mul_of_nonneg_right (le_abs_self M) (abs_nonneg _))
  set p := eigenProj T t₀ x₀ with hp
  have hpmem : p ∈ eigenspace T t₀ := Submodule.starProjection_apply_mem _ _
  have hw : x₀ - p ∈ (eigenspace T t₀)ᗮ := Submodule.sub_starProjection_mem_orthogonal x₀
  rw [orthogonal_eigenspace hT t₀] at hw
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- approximate `x₀ - p` by an element of the range
  have hw' : x₀ - p ∈ closure
      (LinearMap.range ((T - (t₀ : ℂ) • (1 : H →L[ℂ] H) : H →L[ℂ] H) : H →ₗ[ℂ] H) : Set H) := by
    rw [← Submodule.topologicalClosure_coe]; exact hw
  obtain ⟨_, ⟨y, rfl⟩, hy⟩ := Metric.mem_closure_iff.mp hw' (ε / (2 * (M' + 1))) (by positivity)
  have hzn : Tendsto (fun i => ‖z i - t₀‖ * ((1 + M') * ‖y‖)) l (𝓝 0) := by
    have h0 : Tendsto (fun i => ‖z i - t₀‖) l (𝓝 0) := by
      have := (hz.sub_const (t₀ : ℂ)).norm
      simpa using this
    simpa using h0.mul_const ((1 + M') * ‖y‖)
  have hsmall : ∀ᶠ i in l, ‖z i - t₀‖ * ((1 + M') * ‖y‖) < ε / 2 :=
    hzn.eventually (gt_mem_nhds (by positivity))
  filter_upwards [him, hcone', hsmall] with i hi hci hsi
  set r : H := (x₀ - p) - (T - (t₀ : ℂ) • (1 : H →L[ℂ] H)) y with hr
  have hrn : ‖r‖ < ε / (2 * (M' + 1)) := by
    rw [hr, ← dist_eq_norm]; exact hy
  have hdecomp : x₀ = p + r + (T - (t₀ : ℂ) • (1 : H →L[ℂ] H)) y := by
    rw [hr]; abel
  have hA : ((t₀ : ℂ) - z i) • shiftInv T (z i) x₀ - p =
      ((t₀ : ℂ) - z i) • shiftInv T (z i) r +
        ((t₀ : ℂ) - z i) • shiftInv T (z i) ((T - (t₀ : ℂ) • (1 : H →L[ℂ] H)) y) := by
    conv_lhs => rw [hdecomp]
    rw [map_add, map_add, smul_add, smul_add, residue_apply_of_mem hT t₀ hi hpmem]
    abel
  rw [dist_eq_norm, hA]
  have h1 := norm_residue_apply_le hT t₀ hM'0 hci r
  have h2 := norm_residue_apply_range_le hT t₀ hi hM'0 hci y
  have h3 : M' * ‖r‖ ≤ ε / 2 := by
    have : M' * ‖r‖ ≤ (M' + 1) * (ε / (2 * (M' + 1))) := by
      have := hrn.le
      nlinarith [norm_nonneg r]
    have h4 : (M' + 1) * (ε / (2 * (M' + 1))) = ε / 2 := by
      field_simp
    linarith
  calc _ ≤ _ + _ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

/-- **Lemma C1 (strong residue), continuous-convergence form**: along a moving family `x i → x₀`. -/
theorem tendsto_residue {ι : Type*} {l : Filter ι} {T : H →L[ℂ] H} (hT : IsSelfAdjoint T)
    (t₀ : ℝ) {z : ι → ℂ} {M : ℝ} (hz : Tendsto z l (𝓝 (t₀ : ℂ)))
    (him : ∀ᶠ i in l, (z i).im ≠ 0) (hcone : ∀ᶠ i in l, ‖z i - t₀‖ ≤ M * |(z i).im|)
    {x : ι → H} {x₀ : H} (hx : Tendsto x l (𝓝 x₀)) :
    Tendsto (fun i => ((t₀ : ℂ) - z i) • shiftInv T (z i) (x i)) l (𝓝 (eigenProj T t₀ x₀)) := by
  have h1 := tendsto_residue_apply hT t₀ hz him hcone x₀
  have hcone' : ∀ᶠ i in l, ‖z i - t₀‖ ≤ |M| * |(z i).im| := by
    filter_upwards [hcone] with i hi
    exact hi.trans (mul_le_mul_of_nonneg_right (le_abs_self M) (abs_nonneg _))
  have h2 : Tendsto (fun i => ((t₀ : ℂ) - z i) • shiftInv T (z i) (x i - x₀)) l (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun i => |M| * ‖x i - x₀‖)
    · filter_upwards [hcone'] with i hi
      exact norm_residue_apply_le hT t₀ (abs_nonneg M) hi _
    · have : Tendsto (fun i => ‖x i - x₀‖) l (𝓝 0) := by
        simpa using (hx.sub_const x₀).norm
      simpa using this.const_mul |M|
  have h3 := h2.add h1
  rw [zero_add] at h3
  refine h3.congr fun i => ?_
  rw [← smul_add, ← map_add, sub_add_cancel]

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

lemma mem_resolventDomain_of_im_ne_zero {lam : ℂ} (h : lam.im ≠ 0) : lam ∈ resolventDomain :=
  Or.inr h

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

lemma inner_riesz_right (f : H) (u : V) : ⟪u, E.riesz f⟫_ℂ = ⟪E.j u, f⟫_ℂ :=
  ContinuousLinearMap.adjoint_inner_right E.j u f

lemma T_apply (f : H) : E.T f = E.j (E.riesz f) := rfl

lemma inner_T (f g : H) : ⟪E.T f, g⟫_ℂ = ⟪E.riesz f, E.riesz g⟫_ℂ := by
  rw [T_apply, inner_riesz_right]

lemma isPositive_T : E.T.IsPositive :=
  ContinuousLinearMap.isPositive_self_comp_adjoint E.j

lemma isSelfAdjoint_T : IsSelfAdjoint E.T :=
  (ContinuousLinearMap.isPositive_def'.mp E.isPositive_T).1

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

lemma G_one_sub_smul_T_apply {lam : ℂ} (h : lam ∈ resolventDomain) (f : H) :
    E.G lam ((1 - (lam + 1) • E.T : H →L[ℂ] H) f) = f := by
  have := Ring.inverse_mul_cancel _ (E.isUnit_of_mem_resolventDomain h)
  exact congrArg (fun A : H →L[ℂ] H => A f) this

end EnergySpace

end

end ArtinKP.CAbs
end

section
-- module Solutions.Artin.KP.X2_H1
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup
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

lemma X.toL2_sub {f g : X F → ℂ} (hf : X.L2Rep Γ f) (hg : X.L2Rep Γ g) :
    X.toL2 Γ (fun P => f P - g P) (hf.sub hg) = X.toL2 Γ f hf - X.toL2 Γ g hg :=
  MemLp.toLp_sub hf.memLp hg.memLp

/-! ### Local integrability of pull-backs -/

/-! ### The core -/

/-! ### Density of the core -/

/-! ### The symmetric operator and the energy space -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.C5_Holo
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup
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

variable {F : Type*} [Field F] [NumberField F] {Γ : Subgroup (SL(2, 𝓞 F))}

/-- A bounded measurable invariant function is square integrable modulo `Γ` (finite volume). -/
lemma l2Rep_of_bdd (hvol : X.quotVol Γ Set.univ < ⊤) {f : X F → ℂ} (hf : Measurable f)
    (hinv : X.IsInv Γ f) {B : ℝ} (hb : ∀ P, ‖f P‖ ≤ B) : X.L2Rep Γ f := by
  have : IsFiniteMeasure (X.quotVol Γ) := ⟨hvol⟩
  exact ⟨hf, hinv, MemLp.of_bound (X.measurable_desc hf hinv).aestronglyMeasurable B
    (Filter.Eventually.of_forall fun q => hb _)⟩

/-- `‖[f]‖ ≤ vol(Γ\X)^{1/2} · sup |f|`. -/
lemma norm_toL2_le (hvol : X.quotVol Γ Set.univ < ⊤) {f : X F → ℂ} (h : X.L2Rep Γ f) {B : ℝ}
    (hB0 : 0 ≤ B) (hb : ∀ P, ‖f P‖ ≤ B) :
    ‖X.toL2 Γ f h‖ ≤ (X.quotVol Γ Set.univ).toReal ^ (1 / 2 : ℝ) * B := by
  have : IsFiniteMeasure (X.quotVol Γ) := ⟨hvol⟩
  unfold X.toL2
  rw [Lp.norm_toLp]
  have h1 : eLpNorm (X.desc Γ f) 2 (X.quotVol Γ) ≤
      X.quotVol Γ Set.univ ^ (1 / 2 : ℝ) * ENNReal.ofReal B := by
    have := eLpNorm_le_of_ae_bound (μ := X.quotVol Γ) (p := 2) (f := X.desc Γ f) (C := B)
      (Filter.Eventually.of_forall fun q => hb _)
    simpa using this
  have h2 : X.quotVol Γ Set.univ ^ (1 / 2 : ℝ) * ENNReal.ofReal B ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hvol.ne) ENNReal.ofReal_ne_top
  have h3 := ENNReal.toReal_mono h2 h1
  rwa [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hB0] at h3

/-- **Bounded holomorphic families are holomorphic into `L²(Γ\X)`.** -/
theorem differentiable_toL2 (hvol : X.quotVol Γ Set.univ < ⊤) {f : ℂ → X F → ℂ}
    (hmeas : ∀ s, Measurable (f s)) (hinv : ∀ s, X.IsInv Γ (f s))
    (hdiff : ∀ P, Differentiable ℂ fun s => f s P)
    (hbdd : ∀ s₀ : ℂ, ∃ R B : ℝ, 0 < R ∧ ∀ s ∈ ball s₀ R, ∀ P, ‖f s P‖ ≤ B)
    (hrep : ∀ s, X.L2Rep Γ (f s)) :
    Differentiable ℂ fun s => X.toL2 Γ (f s) (hrep s) := by
  intro s₀
  obtain ⟨R, B₀, hR, hB₀⟩ := hbdd s₀
  set B : ℝ := max B₀ 0 with hBdef
  have hB0 : 0 ≤ B := le_max_right _ _
  have hB : ∀ s ∈ ball s₀ R, ∀ P, ‖f s P‖ ≤ B := fun s hs P =>
    (hB₀ s hs P).trans (le_max_left _ _)
  set g : X F → ℂ := fun P => deriv (fun s => f s P) s₀ with hg
  have hgb : ∀ P, ‖g P‖ ≤ 2 * B / R := fun P =>
    norm_deriv_le hR (hdiff P).differentiableOn fun z hz => hB z hz P
  have hginv : X.IsInv Γ g := fun γ P => by
    change deriv (fun s => f s (γ • P)) s₀ = deriv (fun s => f s P) s₀
    congr 1
    funext s
    exact hinv s γ P
  have hgmeas : Measurable g := by
    set k : ℕ → ℂ := fun n => 1 / ((n : ℂ) + 1) with hk
    have hk0 : ∀ n, k n ≠ 0 := fun n => by
      rw [hk]
      exact one_div_ne_zero (Nat.cast_add_one_ne_zero n)
    have hkt : Tendsto k atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)
    refine measurable_of_tendsto_metrizable
      (f := fun n P => (k n)⁻¹ * (f (s₀ + k n) P - f s₀ P))
      (fun n => ((hmeas _).sub (hmeas _)).const_mul _) ?_
    rw [tendsto_pi_nhds]
    intro P
    have h1 := (hdiff P s₀).hasDerivAt.tendsto_slope
    have h2 : Tendsto (fun n => s₀ + k n) atTop (𝓝[≠] s₀) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
      · simpa using (tendsto_const_nhds (x := s₀)).add hkt
      · simpa using hk0 n
    refine (h1.comp h2).congr fun n => ?_
    simp [slope_def_module]
  have hgrep : X.L2Rep Γ g := l2Rep_of_bdd hvol hgmeas hginv hgb
  refine (HasDerivAt.differentiableAt (f' := X.toL2 Γ g hgrep) ?_)
  rw [hasDerivAt_iff_isLittleO]
  set V : ℝ := (X.quotVol Γ Set.univ).toReal ^ (1 / 2 : ℝ) with hV
  have key : ∀ z ∈ ball s₀ R,
      ‖X.toL2 Γ (f z) (hrep z) - X.toL2 Γ (f s₀) (hrep s₀) - (z - s₀) • X.toL2 Γ g hgrep‖ ≤
        V * (4 * B / R ^ 2) * ‖z - s₀‖ ^ 2 := by
    intro z hz
    have hrep' := ((hrep z).sub (hrep s₀)).sub (hgrep.const_mul (z - s₀))
    have e : X.toL2 Γ (f z) (hrep z) - X.toL2 Γ (f s₀) (hrep s₀) - (z - s₀) • X.toL2 Γ g hgrep =
        X.toL2 Γ _ hrep' := by
      rw [X.toL2_sub ((hrep z).sub (hrep s₀)) (hgrep.const_mul (z - s₀)),
        X.toL2_sub (hrep z) (hrep s₀), X.toL2_const_mul hgrep]
    rw [e]
    have hb' : ∀ P, ‖f z P - f s₀ P - (z - s₀) * g P‖ ≤ 4 * B / R ^ 2 * ‖z - s₀‖ ^ 2 := fun P =>
      norm_sub_sub_le hR (hdiff P).differentiableOn (fun w hw => hB w hw P) hz
    have := norm_toL2_le hvol hrep' (by positivity) hb'
    linarith [this, mul_assoc V (4 * B / R ^ 2) (‖z - s₀‖ ^ 2)]
  have hO : (fun z => X.toL2 Γ (f z) (hrep z) - X.toL2 Γ (f s₀) (hrep s₀) -
      (z - s₀) • X.toL2 Γ g hgrep) =O[𝓝 s₀] fun z => ‖z - s₀‖ ^ 2 := by
    refine Asymptotics.IsBigO.of_bound (V * (4 * B / R ^ 2)) ?_
    filter_upwards [ball_mem_nhds s₀ hR] with z hz
    rw [norm_pow, norm_norm]
    exact key z hz
  exact hO.trans_isLittleO (Asymptotics.isLittleO_pow_sub_sub s₀ one_lt_two)

end

end ArtinKP.C5
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

lemma norm_pe_le {a : PairClass S → ℂ} {g : ℝ → ℂ} (hg : VanishLow g) {A B : ℝ}
    (ha : ∀ p, ‖a p‖ ≤ A) (hb : ∀ τ, ‖g τ‖ ≤ B) (P : X F) : ‖pe S a g P‖ ≤ A * B := by
  obtain ⟨p₁, h⟩ := pe_single S P
  rw [h a g hg, norm_mul]
  exact mul_le_mul (ha p₁) (hb _) (norm_nonneg _) ((norm_nonneg _).trans (ha p₁))

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

lemma vanishLow_phiS (s : ℂ) : VanishLow (phiS F s) := fun τ h => by
  unfold phiS
  rw [vanishLow_rt1 τ h, vanishLow_rt2 τ h]
  simp

lemma vanishHigh_phiS (s : ℂ) : VanishHigh (phiS F s) := fun τ h => by
  unfold phiS
  rw [vanishHigh_rt1 τ h, vanishHigh_rt2 τ h]
  simp

lemma differentiable_phiS (τ : ℝ) : Differentiable ℂ fun s : ℂ => phiS F s τ := by
  unfold phiS
  fun_prop

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

lemma src_eq_pe (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) (s : ℂ) :
    src Ψ s = pe (RO.SOf 𝔪) (wt h𝔪 Ψ s) (phiS F s) :=
  funext fun Q => tsum_eq_pe h𝔪 Ψ s (phiS F s) Q

/-! ### The Eisenstein series on pair classes -/

/-! ### Invariance, regularity -/

lemma isInv_pe_wt (h𝔪 : 𝔪 ≠ ⊥) {Γ : Subgroup (SL(2, 𝓞 F))} {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ)
    (s : ℂ) (g : ℝ → ℂ) : X.IsInv Γ (pe (RO.SOf 𝔪) (wt h𝔪 Ψ s) g) := fun γ Q =>
  pe_smul g (fun p => wt_act h𝔪 hΓ γ.2 s p) Q

lemma isInv_src (h𝔪 : 𝔪 ≠ ⊥) {Γ : Subgroup (SL(2, 𝓞 F))} {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ)
    (s : ℂ) : X.IsInv Γ (src Ψ s) := by
  rw [src_eq_pe h𝔪]
  exact isInv_pe_wt h𝔪 hΓ s _

/-! ### The source -/

/-- `F_s` is bounded on `{‖s‖ ≤ M} × X`. -/
theorem exists_norm_src_le (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, ‖s‖ ≤ M → ∀ Q : X F, ‖src Ψ s Q‖ ≤ C := by
  obtain ⟨Bd, hB0, hB⟩ := exists_wt_bound h𝔪 Ψ M
  obtain ⟨C, hC0, hC⟩ := exists_norm_phiS_le F M
  refine ⟨Bd * C, mul_nonneg hB0 hC0, fun s hs Q => ?_⟩
  rw [src_eq_pe h𝔪]
  exact norm_pe_le (vanishLow_phiS s) (hB s hs) (hC s hs) Q

/-- `s ↦ F_s(Q)` is entire. -/
theorem differentiable_src (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) (Q : X F) :
    Differentiable ℂ fun s : ℂ => src Ψ s Q := by
  obtain ⟨p₁, h⟩ := pe_single (RO.SOf 𝔪) Q
  have e : (fun s : ℂ => src Ψ s Q) =
      fun s => wt h𝔪 Ψ s p₁ * phiS F s (Real.log (p₁.ht Q)) := by
    funext s
    rw [src_eq_pe h𝔪, h _ _ (vanishLow_phiS s)]
  rw [e]
  exact (differentiable_wt h𝔪 Ψ p₁).mul (differentiable_phiS _)

end

end ArtinKP.C5
end

section
-- module Solutions.Artin.KP.CAbs_Limit
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulGinfX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX
attribute [-simp] _root_.ArtinKP.X.SymmOp.energySpace_j
/-!
# WP-C-abs, parts 3 and 4: the soft resolvent limit and its consequences

With `E : EnergySpace V H`, `Res lam = T (1 - (lam + 1) T)⁻¹` and `proj lam₀` the orthogonal
projection of `H` onto the weak `lam₀`-eigenspace (`= ker (T - (lam₀ + 1)⁻¹)`):

* `(lam - lam₀) • Res lam f → - proj lam₀ f` as `lam → lam₀` (real, `≠ -1`) inside a cone
  `‖lam - lam₀‖ ≤ C |Im lam|`;
* for `lamf` differentiable at `s₀` with `lamf s₀ = lam₀`, `lamf' s₀ ≠ 0`:
  `(s - s₀) • Res (lamf s) f_s → c₀ • proj lam₀ f`, with **`c₀ = - 1 / lamf' s₀`**;
* along a ray `s₀ + t d`, `t ↓ 0`, the cone condition is automatic as soon as
  `Im (lamf' s₀ * d) ≠ 0`;
* consequences: the limit is a weak eigenvector in `V`, the norm formula, functionals.
-/

namespace ArtinKP.CAbs

open Filter Topology ComplexConjugate
open scoped InnerProductSpace NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace EnergySpace

variable {V : Type*} {H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : EnergySpace V H)

/-- `Res lam` in terms of the shifted inverse `(T - z)⁻¹`, `z = (lam + 1)⁻¹`, for non-real `lam`. -/
lemma Res_apply_eq {lam : ℂ} (him : lam.im ≠ 0) (f : H) :
    E.Res lam f =
      -((lam + 1)⁻¹ • (f + (lam + 1)⁻¹ • shiftInv E.T (lam + 1)⁻¹ f)) := by
  set μ : ℂ := lam + 1 with hμ
  have hμim : μ.im ≠ 0 := by simpa [hμ] using him
  have hμ0 : μ ≠ 0 := fun h => hμim (by simp [h])
  set z : ℂ := μ⁻¹ with hz
  have hzim : z.im ≠ 0 := by
    rw [hz, Complex.inv_im]
    exact div_ne_zero (neg_ne_zero.mpr hμim) (Complex.normSq_pos.mpr hμ0).ne'
  set g : H := shiftInv E.T z f with hg
  have h1 : (E.T - z • (1 : H →L[ℂ] H)) g = f :=
    sub_smul_shiftInv_apply E.isSelfAdjoint_T hzim f
  have hTg : E.T g = f + z • g := by
    have : E.T g - z • g = f := by simpa using h1
    rw [← this]; abel
  have h2 : (1 - μ • E.T : H →L[ℂ] H) (-(z • g)) = f := by
    have e : (1 - μ • E.T : H →L[ℂ] H) (-(z • g)) = -(z • g) + (μ * z) • E.T g := by
      simp [smul_smul, sub_eq_add_neg, add_comm]
    rw [e, hz, mul_inv_cancel₀ hμ0, one_smul, hTg]; abel
  have h3 : E.G lam f = -(z • g) := by
    rw [← h2]
    exact E.G_one_sub_smul_T_apply (mem_resolventDomain_of_im_ne_zero him) _
  show E.T (E.G lam f) = _
  rw [h3, map_neg, map_smul, hTg]

/-- **The limit in the spectral variable**: `(lam - lam₀) • Res lam f → - P_{lam₀} f` as
`lam → lam₀` in a cone off the real axis (with a moving right-hand side `f i → f₀`). -/
theorem tendsto_sub_smul_Res {ι : Type*} {l : Filter ι} {lam : ι → ℂ} {lam₀ : ℝ} {C : ℝ}
    (h1 : lam₀ + 1 ≠ 0) (hlam : Tendsto lam l (𝓝 (lam₀ : ℂ)))
    (him : ∀ᶠ i in l, (lam i).im ≠ 0)
    (hcone : ∀ᶠ i in l, ‖lam i - lam₀‖ ≤ C * |(lam i).im|)
    {f : ι → H} {f₀ : H} (hf : Tendsto f l (𝓝 f₀)) :
    Tendsto (fun i => (lam i - lam₀) • E.Res (lam i) (f i)) l (𝓝 (-(E.proj lam₀ f₀))) := by
  set μ₀ : ℝ := lam₀ + 1 with hμ₀
  set t₀ : ℝ := μ₀⁻¹ with ht₀
  have hμ₀c : ((lam₀ : ℂ) + 1) = (μ₀ : ℂ) := by rw [hμ₀]; push_cast; ring
  have hμ₀c0 : (μ₀ : ℂ) ≠ 0 := by exact_mod_cast h1
  have ht₀c : ((t₀ : ℝ) : ℂ) = ((lam₀ : ℂ) + 1)⁻¹ := by rw [hμ₀c, ht₀]; push_cast; ring
  set z : ι → ℂ := fun i => (lam i + 1)⁻¹ with hz
  have hμt : Tendsto (fun i => lam i + 1) l (𝓝 (μ₀ : ℂ)) := by
    rw [← hμ₀c]; exact hlam.add_const 1
  have hzt : Tendsto z l (𝓝 (t₀ : ℂ)) := by
    rw [ht₀c, hμ₀c]; exact hμt.inv₀ hμ₀c0
  have hμnorm : ∀ᶠ i in l, ‖lam i + 1‖ < |μ₀| + 1 := by
    have : Tendsto (fun i => ‖lam i + 1‖) l (𝓝 ‖(μ₀ : ℂ)‖) := hμt.norm
    rw [Complex.norm_real, Real.norm_eq_abs] at this
    exact this.eventually (gt_mem_nhds (by linarith))
  have hb : 0 < |μ₀| := abs_pos.mpr h1
  -- the cone condition for `z`
  have hzcone : ∀ᶠ i in l, ‖z i - t₀‖ ≤ (|C| * (|μ₀| + 1) / |μ₀|) * |(z i).im| := by
    filter_upwards [him, hcone, hμnorm] with i hi hci hni
    have hμim : (lam i + 1).im ≠ 0 := by simpa using hi
    have hμ0 : lam i + 1 ≠ 0 := fun h => hμim (by simp [h])
    have hm : 0 < ‖lam i + 1‖ := norm_pos_iff.mpr hμ0
    have e1 : z i - t₀ = ((lam₀ : ℂ) - lam i) / ((lam i + 1) * μ₀) := by
      rw [ht₀c, hμ₀c]; simp only [hz]; field_simp; rw [← hμ₀c]; ring
    have e2 : ‖z i - t₀‖ = ‖lam i - lam₀‖ / (‖lam i + 1‖ * |μ₀|) := by
      rw [e1, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_sub_rev]
    have e3 : |(z i).im| = |(lam i).im| / ‖lam i + 1‖ ^ 2 := by
      have e0 : (z i).im = -(lam i + 1).im / ‖lam i + 1‖ ^ 2 := by
        simp only [hz]
        rw [Complex.inv_im, Complex.normSq_eq_norm_sq]
      rw [e0, abs_div, abs_neg, abs_of_nonneg (sq_nonneg ‖lam i + 1‖)]
      simp
    rw [e2, e3]
    have hci' : ‖lam i - lam₀‖ ≤ |C| * |(lam i).im| :=
      hci.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (abs_nonneg _))
    have hy : 0 ≤ |(lam i).im| := abs_nonneg _
    calc ‖lam i - lam₀‖ / (‖lam i + 1‖ * |μ₀|)
        ≤ (|C| * |(lam i).im|) / (‖lam i + 1‖ * |μ₀|) := by gcongr
      _ = (|C| * |(lam i).im| * ‖lam i + 1‖) / (‖lam i + 1‖ ^ 2 * |μ₀|) := by
          field_simp
      _ ≤ (|C| * |(lam i).im| * (|μ₀| + 1)) / (‖lam i + 1‖ ^ 2 * |μ₀|) := by
          gcongr
      _ = |C| * (|μ₀| + 1) / |μ₀| * (|(lam i).im| / ‖lam i + 1‖ ^ 2) := by
          field_simp
  have hzim : ∀ᶠ i in l, (z i).im ≠ 0 := by
    filter_upwards [him] with i hi
    have hμim : (lam i + 1).im ≠ 0 := by simpa using hi
    have hμ0 : lam i + 1 ≠ 0 := fun h => hμim (by simp [h])
    simp only [hz]
    rw [Complex.inv_im]
    exact div_ne_zero (neg_ne_zero.mpr hμim) (Complex.normSq_pos.mpr hμ0).ne'
  have hres := tendsto_residue E.isSelfAdjoint_T t₀ hzt hzim hzcone hf
  -- assemble
  have hA : Tendsto (fun i => ((μ₀ : ℂ) * ((t₀ : ℂ) - z i)) • f i) l (𝓝 0) := by
    have h0 : Tendsto (fun i => (μ₀ : ℂ) * ((t₀ : ℂ) - z i)) l (𝓝 0) := by
      have := (tendsto_const_nhds (x := (t₀ : ℂ))).sub hzt
      rw [sub_self] at this
      simpa using this.const_mul (μ₀ : ℂ)
    simpa using h0.smul hf
  have hB : Tendsto (fun i => ((μ₀ : ℂ) * z i) •
      (((t₀ : ℂ) - z i) • shiftInv E.T (z i) (f i))) l
      (𝓝 (eigenProj E.T (t₀ : ℂ) f₀)) := by
    have h0 : Tendsto (fun i => (μ₀ : ℂ) * z i) l (𝓝 1) := by
      have := hzt.const_mul (μ₀ : ℂ)
      have e : (μ₀ : ℂ) * (t₀ : ℂ) = 1 := by
        rw [ht₀]; push_cast; exact mul_inv_cancel₀ hμ₀c0
      rwa [e] at this
    simpa using h0.smul hres
  have hAB := (hA.add hB).neg
  rw [zero_add] at hAB
  have hproj : E.proj lam₀ f₀ = eigenProj E.T (t₀ : ℂ) f₀ := by
    unfold proj; rw [ht₀c]
  rw [hproj]
  refine hAB.congr' ?_
  filter_upwards [him] with i hi
  have hμim : (lam i + 1).im ≠ 0 := by simpa using hi
  have hμ0 : lam i + 1 ≠ 0 := fun h => hμim (by simp [h])
  have key : (lam i - lam₀) * z i = (μ₀ : ℂ) * ((t₀ : ℂ) - z i) := by
    rw [ht₀c, hμ₀c]; simp only [hz]; field_simp; rw [← hμ₀c]; ring
  rw [E.Res_apply_eq hi]
  show _ = (lam i - lam₀) • -(z i • (f i + z i • shiftInv E.T (z i) (f i)))
  have : (lam i - lam₀) • -(z i • (f i + z i • shiftInv E.T (z i) (f i))) =
      (-((lam i - lam₀) * z i)) • (f i + z i • shiftInv E.T (z i) (f i)) := by
    rw [smul_neg, smul_smul, neg_smul]
  rw [this, key]
  module

/-- **The soft resolvent limit** (MATH §3.1, end; (C7)).  If `lamf` has derivative `lam' ≠ 0` at
`s₀`, `lamf s₀ = lam₀` real (`≠ -1`; in the application `lam₀ > 0`), and `s i → s₀`, `s i ≠ s₀`,
with `lamf (s i)` in a cone off the real axis, then for `f i → f₀` in `H`:
`(s i - s₀) • Res (lamf (s i)) (f i) → c₀ • P_{lam₀} f₀` with `c₀ = -1 / lam'`. -/
theorem tendsto_sub_smul_Res_comp {ι : Type*} {l : Filter ι} {lamf : ℂ → ℂ} {s₀ lam' : ℂ}
    {lam₀ : ℝ} {C : ℝ} (hd : HasDerivAt lamf lam' s₀) (hlam' : lam' ≠ 0)
    (h0 : lamf s₀ = lam₀) (h1 : lam₀ + 1 ≠ 0) {s : ι → ℂ} (hs : Tendsto s l (𝓝[≠] s₀))
    (him : ∀ᶠ i in l, (lamf (s i)).im ≠ 0)
    (hcone : ∀ᶠ i in l, ‖lamf (s i) - lam₀‖ ≤ C * |(lamf (s i)).im|)
    {f : ι → H} {f₀ : H} (hf : Tendsto f l (𝓝 f₀)) :
    Tendsto (fun i => (s i - s₀) • E.Res (lamf (s i)) (f i)) l
      (𝓝 ((-lam'⁻¹) • E.proj lam₀ f₀)) := by
  have hs' : Tendsto s l (𝓝 s₀) := hs.mono_right nhdsWithin_le_nhds
  have hlam : Tendsto (fun i => lamf (s i)) l (𝓝 (lam₀ : ℂ)) := by
    rw [← h0]; exact hd.continuousAt.tendsto.comp hs'
  have hmain := E.tendsto_sub_smul_Res h1 hlam him hcone hf
  have hslope : Tendsto (fun i => (slope lamf s₀ (s i))⁻¹) l (𝓝 lam'⁻¹) :=
    ((hd.tendsto_slope).comp hs).inv₀ hlam'
  have h2 := hslope.smul hmain
  have e : lam'⁻¹ • -(E.proj lam₀ f₀) = (-lam'⁻¹) • E.proj lam₀ f₀ := by
    rw [smul_neg, neg_smul]
  rw [e] at h2
  refine h2.congr' ?_
  filter_upwards [him] with i hi
  have hne : lamf (s i) - lam₀ ≠ 0 := by
    intro h
    apply hi
    rw [sub_eq_zero.mp h]; simp
  rw [smul_smul]
  congr 1
  rw [slope_def_field, h0, inv_div, div_mul_cancel₀ _ hne]

/-- Along a ray `s₀ + t d` (`t ↓ 0`) with `Im (lam' * d) ≠ 0`, `lamf` eventually takes non-real
values inside a cone around `lam₀`. -/
lemma eventually_cone_ray {lamf : ℂ → ℂ} {s₀ lam' : ℂ} {lam₀ : ℝ}
    (hd : HasDerivAt lamf lam' s₀) (h0 : lamf s₀ = lam₀) {d : ℂ} (hdir : (lam' * d).im ≠ 0) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, (lamf (s₀ + t * d)).im ≠ 0 ∧
      ‖lamf (s₀ + t * d) - lam₀‖ ≤
        (2 * (‖lam' * d‖ + 1) / |(lam' * d).im|) * |(lamf (s₀ + t * d)).im| := by
  have hd0 : d ≠ 0 := fun h => hdir (by simp [h])
  have hs : Tendsto (fun t : ℝ => s₀ + t * d) (𝓝[>] 0) (𝓝[≠] s₀) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have : Tendsto (fun t : ℝ => s₀ + (t : ℂ) * d) (𝓝 0) (𝓝 (s₀ + ((0 : ℝ) : ℂ) * d)) :=
        (Continuous.tendsto (by fun_prop) 0)
      simp only [Complex.ofReal_zero, zero_mul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
      simp [ht0, hd0]
  have hq : Tendsto (fun t : ℝ => slope lamf s₀ (s₀ + t * d) * d) (𝓝[>] 0) (𝓝 (lam' * d)) :=
    ((hd.tendsto_slope).comp hs).mul_const d
  have hw : 0 < |(lam' * d).im| := abs_pos.mpr hdir
  have h1 : ∀ᶠ t : ℝ in 𝓝[>] 0,
      |(lam' * d).im| / 2 < |(slope lamf s₀ (s₀ + t * d) * d).im| := by
    have : Tendsto (fun t : ℝ => |(slope lamf s₀ (s₀ + t * d) * d).im|) (𝓝[>] 0)
        (𝓝 |(lam' * d).im|) :=
      ((Complex.continuous_im.tendsto _).comp hq).abs
    exact this.eventually (lt_mem_nhds (by linarith))
  have h2 : ∀ᶠ t : ℝ in 𝓝[>] 0, ‖slope lamf s₀ (s₀ + t * d) * d‖ < ‖lam' * d‖ + 1 :=
    hq.norm.eventually (gt_mem_nhds (by linarith))
  filter_upwards [h1, h2, self_mem_nhdsWithin] with t ht1 ht2 ht
  have ht' : (0 : ℝ) < t := ht
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht')
  set q : ℂ := slope lamf s₀ (s₀ + t * d) * d with hq'
  have e : lamf (s₀ + t * d) - lam₀ = t * q := by
    rw [hq', slope_def_field, h0]
    field_simp
    ring
  have eim : (lamf (s₀ + t * d)).im = t * q.im := by
    have : lamf (s₀ + t * d) = lam₀ + t * q := by rw [← e]; ring
    rw [this]; simp
  have hqim : 0 < |q.im| := lt_trans (by positivity) ht1
  refine ⟨?_, ?_⟩
  · rw [eim]
    exact mul_ne_zero (ne_of_gt ht') (abs_pos.mp hqim)
  · rw [e, eim, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos ht']
    have h3 : (‖lam' * d‖ + 1) ≤
        2 * (‖lam' * d‖ + 1) / |(lam' * d).im| * |q.im| := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hw]
      nlinarith [norm_nonneg (lam' * d)]
    calc t * ‖q‖ ≤ t * (‖lam' * d‖ + 1) := by gcongr
      _ ≤ t * (2 * (‖lam' * d‖ + 1) / |(lam' * d).im| * |q.im|) := by gcongr
      _ = _ := by ring

/-- **The soft resolvent limit along a ray** `s_t = s₀ + t d`, `t ↓ 0`: the only condition on the
direction is `Im (lamf' s₀ * d) ≠ 0`.  The limit is `c₀ • P_{lam₀} f₀`, `c₀ = -1 / lamf' s₀`. -/
theorem tendsto_ray_smul_Res {lamf : ℂ → ℂ} {s₀ lam' : ℂ} {lam₀ : ℝ}
    (hd : HasDerivAt lamf lam' s₀) (h0 : lamf s₀ = lam₀) (h1 : lam₀ + 1 ≠ 0)
    {d : ℂ} (hdir : (lam' * d).im ≠ 0) {f : ℝ → H} {f₀ : H}
    (hf : Tendsto f (𝓝[>] 0) (𝓝 f₀)) :
    Tendsto (fun t : ℝ => ((s₀ + t * d) - s₀) • E.Res (lamf (s₀ + t * d)) (f t)) (𝓝[>] 0)
      (𝓝 ((-lam'⁻¹) • E.proj lam₀ f₀)) := by
  have hd0 : d ≠ 0 := fun h => hdir (by simp [h])
  have hlam' : lam' ≠ 0 := fun h => hdir (by simp [h])
  have hs : Tendsto (fun t : ℝ => s₀ + t * d) (𝓝[>] 0) (𝓝[≠] s₀) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have : Tendsto (fun t : ℝ => s₀ + (t : ℂ) * d) (𝓝 0) (𝓝 (s₀ + ((0 : ℝ) : ℂ) * d)) :=
        (Continuous.tendsto (by fun_prop) 0)
      simp only [Complex.ofReal_zero, zero_mul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
      simp [ht0, hd0]
  have hc := eventually_cone_ray hd h0 hdir
  exact E.tendsto_sub_smul_Res_comp hd hlam' h0 h1 hs (hc.mono fun _ h => h.1)
    (hc.mono fun _ h => h.2) hf

/-! ### Consequences (MATH (C6)–(C8)) -/

end EnergySpace

end

end ArtinKP.CAbs
end

section
-- module Solutions.Artin.KP.C5_Main
attribute [-simp] _root_.ArtinKP.S.GSection.nT_apply _root_.ArtinKP.S.GSection.twist_apply _root_.ArtinKP.S2.cubicSymbol_sym
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

lemma lam_four_thirds : lam F (4 / 3) = ((lam0 F : ℝ) : ℂ) := by
  unfold lam lam0
  push_cast
  ring

lemma lam0_add_one_ne_zero' : lam0 F + 1 ≠ 0 := by
  have h : (0 : ℝ) < lam0 F + 1 := by
    unfold lam0
    have := card_pos' (F := F)
    positivity
  exact h.ne'

lemma hasDerivAt_lam (s : ℂ) :
    HasDerivAt (lam F) ((Fintype.card (InfinitePlace F) : ℂ) * (2 - 2 * s)) s := by
  have h := (((hasDerivAt_id s).mul ((hasDerivAt_id s).const_sub 2)).const_mul
    (Fintype.card (InfinitePlace F) : ℂ))
  have e : (Fintype.card (InfinitePlace F) : ℂ) * (2 - 2 * s) =
      (Fintype.card (InfinitePlace F) : ℂ) * (1 * (2 - id s) + id s * -1) := by
    simp only [id]
    ring
  rw [e]
  exact h

/-! ### The classes in `L²(Γ\X)` -/

lemma srcL2_eq {Γ : Subgroup (SL(2, 𝓞 F))} {Ψ : TSection ι 𝔪} {s : ℂ}
    (h : X.L2Rep Γ (src Ψ s)) : srcL2 Γ Ψ s = X.toL2 Γ (src Ψ s) h := dif_pos h

variable [IsTotallyComplex F]

/-- **`s ↦ [F_s] ∈ L²(Γ\X)` is entire.** -/
theorem differentiable_srcL2 (hG : Good 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) : Differentiable ℂ fun s : ℂ => srcL2 Γ Ψ s := by
  have h𝔪 := hG.ne_bot
  have h := differentiable_toL2 (quotVol_lt_top hG Γ) (f := src Ψ)
    (fun s => (smooth_src h𝔪 Ψ s).continuous.measurable) (fun s => isInv_src h𝔪 hΓ s)
    (fun Q => differentiable_src h𝔪 Ψ Q)
    (fun s₀ => by
      obtain ⟨C, -, hC⟩ := exists_norm_src_le h𝔪 Ψ (‖s₀‖ + 1)
      refine ⟨1, C, one_pos, fun s hs Q => hC s ?_ Q⟩
      have h1 : ‖s - s₀‖ < 1 := by simpa [dist_eq_norm] using hs
      calc ‖s‖ = ‖s₀ + (s - s₀)‖ := by rw [add_sub_cancel]
        _ ≤ ‖s₀‖ + ‖s - s₀‖ := norm_add_le _ _
        _ ≤ ‖s₀‖ + 1 := by linarith)
    (fun s => l2Rep_src hG Γ hΓ s)
  have e : (fun s : ℂ => srcL2 Γ Ψ s) =
      fun s => X.toL2 Γ (src Ψ s) (l2Rep_src hG Γ hΓ s) := funext fun s => srcL2_eq _
  rw [e]
  exact h

/-! ### (C5) -/

/-! ### Continuation -/

/-! ### The limit (C7) -/

/-- **(C7)**: `(s_t − s₀) • (−Res(λ(s_t))[F_{s_t}]) → θ_Ψ = −c₀ P_{λ₀}[F_{s₀}]` in `L²(Γ\X)` along
the ray `s_t = 4/3 + t(1 + i)`, `t ↓ 0`. -/
theorem tendsto_ray_resPart (hG : Good 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) :
    Tendsto (fun t : ℝ => (((4 / 3 : ℂ) + t * (1 + Complex.I)) - 4 / 3) •
      resPart Γ Ψ ((4 / 3 : ℂ) + t * (1 + Complex.I))) (𝓝[>] 0) (𝓝 (theta Γ Ψ)) := by
  have hr := card_pos' (F := F)
  have hd := hasDerivAt_lam (F := F) (4 / 3)
  have hdir : ((Fintype.card (InfinitePlace F) : ℂ) * (2 - 2 * (4 / 3)) * (1 + Complex.I)).im ≠ 0 := by
    have e : (Fintype.card (InfinitePlace F) : ℂ) * (2 - 2 * (4 / 3)) * (1 + Complex.I) =
        ((-(2 / 3) * (Fintype.card (InfinitePlace F) : ℝ) : ℝ) : ℂ) * (1 + Complex.I) := by
      push_cast; ring
    rw [e, Complex.im_ofReal_mul]
    simp only [Complex.add_im, Complex.one_im, Complex.I_im, zero_add, mul_one]
    nlinarith
  have hf : Tendsto (fun t : ℝ => srcL2 Γ Ψ ((4 / 3 : ℂ) + t * (1 + Complex.I))) (𝓝[>] 0)
      (𝓝 (srcL2 Γ Ψ (4 / 3))) := by
    have hc : Continuous fun t : ℝ => srcL2 Γ Ψ ((4 / 3 : ℂ) + t * (1 + Complex.I)) :=
      (differentiable_srcL2 hG Γ hΓ).continuous.comp (by fun_prop)
    have := hc.tendsto 0
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h := (X.energy Γ).tendsto_ray_smul_Res hd lam_four_thirds (lam0_add_one_ne_zero' (F := F)) hdir hf
  have hc0 : -((Fintype.card (InfinitePlace F) : ℂ) * (2 - 2 * (4 / 3)))⁻¹ = c0 F := by
    have hr' : (Fintype.card (InfinitePlace F) : ℂ) ≠ 0 := by
      exact_mod_cast hr.ne'
    unfold c0
    field_simp
    ring
  rw [hc0] at h
  refine h.neg.congr fun t => ?_
  unfold resPart
  rw [smul_neg]

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

/-- Local pairings of the limit: `(s_t − s₀) ℓ(−Res(λ(s_t))[F_{s_t}]) → ℓ(θ_Ψ)`. -/
theorem tendsto_ray_functional_resPart_theta_oai (hG : Good 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) (ℓ : X.L2 Γ →L[ℂ] ℂ) :
    Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) *
      ℓ (resPart Γ Ψ ((4 / 3 : ℂ) + t * (1 + Complex.I)))) (𝓝[>] 0) (𝓝 (ℓ (theta Γ Ψ))) := by
  have h := (ℓ.continuous.tendsto _).comp (tendsto_ray_resPart hG Γ hΓ)
  refine h.congr fun t => ?_
  simp only [Function.comp_apply, map_smul, smul_eq_mul, add_sub_cancel_left]

/-! ### A bound for the cut-off part on compact sets -/

end

end ArtinKP.C5
end

theorem solution.{u_1} : type_of% @ArtinKP.C5.tendsto_ray_functional_resPart_theta_oai.{u_1} := @ArtinKP.C5.tendsto_ray_functional_resPart_theta_oai.{u_1}
