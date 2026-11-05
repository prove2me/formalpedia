-- Prove2me | Definitions.Def_ChapterSmFarisLavine
-- name    : ChapterSmFarisLavine
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-04T17:31:08.130634+00:00
-- url     : https://prove2.me/theorems/ac1d5ba6-3de3-4868-a6f5-c8766bdec8a1
-- title:
--   The Lean 4 theorem `norm_add_sq_re` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSmFarisLavine.lean`): generated def bundle for ChapterSmFarisLavine. See BookProof/ChapterSmFarisLavine.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSmFarisLavine.lean

import Theorems.Thm_BookProof_SmHamiltonian_smHamiltonian_quadForm_nonneg

import Theorems.Thm_BookProof_FarisLavine_quadForm_im

import Theorems.Thm_BookProof_SmHamiltonian_smField_symmetricOn

import Theorems.Thm_BookProof_SmHamiltonian_smHamiltonian_quadForm


import Theorems.Thm_BookProof_SmHamiltonian_smHamiltonian_symmetricOn


import Theorems.Thm_BookProof_YangMillsHermite_CoreRep_symmetricOn_op

import Theorems.Thm_BookProof_YangMillsHermite_mulOp_polySym

import Theorems.Thm_BookProof_YangMillsHermite_realCoeff_X

import Theorems.Thm_BookProof_QgOuterFockFL_friedrichsComparison_extends


import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_mul

import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_sum






import Theorems.Thm_BookProof_SmHamiltonian_smPi_symmetricOn

import Definitions.Def_ChapterSmComparison
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterSmHamiltonian
import Definitions.Def_ChapterSmOneParticle
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsHermite
import Mathlib
import Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_ext_essentiallySelfAdjointOn
import Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_ext_core
import Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_ext_norm_le
import Theorems.Thm_BookProof_FarisLavine_essentiallySelfAdjointOn_restrict_of_graph_core
import Theorems.Thm_BookProof_YangMillsHermite_CoreRep_op_apply
import Theorems.Thm_BookProof_YangMillsHermite_mulOp_apply
import Theorems.Thm_BookProof_YangMillsHermite_momOp_apply
import Theorems.Thm_BookProof_FarisLavine_inner_apply_self_im
import Theorems.Thm_BookProof_FarisLavine_commForm_eq
import Theorems.Thm_BookProof_QgOuterFockCoreFL_commForm_congr
import Theorems.Thm_BookProof_QgOuterFockCoreFL_quadForm_congr
import Theorems.Thm_BookProof_FriedrichsExtension_FormDom_dom_le_range
import Theorems.Thm_BookProof_FarisLavine_dense_range_of_deficiencyTrivialAt


/-!
# The Faris–Lavine data of the Standard-Model one-particle Hamiltonian

`CONSOLIDATED_PLAN.md` §D6b-SM Step 3 (handover §2026-09-23e) asks for the Faris–Lavine
hypotheses of the **bosonic** Standard-Model one-particle Hamiltonian `smHamiltonian P` of
`BookProof.ChapterSmHamiltonian`, and for the instantiation of Theorem 1 / Corollary 1.1 of
`BookProof.ChapterFarisLavineCore` that turns them into essential self-adjointness on the
Gauss–polynomial core of `L²(ℝ¹⁶³)`.

This module supplies

1. the **missing last mile** of the abstract machinery — `CoreData.esa_core`, which
   descends `CoreData.ext_essentiallySelfAdjointOn` from the comparison domain back to the
   graph core, so that what one gets is essential self-adjointness of the *given* operator
   on the *given* core;
2. the Standard-Model **Faris–Lavine comparison operator**
   `smFlN P c₀ = 2h + Σ_m q_m² + c₀`, its symmetry, its quadratic form, its positivity, and
   the Friedrichs `Comparison` built from it;
3. the two Faris–Lavine inequalities for the pair `(h, N)` on the core:
   * `sm_commForm_le` — `|⟪u, i[h, N]u⟫| ≤ ⟪u, N u⟫` (hypothesis (ii), constant `c = 1`);
   * `sm_norm_le_shift` — `‖h u‖ ≤ ‖(N + 1)u‖` (the relative bound, constant `K = 1`);
4. `sm_h_esa_of_graph_core` — essential self-adjointness of `smHamiltonian P` on
   `polyGaussCore 163`, from the single remaining hypothesis that the core is a graph core
   of the comparison operator;
5. `isGraphCore_of_esa` and **`sm_h_esa_of_comparison_esa`** — that hypothesis is implied by
   essential self-adjointness of the comparison operator itself on the same core, so the
   final statement is: *if `N = 2h + Σ_m q_m² + c₀` is essentially self-adjoint on
   `polyGaussCore 163`, then so is `h`.*

## Why the comparison operator is `2h + Σ q² + c₀` and not `smComparison`

The plan proposed `smComparison c₀ = Σ_m π_m² + Σ_s Ψ_s² + c₀` (quartic confinement in the
non-abelian and Higgs coordinates, quadratic in the abelian and the derivative coordinates)
as the Faris–Lavine comparison operator.  That operator **cannot** satisfy Faris–Lavine
hypothesis (ii) against `smHamiltonian`.  Writing `h = ½T + V_h` and `N = T + V_N + c₀`
with `T = Σ_m π_m²`, the commutator is first order,

`i[h, N] = Σ_m (π_m G_m + G_m π_m)`,  `G = ∇(½V_N − V_h)`,

and `± i[h,N] ≤ c N` forces the pointwise bound `|G|² ≤ c²(V_N + c₀)`: test the form on a
wave packet `e^{iξ·x}φ` concentrated at a point and optimize in `ξ`.  For `V_N = Σ_m q_m⁴`
the gradient `G` is cubic while `V_N` is quartic, and along a single gluon direction — where
the non-abelian magnetic energy and the covariant Higgs derivative both vanish, so that
`∇V_h = 0` there — the required bound reads `4R⁶ ≤ c²R⁴`, which fails for large `R`.  The
failure is already present for the free Hamiltonian: it is caused by the quartic confinement
of `N` itself, not by the interaction.

The cure is the one Faris and Lavine use in their own application: let the comparison
operator **contain the Hamiltonian**, so that `∇V_h` cancels.  With

`N = 2h + Σ_m q_m² + c₀`,  i.e. `V_N = 2V_h + Σ_m q_m²`,

one gets `G = ∇(½V_N − V_h) = ½∇(Σ_m q_m²)`, which is *linear*, and both Faris–Lavine
inequalities hold with the absolute constants `c = 1` and `K = 1` — this is what is proved
below, for **every** choice of couplings, structure constants and electroweak generators.

## Honest boundary

What is **not** proved here is `IsGraphCore (smFlComparison P hc₀) (polyGaussCore 163)`:
that the Gauss–polynomial core is dense, in the graph norm of the Friedrichs extension of
`N`, in the whole Friedrichs domain.  For a positive symmetric operator that property is
equivalent to essential self-adjointness of `N` on the core, and `N = 2h + Σ q² + c₀` is a
Schrödinger operator with a coupled quartic potential, exactly as hard as `h` itself.  So
the Faris–Lavine criterion, whichever comparison operator is chosen, cannot by itself close
the obligation: an independent essential-self-adjointness input (a Kato-type theorem for
`−Δ + V` with `V ≥ 0` in several variables) is required.  `sm_h_esa_of_graph_core` isolates
that input as a single hypothesis, and `sm_h_esa_of_comparison_esa` restates it in the
plainest possible form — essential self-adjointness of `N` on the same core.  Everything
else on the Faris–Lavine route is proved here.

**Discharged downstream.**  That hypothesis is proved in
`BookProof/ChapterSmComparisonEsa.lean` (`smFlN_esa`, from the Kato theorem
`BookProof.DegKatoEsa.ccHamS_esa` and the core transfer
`BookProof.HermiteGraphApprox.hamCoreS_esa`), which also states the unconditional
`BookProof.SmComparisonEsa.sm_h_esa`.

Everything in this module is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmFarisLavine

open MvPolynomial
open BookProof.SmOneParticle BookProof.SmHamiltonian
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.FriedrichsExtension
open BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL

noncomputable section

/-! ## 1. Two abstract lemmas -/

section Abstract

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The polarization identity in the form used below. -/
theorem norm_add_sq_re (u v : F) :
    ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + 2 * (inner ℂ u v : ℂ).re + ‖v‖ ^ 2 := by
  rw [@norm_add_sq ℂ]
  simp

variable [CompleteSpace F]

/-- **Faris–Lavine on the graph core.**  `CoreData.ext_essentiallySelfAdjointOn` gives
essential self-adjointness of the *extension* on the whole domain of the comparison
operator.  The relative bound transports the graph-norm approximation of the core from `N`
to the extension, so the restriction back to the core — which is the original operator
`H₀`, by `CoreData.ext_core` — is essentially self-adjoint as well.  This is the step that
turns the abstract criterion into a statement about the operator one started with. -/
theorem CoreData.esa_core (d : CoreData F) (hsym : SymmetricOn d.C₀ d.H₀) {c : ℝ}
    (hc : 0 ≤ c) (hcomm : ∀ p : d.C₀, |commForm d.H₀ d.coreN p| ≤ c * quadForm d.coreN p) :
    EssentiallySelfAdjointOn d.C₀ d.H₀ := by
  have hD : EssentiallySelfAdjointOn d.C.dom d.ext :=
    d.ext_essentiallySelfAdjointOn hsym hc hcomm
  have hcore : ∀ (x : d.C.dom) (ε : ℝ), 0 < ε → ∃ y : d.C.dom, (y : F) ∈ d.C₀ ∧
      ‖(y : F) - (x : F)‖ < ε ∧ ‖d.ext y - d.ext x‖ < ε := by
    intro x ε hε
    have hK : 0 ≤ d.K := d.hK
    set δ : ℝ := min ε (ε / (2 * d.K + 1)) with hδdef
    have hpos : (0 : ℝ) < 2 * d.K + 1 := by positivity
    have hδ : 0 < δ := lt_min hε (by positivity)
    obtain ⟨y, hyC, hy1, hy2⟩ := d.gc.approx x δ hδ
    refine ⟨y, hyC, lt_of_lt_of_le hy1 (min_le_left _ _), ?_⟩
    have hlin : d.ext y - d.ext x = d.ext (y - x) := by rw [map_sub]
    have hcoe : ((y - x : d.C.dom) : F) = (y : F) - (x : F) := rfl
    have hop : d.C.op (y - x) = d.C.op y - d.C.op x := by rw [map_sub]
    have hbd := d.ext_norm_le (y - x)
    rw [hop, hcoe] at hbd
    have htri : ‖(d.C.op y - d.C.op x) + ((y : F) - (x : F))‖
        ≤ ‖d.C.op y - d.C.op x‖ + ‖(y : F) - (x : F)‖ := norm_add_le _ _
    have hsum : ‖d.C.op y - d.C.op x‖ + ‖(y : F) - (x : F)‖ ≤ 2 * δ := by linarith
    have hfin : ‖d.ext (y - x)‖ ≤ d.K * (2 * δ) :=
      hbd.trans (mul_le_mul_of_nonneg_left (htri.trans hsum) hK)
    have hδ2 : δ ≤ ε / (2 * d.K + 1) := min_le_right _ _
    have h1 : (2 * d.K + 1) * δ ≤ ε := by
      rw [le_div_iff₀ hpos] at hδ2
      linarith
    have hlt : d.K * (2 * δ) < ε := by nlinarith
    rw [hlin]
    exact lt_of_le_of_lt hfin hlt
  have hres := essentiallySelfAdjointOn_restrict_of_graph_core d.gc.le d.ext hcore hD
  have hid : d.ext.comp (Submodule.inclusion d.gc.le) = d.H₀ := by
    refine LinearMap.ext fun p => ?_
    simpa only [LinearMap.comp_apply, Submodule.inclusion_apply] using d.ext_core p
  rwa [hid] at hres

end Abstract

/-! ## 2. The momentum coordinates and the harmonic operator -/

/-- The `40` momentum-carrying coordinates are pairwise distinct. -/
theorem smMomCoord_injective : Function.Injective smMomCoord := by
  intro a b h
  rcases a with ⟨a1, i1⟩ | ⟨k1, i1⟩ | i1 | a1 <;> rcases b with ⟨a2, i2⟩ | ⟨k2, i2⟩ | i2 | a2 <;>
    simp only [smMomCoord, smG, smW, smB, smPhi, EmbeddingLike.apply_eq_iff_eq] at h <;>
    simp_all

/-- The coordinate carrying the `m`-th momentum, in the labelling `smMomFin`. -/
def smCoord (m : Fin 40) : Fin 163 := smMomCoord (smMomFin.symm m)

theorem smCoord_injective : Function.Injective smCoord :=
  smMomCoord_injective.comp smMomFin.symm.injective

/-- The harmonic polynomial `Σ_m q_m²` over the `40` momentum-carrying coordinates. -/
def smQPoly : MvPolynomial (Fin 163) ℂ := ∑ m : Fin 40, X (smCoord m) * X (smCoord m)

theorem realCoeff_smQPoly : RealCoeff smQPoly :=
  RealCoeff.sum fun _ _ => (realCoeff_X _).mul (realCoeff_X _)

/-- `∂_{q_k}(Σ_m q_m²) = 2 q_k`. -/
theorem pderiv_smQPoly (k : Fin 40) :
    pderiv (smCoord k) smQPoly = (2 : ℂ) • X (smCoord k) := by
  classical
  rw [smQPoly, map_sum, Finset.sum_eq_single k]
  · rw [Derivation.leibniz]
    simp [two_smul]
  · intro m _ hm
    have hne : smCoord k ≠ smCoord m := fun hc => hm (smCoord_injective hc).symm
    rw [Derivation.leibniz]
    simp [pderiv_X, hne]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-! ### Transport of polynomial operators to the core -/

theorem op_comp (S T : Module.End ℂ (MvPolynomial (Fin 163) ℂ)) :
    ((coreRepPoly 163).op S).comp ((coreRepPoly 163).op T)
      = (coreRepPoly 163).op (S.comp T) := by
  refine LinearMap.ext fun x => ?_
  simp [CoreRep.op_apply]

theorem op_sum {ι : Type*} (s : Finset ι) (f : ι → Module.End ℂ (MvPolynomial (Fin 163) ℂ)) :
    (coreRepPoly 163).op (∑ i ∈ s, f i) = ∑ i ∈ s, (coreRepPoly 163).op (f i) := by
  classical
  refine LinearMap.ext fun x => ?_
  simp [CoreRep.op_apply, LinearMap.sum_apply, map_sum]

theorem op_add (S T : Module.End ℂ (MvPolynomial (Fin 163) ℂ)) :
    (coreRepPoly 163).op (S + T)
      = (coreRepPoly 163).op S + (coreRepPoly 163).op T := by
  refine LinearMap.ext fun x => ?_
  simp [CoreRep.op_apply]

theorem op_smul (c : ℂ) (S : Module.End ℂ (MvPolynomial (Fin 163) ℂ)) :
    (coreRepPoly 163).op (c • S) = c • (coreRepPoly 163).op S := by
  refine LinearMap.ext fun x => ?_
  simp [CoreRep.op_apply]

/-- Multiplication operators compose to multiplication by the product. -/
theorem mulOp_comp (a b : MvPolynomial (Fin 163) ℂ) :
    (mulOp a).comp (mulOp b) = mulOp (a * b) := by
  refine LinearMap.ext fun p => ?_
  simp [mulOp_apply, mul_assoc]

/-- **The canonical commutation relation on polynomials**:
`π_j (a·p) = a·(π_j p) − i (∂_j a) p`. -/
theorem momOp_mulOp (j : Fin 163) (a : MvPolynomial (Fin 163) ℂ) :
    (momOp j).comp (mulOp a)
      = (mulOp a).comp (momOp j) + (-Complex.I) • mulOp (pderiv j a) := by
  refine LinearMap.ext fun p => ?_
  have hleib : pderiv j (a * p) = a * pderiv j p + pderiv j a * p := by
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    ring
  simp only [LinearMap.comp_apply, mulOp_apply, momOp_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.neg_apply, hleib, neg_smul, smul_eq_C_mul]
  ring

/-! ## 3. The harmonic part of the comparison operator -/

/-- Multiplication by the `m`-th momentum-carrying coordinate. -/
def smMomField (m : Fin 40) :
    (polyGaussCore (d := 163)) →ₗ[ℂ] (polyGaussCore (d := 163)) :=
  (coreRepPoly 163).op (mulOp (X (smCoord m)))

set_option maxHeartbeats 2000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
theorem smMomField_symmetricOn (m : Fin 40) :
    SymmetricOn (polyGaussCore (d := 163))
      ((polyGaussCore (d := 163)).subtype.comp (smMomField m)) :=
  (coreRepPoly 163).symmetricOn_op (mulOp_polySym (realCoeff_X _))

/-- The harmonic operator `Σ_m q_m²` on the core. -/
def smQOp : (polyGaussCore (d := 163)) →ₗ[ℂ] (polyGaussCore (d := 163)) :=
  (coreRepPoly 163).op (mulOp smQPoly)

/-- The harmonic operator, into the ambient space. -/
def smQL : (polyGaussCore (d := 163)) →ₗ[ℂ] L2d 163 :=
  (polyGaussCore (d := 163)).subtype.comp smQOp

set_option maxHeartbeats 2000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
theorem smQL_symmetricOn : SymmetricOn (polyGaussCore (d := 163)) smQL :=
  (coreRepPoly 163).symmetricOn_op (mulOp_polySym realCoeff_smQPoly)

theorem smQL_apply (x : polyGaussCore (d := 163)) :
    smQL x = ((smQOp x : polyGaussCore (d := 163)) : L2d 163) := rfl

set_option maxHeartbeats 2000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- The harmonic operator is the sum of the squares of the coordinate multiplications. -/
theorem smQOp_eq_sum : smQOp = ∑ m : Fin 40, (smMomField m).comp (smMomField m) := by
  have hpoly : mulOp smQPoly
      = ∑ m : Fin 40, (mulOp (X (smCoord m))).comp (mulOp (X (smCoord m))) := by
    simp only [mulOp_comp]
    refine LinearMap.ext fun p => ?_
    simp [smQPoly, mulOp_apply, LinearMap.sum_apply, Finset.sum_mul]
  rw [smQOp, hpoly, op_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [smMomField, op_comp]

set_option maxHeartbeats 2000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
theorem smQOp_apply_sum (x : polyGaussCore (d := 163)) :
    smQOp x = ∑ m : Fin 40, smMomField m (smMomField m x) := by
  rw [smQOp_eq_sum]
  simp [LinearMap.sum_apply]

set_option maxHeartbeats 2000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- The quadratic form of the harmonic operator is the sum of the coordinate squares. -/
theorem smQL_quadForm (x : polyGaussCore (d := 163)) :
    quadForm smQL x
      = ∑ m : Fin 40, ‖((smMomField m x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2 := by
  have hval : smQL x
      = ∑ m : Fin 40,
        ((smMomField m (smMomField m x) : polyGaussCore (d := 163)) : L2d 163) := by
    rw [smQL, LinearMap.comp_apply, smQOp_apply_sum, map_sum]
    rfl
  rw [quadForm, hval, inner_sum]
  rw [Finset.sum_congr rfl fun m (_ : m ∈ Finset.univ) =>
    inner_sq_eq_normSq (smMomField_symmetricOn m) x]
  rw [← Complex.ofReal_sum]
  exact Complex.ofReal_re _

theorem smQL_quadForm_nonneg (x : polyGaussCore (d := 163)) : 0 ≤ quadForm smQL x := by
  rw [smQL_quadForm]
  positivity

/-! ## 4. The comparison operator -/

/-- **The Faris–Lavine comparison operator of the Standard Model**:
`N = 2h + Σ_m q_m² + c₀`, on the Gauss–polynomial core of `L²(ℝ¹⁶³)`. -/
def smFlN (P : SmParams) (c0 : ℝ) : (polyGaussCore (d := 163)) →ₗ[ℂ] L2d 163 :=
  (2 : ℂ) • smHamiltonian P + smQL + ((c0 : ℝ) : ℂ) • (polyGaussCore (d := 163)).subtype

theorem smFlN_apply (P : SmParams) (c0 : ℝ) (x : polyGaussCore (d := 163)) :
    smFlN P c0 x = (2 : ℂ) • smHamiltonian P x + smQL x
      + ((c0 : ℝ) : ℂ) • ((x : polyGaussCore (d := 163)) : L2d 163) := rfl

set_option maxHeartbeats 2000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
theorem smFlN_symmetricOn (P : SmParams) (c0 : ℝ) :
    SymmetricOn (polyGaussCore (d := 163)) (smFlN P c0) := by
  intro x y
  have hH := smHamiltonian_symmetricOn P x y
  have hQ := smQL_symmetricOn x y
  simp only [smFlN, LinearMap.add_apply, LinearMap.smul_apply, Submodule.subtype_apply,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    map_ofNat]
  rw [hH, hQ]

set_option maxHeartbeats 2000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- The quadratic form of the comparison operator: twice that of the Hamiltonian, plus the
harmonic squares, plus `c₀‖x‖²`. -/
theorem smFlN_quadForm (P : SmParams) (c0 : ℝ) (x : polyGaussCore (d := 163)) :
    quadForm (smFlN P c0) x
      = 2 * quadForm (smHamiltonian P) x + quadForm smQL x
        + c0 * ‖((x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2 := by
  have hself : (inner ℂ ((x : polyGaussCore (d := 163)) : L2d 163)
      ((x : polyGaussCore (d := 163)) : L2d 163) : ℂ)
      = ((‖((x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [quadForm, smFlN_apply, inner_add_right, inner_add_right, inner_smul_right,
    inner_smul_right, hself, Complex.add_re, Complex.add_re, Complex.mul_re, Complex.mul_re]
  simp only [Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [quadForm, quadForm]

theorem smFlN_quadForm_nonneg (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0)
    (x : polyGaussCore (d := 163)) : 0 ≤ quadForm (smFlN P c0) x := by
  rw [smFlN_quadForm]
  have h1 := smHamiltonian_quadForm_nonneg P x
  have h2 := smQL_quadForm_nonneg x
  have h3 : 0 ≤ c0 * ‖((x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2 := by positivity
  linarith

/-! ## 5. The commutator of the Hamiltonian with the harmonic operator -/

set_option maxHeartbeats 2000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- The commutator of a momentum with the harmonic operator, on the core. -/
theorem smPi_smQOp (m : Fin 40) (x : polyGaussCore (d := 163)) :
    smPi m (smQOp x) = smQOp (smPi m x) + ((-2 : ℂ) * Complex.I) • smMomField m x := by
  have hop : (smPi m).comp smQOp
      = smQOp.comp (smPi m) + ((-2 : ℂ) * Complex.I) • smMomField m := by
    have hpi : smPi m = (coreRepPoly 163).op (momOp (smCoord m)) := rfl
    have hsm : mulOp ((2 : ℂ) • X (smCoord m)) = (2 : ℂ) • mulOp (X (smCoord m)) := by
      refine LinearMap.ext fun p => ?_
      simp [mulOp_apply]
    rw [hpi, smQOp, op_comp, op_comp, momOp_mulOp, pderiv_smQPoly, hsm, smul_smul, op_add,
      op_smul, smMomField, ← op_comp]
    congr 2
    ring
  have hx := congrArg
    (fun T : polyGaussCore (d := 163) →ₗ[ℂ] polyGaussCore (d := 163) => T x) hop
  simpa using hx

set_option maxHeartbeats 2000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- Multiplication operators on the core commute. -/
theorem smField_comm_smQOp (P : SmParams) (r : Fin 49) (x : polyGaussCore (d := 163)) :
    smField P r (smQOp x) = smQOp (smField P r x) := by
  have hop : (smField P r).comp smQOp = smQOp.comp (smField P r) := by
    have h1 : smField P r
        = (coreRepPoly 163).op (mulOp (smFormPoly P (id : Fin 163 → Fin 163)
            (smFormFin.symm r))) := rfl
    rw [h1, smQOp, op_comp, op_comp, mulOp_comp, mulOp_comp, mul_comm]
  have hx := congrArg
    (fun T : polyGaussCore (d := 163) →ₗ[ℂ] polyGaussCore (d := 163) => T x) hop
  simpa using hx

set_option maxHeartbeats 2000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- The field squares contribute a *real*, non-negative amount to `⟪h x, Q x⟫`. -/
theorem inner_smField_sq_smQ (P : SmParams) (r : Fin 49) (x : polyGaussCore (d := 163)) :
    (inner ℂ ((smField P r (smField P r x) : polyGaussCore (d := 163)) : L2d 163)
      (smQL x) : ℂ)
      = ((quadForm smQL (smField P r x) : ℝ) : ℂ) := by
  have h1 := smField_symmetricOn P r (smField P r x) (smQOp x)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
  have hstep : (inner ℂ ((smField P r (smField P r x) : polyGaussCore (d := 163)) : L2d 163)
      (smQL x) : ℂ)
      = inner ℂ ((smField P r x : polyGaussCore (d := 163)) : L2d 163)
          (smQL (smField P r x)) := by
    rw [smQL_apply, h1, smQL_apply, smField_comm_smQOp P r x]
  rw [hstep]
  have him := quadForm_im smQL smQL_symmetricOn (smField P r x)
  refine Complex.ext ?_ ?_
  · simp [quadForm]
  · simpa using him

set_option maxHeartbeats 2000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- The momentum squares: `⟪π_m² x, Q x⟫ = ⟪π_m x, Q π_m x⟫ − 2i⟪π_m x, q_m x⟫`. -/
theorem inner_smPi_sq_smQ (m : Fin 40) (x : polyGaussCore (d := 163)) :
    (inner ℂ ((smPi m (smPi m x) : polyGaussCore (d := 163)) : L2d 163) (smQL x) : ℂ)
      = ((quadForm smQL (smPi m x) : ℝ) : ℂ)
        + ((-2 : ℂ) * Complex.I) * (inner ℂ ((smPi m x : polyGaussCore (d := 163)) : L2d 163)
            ((smMomField m x : polyGaussCore (d := 163)) : L2d 163) : ℂ) := by
  have hsym := smPi_symmetricOn m (smPi m x) (smQOp x)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hsym
  have hstep : (inner ℂ ((smPi m (smPi m x) : polyGaussCore (d := 163)) : L2d 163)
      (smQL x) : ℂ)
      = inner ℂ ((smPi m x : polyGaussCore (d := 163)) : L2d 163)
          ((smPi m (smQOp x) : polyGaussCore (d := 163)) : L2d 163) := by
    rw [smQL_apply, hsym]
  have hsplit : ((smPi m (smQOp x) : polyGaussCore (d := 163)) : L2d 163)
      = smQL (smPi m x)
        + ((-2 : ℂ) * Complex.I)
          • ((smMomField m x : polyGaussCore (d := 163)) : L2d 163) := by
    rw [smPi_smQOp m x]
    push_cast
    rfl
  rw [hstep, hsplit, inner_add_right, inner_smul_right]
  congr 1
  have him := quadForm_im smQL smQL_symmetricOn (smPi m x)
  refine Complex.ext ?_ ?_
  · simp [quadForm]
  · simpa using him

/-! ### The expansion of `⟪h x, w⟫` -/

set_option maxHeartbeats 2000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
theorem inner_smHamiltonian (P : SmParams) (x : polyGaussCore (d := 163)) (w : L2d 163) :
    (inner ℂ (smHamiltonian P x) w : ℂ)
      = ((1 / 2 : ℝ) : ℂ)
        * ((∑ m : Fin 40, (inner ℂ
              ((smPi m (smPi m x) : polyGaussCore (d := 163)) : L2d 163) w : ℂ))
          + ∑ r : Fin 49, (inner ℂ
              ((smField P r (smField P r x) : polyGaussCore (d := 163)) : L2d 163) w : ℂ)) := by
  have hval : smHamiltonian P x = ((1 / 2 : ℝ) : ℂ) •
      ((∑ m : Fin 40, ((smPi m (smPi m x) : polyGaussCore (d := 163)) : L2d 163))
        + ∑ r : Fin 49,
          ((smField P r (smField P r x) : polyGaussCore (d := 163)) : L2d 163)) :=
    weylOp_apply _ _ x
  rw [hval, inner_smul_left, Complex.conj_ofReal, inner_add_left, sum_inner, sum_inner]


theorem im_neg_two_I_mul (z : ℂ) : (((-2 : ℂ) * Complex.I) * z).im = -2 * z.re := by
  simp [Complex.mul_im, Complex.mul_re]

theorem re_neg_two_I_mul (z : ℂ) : (((-2 : ℂ) * Complex.I) * z).re = 2 * z.im := by
  simp [Complex.mul_re, Complex.mul_im]

set_option maxHeartbeats 2000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- The imaginary part of `⟪h x, Q x⟫` — the whole content of the commutator form. -/
theorem im_inner_smHamiltonian_smQL (P : SmParams) (x : polyGaussCore (d := 163)) :
    (inner ℂ (smHamiltonian P x) (smQL x) : ℂ).im
      = 1 / 2 * ∑ m : Fin 40, (-2) *
          (inner ℂ ((smPi m x : polyGaussCore (d := 163)) : L2d 163)
            ((smMomField m x : polyGaussCore (d := 163)) : L2d 163) : ℂ).re := by
  rw [inner_smHamiltonian,
    Finset.sum_congr rfl fun m (_ : m ∈ Finset.univ) => inner_smPi_sq_smQ m x,
    Finset.sum_congr rfl fun r (_ : r ∈ Finset.univ) => inner_smField_sq_smQ P r x,
    Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rw [Complex.add_im, Complex.im_sum, Complex.im_sum]
  simp only [Complex.add_im, Complex.ofReal_im, zero_add, im_neg_two_I_mul,
    Finset.sum_const_zero, add_zero]

set_option maxHeartbeats 2000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- The real part of `⟪h x, Q x⟫`: the harmonic quadratic forms, plus the cross terms. -/
theorem re_inner_smHamiltonian_smQL (P : SmParams) (x : polyGaussCore (d := 163)) :
    (inner ℂ (smHamiltonian P x) (smQL x) : ℂ).re
      = 1 / 2 * ((∑ m : Fin 40, (quadForm smQL (smPi m x)
            + 2 * (inner ℂ ((smPi m x : polyGaussCore (d := 163)) : L2d 163)
                ((smMomField m x : polyGaussCore (d := 163)) : L2d 163) : ℂ).im))
          + ∑ r : Fin 49, quadForm smQL (smField P r x)) := by
  rw [inner_smHamiltonian,
    Finset.sum_congr rfl fun m (_ : m ∈ Finset.univ) => inner_smPi_sq_smQ m x,
    Finset.sum_congr rfl fun r (_ : r ∈ Finset.univ) => inner_smField_sq_smQ P r x,
    Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [Complex.add_re, Complex.re_sum, Complex.re_sum]
  simp only [Complex.add_re, Complex.ofReal_re, re_neg_two_I_mul]

set_option maxHeartbeats 2000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- Only the harmonic summand of the comparison operator contributes to the commutator. -/
theorem im_inner_smHamiltonian_smFlN (P : SmParams) (c0 : ℝ)
    (x : polyGaussCore (d := 163)) :
    (inner ℂ (smHamiltonian P x) (smFlN P c0 x) : ℂ).im
      = (inner ℂ (smHamiltonian P x) (smQL x) : ℂ).im := by
  have h1 : (inner ℂ (smHamiltonian P x) (smHamiltonian P x) : ℂ).im = 0 := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have h2 : (inner ℂ (smHamiltonian P x)
      ((x : polyGaussCore (d := 163)) : L2d 163) : ℂ).im = 0 :=
    inner_apply_self_im (smHamiltonian P) (smHamiltonian_symmetricOn P) x
  rw [smFlN_apply, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
    Complex.add_im, Complex.add_im, Complex.mul_im, Complex.mul_im, h1, h2]
  simp

/-- The Cauchy–Schwarz estimate of one cross term. -/
theorem abs_re_inner_smPi_smMom_le (m : Fin 40) (x : polyGaussCore (d := 163)) :
    |(inner ℂ ((smPi m x : polyGaussCore (d := 163)) : L2d 163)
        ((smMomField m x : polyGaussCore (d := 163)) : L2d 163) : ℂ).re|
      ≤ 1 / 2 * (‖((smPi m x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2
        + ‖((smMomField m x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2) := by
  have h := (Complex.abs_re_le_norm
    (inner ℂ ((smPi m x : polyGaussCore (d := 163)) : L2d 163)
      ((smMomField m x : polyGaussCore (d := 163)) : L2d 163) : ℂ)).trans
    (norm_inner_le_norm _ _)
  nlinarith [sq_nonneg (‖((smPi m x : polyGaussCore (d := 163)) : L2d 163)‖
    - ‖((smMomField m x : polyGaussCore (d := 163)) : L2d 163)‖)]

/-- The same estimate for the imaginary part. -/
theorem abs_im_inner_smPi_smMom_le (m : Fin 40) (x : polyGaussCore (d := 163)) :
    |(inner ℂ ((smPi m x : polyGaussCore (d := 163)) : L2d 163)
        ((smMomField m x : polyGaussCore (d := 163)) : L2d 163) : ℂ).im|
      ≤ 1 / 2 * (‖((smPi m x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2
        + ‖((smMomField m x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2) := by
  have h := (Complex.abs_im_le_norm
    (inner ℂ ((smPi m x : polyGaussCore (d := 163)) : L2d 163)
      ((smMomField m x : polyGaussCore (d := 163)) : L2d 163) : ℂ)).trans
    (norm_inner_le_norm _ _)
  nlinarith [sq_nonneg (‖((smPi m x : polyGaussCore (d := 163)) : L2d 163)‖
    - ‖((smMomField m x : polyGaussCore (d := 163)) : L2d 163)‖)]

set_option maxHeartbeats 2000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- **Faris–Lavine hypothesis (ii) for the Standard Model.**  With the comparison operator
`N = 2h + Σ_m q_m² + c₀` the commutator form is bounded by the quadratic form of `N` with
the absolute constant `c = 1`, for every set of couplings, structure constants and
electroweak generators and every `c₀ ≥ 0`. -/
theorem sm_commForm_le (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0)
    (x : polyGaussCore (d := 163)) :
    |commForm (smHamiltonian P) (smFlN P c0) x| ≤ 1 * quadForm (smFlN P c0) x := by
  set kin : ℝ := ∑ m : Fin 40,
    ‖((smPi m x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2 with hkin
  set har : ℝ := ∑ m : Fin 40,
    ‖((smMomField m x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2 with hhar
  set S : ℝ := ∑ m : Fin 40, (inner ℂ ((smPi m x : polyGaussCore (d := 163)) : L2d 163)
    ((smMomField m x : polyGaussCore (d := 163)) : L2d 163) : ℂ).re with hS
  have hform : commForm (smHamiltonian P) (smFlN P c0) x = 2 * S := by
    rw [commForm_eq, im_inner_smHamiltonian_smFlN, im_inner_smHamiltonian_smQL, hS,
      ← Finset.mul_sum]
    ring
  have hSbound : |S| ≤ 1 / 2 * (kin + har) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [hkin, hhar, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_le_sum fun m _ => abs_re_inner_smPi_smMom_le m x
  have hquad : kin + har ≤ quadForm (smFlN P c0) x := by
    rw [smFlN_quadForm, smHamiltonian_quadForm P, smQL_quadForm]
    have hf : (0 : ℝ) ≤ ∑ r : Fin 49,
        ‖((smField P r x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => by positivity
    have hx : (0 : ℝ) ≤ c0 * ‖((x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2 := by positivity
    rw [hkin, hhar]
    linarith
  rw [hform, one_mul, abs_mul, abs_two]
  linarith [hSbound]

set_option maxHeartbeats 2000000 in
-- the `L²`-coercion unifications of the 163-dimensional core exceed the default budget
/-- **The relative bound for the Standard Model**: `‖h u‖ ≤ ‖(N + 1)u‖` on the core, with
the absolute constant `K = 1`. -/
theorem sm_norm_le_shift (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0)
    (x : polyGaussCore (d := 163)) :
    ‖smHamiltonian P x‖
      ≤ 1 * ‖smFlN P c0 x + ((x : polyGaussCore (d := 163)) : L2d 163)‖ := by
  set kin : ℝ := ∑ m : Fin 40,
    ‖((smPi m x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2 with hkin
  set har : ℝ := ∑ m : Fin 40,
    ‖((smMomField m x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2 with hhar
  set fld : ℝ := ∑ r : Fin 49,
    ‖((smField P r x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2 with hfld
  set nx : ℝ := ‖((x : polyGaussCore (d := 163)) : L2d 163)‖ with hnx
  set nH : ℝ := ‖smHamiltonian P x‖ with hnH
  set b : L2d 163 := smQL x
    + (((c0 + 1 : ℝ)) : ℂ) • ((x : polyGaussCore (d := 163)) : L2d 163) with hb
  have hharnn : 0 ≤ har := by
    rw [hhar]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hkinnn : 0 ≤ kin := by
    rw [hkin]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hfldnn : 0 ≤ fld := by
    rw [hfld]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hnxnn : 0 ≤ nx := by rw [hnx]; exact norm_nonneg _
  have hnHnn : 0 ≤ nH := by rw [hnH]; exact norm_nonneg _
  have hsum : smFlN P c0 x + ((x : polyGaussCore (d := 163)) : L2d 163)
      = (2 : ℂ) • smHamiltonian P x + b := by
    rw [smFlN_apply, hb]
    push_cast
    module
  -- the quadratic form of the Hamiltonian
  have hHself : (inner ℂ (smHamiltonian P x)
      ((x : polyGaussCore (d := 163)) : L2d 163) : ℂ).re = quadForm (smHamiltonian P) x := by
    have h := smHamiltonian_symmetricOn P x x
    rw [quadForm, ← h]
  have hqH : quadForm (smHamiltonian P) x = 1 / 2 * kin + 1 / 2 * fld := by
    rw [smHamiltonian_quadForm P, hkin, hfld]
  have hqHnn : 0 ≤ quadForm (smHamiltonian P) x := smHamiltonian_quadForm_nonneg P x
  -- the cross term
  have hcrossge : -(1 / 2) * (kin + har)
      ≤ (inner ℂ (smHamiltonian P x) (smQL x) : ℂ).re := by
    rw [re_inner_smHamiltonian_smQL]
    have h1 : ∀ m : Fin 40, -(‖((smPi m x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2
        + ‖((smMomField m x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2)
        ≤ quadForm smQL (smPi m x)
          + 2 * (inner ℂ ((smPi m x : polyGaussCore (d := 163)) : L2d 163)
              ((smMomField m x : polyGaussCore (d := 163)) : L2d 163) : ℂ).im := by
      intro m
      have ha := abs_im_inner_smPi_smMom_le m x
      have hq := smQL_quadForm_nonneg (smPi m x)
      have hb2 := neg_abs_le (inner ℂ ((smPi m x : polyGaussCore (d := 163)) : L2d 163)
        ((smMomField m x : polyGaussCore (d := 163)) : L2d 163) : ℂ).im
      linarith
    have h2 : -(kin + har) ≤ ∑ m : Fin 40, (quadForm smQL (smPi m x)
        + 2 * (inner ℂ ((smPi m x : polyGaussCore (d := 163)) : L2d 163)
            ((smMomField m x : polyGaussCore (d := 163)) : L2d 163) : ℂ).im) := by
      have heq : (∑ m : Fin 40, -(‖((smPi m x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2
          + ‖((smMomField m x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2)) = -(kin + har) := by
        rw [Finset.sum_neg_distrib, Finset.sum_add_distrib, hkin, hhar]
      rw [← heq]
      exact Finset.sum_le_sum fun m _ => h1 m
    have h3 : (0 : ℝ) ≤ ∑ r : Fin 49, quadForm smQL (smField P r x) :=
      Finset.sum_nonneg fun r _ => smQL_quadForm_nonneg (smField P r x)
    linarith
  -- the square of the harmonic part
  have hQself : (inner ℂ (smQL x) ((x : polyGaussCore (d := 163)) : L2d 163) : ℂ).re = har := by
    have h := smQL_symmetricOn x x
    have hq := smQL_quadForm x
    rw [quadForm] at hq
    rw [h, hq, hhar]
  have hbsq : 2 * har + nx ^ 2 ≤ ‖b‖ ^ 2 := by
    have hexp : ‖b‖ ^ 2 = ‖smQL x‖ ^ 2
        + 2 * ((c0 + 1) * (inner ℂ (smQL x)
            ((x : polyGaussCore (d := 163)) : L2d 163) : ℂ).re) + (c0 + 1) ^ 2 * nx ^ 2 := by
      rw [hb, norm_add_sq_re, inner_smul_right, norm_smul]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      rw [hnx]
    rw [hexp, hQself]
    have h1 : (0 : ℝ) ≤ ‖smQL x‖ ^ 2 := sq_nonneg _
    nlinarith [h1, mul_nonneg hc0 hharnn, mul_nonneg (mul_nonneg hc0 hc0) (sq_nonneg nx),
      mul_nonneg hc0 (sq_nonneg nx)]
  -- the main inequality
  have hmain : 2 * nH ^ 2 - nx ^ 2
      ≤ ‖smFlN P c0 x + ((x : polyGaussCore (d := 163)) : L2d 163)‖ ^ 2 := by
    rw [hsum, norm_add_sq_re]
    have hcross : (inner ℂ ((2 : ℂ) • smHamiltonian P x) b : ℂ).re
        = 2 * ((inner ℂ (smHamiltonian P x) (smQL x) : ℂ).re
          + (c0 + 1) * (inner ℂ (smHamiltonian P x)
              ((x : polyGaussCore (d := 163)) : L2d 163) : ℂ).re) := by
      rw [hb, inner_smul_left, inner_add_right, inner_smul_right]
      simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        map_ofNat, Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, add_zero]
    have hnormsq : ‖(2 : ℂ) • smHamiltonian P x‖ ^ 2 = 4 * nH ^ 2 := by
      rw [norm_smul, hnH, mul_pow]
      norm_num
    have hkinle : kin ≤ nH ^ 2 + nx ^ 2 := by
      have h1 : 1 / 2 * kin + 1 / 2 * fld ≤ nx * nH := by
        rw [← hqH, ← hHself]
        calc (inner ℂ (smHamiltonian P x)
              ((x : polyGaussCore (d := 163)) : L2d 163) : ℂ).re
            ≤ ‖(inner ℂ (smHamiltonian P x)
                ((x : polyGaussCore (d := 163)) : L2d 163) : ℂ)‖ := Complex.re_le_norm _
          _ ≤ nH * nx := norm_inner_le_norm _ _
          _ = nx * nH := by ring
      nlinarith [sq_nonneg (nH - nx)]
    rw [hnormsq, hcross, hHself]
    nlinarith [hcrossge, hbsq, hkinle, hqHnn, hc0]
  have hxle : nx ≤ ‖smFlN P c0 x + ((x : polyGaussCore (d := 163)) : L2d 163)‖ :=
    norm_le_norm_shift (smFlN P c0) (smFlN_quadForm_nonneg P hc0) x
  have hSnn : 0 ≤ ‖smFlN P c0 x + ((x : polyGaussCore (d := 163)) : L2d 163)‖ := norm_nonneg _
  rw [one_mul]
  nlinarith [hmain, hxle, hnxnn, hnHnn, hSnn]

/-! ## 7. The comparison operator and the conditional conclusion -/

/-- The comparison operator as a positive symmetric operator on the core. -/
def smFlPosSymOp (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0) : PosSymOp (L2d 163) where
  dom := polyGaussCore (d := 163)
  op := smFlN P c0
  sym := smFlN_symmetricOn P c0
  pos := smFlN_quadForm_nonneg P hc0

/-- **The Faris–Lavine comparison operator of the Standard Model**, as a `Comparison`: the
Friedrichs extension of `N = 2h + Σ_m q_m² + c₀`, for which `N + 1` is onto by
construction. -/
def smFlComparison (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0) : Comparison (L2d 163) :=
  friedrichsComparison (smFlPosSymOp P hc0) polyGaussCore_dense

theorem smFlComparison_extends (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0)
    (x : polyGaussCore (d := 163)) :
    ∃ h : ((x : polyGaussCore (d := 163)) : L2d 163) ∈ (smFlComparison P hc0).dom,
      (smFlComparison P hc0).op ⟨((x : polyGaussCore (d := 163)) : L2d 163), h⟩
        = smFlN P c0 x :=
  friedrichsComparison_extends (smFlPosSymOp P hc0) polyGaussCore_dense x

/-- The `CoreData` package of the Standard Model, given the graph-core hypothesis. -/
def smCoreData (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0)
    (hgc : IsGraphCore (smFlComparison P hc0) (polyGaussCore (d := 163))) :
    CoreData (L2d 163) where
  C := smFlComparison P hc0
  C₀ := polyGaussCore (d := 163)
  gc := hgc
  H₀ := smHamiltonian P
  K := 1
  hK := zero_le_one
  rel := by
    intro p
    obtain ⟨h, hx⟩ := smFlComparison_extends P hc0 p
    have hpt : (smFlComparison P hc0).op
        ⟨((p : polyGaussCore (d := 163)) : L2d 163), hgc.le p.2⟩ = smFlN P c0 p := hx
    rw [hpt]
    exact sm_norm_le_shift P hc0 p

/-- **The Standard-Model one-particle Hamiltonian is essentially self-adjoint on the
Gauss–polynomial core, given the graph-core property of the Faris–Lavine comparison
operator.**  Both Faris–Lavine inequalities are proved above with absolute constants; the
hypothesis `hgc` — that the Gauss–polynomial core is dense in the graph norm of the
Friedrichs extension of `N = 2h + Σ_m q_m² + c₀` — is the one analytic input that the
criterion cannot supply by itself. -/
theorem sm_h_esa_of_graph_core (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0)
    (hgc : IsGraphCore (smFlComparison P hc0) (polyGaussCore (d := 163))) :
    EssentiallySelfAdjointOn (polyGaussCore (d := 163)) (smHamiltonian P) := by
  refine CoreData.esa_core (smCoreData P hc0 hgc) (smHamiltonian_symmetricOn P)
    zero_le_one fun p => ?_
  obtain ⟨h, hx⟩ := smFlComparison_extends P hc0 p
  have hcoreN : (smCoreData P hc0 hgc).coreN p = smFlN P c0 p := hx
  have h1 : commForm (smCoreData P hc0 hgc).H₀ (smCoreData P hc0 hgc).coreN p
      = commForm (smHamiltonian P) (smFlN P c0) p :=
    commForm_congr _ _ _ _ _ _ rfl hcoreN
  have h2 : quadForm (smCoreData P hc0 hgc).coreN p = quadForm (smFlN P c0) p :=
    quadForm_congr _ _ _ _ rfl hcoreN
  rw [h1, h2]
  exact sm_commForm_le P hc0 p


/-! ## 8. Removing the graph-core hypothesis in favour of essential self-adjointness of `N` -/

section GraphCoreFromEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- For a symmetric operator, the shift by `i` is bounded below: `‖z‖ ≤ ‖A z + i z‖`. -/
theorem norm_le_norm_shift_I {D : Submodule ℂ F} (A : D →ₗ[ℂ] F) (hA : SymmetricOn D A)
    (z : D) : ‖(z : F)‖ ≤ ‖A z - (-Complex.I) • (z : F)‖ := by
  have hre : (inner ℂ (A z) ((z : F)) : ℂ).im = 0 := inner_apply_self_im A hA z
  have hrw : A z - (-Complex.I) • (z : F) = A z + Complex.I • (z : F) := by module
  have hcross : (inner ℂ (A z) (Complex.I • (z : F)) : ℂ).re = 0 := by
    rw [inner_smul_right, Complex.mul_re, Complex.I_re, Complex.I_im, hre]
    ring
  have hnorm : ‖Complex.I • (z : F)‖ = ‖(z : F)‖ := by
    rw [norm_smul]
    simp
  have hexp : ‖A z - (-Complex.I) • (z : F)‖ ^ 2 = ‖A z‖ ^ 2 + ‖(z : F)‖ ^ 2 := by
    rw [hrw, norm_add_sq_re, hcross, hnorm]
    ring
  nlinarith [norm_nonneg (A z), norm_nonneg ((z : F)),
    norm_nonneg (A z - (-Complex.I) • (z : F)), hexp]

/-- **A core of an essentially self-adjoint positive operator is a graph core of its
Friedrichs comparison operator.**  If `P` is essentially self-adjoint on its domain then
`P + i` has dense range there, and the bound `‖z‖ ≤ ‖(N + i)z‖` for the symmetric Friedrichs
extension `N` transports that density back to the graph norm of `N`. -/
theorem isGraphCore_of_esa (P : PosSymOp F) (hdense : Dense (P.dom : Set F))
    (hesa : EssentiallySelfAdjointOn P.dom P.op) :
    IsGraphCore (friedrichsComparison P hdense) P.dom := by
  set C : Comparison F := friedrichsComparison P hdense with hC
  have hle : P.dom ≤ C.dom := fun _ hv => FormDom.dom_le_range P hv
  have hext : ∀ y : P.dom, C.op ⟨(y : F), hle y.2⟩ = P.op y := by
    intro y
    obtain ⟨h, hh⟩ := friedrichsComparison_extends P hdense y
    exact hh
  refine ⟨hle, ?_⟩
  intro x ε hε
  have hconj : (starRingEnd ℂ) (-Complex.I) = Complex.I := by simp
  have hdr : Dense (Set.range fun y : P.dom => P.op y - (-Complex.I) • (y : F)) :=
    dense_range_of_deficiencyTrivialAt P.op (-Complex.I) (by rw [hconj]; exact hesa.1)
  obtain ⟨g, hgball, y, hy⟩ :=
    Metric.dense_iff.mp hdr (C.op x - (-Complex.I) • (x : F)) (ε / 2) (by positivity)
  have hdist : ‖g - (C.op x - (-Complex.I) • (x : F))‖ < ε / 2 := by
    have hball := Metric.mem_ball.mp hgball
    rwa [dist_eq_norm] at hball
  refine ⟨⟨(y : F), hle y.2⟩, y.2, ?_, ?_⟩
  · have hb := norm_le_norm_shift_I C.op C.sym (⟨(y : F), hle y.2⟩ - x)
    have hkey : C.op (⟨(y : F), hle y.2⟩ - x)
        - (-Complex.I) • ((⟨(y : F), hle y.2⟩ - x : C.dom) : F)
        = g - (C.op x - (-Complex.I) • (x : F)) := by
      have hcoe : ((⟨(y : F), hle y.2⟩ - x : C.dom) : F) = (y : F) - (x : F) := rfl
      rw [map_sub, hext y, hcoe, ← hy]
      module
    rw [hkey] at hb
    have hb' : ‖((y : F)) - (x : F)‖ ≤ ‖g - (C.op x - (-Complex.I) • (x : F))‖ := hb
    linarith
  · have hkey : C.op (⟨(y : F), hle y.2⟩ - x)
        - (-Complex.I) • ((⟨(y : F), hle y.2⟩ - x : C.dom) : F)
        = g - (C.op x - (-Complex.I) • (x : F)) := by
      have hcoe : ((⟨(y : F), hle y.2⟩ - x : C.dom) : F) = (y : F) - (x : F) := rfl
      rw [map_sub, hext y, hcoe, ← hy]
      module
    have hb := norm_le_norm_shift_I C.op C.sym (⟨(y : F), hle y.2⟩ - x)
    rw [hkey] at hb
    have hb' : ‖((y : F)) - (x : F)‖ ≤ ‖g - (C.op x - (-Complex.I) • (x : F))‖ := hb
    have hmapsub : C.op (⟨(y : F), hle y.2⟩ - x)
        = C.op ⟨(y : F), hle y.2⟩ - C.op x := map_sub _ _ _
    rw [hmapsub] at hkey
    have hsplit : C.op ⟨(y : F), hle y.2⟩ - C.op x
        = (g - (C.op x - (-Complex.I) • (x : F)))
          + (-Complex.I) • (((y : F)) - (x : F)) := by
      have hcoe : ((⟨(y : F), hle y.2⟩ - x : C.dom) : F) = (y : F) - (x : F) := rfl
      rw [hcoe] at hkey
      exact sub_eq_iff_eq_add.mp hkey
    have hns : ‖(-Complex.I) • (((y : F)) - (x : F))‖ = ‖((y : F)) - (x : F)‖ := by
      rw [norm_smul]
      simp
    calc ‖C.op ⟨(y : F), hle y.2⟩ - C.op x‖
        ≤ ‖g - (C.op x - (-Complex.I) • (x : F))‖
          + ‖(-Complex.I) • (((y : F)) - (x : F))‖ := by
          rw [hsplit]; exact norm_add_le _ _
      _ = ‖g - (C.op x - (-Complex.I) • (x : F))‖ + ‖((y : F)) - (x : F)‖ := by rw [hns]
      _ < ε := by linarith

end GraphCoreFromEsa

/-- **The Standard-Model one-particle Hamiltonian is essentially self-adjoint on the
Gauss–polynomial core as soon as its Faris–Lavine comparison operator is.**  This is the
sharpest unconditional reduction the criterion allows: the two Faris–Lavine inequalities are
theorems, and the only remaining input is essential self-adjointness of
`N = 2h + Σ_m q_m² + c₀` on the same core.  Since `N` is itself a Schrödinger operator with
a coupled quartic potential in `163` variables, that input is of Kato type and is *not*
supplied by Faris–Lavine. -/
theorem sm_h_esa_of_comparison_esa (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0)
    (hN : EssentiallySelfAdjointOn (polyGaussCore (d := 163)) (smFlN P c0)) :
    EssentiallySelfAdjointOn (polyGaussCore (d := 163)) (smHamiltonian P) :=
  sm_h_esa_of_graph_core P hc0
    (isGraphCore_of_esa (smFlPosSymOp P hc0) polyGaussCore_dense hN)

end

end BookProof.SmFarisLavine


