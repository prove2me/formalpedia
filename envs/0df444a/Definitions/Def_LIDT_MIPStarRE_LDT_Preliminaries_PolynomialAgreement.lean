-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
-- name    : LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:32:13.754986+00:00
-- url     : https://prove2.me/theorems/553ee2ec-83f6-4a6e-86bf-964bba1e333e
-- title:
--   LIDT definitions: LDT / Preliminaries / PolynomialAgreement
-- statement:
--   This bundle connects the coded finite-field representation to scalar polynomial agreement estimates. It reindexes point and axis-line evaluations, applies the Schwartz-Zippel bounds to distinct outcomes, and packages the collision mass used in the main error cascade.
--
--   Principal definitions:
--   - `pointScalarEquiv`: coordinatewise equivalence between coded field points and the scalar field model.
--   - `polynomialAgreement_avg_eq_scalarDomain`: reindexing identity from coded point averaging to the scalar-domain evaluation average.
--   - `polynomialAgreement_avg_le_mdq`: the agreement probability bound for two distinct full polynomial outcomes.
--   - `axisLinePolynomialAgreement_avg_eq_scalarDomain`: the corresponding reindexing identity for degree-`d` axis-line polynomials.
--   - `axisLinePolynomialAgreement_avg_le_mdq`: the axis-line agreement bound with the `m d / q` loss.
--   - `polynomialCollision_sandwichTensor_le_mdq`: the tensor-form collision bound for polynomial outcomes.
--   - `polynomialCollisionMass`: the off-diagonal polynomial-collision mass used in the fifth main-theorem step.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Preliminaries/PolynomialAgreement.lean#L38-L400

-- Generated from MIPStarRE/LDT/Preliminaries/PolynomialAgreement.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic

namespace LIDT

/-!
# Polynomial agreement bound (Step 5 hammer)

Public packaging of Schwartz-Zippel for the project's `Polynomial params`
class. This is the building block invoked at:

* paper `references/ldt-paper/inductive_step.tex`, lines 119–133 — the
  `md/q` term in the `mainFormal` self-consistency cascade,
* paper `references/ldt-paper/commutativity-G.tex`, the analogous step in
  `comMain` (issue #297).

The earlier private form of this lemma lived in
`MIPStarRE.LDT.Commutativity.Scaffold.Symmetry`. Promoting it lets both `comMain`
and `mainFormal` Step 5 (#425) share one proof.

## References

* `references/ldt-paper/inductive_step.tex`
* `references/ldt-paper/preliminaries.tex`, Section 3
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- Coordinatewise transport between coded `F_q` points and the underlying
scalar model. This is the equivalence used to apply Schwartz-Zippel inside
`MvPolynomial`'s scalar function space. -/
def pointScalarEquiv (params : Parameters) [FieldModel params.q] :
    Point params ≃ (Fin params.m → Scalar params) where
  toFun := decodePoint
  invFun := fun u i => encodeScalar (u i)
  left_inv := fun u => by funext i; simp [decodePoint, encode_decodeScalar]
  right_inv := fun u => by funext i; simp [decodePoint, decode_encodeScalar]

/-- Reindex evaluation equality from coded `Point params` points to the scalar
function space used by `schwartzZippel_individualDegree`. -/
lemma polynomialAgreement_avg_eq_scalarDomain
    (params : Parameters) [FieldModel params.q]
    (g g' : Polynomial params) :
    avgOver (uniformDistribution (Point params))
      (fun u => if g u = g' u then (1 : Error) else 0) =
      avgOver (uniformDistribution (Fin params.m → Scalar params))
        (fun u =>
          if MvPolynomial.eval u g.poly = MvPolynomial.eval u g'.poly then
            (1 : Error)
          else 0) := by
  let e := pointScalarEquiv params
  calc
    avgOver (uniformDistribution (Point params))
        (fun u => if g u = g' u then (1 : Error) else 0)
      = avgOver (uniformDistribution (Fin params.m → Scalar params))
          (fun u => if g (e.symm u) = g' (e.symm u) then (1 : Error) else 0) := by
            simpa [e] using
              (avgOver_uniform_equiv e
                (fun u : Point params => if g u = g' u then (1 : Error) else 0))
    _ = avgOver (uniformDistribution (Fin params.m → Scalar params))
          (fun u =>
            if MvPolynomial.eval u g.poly = MvPolynomial.eval u g'.poly then
              (1 : Error)
            else 0) := by
            apply avgOver_congr
            intro u
            have hdecode : decodePoint (e.symm u) = u := by
              simpa [e, pointScalarEquiv] using e.right_inv u
            by_cases hEval : MvPolynomial.eval u g.poly = MvPolynomial.eval u g'.poly
            · have hPointEval : g (e.symm u) = g' (e.symm u) := by
                change encodeScalar (MvPolynomial.eval (decodePoint (e.symm u)) g.poly) =
                  encodeScalar (MvPolynomial.eval (decodePoint (e.symm u)) g'.poly)
                congr 1
                simpa [hdecode] using hEval
              simp [hEval, hPointEval]
            · have hPointEval : ¬ g (e.symm u) = g' (e.symm u) := by
                intro hEq
                apply hEval
                apply (FieldModel.equiv (q := params.q)).injective
                change encodeScalar (MvPolynomial.eval (decodePoint (e.symm u)) g.poly) =
                  encodeScalar (MvPolynomial.eval (decodePoint (e.symm u)) g'.poly) at hEq
                simpa [encodeScalar, hdecode] using hEq
              simp [hEval, hPointEval]

/-- Schwartz-Zippel bound for the pointwise agreement indicator of two distinct
full polynomial outcomes.

Packages the `md/q` loss term that appears at:
- `references/ldt-paper/inductive_step.tex` lines 119–133 (the `mainFormal`
  Step 5 self-consistency cascade, issue #425),
- `references/ldt-paper/commutativity-G.tex` (the `comMain` step, issue #297).

Both call sites previously held a private duplicate of this proof; this is the
shared, reusable form. -/
lemma polynomialAgreement_avg_le_mdq
    (params : Parameters) [FieldModel params.q]
    (g g' : Polynomial params) (hneq : g ≠ g') :
    avgOver (uniformDistribution (Point params))
      (fun u => if g u = g' u then (1 : Error) else 0) ≤
      (params.m * params.d : Error) / params.q := by
  classical
  let gLow : polyFunc params.m (Scalar params) params.d :=
    ⟨g.poly, by
      rw [MvPolynomial.mem_restrictDegree_iff_sup]
      simpa [MvPolynomial.degreeOf_def] using g.lowIndividualDegree⟩
  let g'Low : polyFunc params.m (Scalar params) params.d :=
    ⟨g'.poly, by
      rw [MvPolynomial.mem_restrictDegree_iff_sup]
      simpa [MvPolynomial.degreeOf_def] using g'.lowIndividualDegree⟩
  have hneqLow : gLow ≠ g'Low := by
    intro hEq
    have hpoly : g.poly = g'.poly := congrArg Subtype.val hEq
    apply hneq
    cases g
    cases g'
    cases hpoly
    rfl
  have hsz := schwartzZippel_individualDegree gLow g'Low hneqLow
  have havg_scalar :
      avgOver (uniformDistribution (Fin params.m → Scalar params))
        (fun u =>
          if MvPolynomial.eval u g.poly = MvPolynomial.eval u g'.poly then
            (1 : Error)
          else 0) =
      (polynomialAgreementProbability
        params.m (Scalar params) g.poly g'.poly : Error) := by
    calc
      avgOver (uniformDistribution (Fin params.m → Scalar params))
          (fun u =>
            if MvPolynomial.eval u g.poly = MvPolynomial.eval u g'.poly then
              (1 : Error)
            else 0)
        = ∑ u : Fin params.m → Scalar params,
            if MvPolynomial.eval u g.poly = MvPolynomial.eval u g'.poly then
              (Fintype.card (Scalar params) ^ params.m : Error)⁻¹
            else 0 := by
              simp [avgOver, uniformDistribution]
      _ = Finset.sum
            ((Finset.univ : Finset (Fin params.m → Scalar params)).filter
              (fun u => MvPolynomial.eval u g.poly = MvPolynomial.eval u g'.poly))
            (fun _ => (Fintype.card (Scalar params) ^ params.m : Error)⁻¹) := by
              rw [← Finset.sum_filter]
      _ = (((Finset.univ.filter fun u : Fin params.m → Scalar params =>
              MvPolynomial.eval u g.poly = MvPolynomial.eval u g'.poly).card : ℕ) : Error) *
            (Fintype.card (Scalar params) ^ params.m : Error)⁻¹ := by
              simp
      _ = (polynomialAgreementProbability
            params.m (Scalar params) g.poly g'.poly : Error) := by
              simp [polynomialAgreementProbability, div_eq_mul_inv]
  calc
    avgOver (uniformDistribution (Point params))
        (fun u => if g u = g' u then (1 : Error) else 0)
      = avgOver (uniformDistribution (Fin params.m → Scalar params))
          (fun u =>
            if MvPolynomial.eval u g.poly = MvPolynomial.eval u g'.poly then
              (1 : Error)
            else 0) :=
            polynomialAgreement_avg_eq_scalarDomain params g g'
    _ = (polynomialAgreementProbability
          params.m (Scalar params) g.poly g'.poly : Error) :=
          havg_scalar
    _ ≤ ((((params.m * params.d : ℕ) : ℚ≥0) / Fintype.card (Scalar params)) : Error) := by
          exact_mod_cast hsz
    _ = (params.m * params.d : Error) / params.q := by
          simp [div_eq_mul_inv]

/-- Reindex evaluation equality for degree-`d` line polynomials from coded
`Fq params` parameters to the scalar field used by Mathlib's univariate
polynomial API. -/
lemma axisLinePolynomialAgreement_avg_eq_scalarDomain
    (params : Parameters) [FieldModel params.q]
    (f h : AxisLinePolynomial params) :
    avgOver (uniformDistribution (Fq params))
      (fun t => if f t = h t then (1 : Error) else 0) =
      avgOver (uniformDistribution (Scalar params))
        (fun x =>
          if _root_.Polynomial.eval x f.poly = _root_.Polynomial.eval x h.poly then
            (1 : Error)
          else 0) := by
  let e : Fq params ≃ Scalar params := (FieldModel.equiv (q := params.q)).symm
  calc
    avgOver (uniformDistribution (Fq params))
        (fun t => if f t = h t then (1 : Error) else 0)
      = avgOver (uniformDistribution (Scalar params))
          (fun x => if f (e.symm x) = h (e.symm x) then (1 : Error) else 0) := by
            simpa [e] using
              (avgOver_uniform_equiv e
                (fun t : Fq params => if f t = h t then (1 : Error) else 0))
    _ = avgOver (uniformDistribution (Scalar params))
        (fun x =>
          if _root_.Polynomial.eval x f.poly = _root_.Polynomial.eval x h.poly then
            (1 : Error)
          else 0) := by
            apply avgOver_congr
            intro x
            by_cases hx : _root_.Polynomial.eval x f.poly = _root_.Polynomial.eval x h.poly
            · have hdecode : decodeScalar (e.symm x) = x := by
                simp [e, decodeScalar]
              have hcoded : f (e.symm x) = h (e.symm x) := by
                change encodeScalar (_root_.Polynomial.eval (decodeScalar (e.symm x)) f.poly) =
                  encodeScalar (_root_.Polynomial.eval (decodeScalar (e.symm x)) h.poly)
                simpa [hdecode] using congrArg encodeScalar hx
              simp [hx, hcoded]
            · have hdecode : decodeScalar (e.symm x) = x := by
                simp [e, decodeScalar]
              have hcoded : ¬ f (e.symm x) = h (e.symm x) := by
                intro hEq
                apply hx
                have henc :
                    encodeScalar (_root_.Polynomial.eval x f.poly) =
                      encodeScalar (_root_.Polynomial.eval x h.poly) := by
                  simpa [AxisLinePolynomial.toFun, evalLinePolynomialModel, hdecode] using hEq
                exact (FieldModel.equiv (q := params.q)).injective henc
              simp [hx, hcoded]

/-- Schwartz--Zippel for two distinct degree-`d` axis-line answers, stated with
the ambient `m*d/q` loss used in the LDT estimates.  The underlying univariate
root count gives `d/q`, and `params.hm` deliberately pads it to the paper's
ambient `m*d/q` loss. -/
lemma axisLinePolynomialAgreement_avg_le_mdq
    (params : Parameters) [FieldModel params.q]
    (f h : AxisLinePolynomial params) (hneq : f.poly ≠ h.poly) :
    avgOver (uniformDistribution (Fq params))
      (fun t => if f t = h t then (1 : Error) else 0) ≤
      (params.m * params.d : Error) / params.q := by
  classical
  let S : Finset (Scalar params) :=
    Finset.univ.filter (fun x : Scalar params =>
      _root_.Polynomial.eval x f.poly = _root_.Polynomial.eval x h.poly)
  have hS_card_le : S.card ≤ params.d := by
    have hsub_ne : f.poly - h.poly ≠ 0 := sub_ne_zero.mpr hneq
    have hsubset : S.val ⊆ (f.poly - h.poly).roots := by
      intro x hx
      have hx_eval : _root_.Polynomial.eval x f.poly = _root_.Polynomial.eval x h.poly := by
        simpa [S] using hx
      have hxroot : _root_.Polynomial.IsRoot (f.poly - h.poly) x := by
        rw [_root_.Polynomial.IsRoot.def, _root_.Polynomial.eval_sub, sub_eq_zero]
        exact hx_eval
      exact (_root_.Polynomial.mem_roots hsub_ne).2 hxroot
    have hcard := _root_.Polynomial.card_le_degree_of_subset_roots (p := f.poly - h.poly)
      (Z := S) hsubset
    have hdeg : (f.poly - h.poly).natDegree ≤ max f.poly.natDegree h.poly.natDegree := by
      simpa [sub_eq_add_neg, _root_.Polynomial.natDegree_neg] using
        (_root_.Polynomial.natDegree_add_le f.poly (-h.poly))
    exact le_trans hcard (le_trans hdeg (max_le f.degreeBounded h.degreeBounded))
  have havg_scalar :
      avgOver (uniformDistribution (Scalar params))
        (fun x =>
          if _root_.Polynomial.eval x f.poly = _root_.Polynomial.eval x h.poly then
            (1 : Error)
          else 0) =
        (S.card : Error) / Fintype.card (Scalar params) := by
    calc
      avgOver (uniformDistribution (Scalar params))
        (fun x =>
          if _root_.Polynomial.eval x f.poly = _root_.Polynomial.eval x h.poly then
            (1 : Error)
          else 0)
        = ∑ x : Scalar params,
            if _root_.Polynomial.eval x f.poly = _root_.Polynomial.eval x h.poly then
              (1 / (Fintype.card (Scalar params) : Error))
            else 0 := by
              simp [avgOver, uniformDistribution]
      _ = ∑ x ∈ S, (1 / (Fintype.card (Scalar params) : Error)) := by
              rw [← Finset.sum_filter]
      _ = (S.card : Error) * (1 / (Fintype.card (Scalar params) : Error)) := by
              simp
      _ = (S.card : Error) / Fintype.card (Scalar params) := by ring
  have hline :
      (S.card : Error) / Fintype.card (Scalar params) ≤
        (params.d : Error) / params.q := by
    rw [scalar_card]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hS_card_le) (by positivity)
  have hmd : (params.d : Error) / params.q ≤ (params.m * params.d : Error) / params.q := by
    apply div_le_div_of_nonneg_right ?_ (by positivity)
    have hm : (1 : Error) ≤ (params.m : Error) := by exact_mod_cast params.hm
    have hd : 0 ≤ (params.d : Error) := by positivity
    calc
      (params.d : Error) = (1 : Error) * (params.d : Error) := by ring
      _ ≤ (params.m : Error) * (params.d : Error) :=
          mul_le_mul_of_nonneg_right hm hd
      _ = (params.m * params.d : Error) := by norm_num
  calc
    avgOver (uniformDistribution (Fq params))
      (fun t => if f t = h t then (1 : Error) else 0)
      = avgOver (uniformDistribution (Scalar params))
        (fun x =>
          if _root_.Polynomial.eval x f.poly = _root_.Polynomial.eval x h.poly then
            (1 : Error)
          else 0) := axisLinePolynomialAgreement_avg_eq_scalarDomain params f h
    _ = (S.card : Error) / Fintype.card (Scalar params) := havg_scalar
    _ ≤ (params.d : Error) / params.q := hline
    _ ≤ (params.m * params.d : Error) / params.q := hmd

open Classical in
/-- Tensor-form Schwartz-Zippel collision bound.

For each off-diagonal pair of polynomial outcomes, the point-collision
coefficient is bounded by `params.m * params.d / params.q` via
`polynomialAgreement_avg_le_mdq`. The remaining tensor residual is bounded by
`1` using `sandwichTensor_residual_sum_le_one`, so the whole nonnegative
collision sum has the same `m d / q` bound. -/
lemma polynomialCollision_sandwichTensor_le_mdq
    {ιA ιB β : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Fintype β]
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ιA × ιB)) (hnorm : ψ.IsNormalized)
    (Outer : SubMeas β ιA)
    (Inner : SubMeas (Polynomial params) ιA) (Right : SubMeas (Polynomial params) ιB) :
    (∑ gg : Polynomial params × Polynomial params, ∑ o : β,
        (if gg.1 = gg.2 then 0 else
          avgOver (uniformDistribution (Point params))
            (fun u => if gg.1 u = gg.2 u then (1 : Error) else 0)) *
          ev ψ
            (leftTensor (ι₂ := ιB)
                (Outer.outcome o * Inner.outcome gg.1 * Outer.outcome o) *
              rightTensor (ι₁ := ιA) (Right.outcome gg.2))) ≤
      (params.m * params.d : Error) / params.q := by
  let δ : Error := (params.m * params.d : Error) / params.q
  have hδ_nonneg : 0 ≤ δ := by
    exact div_nonneg (by positivity) (by positivity)
  have hcoef_le (gg : Polynomial params × Polynomial params) :
      (if gg.1 = gg.2 then 0 else
          avgOver (uniformDistribution (Point params))
            (fun u => if gg.1 u = gg.2 u then (1 : Error) else 0)) ≤ δ := by
    by_cases hEq : gg.1 = gg.2
    · simp [hEq, hδ_nonneg, δ]
    · simpa [hEq, δ] using
        polynomialAgreement_avg_le_mdq params gg.1 gg.2 hEq
  calc
    (∑ gg : Polynomial params × Polynomial params, ∑ o : β,
        (if gg.1 = gg.2 then 0 else
          avgOver (uniformDistribution (Point params))
            (fun u => if gg.1 u = gg.2 u then (1 : Error) else 0)) *
          ev ψ
            (leftTensor (ι₂ := ιB)
                (Outer.outcome o * Inner.outcome gg.1 * Outer.outcome o) *
              rightTensor (ι₁ := ιA) (Right.outcome gg.2)))
      ≤ ∑ gg : Polynomial params × Polynomial params, ∑ o : β,
          δ * ev ψ
            (leftTensor (ι₂ := ιB)
                (Outer.outcome o * Inner.outcome gg.1 * Outer.outcome o) *
              rightTensor (ι₁ := ιA) (Right.outcome gg.2)) := by
          refine Finset.sum_le_sum ?_
          intro gg _
          refine Finset.sum_le_sum ?_
          intro o _
          have hnonneg :
              0 ≤ ev ψ
                (leftTensor (ι₂ := ιB)
                    (Outer.outcome o * Inner.outcome gg.1 * Outer.outcome o) *
                  rightTensor (ι₁ := ιA) (Right.outcome gg.2)) :=
            sandwichTensorSummand_nonneg (ψ := ψ)
              (Outer := Outer) (Inner := Inner) (Right := Right) o gg.1 gg.2
          exact mul_le_mul_of_nonneg_right (hcoef_le gg)
            hnonneg
    _ = δ * (∑ gg : Polynomial params × Polynomial params, ∑ o : β,
          ev ψ
            (leftTensor (ι₂ := ιB)
                (Outer.outcome o * Inner.outcome gg.1 * Outer.outcome o) *
              rightTensor (ι₁ := ιA) (Right.outcome gg.2))) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro gg _
          rw [Finset.mul_sum]
    _ ≤ δ * 1 := by
          exact mul_le_mul_of_nonneg_left
            (sandwichTensor_residual_sum_le_one (ψ := ψ) hnorm
              (Outer := Outer) (Inner := Inner) (Right := Right))
            hδ_nonneg
    _ = (params.m * params.d : Error) / params.q := by
          simp [δ]

open Classical in
/-- The off-diagonal polynomial-collision mass used in `mainFormal` Step 5.

This is the weighted collision term in `inductive_step.tex` lines 122--127:
for every distinct pair of full polynomial outcomes `(g, h)`, the coefficient is
`Pr_u[g(u) = h(u)]`, and the quantum weight is the fixed cross-register mass
`⟨ψ | G^A_g ⊗ G^B_h | ψ⟩`. -/
noncomputable def polynomialCollisionMass
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ιA × ιB))
    (Left : SubMeas (Polynomial params) ιA) (Right : SubMeas (Polynomial params) ιB) :
    Error :=
  ∑ gg : Polynomial params × Polynomial params,
    (if gg.1 = gg.2 then 0 else
      avgOver (uniformDistribution (Point params))
        (fun u => if gg.1 u = gg.2 u then (1 : Error) else 0)) *
      ev ψ (opTensor (Left.outcome gg.1) (Right.outcome gg.2))



end MIPStarRE.LDT.Preliminaries

end

end LIDT


