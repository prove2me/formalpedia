-- Prove2me | Definitions.Def_FreeGroupFactorProof20
-- name    : FreeGroupFactorProof20
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T04:16:00.103736+00:00
-- url     : https://prove2.me/theorems/28e3dc70-38be-4699-b818-02036b22656e
-- title:
--   Free group factors: supporting development, part 20
-- statement:
--   Part 20 of the supporting Lean development for the isomorphism of all interpolated free group factors. It continues the chain of earlier parts and contains proved upstream lemmas on the polynomial flow and on corners of the stabilization, with the declarations they rest on, in source order. No result is assumed.
--
--   **Formalization Note** Eight of these lemmas were first published as child theorems, but the platform's target-type check rejected their universe-polymorphic solutions even though the solution type and the published statement have the same elaborated term locally. They are therefore proved here, so that the parent theorems can use them. The code is OpenAI's, carved from `lean/OAI/Analysis/FreeGroupFactor` and `lean/OAI/Analysis/InterpolatedFactors` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0)

import Mathlib
import Definitions.Def_FreeGroupFactorProof19

set_option linter.all false

section
namespace OAI

noncomputable section

universe uG uH

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain

open scoped ENNReal

def canonicalTraceCLM {G : Type uG} [Group G] : groupVonNeumann G →L[ℂ] ℂ :=
  canonicalTraceLinear.mkContinuous 1 (fun T => by
    change ‖canonicalTrace T‖ ≤ 1 * ‖T‖
    simpa only [one_mul] using norm_canonicalTrace_le T)

@[simp] theorem canonicalTraceCLM_apply {G : Type uG} [Group G] (T : groupVonNeumann G) :
    canonicalTraceCLM T = canonicalTrace T := rfl

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe uA uG uι

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain

 def groupUnitaryHom (G : Type uG) [Group G] : G →* groupVonNeumann G where
  toFun := groupUnitary
  map_one' := Subtype.ext (leftRegular_one)
  map_mul' g b := Subtype.ext (leftRegular_mul g b)

 def groupAlgebraEvaluation (G : Type uG) [Group G] :
    MonoidAlgebra ℂ G →ₐ[ℂ] groupVonNeumann G :=
  MonoidAlgebra.lift ℂ (groupVonNeumann G) G (groupUnitaryHom G)

 @[simp] theorem groupAlgebraEvaluation_of {G : Type uG} [Group G] (g : G) :
    groupAlgebraEvaluation G (MonoidAlgebra.of ℂ G g) = groupUnitary g := by
  simp [groupAlgebraEvaluation, groupUnitaryHom]

 theorem canonicalTrace_groupAlgebraEvaluation {G : Type uG} [Group G] [DecidableEq G]
    (p : MonoidAlgebra ℂ G) : canonicalTrace (groupAlgebraEvaluation G p) = p.coeff 1 := by
  induction p using MonoidAlgebra.induction_on with
  | of g =>
    rw [groupAlgebraEvaluation_of, canonicalTrace_groupUnitary]
    simp only [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  | add p q hp hq =>
    change canonicalTraceCLM (groupAlgebraEvaluation G (p + q)) = _
    simp only [map_add, canonicalTraceCLM_apply, hp, hq, MonoidAlgebra.coeff_add,
      Finsupp.add_apply]
  | smul c p hp =>
    change canonicalTraceCLM (groupAlgebraEvaluation G (c • p)) = _
    simp only [map_smul, canonicalTraceCLM_apply, hp, MonoidAlgebra.coeff_smul,
      Finsupp.smul_apply]

 theorem canonicalTrace_eval {ι : Type uι} [DecidableEq ι]
    (p : NCPolynomial.Expr (ι × Bool)) :
    canonicalTrace (NCPolynomial.eval (fun ib => groupUnitary (AlgebraPolynomial.signed ib)) p) =
      (NCPolynomial.eval (fun ib => MonoidAlgebra.of ℂ (FreeGroup ι)
        (AlgebraPolynomial.signed ib)) p).coeff 1 := by
  rw [← canonicalTrace_groupAlgebraEvaluation]
  congr 1
  rw [AlgebraPolynomial.map_eval]
  congr 1
  funext ib
  exact (groupAlgebraEvaluation_of _).symm

theorem source_laurent_moments {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (h : ι → FreeGroup ι →₀ ℝ) (l : ℤ →₀ ℂ)
    (Y : ℝ → (Option ι × Bool) → groupVonNeumann (FreeGroup (Option ι)))
    (hY₀ : ∀ ib, Y 0 ib = groupUnitary (AlgebraPolynomial.signed ib))
    (hsmooth : ∀ ib, ContDiff ℝ ∞ (fun t => Y t ib))
    (hbounded : ∀ t ib, ‖Y t ib‖ ≤ 1)
    (hODE : ∀ t ib, HasDerivAt (fun s => Y s ib)
      (NCPolynomial.eval (Y t)
        (AlgebraPolynomial.encodedField (TraceCocycle.fieldCoefficients h l) ib)) t)
    (p : NCPolynomial.Expr (Option ι × Bool)) (t : ℝ) :
    canonicalTrace (NCPolynomial.eval (Y t) p) =
      canonicalTrace (NCPolynomial.eval (Y 0) p) := by
  classical
  let V := AlgebraPolynomial.encodedField (TraceCocycle.fieldCoefficients h l)
  let J := Finset.univ.sup (fun ib => NCPolynomial.degree (V ib))
  let B := ∑ ib, NCPolynomial.mass (V ib)
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => NCPolynomial.mass_nonneg _
  have hdeg (ib) : NCPolynomial.degree (V ib) ≤ J + 1 := by
    exact (Finset.le_sup (f := fun ib => NCPolynomial.degree (V ib))
      (Finset.mem_univ ib)).trans (Nat.le_succ _)
  have hmass (ib) : NCPolynomial.mass (V ib) ≤ B :=
    Finset.single_le_sum (fun i _ => NCPolynomial.mass_nonneg (V i)) (Finset.mem_univ ib)
  have hinitial (q) : canonicalTrace (NCPolynomial.eval (Y 0) (NCPolynomial.delta V q)) = 0 := by
    have hinit : Y 0 = fun ib => groupUnitary (AlgebraPolynomial.signed ib) := funext hY₀
    rw [hinit, canonicalTrace_eval]
    exact AlgebraPolynomial.encoded_initial_trace h l q
  have hreal (L : ℂ →L[ℝ] ℝ) :
      L (canonicalTrace (NCPolynomial.eval (Y t) p)) =
      L (canonicalTrace (NCPolynomial.eval (Y 0) p)) := by
    let Lt := L.comp ((canonicalTraceCLM (G := FreeGroup (Option ι))).restrictScalars ℝ)
    apply NCPolynomial.polynomial_moments Y V Lt hsmooth hODE 1 le_rfl hbounded
      J B hB hdeg hmass
    intro q
    change L (canonicalTrace (NCPolynomial.eval (Y 0) (NCPolynomial.delta V q))) = 0
    rw [hinitial, map_zero]
  exact Complex.ext (hreal Complex.reCLM) (hreal Complex.imCLM)

end FreeGroupFactorMain

namespace FreeGroupFactorMain.UnitaryEvaluation
open scoped ContDiff
variable {A : Type uA} [CStarAlgebra A] {ι : Type uι}
 theorem norm_signedTrajectory_le_one [Nontrivial A]
    (X : ℝ → ι → A) (hU : ∀ t j, X t j ∈ unitary A)
    (C : unitary A) (t : ℝ) (ib : Option ι × Bool) :
    ‖signedTrajectory X hU C t ib‖ ≤ 1 := by
  change ‖((FreeGroup.lift (extendUnitary (fun j => ⟨X t j, hU t j⟩) C)
    (AlgebraPolynomial.signed ib) : unitary A) : A)‖ ≤ 1
  exact (CStarRing.norm_of_mem_unitary (Subtype.property _)).le

 theorem smooth_signedTrajectory [Fintype ι]
    (X : ℝ → ι → A) (hU : ∀ t j, X t j ∈ unitary A)
    (C : unitary A) (hs : ContDiff ℝ ∞ X) (ib : Option ι × Bool) :
    ContDiff ℝ ∞ (fun t => signedTrajectory X hU C t ib) := by
  rcases ib with ⟨i,b⟩
  cases i with
  | none => cases b <;>
      simp only [signedTrajectory_none_pos, signedTrajectory_none_neg] <;> exact contDiff_const
  | some j => cases b
              · simp only [signedTrajectory_some_neg]
                exact (starL ℝ (A := A)).contDiff.comp ((contDiff_apply ℝ A j).comp hs)
              · simp only [signedTrajectory_some_pos]
                exact (contDiff_apply ℝ A j).comp hs
end FreeGroupFactorMain.UnitaryEvaluation

namespace FreeGroupFactorMain
open scoped ContDiff

 theorem wordHom_generatorUnitary {ι : Type uι} (g : FreeGroup ι) :
    UnitaryEvaluation.wordHom generatorUnitary g = groupUnitary g := by
  have he : UnitaryEvaluation.wordHom (generatorUnitary (ι := ι)) =
      groupUnitaryHom (FreeGroup ι) := by
    apply FreeGroup.ext_hom
    intro i
    rfl
  exact DFunLike.congr_fun he g

end FreeGroupFactorMain

namespace FreeGroupFactorMain.PolynomialFlow
variable {A : Type uA} [CStarAlgebra A] [Nontrivial A]
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end FreeGroupFactorMain.PolynomialFlow

end

end OAI
end


