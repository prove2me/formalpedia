-- Prove2me | Definitions.Def_OAIQWRHT003
-- name    : OAIQWRHT003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T22:17:49.624733+00:00
-- url     : https://prove2.me/theorems/030ae47f-21d7-496b-8272-58f326c737d0
-- title:
--   OpenAI rational hitting lists split: definitions bundle OAIQWRHT003
-- statement:
--   One of the five definitions bundles (`OAIQWRHT000` to `OAIQWRHT004`) of the split of OpenAI's proof that one deterministic Turing machine writes, in polynomial time, a polynomial-size list of rational matrix tuples hitting every admissible nonzero noncommutative rational formula of size at most $s$ (`OAI.RationalHitting.main`, the paper's Theorem 1.1). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Computability/RationalHitting` (OpenAI, *Polynomial Hitting Lists for Noncommutative Rational Formulas*, OpenAI Math Release, September 24, 2026, result family 116, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies. Among them are the cyclotomic grid construction of the list (`Generator.list`, `ExecutableGenerator.list`), the pencil certificates, the binary arithmetic procedures, the stack language with its time bounds, and the compiler to `Turing.TM0` machines. The bundles split the material only to keep each one within the platform's compile limits.
--
--   The definitions of the published statement (`Formula`, `Evaluates`, `Admissible`, `Nonzero`, `Output`, `encodeOutput`, `Machine`, `run`, `OutputsWithin`, `Hits`, `MainStatement` and the rest) are not repeated: the bundles import them from the published bundle `Def_RationalHitting`. It also imports the bundles `OAIQWRHT000`, `OAIQWRHT001` of this split.
--
--   Modules (some only in part): `Deformation`, `GridComputation`, `MatrixComputation`, `PaddedRank`, `Tabulation`.
--
--   The theorems the definitions do not need are proved in the three solutions of this split. One proves the published intermediate statement `OAI.RationalHitting.Generator.list_hits` (the paper's Proposition 5.1), one proves `OAI.RationalHitting.ExecutableGenerator.implementation` (Proposition 5.3) using it, and the third proves `OAI.RationalHitting.main` from both. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, Polynomial Hitting Lists for Noncommutative Rational Formulas, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 116; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-Hitting-Lists-for-Noncommutative-Rational-Formulas-September-24-2026/Polynomial-Hitting-Lists-for-Noncommutative-Rational-Formulas-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability/RationalHitting at commit adc7f12

import Mathlib
import Definitions.Def_RationalHitting
import Definitions.Def_OAIQWRHT000
import Definitions.Def_OAIQWRHT001

section
-- module Solutions.OAIQW_RationalHitting.PaddedRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.TestPolynomial
open Polynomial Matrix Module
open LaurentReduction SmallExpansion Rectangular
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K]

/-- The original t indeterminate embeds into the fresh Laurent indeterminate. -/
def embed : K[X] →+* F K := Polynomial.eval₂RingHom HahnSeries.C (HahnSeries.single 1 1)

end
end RationalHitting.TestPolynomial

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.Deformation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace RationalHitting.ThreeLift
open Matrix Polynomial MvPolynomial
open QuantumMatrices
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K] {d : ℕ} [NeZero d]
variable (χ : AddChar (ZMod d) K)

lemma coeffP_add (R S : Matrix (ZMod d) (ZMod d) K[X]) (a b : ZMod d) :
    coeffP χ (R+S) a b = coeffP χ R a b + coeffP χ S a b := by
  simp [coeffP,mul_add,Finset.sum_add_distrib]
lemma coeffP_smul (c : K) (R : Matrix (ZMod d) (ZMod d) K[X]) (a b : ZMod d) :
    coeffP χ (c • R) a b = Polynomial.C c * coeffP χ R a b := by
  simp only [coeffP,Matrix.smul_apply,Polynomial.smul_eq_C_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma lift_add (R S : Matrix (ZMod d) (ZMod d) K[X]) :
    lift χ (R+S) = lift χ R + lift χ S := by
  funext i j
  simp [lift,coeffP_add,map_add,add_mul,Finset.sum_add_distrib]
lemma lift_smul (c : K) (R : Matrix (ZMod d) (ZMod d) K[X]) :
    lift χ (c • R) = c • lift χ R := by
  funext i j
  simp only [lift,coeffP_smul,map_mul,uni,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,
    Matrix.smul_apply,MvPolynomial.smul_eq_C_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

def linear : Matrix (ZMod d) (ZMod d) K[X] →ₗ[K]
    Matrix (ZMod d) (ZMod d) (MvPolynomial (Fin 3) K) where
  toFun := lift χ
  map_add' := lift_add χ
  map_smul' := by intro c R; simpa using lift_smul χ c R

end
end RationalHitting.ThreeLift

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.Tabulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace RationalHitting.StackLanguage

export Coding (code)

instance instCodingBitWord : Coding BitWord := ⟨BitWord.val⟩

end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.MatrixComputation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace RationalHitting.StackLanguage
open Function

instance instInhabitedBitWord : Inhabited BitWord := ⟨⟨[]⟩⟩

def concatStep (a : List BitWord×BitWord) : List BitWord×BitWord :=
  (a.1.tail,⟨a.2.val++(a.1.headD ⟨[]⟩).val⟩)

end RationalHitting.StackLanguage


end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.GridComputation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace RationalHitting.StackLanguage
namespace Runtime

def matrixWord (A B : DenseSquare) (den : ℤ) : BitWord :=
  ⟨(List.range A.dim).flatMap fun i =>
    (List.range A.dim).flatMap fun j =>
      encodeRat (Rat.divInt (cramer A B i j).val.det den)⟩

end Runtime
end RationalHitting.StackLanguage


end OAI
end


