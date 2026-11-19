-- Prove2me | Definitions.Def_KunenZF_theory
-- name    : KunenZF_theory
-- status  : Definition
-- author  : @LG
-- created : 2026-11-18T16:36:10.237772+00:00
-- url     : https://prove2.me/theorems/129130b5-f5fa-44b8-ac66-50836ece718f
-- title:
--   $\mathrm{ZF}(j)$ and the Reinhardt-embedding theory
-- statement:
--   This definition builds the first-order theory whose consistency is the open problem. $\mathrm{ZF}(j)$ is Zermelo–Fraenkel set theory in the language $\{\in, j\}$ with the Separation and Collection schemes extended to every formula in which the function symbol $j$ appears (with parameters); the pure $\mathrm{ZF}$ axioms are imported from the platform's `ContinuumHypothesis.ZF`. The elementarity scheme asserts, for each pure $\in$-formula $\varphi(\vec x)$, the sentence $\forall \vec x\,(\varphi(\vec x) \leftrightarrow \varphi(j\vec x))$; it ranges over $\in$-formulas only, not formulas mentioning $j$. Nontriviality is $\exists x\, j(x) \ne x$. The **Reinhardt theory** is $\mathrm{ZF}(j)$ plus elementarity plus nontriviality; its inconsistency is exactly the statement that $\mathrm{ZF}$ refutes Reinhardt cardinals. Variants add the Axiom of Choice (for Kunen's theorem), the assertion that $j$ fixes every ordinal (for the critical-point lemma), or the assertion that $j$ is definable from parameters by a fixed pure formula $\delta$ (for Suzuki's theorem).
--
--   **Formalization Note.** Theories are sets of Mathlib sentences; schemes are formed by universal closure. The definability sentence existentially closes the parameter variables of $\delta$ after universally closing the input and output variables.
-- source:
--   Hamkins–Kirmayer–Perlmutter, Generalizations of the Kunen inconsistency, §1 (ZF(j), ZFC(j)); https://arxiv.org/abs/1106.1951. Wikipedia, Reinhardt cardinal (Separation and Collection for formulas involving j).

import Mathlib
import Definitions.Def_KunenZF_language
import Definitions.Def_CH_ZFC

/-!
# The theory `ZF(j)` and the Reinhardt-embedding axioms

`ZFj` is ZF with the Separation and Collection schemes extended to all formulas
mentioning `j`.  `ElemSchema` is the elementarity scheme for `j` over pure
`∈`-formulas; `nontrivFormula` says `j` moves some set.  `reinhardtTheory` is
`ZF(j) + "j is a nontrivial elementary embedding V → V"`.
-/

namespace KunenZF

open FirstOrder FirstOrder.Language
open SFormulaJ

noncomputable section

/-- An instance of the Separation scheme for `{∈, j}`-formulas. -/
def IsSeparationJ (σ : SFormulaJ) : Prop :=
  ∃ (φ : SFormulaJ) (x a b : ℕ), x ≠ a ∧ x ≠ b ∧ a ≠ b ∧ b ∉ φ.freeVarFinset ∧
    σ = allJ a (exJ b (allJ x (memJ x b ⇔ (memJ x a ⊓ φ))))

/-- An instance of the Collection scheme for `{∈, j}`-formulas. -/
def IsCollectionJ (σ : SFormulaJ) : Prop :=
  ∃ (φ : SFormulaJ) (x y a b : ℕ), [x, y, a, b].Nodup ∧ b ∉ φ.freeVarFinset ∧
    σ = allJ a ((allJ x (memJ x a ⟹ exJ y φ)) ⟹
      exJ b (allJ x (memJ x a ⟹ exJ y (memJ y b ⊓ φ))))

/-- `ZF(j)`: ZF with Separation and Collection for all `{∈, j}`-formulas. -/
def ZFj : setLangJ.Theory :=
  incl.onTheory ContinuumHypothesis.ZF ∪ closeJ '' {σ | IsSeparationJ σ} ∪
    closeJ '' {σ | IsCollectionJ σ}

/-- The elementarity instance for a pure `∈`-formula `φ`: `∀ x̄, φ(x̄) ↔ φ(j x̄)`. -/
def elemFormula (φ : ContinuumHypothesis.SFormula) : SFormulaJ :=
  incl.onBoundedFormula φ ⇔ (incl.onBoundedFormula φ).subst (fun v => jTerm v)

/-- The elementarity scheme for `j`, over pure `∈`-formulas. -/
def ElemSchema : setLangJ.Theory :=
  closeJ '' {σ | ∃ φ : ContinuumHypothesis.SFormula, σ = elemFormula φ}

/-- `j` is nontrivial: it moves some set. -/
def nontrivFormula : SFormulaJ := exJ 0 (∼(Term.equal (jTerm 0) (Term.var 0)))

/-- `j` fixes every ordinal. -/
def fixesOrdinalsFormula : SFormulaJ :=
  allJ 0 (isOrdinalJ 0 ⟹ Term.equal (jTerm 0) (Term.var 0))

/-- Existentially bind each named variable in the list `s`. -/
def exJsJ (s : List ℕ) (φ : SFormulaJ) : SFormulaJ :=
  s.foldr (fun v acc => exJ v acc) φ

/-- `j` is definable from parameters by the pure formula `δ(x, y, p̄)`. -/
def defByFormula (δ : ContinuumHypothesis.SFormula) : setLangJ.Sentence :=
  let body := allJ 0 (allJ 1 (Term.equal (jTerm 0) (Term.var 1) ⇔ incl.onBoundedFormula δ))
  closeJ (exJsJ body.freeVarFinset.toList body)

/-- `ZF(j) + "j is a nontrivial elementary embedding V → V"`. -/
def reinhardtTheory : setLangJ.Theory := ZFj ∪ ElemSchema ∪ {closeJ nontrivFormula}

/-- The same theory with the Axiom of Choice added. -/
def zfcReinhardtTheory : setLangJ.Theory :=
  reinhardtTheory ∪ {incl.onSentence ContinuumHypothesis.acSentence}

/-- The Reinhardt theory plus "`j` is definable from parameters by `δ`". -/
def reinhardtDefinableTheory (δ : ContinuumHypothesis.SFormula) : setLangJ.Theory :=
  reinhardtTheory ∪ {defByFormula δ}

end

end KunenZF


