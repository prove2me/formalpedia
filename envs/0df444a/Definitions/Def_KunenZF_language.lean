-- Prove2me | Definitions.Def_KunenZF_language
-- name    : KunenZF_language
-- status  : Definition
-- author  : @LG
-- created : 2026-11-18T16:35:40.53647+00:00
-- url     : https://prove2.me/theorems/b77522fa-6c73-4580-b96e-4ac158e9e19c
-- title:
--   The language $\{\in, j\}$ of set theory with a self-embedding
-- statement:
--   This definition introduces the first-order language used to state the Kunen inconsistency problem without the Axiom of Choice. The language $\{\in, j\}$ extends the usual language of set theory $\{\in\}$ by a single unary function symbol $j$, intended to name a class elementary embedding $j : V \to V$. Formulas have free variables named by natural numbers, and the usual quantifiers and universal closure are provided. The inclusion $\mathrm{incl} : \{\in\} \hookrightarrow \{\in, j\}$ lets every pure set-theoretic formula be read in the expanded language, which is how the elementarity scheme for $j$ is formed. Auxiliary formulas define subset, transitivity, and the property of being an ordinal (a transitive set all of whose elements are transitive), used to speak about the critical point of $j$.
--
--   **Formalization Note.** Built on Mathlib's `FirstOrder.Language` and the platform's `ContinuumHypothesis.setLang`; the relation symbol is shared with the pure language so the inclusion acts as the identity on $\in$.
-- source:
--   Hamkins–Kirmayer–Perlmutter, Generalizations of the Kunen inconsistency, §1 (the theory ZF(j)); https://arxiv.org/abs/1106.1951. Wikipedia, Reinhardt cardinal (formulation with a function symbol j).

import Mathlib
import Definitions.Def_CH_SetTheoryLanguage

/-!
# The language of set theory with a class self-embedding `j`

`setLangJ` extends the first-order language of set theory `{∈}` by a single unary
function symbol `j`, intended to name a (class) elementary embedding `j : V → V`.
`incl` is the inclusion of the pure language `{∈}` into `{∈, j}`.
-/

namespace KunenZF

open FirstOrder FirstOrder.Language

noncomputable section

/-- The function symbols of the expanded language: a single unary symbol `j`. -/
inductive JFun : ℕ → Type
  | j : JFun 1

/-- The first-order language `{∈, j}`: membership plus a unary function symbol `j`. -/
@[reducible] def setLangJ : FirstOrder.Language.{0, 0} where
  Functions := JFun
  Relations := ContinuumHypothesis.SetRel

/-- Formulas of `{∈, j}` with free variables named by natural numbers. -/
abbrev SFormulaJ : Type := setLangJ.BoundedFormula ℕ 0

/-- The inclusion of the pure language of set theory into `{∈, j}`. -/
def incl : ContinuumHypothesis.setLang →ᴸ setLangJ where
  onFunction := fun {_} e => Empty.elim e
  onRelation := fun {_} r => r

/-- The term `j(v)`. -/
def jTerm (v : ℕ) : setLangJ.Term ℕ := Term.func JFun.j (fun _ => Term.var v)

namespace SFormulaJ

/-- The atomic formula `x ∈ y`. -/
def memJ (x y : ℕ) : SFormulaJ :=
  Relations.formula₂ (ContinuumHypothesis.SetRel.mem : setLangJ.Relations 2) (Term.var x) (Term.var y)

/-- The atomic formula `x = y`. -/
def eqJ (x y : ℕ) : SFormulaJ := Term.equal (Term.var x) (Term.var y)

/-- `∀ x, φ`, binding the named variable `x`. -/
def allJ (x : ℕ) (φ : SFormulaJ) : SFormulaJ :=
  Formula.iAlls Unit (Formula.relabel (fun v => if v = x then Sum.inr () else Sum.inl v) φ)

/-- `∃ x, φ`, binding the named variable `x`. -/
def exJ (x : ℕ) (φ : SFormulaJ) : SFormulaJ :=
  Formula.iExs Unit (Formula.relabel (fun v => if v = x then Sum.inr () else Sum.inl v) φ)

/-- An upper bound for the names of the free variables of `φ`. -/
def varBoundJ (φ : SFormulaJ) : ℕ := φ.freeVarFinset.sup id

/-- The universal closure of `φ`, a sentence. -/
def closeJ (φ : SFormulaJ) : setLangJ.Sentence :=
  Formula.iAlls (Fin (varBoundJ φ + 1))
    (Formula.relabel (fun n =>
      (Sum.inr ⟨n % (varBoundJ φ + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ : Empty ⊕ Fin _)) φ)

/-- `x ⊆ y`. -/
def subsetJ (x y : ℕ) : SFormulaJ := allJ 1040 (memJ 1040 x ⟹ memJ 1040 y)

/-- `t` is transitive. -/
def isTransitiveJ (t : ℕ) : SFormulaJ := allJ 1041 (memJ 1041 t ⟹ subsetJ 1041 t)

/-- `α` is an ordinal: a transitive set all of whose elements are transitive. -/
def isOrdinalJ (α : ℕ) : SFormulaJ :=
  isTransitiveJ α ⊓ allJ 1042 (memJ 1042 α ⟹ isTransitiveJ 1042)

end SFormulaJ

end

end KunenZF


