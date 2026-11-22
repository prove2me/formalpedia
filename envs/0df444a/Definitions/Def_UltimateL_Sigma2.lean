-- Prove2me | Definitions.Def_UltimateL_Sigma2
-- name    : UltimateL_Sigma2
-- status  : Definition
-- author  : @LG
-- created : 2026-11-22T21:28:41.566695+00:00
-- url     : https://prove2.me/theorems/ec93814c-b9fd-4b21-99a3-528a982b4f54
-- title:
--   The Lévy hierarchy: Δ₀ formulas and Σ₂ sentences
-- statement:
--   This file defines the syntactic classes of the Lévy hierarchy needed by the axiom $V=\mathrm{Ultimate}\text{-}L$. A formula is **$\Delta_0$ (bounded)** if it is generated from atomic formulas by the propositional connectives and by quantifiers bounded by a variable, $\forall x\in y$ (bounded existential quantifiers arise as $\neg\forall\neg$). A **$\Sigma_2$ sentence** is a sentence of the form $\exists x_1\cdots\exists x_k\,\forall y_1\cdots\forall y_m\,\psi$ with $\psi$ a $\Delta_0$ formula. The axiom $V=\mathrm{Ultimate}\text{-}L$ reflects the truth of every $\Sigma_2$ sentence of $V$ into the $\mathrm{HOD}$ of a determinacy model, so the precise syntactic class matters.
-- source:
--   W. Hugh Woodin, In Search of Ultimate-L, BSL 23(1) (2017) 1-109, doi:10.1017/bsl.2016.34, Definition 7.14 and Lemma 7.2 (Σ₂ reflection); the Lévy hierarchy is standard (Kanamori, The Higher Infinite, 2nd ed., Springer 2003, §1; Jech, Set Theory, 3rd ed., Springer 2003, Ch. 12).

import Mathlib
import Definitions.Def_OmegaLogic_Semantics

namespace UltimateL

universe u

open FirstOrder FirstOrder.Language OmegaLogic

/-- The membership atom `x_i ∈ x_j` among the variables of a bounded formula. -/
def bmem {n : ℕ} (i j : Fin n) : setLang.BoundedFormula Empty n :=
  BoundedFormula.rel SetRel.mem ![Term.var (Sum.inr i), Term.var (Sum.inr j)]

/-- The class of `Δ₀` (bounded) formulas of set theory: generated from atomic formulas by
implication and falsum (hence by all propositional connectives) and by quantifiers bounded by a
variable, `∀ x ∈ y`. Bounded existential quantifiers are obtained as `¬∀¬`. -/
inductive IsDelta0 : {n : ℕ} → setLang.BoundedFormula Empty n → Prop
  | falsum {n} : IsDelta0 (BoundedFormula.falsum : setLang.BoundedFormula Empty n)
  | equal {n} (t₁ t₂ : setLang.Term (Empty ⊕ Fin n)) :
      IsDelta0 (BoundedFormula.equal t₁ t₂)
  | rel {n l} (R : setLang.Relations l) (ts : Fin l → setLang.Term (Empty ⊕ Fin n)) :
      IsDelta0 (BoundedFormula.rel R ts)
  | imp {n} {f₁ f₂ : setLang.BoundedFormula Empty n} :
      IsDelta0 f₁ → IsDelta0 f₂ → IsDelta0 (BoundedFormula.imp f₁ f₂)
  | ball {n} (i : Fin n) {f : setLang.BoundedFormula Empty (n + 1)} :
      IsDelta0 f →
      IsDelta0 (BoundedFormula.all (BoundedFormula.imp (bmem (Fin.last n) (Fin.castSucc i)) f))

/-- Existential quantification of a bounded formula, written `¬∀¬`. -/
def bEx {n : ℕ} (f : setLang.BoundedFormula Empty (n + 1)) : setLang.BoundedFormula Empty n :=
  BoundedFormula.imp (BoundedFormula.all (BoundedFormula.imp f BoundedFormula.falsum))
    BoundedFormula.falsum

/-- A block of `m` universal quantifiers. -/
def allBlock (k : ℕ) :
    (m : ℕ) → setLang.BoundedFormula Empty (k + m) → setLang.BoundedFormula Empty k
  | 0, ψ => ψ
  | m + 1, ψ => allBlock k m (BoundedFormula.all ψ)

/-- A block of `k` existential quantifiers, closing a formula to a sentence. -/
def exBlock : (k : ℕ) → setLang.BoundedFormula Empty k → setLang.BoundedFormula Empty 0
  | 0, ψ => ψ
  | k + 1, ψ => exBlock k (bEx ψ)

/-- A `Σ₂` sentence of set theory (Lévy hierarchy): a sentence of the form
`∃ x₁ … ∃ xₖ ∀ y₁ … ∀ yₘ ψ` with `ψ` a `Δ₀` formula. -/
def IsSigma2Sentence (φ : Sent) : Prop :=
  ∃ (k m : ℕ) (ψ : setLang.BoundedFormula Empty (k + m)),
    IsDelta0 ψ ∧ φ = exBlock k (allBlock k m ψ)

end UltimateL


