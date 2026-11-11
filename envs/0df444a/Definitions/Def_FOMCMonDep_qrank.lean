-- Prove2me | Definitions.Def_FOMCMonDep_qrank
-- name    : FOMCMonDep_qrank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:22:09.080035+00:00
-- url     : https://prove2.me/theorems/c7b8b24f-606b-4fc2-b0bf-daccc3e73c93
-- title:
--   Quantifier rank of a first-order formula
-- statement:
--   The **quantifier rank** $\mathrm{qr}(\varphi)$ of a first-order formula $\varphi$ is the maximal nesting depth of quantifiers in $\varphi$: atoms ($\bot$, equalities $t_1=t_2$ and relation atoms $R(t_1,\dots,t_m)$) have rank $0$, an implication $\varphi\to\psi$ has rank $\max(\mathrm{qr}(\varphi),\mathrm{qr}(\psi))$, and a universal quantification $\forall x\,\varphi$ has rank $\mathrm{qr}(\varphi)+1$.
--
--   Types of quantifier rank $q$ (the sets of formulas of quantifier rank at most $q$ satisfied by a tuple) are the basic objects of the whole mission: the type bounds of Part I, the type-based width of construction sequences, and the definability of partial graphs are all measured in quantifier rank.
--
--   **Formalization Note** Mathlib's first-order formulas are built from $\bot$, equality, relation atoms, $\to$ and $\forall$; negation, the other connectives and $\exists=\neg\forall\neg$ are abbreviations and get the rank of their expansion, which is the usual quantifier rank. Mathlib has no such function.
-- source:
--   Dreier, Mählmann, Toruńczyk, First-Order Model Checking on Monadically Dependent Graph Classes, STOC 2027 submission (held manuscript, sha256 98040ab52fa9eeb6577af7e100d83ff2a156142fed0a0178723cec8569510454), §3, p.11 (PDF 13)

import Mathlib

set_option autoImplicit false

open FirstOrder FirstOrder.Language

namespace FOMCMonDep

/-- **Quantifier rank.** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §3, p.11 (PDF 13), and §1, p.2 (PDF 4): "The type
tp^G_q(v̄/U) is the set of formulas of quantifier rank at most q". The quantifier rank of a first-order formula is the
maximal nesting depth of quantifiers.

**Formalization Note.** Mathlib's first-order formulas are built from `⊥`, equality, relation atoms, `→` and `∀`;
negation, the other connectives and `∃` are abbreviations (`∃ = ¬∀¬`), so they get the rank of their expansion: atoms
have rank `0`, `φ → ψ` has the larger rank of the two, and `∀ φ` adds `1`. Mathlib has no such function. -/
def qrank {L : Language} {α : Type*} : {l : ℕ} → L.BoundedFormula α l → ℕ
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel _ _ => 0
  | _, .imp φ ψ => max (qrank φ) (qrank ψ)
  | _, .all φ => qrank φ + 1

end FOMCMonDep


