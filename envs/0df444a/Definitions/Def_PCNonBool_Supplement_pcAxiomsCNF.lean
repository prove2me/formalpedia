-- Prove2me | Definitions.Def_PCNonBool_Supplement_pcAxiomsCNF
-- name    : PCNonBool_Supplement_pcAxiomsCNF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:26:37.153994+00:00
-- url     : https://prove2.me/theorems/7888e443-af14-4f97-bd37-03843d34e854
-- title:
--   Polynomial calculus encoding of a CNF over $\{0,1\}$
-- statement:
--   The standard polynomial calculus encoding of a CNF formula $\Phi$ over $\{0,1\}$-valued variables, with $1$ meaning true: each clause $C$ becomes
--   $$\prod_{x\in C}(1-x)\cdot\prod_{\neg x\in C}x,$$
--   which vanishes exactly at the assignments satisfying $C$, and each variable $x$ of $\Phi$ contributes the Boolean range axiom $x^2-x$.
--
--   Part 1 of Theorem 7.1 asserts short refutations of this set for $A(F)$.
--
--   **Formalization Note** The product is over the set of literals of the clause. For upper bounds no reduction modulo the range axioms is applied (p.11).
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §3.4, p.11 (PDF p.14); Theorem 7.1(1), p.50 (PDF p.53)

import Mathlib
import Definitions.Def_PCNonBool_Supplement_CNF

namespace PCNonBool.Supplement

open MvPolynomial

/-- The standard polynomial calculus encoding of a CNF formula over `{0, 1}`-valued variables
(Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §3.4, p.11 (PDF p.14), and Theorem 7.1(1), p.50 (PDF p.53)): with `1` meaning true, the
clause `C` becomes `∏_{x_v ∈ C} (1 - x_v) · ∏_{¬x_v ∈ C} x_v`, which vanishes exactly at the
assignments satisfying `C`; together with the Boolean range axioms `x_v² - x_v` for every variable
`v ∈ Vars(Φ)`.

**Formalization Note** The product runs over the set of literals of the clause. For upper bounds
no reduction modulo the range axioms is applied (p.11); refutations of this set are taken with
`red = LinearMap.id`. -/
noncomputable def pcAxiomsCNF (F : Type*) [Field F] (Φ : CNF) : Set (MvPolynomial ℕ F) :=
  {p | (∃ v ∈ Φ.vars, p = X v ^ 2 - X v) ∨
    (∃ C ∈ Φ, p = ∏ l ∈ C.toFinset, (if l.2 then 1 - X l.1 else X l.1))}

end PCNonBool.Supplement


