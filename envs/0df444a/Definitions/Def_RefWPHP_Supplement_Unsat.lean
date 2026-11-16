-- Prove2me | Definitions.Def_RefWPHP_Supplement_Unsat
-- name    : RefWPHP_Supplement_Unsat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:19:34.351757+00:00
-- url     : https://prove2.me/theorems/73dabe07-9683-49fd-89f1-91f8d004c4dd
-- title:
--   Unsatisfiability of a CNF formula $\varphi = C_1 \wedge \dots \wedge C_m$
-- statement:
--   Let $\varphi = C_1 \wedge \dots \wedge C_m$ be a CNF formula over the variables $x_1, \dots, x_n$, each clause $C_A$ a set of literals. The formula is **unsatisfiable** if every assignment $a \in \{0,1\}^n$ falsifies some clause:
--
--   $$
--   \forall a \in \{0,1\}^n \;\exists A \in [m] \;\forall \ell \in C_A:\; \ell \text{ is false under } a .
--   $$
--
--   Unsatisfiability is the standing hypothesis of the paper's lower bounds (Theorems 4.4, 4.7) and of its families of formulas (Definitions 4.2, 4.3, Theorem 6.7).
--
--   **Formalization Note** A CNF is the base mission's `φ : Fin m → Finset (Lit n)`, the literal `(i, true)` being $x_i$ and `(i, false)` being $\neg x_i$. The number $n$ counts every variable, including those that occur in no clause, and $m$ counts clauses with repetition.
-- source:
--   Arteche, Resolution Lower Bounds versus the Weak Pigeonhole Principle, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), §2.1.1, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_RefWPHP_LayeredRef

namespace RefWPHP

namespace Supplement

/-- Unsatisfiability of a CNF formula `φ = C_1 ∧ ⋯ ∧ C_m` over the variables `x_1, …, x_n`, as in
N. Arteche, *Resolution Lower Bounds versus the Weak Pigeonhole Principle*, STOC 2027 submission
(held manuscript, sha256 ee75d7f1…), §2.1.1, p.13 (PDF 15): every assignment `a : Fin n → Bool`
falsifies some clause `C_A`, i.e. no literal `(i, b) ∈ C_A` has `a i = b`.

**Formalization Note.** A CNF is the base mission's `φ : Fin m → Finset (Lit n)` (clause `A` is the
set of its literals, `(i, true)` is `x_i`, `(i, false)` is `¬x_i`); `n` is the number of variables
even if some do not occur, and `m` counts clauses with repetition. -/
def Unsat {n m : ℕ} (φ : Fin m → Finset (Lit n)) : Prop :=
  ∀ a : Fin n → Bool, ∃ A : Fin m, ∀ ℓ ∈ φ A, a ℓ.1 ≠ ℓ.2

end Supplement

end RefWPHP


