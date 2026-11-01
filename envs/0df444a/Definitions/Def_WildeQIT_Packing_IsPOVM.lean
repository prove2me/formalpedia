-- Prove2me | Definitions.Def_WildeQIT_Packing_IsPOVM
-- name    : WildeQIT_Packing_IsPOVM
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:04.24865+00:00
-- url     : https://prove2.me/theorems/14f60833-3eb4-4f12-8842-230b31c247da
-- title:
--   POVM $\{\Lambda_m\}$: $\Lambda_m\ge0$, $\sum_m\Lambda_m=I$
-- statement:
--   A family $\{\Lambda_m\}_{m\in\mathcal M}$ of operators on a finite-dimensional Hilbert space $\mathcal H$, indexed by a finite outcome set $\mathcal M$, is a **positive operator-valued measure (POVM)** when
--
--   1. every element is positive semi-definite, $\Lambda_m\ge0$, and
--   2. the elements sum to the identity, $\sum_{m\in\mathcal M}\Lambda_m=I$.
--
--   The probability of outcome $m$ on a state $\rho$ is $\operatorname{Tr}\{\Lambda_m\rho\}$. In the packing lemma the receiver decodes the message with a POVM indexed by the message set.
--
--   **Formalization Note** Operators are complex square matrices indexed by a finite type.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §4.2.1 (POVM formalism); used in §16.2, p. 487

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §4.2.1 (POVM formalism),
used in §16.2, p. 487 ("Bob performs some measurement described by a POVM {Λ_m}_{m∈M}").
-/

open Matrix
open scoped ComplexOrder

namespace WildeQIT.Packing

/-- **POVM** (Wilde, arXiv:1106.1445v8, §4.2.1; used in §16.2, p. 487). A family `{Λ_m}_{m ∈ ι}`
of operators on a finite-dimensional Hilbert space is a positive operator-valued measure when every
element is positive semi-definite and the elements sum to the identity:
`Λ_m ≥ 0` for all `m`, and `∑_m Λ_m = I`.

**Formalization Note.** Operators are complex matrices indexed by a finite type `n`; the outcome
set `ι` is finite. -/
def IsPOVM {ι n : Type} [Fintype ι] [Fintype n] [DecidableEq n]
    (Λ : ι → Matrix n n ℂ) : Prop :=
  (∀ m, (Λ m).PosSemidef) ∧ ∑ m, Λ m = 1

end WildeQIT.Packing


