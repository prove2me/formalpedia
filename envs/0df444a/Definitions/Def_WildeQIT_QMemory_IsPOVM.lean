-- Prove2me | Definitions.Def_WildeQIT_QMemory_IsPOVM
-- name    : WildeQIT_QMemory_IsPOVM
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:16.211002+00:00
-- url     : https://prove2.me/theorems/41aac017-1c9f-4307-8277-f49c18675584
-- title:
--   POVM: $\Lambda_x\ge 0$, $\sum_x\Lambda_x=I$
-- statement:
--   A **POVM** (positive operator-valued measure) on $\mathcal H_A$ with finite outcome set $\mathcal X$ is a family $\{\Lambda_x\}_{x\in\mathcal X}$ of operators on $\mathcal H_A$ such that
--
--   1. every $\Lambda_x$ is positive semi-definite, and
--   2. $\sum_x\Lambda_x=I$.
--
--   Measuring the POVM on a state $\rho$ gives outcome $x$ with probability $\mathrm{Tr}\{\Lambda_x\rho\}$.
--
--   **Formalization Note** Operators are complex matrices indexed by the finite type `a`; outcomes form a finite type `x`.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definition 4.2.1, eq. (4.95), p. 134, as used in §11.1.2 (p. 323) and §11.9.3 (pp. 353–354)

import Mathlib

open scoped ComplexOrder

namespace WildeQIT.QMemory

/-- **POVM** (Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8,
Definition 4.2.1, used in §§11.1.2 and 11.9.3): a finite family `{Λ_x}` of positive
semi-definite operators with `∑_x Λ_x = I`.

**Formalization Note** The outcome set is a finite type `x`; operators are complex matrices
indexed by the finite type `a`. -/
def IsPOVM {a x : Type} [Fintype a] [DecidableEq a] [Fintype x]
    (Λ : x → Matrix a a ℂ) : Prop :=
  (∀ i, (Λ i).PosSemidef) ∧ ∑ i, Λ i = 1

end WildeQIT.QMemory


