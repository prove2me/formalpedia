-- Prove2me | Definitions.Def_MantriCVQ_Supplement_HeightFunction
-- name    : MantriCVQ_Supplement_HeightFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:01:13.809895+00:00
-- url     : https://prove2.me/theorems/09710c16-c091-486c-a778-0e101d597e89
-- title:
--   Height function $h$ (§1.1)
-- statement:
--   A **height function** is a function $h$ from the positive integers to the nonnegative integers such that
--
--   1. $h$ is computable from $1^n$ in polynomial time (by a classical machine with no oracle);
--   2. $h$ is unbounded: for every $H$ there is $n\ge1$ with $h(n)\ge H$;
--   3. $h(n)\le h_{\max}(n)=\lfloor \log_2 n/8\rfloor$ for every $n\ge1$.
--
--   The height function fixes the height $h(n)$ of the recursive instance stored in the oracle at input length $n$. Unboundedness gives, for every constant $h_0$, infinitely many lengths with $h(n)\ge h_0$, as the oracle construction needs; the bound $h\le h_{\max}$ keeps the instances well defined.
--
--   **Formalization Note** The value at $n=0$ is not constrained. The output of the machine is $h(n)$ in unary ($1^{h(n)}0$); since $h(n)\le\log_2 n$ this is equivalent to a binary output.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §1.1, p. 3 (PDF p. 5), definition of a height function

import Mathlib
import Definitions.Def_MantriCVQ_dimsRange
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms.Complexity

namespace MantriCVQ.Supplement

/-- A height function (Mantri, *Classical Verification of Quantum Computation Beyond the Polynomial
Hierarchy*, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §1.1, p. 3 (PDF p. 5): "A height function
is a function `h` from the positive integers to the nonnegative integers, computable from `1^n` in
polynomial time, that is unbounded and satisfies `h(n) ≤ h_max(n)` for every `n`").

**Formalization Note** The domain of the paper is the positive integers; the value `h 0` is never
used, so unboundedness and the bound `h n ≤ h_max(n)` are stated for `n ≥ 1`. "Computable from `1^n`
in polynomial time" is a classical polynomial-time machine with no oracle mapping `1^n` to `h(n)`
written with the shared `encNat` (unary, `1^{h(n)} 0`); since `h(n) ≤ h_max(n) ≤ log₂ n`, this is
equivalent to a binary output. -/
def HeightFunction (h : ℕ → ℕ) : Prop :=
  (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ n : ℕ, f (unary n) = encNat (h n)) ∧
    (∀ H : ℕ, ∃ n : ℕ, 1 ≤ n ∧ H ≤ h n) ∧
    ∀ n : ℕ, 1 ≤ n → h n ≤ hmax n

end MantriCVQ.Supplement


