-- Prove2me | Definitions.Def_TimeSpaceMA_Supplement_TimeConstructible
-- name    : TimeSpaceMA_Supplement_TimeConstructible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T01:43:53.821415+00:00
-- url     : https://prove2.me/theorems/c005f562-de43-465d-a885-4d30f5e27fe9
-- title:
--   Time-constructible functions
-- statement:
--   A function $t:\mathbb N\to\mathbb N$ is **time-constructible** if one fixed machine, on the unary input $1^n$, writes a unary word of length $t(n)$ and halts in $O(t(n))$ time.
--
--   This is the standard clock-machine form of the hypothesis in Theorem 4.1. The clock may have any fixed finite number of sequential work tapes; time constructibility constrains the bound $t$, not the one-tape language decider.
--
--   **Formalization Note** The clock is a published `TimeSpaceMA.RATM`. On one output tape, cells $0,\ldots,t(n)-1$ carry a nonblank marker and cell $t(n)$ is blank; the machine is halted after at most $C t(n)+C$ steps for one uniform $C>0$.
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), Theorem 4.1, p.23 (standard term used without a separate definition)

import Definitions.Def_TimeSpaceMA_RATM

set_option autoImplicit false

namespace TimeSpaceMA
namespace Supplement

/-- A function `t : ℕ → ℕ` is time-constructible (Williams–Xi, *Short Non-Interactive
Proofs for Time-Space Computations*, STOC 2027 submission, manuscript sha256 184c2f95…,
Theorem 4.1, p.23) when one fixed machine, on unary input of length `n`, writes a unary word of
length `t n` and halts in `O(t n)` time.

**Formalization Note** The paper uses the standard complexity-theoretic term without defining a
machine. Here the clock is a published `TimeSpaceMA.RATM`; its work-tape count is unrestricted,
because time constructibility is a property of the bound rather than the one-tape decider. The
unary input is `true^n`. On one output tape, cells `0,…,t(n)-1` contain a nonblank marker and cell
`t(n)` is blank. The uniform time cap is `C·t(n)+C`, with `C>0`. -/
def TimeConstructible (t : ℕ → ℕ) : Prop :=
  ∃ (M : RATM) (out : Fin M.k) (mark : M.Γ) (C : ℕ), mark ≠ M.blank ∧ 0 < C ∧
    ∀ n : ℕ,
      let c := M.run (List.replicate n true) (C * t n + C)
      (c.state = M.qaccept ∨ c.state = M.qreject) ∧
        (∀ j < t n, c.tape out (j : ℤ) = mark) ∧ c.tape out (t n : ℤ) = M.blank

end Supplement
end TimeSpaceMA


