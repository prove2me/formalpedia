-- Prove2me | Definitions.Def_FRouting_StrMachine
-- name    : FRouting_StrMachine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:09.905418+00:00
-- url     : https://prove2.me/theorems/94451b99-ab9b-4a30-9f2e-b4a0be5a0e79
-- title:
--   Classical machines, time bounds and time constructibility
-- statement:
--   A classical machine on binary strings is a Mathlib `FinTM2` with input and output alphabets identified with $\{0,1\}$. `PrintsInTime M w out t` says that $M$ on $w$ halts within $t$ steps with exactly $\mathrm{out}$ on its output stack. A function $g$ is **time-constructible** if some machine prints $g(n)$ in binary from $1^n$ within $C\,g(n)+C$ steps.
--
--   **Formalization Note** `budget B n` is $\max(1,B(n))$. A run takes at least one step, and $T(0)=0$ is allowed by $T(n)\ge n$ (for example $T(n)=n^2$), so bound $0$ could not be met. The budget changes $B$ only where $B=0$.
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), Definition 1.2, p.4; Definition 3.6, p.15

import Definitions.Def_QAlgorithms_ClassicalStringComputability

set_option autoImplicit false

namespace FRouting

open QAlgorithms.Complexity

/-- **A classical deterministic machine on binary strings**: a Mathlib `FinTM2` together with
identifications of its input and output alphabets with `Bool`. Renard, *Computational Bounds for
f-Routing*, arXiv:2609.40278 (held copy, sha256 4a327f29…), Definitions 1.2 and 3.6, pp.4, 15:
"classical Turing machines", "deterministic Turing machines". -/
structure StrMachine where
  /-- The multi-stack machine. -/
  tm : Turing.FinTM2
  /-- Its input alphabet is `Bool`. -/
  inAlpha : tm.Γ tm.k₀ ≃ Bool
  /-- Its output alphabet is `Bool`. -/
  outAlpha : tm.Γ tm.k₁ ≃ Bool

/-- `M` started on `w` halts within `t` steps with exactly `out` on its output stack. A step executes
one statement of the `FinTM2`. -/
def PrintsInTime (M : StrMachine) (w out : Str) (t : ℕ) : Prop :=
  Nonempty (Turing.TM2OutputsInTime M.tm (w.map M.inAlpha.symm)
    (some (out.map M.outAlpha.symm)) t)

/-- **The budget of a time bound `B` at length `n`**: `B n`, but at least `1`.

**Formalization Note** The paper's time bounds have `T(n) ≥ n` only, so `T(0) = 0` for `T(n) = n²`.
A `FinTM2` run takes at least one step, so bound `0` could not be met by any machine: every strategy
family would be excluded for such `T` (the theorem would be vacuous), and `QSZK(T)` would be empty at
length `0`. The budget changes `B` at the lengths where `B = 0` and nowhere else. -/
def budget (B : ℕ → ℕ) (n : ℕ) : ℕ := max 1 (B n)

/-- **Time-constructible** (Definition 1.2, p.4; Definition 3.6, p.15): some machine prints `g n` in
binary from `1ⁿ` within `C · g n + C` steps. -/
def IsTimeConstructible (g : ℕ → ℕ) : Prop :=
  ∃ (M : StrMachine) (C : ℕ), ∀ n,
    PrintsInTime M (List.replicate n true) (g n).bits (C * g n + C)

end FRouting


