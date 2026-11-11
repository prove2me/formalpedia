-- Prove2me | Definitions.Def_CircTrichotomy_IsOmegaPow
-- name    : CircTrichotomy_IsOmegaPow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:07.678456+00:00
-- url     : https://prove2.me/theorems/3393dd7a-c541-43a3-a3e4-434b6432607e
-- title:
--   The $\omega$-power $s^\omega$ in a finite semigroup
-- statement:
--   In a finite semigroup $S$ every element $s$ has a unique **idempotent power** $s^\omega$: an element $e=s^j$ with $j\ge1$ and $e^2=e$.
--
--   The $\omega$-power appears in the identities that define the pseudovariety $\mathbf X$.
--
--   **Formalization Note** `IsOmegaPow x e` says $e\cdot e=e$ and $e=x^{m}$ for some $m\ge1$, with the positive power `FanInSemigroup.ppow` of the published definition `FanInSemigroup_wordProd` (a semigroup has no $x^0$). In a finite semigroup exactly one $e$ satisfies it.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), §A.2, p.16

import Mathlib
import Definitions.Def_FanInSemigroup_wordProd

set_option autoImplicit false

namespace CircTrichotomy

/-- **ω-power** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*,
arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), §A.2, p.16): "In a finite
semigroup S every element s has a unique idempotent power s^ω ∈ E(S)."

`IsOmegaPow x e` says that `e` is an idempotent positive power of `x`: `e·e = e` and `e = x^m` for
some `m ≥ 1` (`FanInSemigroup.ppow x m`, the product of `m` copies of `x`, published definition
`FanInSemigroup_wordProd`).

**Formalization Note** In a finite semigroup exactly one `e` satisfies `IsOmegaPow x e` (it exists
and is unique), so `e` is `x^ω`. The power is positive: `x⁰` (a monoid unit) is never used. -/
def IsOmegaPow {S : Type} [Semigroup S] (x e : S) : Prop :=
  e * e = e ∧ ∃ m : ℕ+, FanInSemigroup.ppow x m = e

end CircTrichotomy


