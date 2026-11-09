-- Prove2me | Definitions.Def_LinfContractionFP_RunsWithin
-- name    : LinfContractionFP_RunsWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:13:04.197998+00:00
-- url     : https://prove2.me/theorems/49902f18-0a96-455c-883d-d22b643bc799
-- title:
--   A program halts within $T$ steps with output $x$
-- statement:
--   For a program $P$, a dimension $d$, an oracle $f:\mathbb R^d\to\mathbb R^d$, inputs $\gamma,\varepsilon$, a step budget $T\in\mathbb N$ and a vector $x\in\mathbb R^d$, $P$ **runs within $T$ steps with output $x$** if for some $t\le T$ the configuration reached after $t$ steps is halted (its program counter carries `accept`) and its output cells $\mathrm{mem}[3],\dots,\mathrm{mem}[3+d-1]$ hold $x$.
--
--   Since a halted configuration does not change, this is "halts within $T$ steps and outputs $x$". It is the form in which the running-time bound of Theorem 1 is stated.
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Theorem 1, p.2

import Mathlib
import Definitions.Def_LinfContractionFP_Machine

namespace LinfContractionFP

/-- `P`, run on input `(d, γ, ε)` with oracle `f`, halts within `T` steps with output `x`: for
some `t ≤ T` the configuration after `t` steps is halted and its output cells hold `x`.

Soleymani–Farina, arXiv:2610.30122 (held version, sha256 595b4493…), Theorem 1, p.2 ("the total
number of arithmetic operations and exact evaluations of f performed by Solve(f, ε) to return an
ε-near fixed point of f is upper bounded by …").

**Formalization Note.** Every executed instruction is one step (see `Machine`): arithmetic,
comparisons, loads, stores, pointer operations, jumps and oracle queries. A halted
configuration is unchanged by further steps, so "halted at some `t ≤ T`" is "halts within `T`
steps". -/
def RunsWithin (P : Program) (d : ℕ) (f : (Fin d → ℝ) → (Fin d → ℝ)) (γ ε : ℝ) (T : ℕ)
    (x : Fin d → ℝ) : Prop :=
  ∃ t ≤ T, Halted P (run P d f γ ε t) ∧ output d (run P d f γ ε t) = x

end LinfContractionFP


