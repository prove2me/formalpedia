-- Prove2me | Definitions.Def_CircTrichotomy_IsMild
-- name    : CircTrichotomy_IsMild
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:33.396318+00:00
-- url     : https://prove2.me/theorems/f2a6ac11-a64c-4fe2-af8f-b85db94b3e46
-- title:
--   Mild functions
-- statement:
--   A function $f:\mathbb N_{>0}\to\mathbb R_{\ge0}$ is **mild** if it is non-decreasing ($f(n)\le f(n+1)$), eventually positive ($f(n)>0$ for all but finitely many $n$), and
--   $$f(n)\in\Theta\bigl(f(\lceil\varepsilon n\rceil)\bigr)\quad\text{for every }\varepsilon>0.$$
--   Examples: $n$, $\log n$, $1$, $\log^k n$; $2^n$ is not mild.
--
--   **Formalization Note** $f:\mathbb N\to\mathbb R$ with $0\le f(n)$ and monotonicity for $n\ge1$; $\Theta$ is $O$ in both directions.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), §A.4.3, p.19

import Mathlib
import Definitions.Def_CircTrichotomy_BigO

set_option autoImplicit false

namespace CircTrichotomy

/-- **Mild function** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), §A.4.3, p.19): "Let f : ℕ>0 → ℝ≥0 be a function. We call f
non-decreasing if f(n) ≤ f(n + 1) for all n ∈ ℕ>0. We call f eventually positive if f(n) > 0 for
all but finitely many n ∈ ℕ>0. Following [GM26b] a function f : ℕ>0 → ℝ≥0 is mild if f is
non-decreasing, eventually positive, and satisfies f(n) ∈ Θ(f(⌈εn⌉)) for every ε ∈ ℝ>0."
(`f ∈ Θ(g)` iff `f ∈ O(g)` and `g ∈ O(f)`, p.17.)

**Formalization Note** `f : ℕ → ℝ`; the codomain `ℝ≥0` is the clause `0 ≤ f n` for `n ≥ 1`. -/
def IsMild (f : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, 0 < n → 0 ≤ f n) ∧ (∀ n : ℕ, 0 < n → f n ≤ f (n + 1)) ∧
    (∃ N : ℕ, ∀ n ≥ N, 0 < f n) ∧
    ∀ ε : ℝ, 0 < ε → BigO f (fun n => f ⌈ε * n⌉₊) ∧ BigO (fun n => f ⌈ε * n⌉₊) f

end CircTrichotomy


