-- Prove2me | Definitions.Def_WICanon_PolyBounds
-- name    : WICanon_PolyBounds
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:00:31.422994+00:00
-- url     : https://prove2.me/theorems/3650389c-6d0a-45ba-97ac-e31b6c058f60
-- title:
--   Inverse-polynomial functions and polynomially bounded lengths
-- statement:
--   A function $\varepsilon:\mathbb N\to\mathbb R$ is in $1/\mathrm{poly}$ if $\varepsilon(n)\ge 1/p(n)$ for a polynomial $p\ge 1$. The error term $1/q$ of "for every polynomial $q$" is $1/(q(n)+1)$. A **polynomially bounded length function** is a function $g:\mathbb N\to\mathbb N$ with $g(n)\le p(n)$ for a polynomial $p$ such that $1^{g(n)}$ is computable from any string of length $n$ in polynomial time; coin counts and round counts have this form.
--
--   **Formalization Note** No upper bound is imposed on $\varepsilon$, so the class contains each $1/p$ and every larger function.
-- source:
--   Arnon, Mazor, Pass, Silbak, Does Witness Indistinguishability Require Cryptography?, STOC 2027 submission manuscript (sha256 3f78ec3d…), §2, p.11; p.13

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_ClassicalUnaryInput

set_option autoImplicit false

namespace WICanon

open QAlgorithms.Complexity

/-- **`ε ∈ 1/poly`** (Arnon, Mazor, Pass, Silbak, STOC 2027 submission manuscript, sha256 3f78ec3d…,
§2, p.11; Theorems 3.3, 3.25): `ε(n) ≥ 1/p(n)` for a polynomial `p` that is at least `1` everywhere.

**Formalization Note.** No upper bound on `ε` is imposed, so this covers every `1/p` and every
larger function. -/
def InvPoly (ε : ℕ → ℝ) : Prop :=
  ∃ p : Polynomial ℕ, (∀ n, 1 ≤ p.eval n) ∧ ∀ n, 1 / ((p.eval n : ℕ) : ℝ) ≤ ε n

/-- The error term `1/q` of "for every polynomial `q`" (Theorems 2.11, 3.1).

**Formalization Note.** Written `1/(q(n) + 1)` so that it is meaningful when `q(n) = 0`. Every
polynomial `q ≥ 1` is covered, with a slightly smaller (stronger) term. -/
noncomputable def oneOver (q : Polynomial ℕ) (n : ℕ) : ℝ :=
  1 / (((q.eval n : ℕ) : ℝ) + 1)

/-- A polynomially bounded length function that a machine can compute from `1^n`: the coin counts,
round counts and domain lengths of §2 ("k = k(|x|) ∈ poly", p.13). -/
def IsPolyLen (g : ℕ → ℕ) : Prop :=
  (∃ p : Polynomial ℕ, ∀ n, g n ≤ p.eval n) ∧ PolyTimeComputable fun s => unary (g s.length)

end WICanon


