-- Prove2me | Definitions.Def_MonDepMW_Subpolynomial
-- name    : MonDepMW_Subpolynomial
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:47:00.770046+00:00
-- url     : https://prove2.me/theorems/54eedeb5-78a1-40ec-ad45-ca36bffff943
-- title:
--   Subpolynomial functions
-- statement:
--   A function $f:\mathbb N\to\mathbb N$ is **subpolynomial** if for every real $\varepsilon>0$,
--   $$\lim_{n\to\infty}\frac{f(n)}{n^{\varepsilon}}=0.$$
--
--   This is the notion of "almost bounded" used throughout the mission: $f(n)\leqslant\mathrm{subpoly}(n)$ means that $f$ is bounded by a subpolynomial function, and subpolynomial functions are closed under sums and products.
--
--   **Formalization Note** The paper's $\mathbb N$ is the positive integers; the Lean function also has a value at $0$, which the limit ignores. A function bounded by a subpolynomial function is itself subpolynomial, so "$k(n)\leqslant\mathrm{subpoly}(n)$" is written as `Subpolynomial k`.
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), §3, p.11

import Mathlib

set_option autoImplicit false

open Filter Topology

namespace MonDepMW

/-- **Subpolynomial functions.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), §3, p.11: "Call a function
f : N → N subpolynomial if for every real ε > 0, we have lim_{n→∞} f(n)/n^ε = 0."

**Formalization Note.** The paper's `N` is the positive integers; here `f : ℕ → ℕ` also has a value at `0`, which the
limit ignores. A function "`⩽ subpoly(n)`" (bounded by a subpolynomial function) is itself subpolynomial by squeezing,
so the statements of this mission write `Subpolynomial k` for "`k(n) ⩽ subpoly(n)`". -/
def Subpolynomial (f : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ) ^ ε) atTop (𝓝 0)

end MonDepMW


