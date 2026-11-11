-- Prove2me | Definitions.Def_CircTrichotomy_LittleO
-- name    : CircTrichotomy_LittleO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:46.337198+00:00
-- url     : https://prove2.me/theorems/10d11ecc-1126-42e8-bd6d-9d585fa13144
-- title:
--   $f\in o(g)$
-- statement:
--   For functions $f,g$ on the positive integers with values in $\mathbb R_{\ge0}$, $f\in o(g)$ means that for every $c>0$
--   $$f(n)< c\,g(n)\quad\text{for all but finitely many } n.$$
--
--   It appears in the $O(1)$-characterization ($c(L)\in o(\log n)$) and the sublinear characterization ($c(L)\in o(n)$).
--
--   **Formalization Note** $f,g:\mathbb N\to\mathbb R$; the value at $n=0$ is irrelevant.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), §A.4.1, p.17

import Mathlib

set_option autoImplicit false

namespace CircTrichotomy

/-- **Little-o** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*,
arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), §A.4.1, p.17): "Recall that
f ∈ o(g) if for all c ∈ ℝ>0 we have f(n) < c · g(n) for all but finitely many n ∈ ℕ>0."

**Formalization Note** The functions are `ℕ → ℝ`; "for all but finitely many n" is
`∃ N, ∀ n ≥ N`, so the value at `n = 0` is never seen. -/
def LittleO (f g : ℕ → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∃ N : ℕ, ∀ n ≥ N, f n < c * g n

end CircTrichotomy


