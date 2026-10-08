-- Prove2me | Definitions.Def_KellyReversibility_Networks_ClassCountQueue
-- name    : KellyReversibility_Networks_ClassCountQueue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:24:19.226394+00:00
-- url     : https://prove2.me/theorems/8a4708a2-49bd-4121-ac08-f2e41f5f2dd0
-- title:
--   The multiclass queue of §3.5 with arrival rates $\nu(c)$ and departure intensities $\nu(c)\phi_c(n)$
-- statement:
--   This is the queue considered at the start of Section 3.5. Its state is the vector $\mathbf n=(n(1),\dots,n(K))$, where $n(c)$ is the number of customers of class $c$ in the queue. Customers of class $c$ arrive in a Poisson stream of rate $\nu(c)$, the streams being independent, and a customer of class $c$ leaves with probability intensity $\nu(c)\phi_c(\mathbf n)$ when the state is $\mathbf n$. Writing $\mathbf e_c$ for the $c$-th unit vector, the transition rates are
--   $$q(\mathbf n,\mathbf n+\mathbf e_c)=\nu(c),\qquad q(\mathbf n,\mathbf n-\mathbf e_c)=\nu(c)\,\phi_c(\mathbf n)\ \ \text{if } n(c)>0,$$
--   and all other rates are $0$.
--
--   This queue is the subject of Lemma 3.13, which characterizes when it is reversible.
--
--   **Formalization Note** The classes are `Fin K` (the book allows a countable class set); the state space is `Fin K → ℕ`. A departure of class $c$ is possible only when $n(c)>0$, so no rate is read through truncated subtraction.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 89, §3.5 (the queue preceding Lemma 3.13)

import Mathlib

namespace KellyReversibility.Networks

/-- The queue of §3.5 (p. 89) with `K` customer classes, whose state is the vector
`n = (n(1), …, n(K))` of class counts. Class-`c` customers arrive in a Poisson stream of rate
`ν(c)`, and a class-`c` customer leaves with probability intensity `ν(c) φ_c(n)` when the state is
`n`. The rate from `n` to `n + e_c` is `ν(c)`; the rate from `n` to `n - e_c` is `ν(c) φ_c(n)` when
`n(c) > 0`; every other rate is `0`. -/
noncomputable def classCountRates {K : ℕ} (ν : Fin K → ℝ) (φ : Fin K → (Fin K → ℕ) → ℝ)
    (n m : Fin K → ℕ) : ℝ :=
  ∑ c : Fin K,
    ((if m = Function.update n c (n c + 1) then ν c else 0) +
     (if 0 < n c ∧ m = Function.update n c (n c - 1) then ν c * φ c n else 0))

end KellyReversibility.Networks


