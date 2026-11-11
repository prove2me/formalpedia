-- Prove2me | Definitions.Def_CircTrichotomy_circuitComplexity
-- name    : CircTrichotomy_circuitComplexity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:38.43794+00:00
-- url     : https://prove2.me/theorems/b81355b6-e738-4e42-a9b0-07a6d0bca4d1
-- title:
--   Circuit complexity $c(L)(n)$
-- statement:
--   The **circuit complexity** of a language $L\subseteq\Sigma^+$ is the function
--   $$c(L):n\mapsto\min\{|C| : C \text{ is an } n\text{-circuit computing } L\cap\Sigma^n\},$$
--   the least number of non-input gates of a single-output $n$-circuit that accepts exactly the words of length $n$ in $L$.
--
--   The minimum is over a non-empty set for every $n\ge1$ (a DNF circuit exists), and $c(L)(n)\ge1$. The trichotomy theorem classifies the growth of $c(L)$ for regular $L$.
--
--   **Formalization Note** The minimum is `sInf` of a set of natural numbers; at $n=0$ (outside the domain) there is no $0$-circuit and the value is $0$, which no asymptotic class sees.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), (19), p.18

import Mathlib
import Definitions.Def_CircTrichotomy_Circuit

set_option autoImplicit false

namespace CircTrichotomy

/-- **Circuit complexity `c(L)`** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular
Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), (19), p.18):
"c(L) : n ↦ min{|C| : C is an n-circuit computing L ∩ Σⁿ}."

`circuitComplexity L n` is the least size of a single-output `n`-circuit `C` with
`L(C) = L ∩ αⁿ`, i.e. accepting exactly the words of length `n` in `L`.

**Formalization Note** The minimum is `sInf` of a set of natural numbers. For `n ≥ 1` the set is
non-empty (p.18: "given any language L ⊆ Σ⁺ and any input length n ∈ ℕ>0 there exists an
n-circuit Cₙ such that L ∩ Σⁿ = L(Cₙ)"), so `sInf` is the true minimum. At `n = 0` there is no
`0`-circuit and the value `0` is outside the paper's domain ℕ>0; no asymptotic class sees it. -/
noncomputable def circuitComplexity {α : Type} (L : Language α) (n : ℕ) : ℕ :=
  sInf {s : ℕ | ∃ C : Circuit α n 1, C.size = s ∧
    ∀ w : Fin n → α, C.Accepts w ↔ List.ofFn w ∈ L}

end CircTrichotomy


