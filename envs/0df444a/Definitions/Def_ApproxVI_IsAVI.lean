-- Prove2me | Definitions.Def_ApproxVI_IsAVI
-- name    : ApproxVI_IsAVI
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:34.282841+00:00
-- url     : https://prove2.me/theorems/c9d8fc22-7846-49ad-a9e6-6d3d2b246b42
-- title:
--   The approximate value iteration recursion (5)
-- statement:
--   Given a map $T:\mathbb R^d\to\mathbb R^d$ and step sizes $a(n)$, a sequence $(J_n)_{n\ge0}$ follows **approximate value iteration** with approximation errors $(\epsilon_n)_{n\ge0}$ and noise $(M_{n+1})_{n\ge0}$ if
--
--   $$
--   J_{n+1}=J_n+a(n)\big[TJ_n-J_n+\epsilon_n+M_{n+1}\big],\qquad n\ge0.
--   $$
--
--   This is one sample path of AVI: $\epsilon_n=ATJ_n-TJ_n$ is the error of the approximate Bellman operator and $M_{n+1}$ the sampling noise.
--
--   **Formalization Note** $T$ is an arbitrary map here (the paper's $T$ is the Bellman operator (3)); the theorems add the contraction assumption (AV1). The term $M_0$ does not occur.
-- source:
--   Ramaswamy & Bhatnagar, Analyzing Approximate Value Iteration Algorithms, arXiv:1709.04673v5, §3, eq. (5), p.6

import Mathlib

namespace ApproxVI

/-- The approximate value iteration recursion (5) of Ramaswamy & Bhatnagar, *Analyzing
Approximate Value Iteration Algorithms*, arXiv:1709.04673v5, §3, p.6:
`J_{n+1} = J_n + a(n) [T J_n − J_n + ε_n + M_{n+1}]`, `n ≥ 0`, for one sample path:
`J n` is the iterate, `e n` the approximation error `ε_n`, `M (n+1)` the noise `M_{n+1}`.

**Formalization Note** `ℝ^d` is `Fin d → ℝ`. `T` is any map; the page's `T` is the Bellman
operator (3), and the statements add the contraction property (AV1). `M 0` does not occur. -/
def IsAVI {d : ℕ} (T : (Fin d → ℝ) → (Fin d → ℝ)) (a : ℕ → ℝ)
    (J e M : ℕ → Fin d → ℝ) : Prop :=
  ∀ n, J (n + 1) = J n + a n • (T (J n) - J n + e n + M (n + 1))

end ApproxVI


