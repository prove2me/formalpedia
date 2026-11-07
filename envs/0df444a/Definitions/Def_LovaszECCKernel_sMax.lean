-- Prove2me | Definitions.Def_LovaszECCKernel_sMax
-- name    : LovaszECCKernel_sMax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:54:43.451012+00:00
-- url     : https://prove2.me/theorems/29c482f5-e54b-400b-a326-38cbc160aa3a
-- title:
--   The function $s(n)=\max\{t: t^2-t\le n\}$
-- statement:
--   For a natural number $n$, let
--   $$s(n)=\max\{t\in\mathbb Z : t^2-t\le n\}.$$
--   Since $t=1$ always qualifies and $t^2-t>n$ for $t\ge n+2$, the maximum exists and $s(n)\ge 1$; for example $s(0)=s(1)=1$, $s(2)=s(5)=2$, $s(6)=3$. It is the second summand of Lovász's bound.
--
--   **Formalization Note** The maximum is taken over $t\in\{0,\dots,n+1\}$, which contains every qualifying integer; the subtraction $t^2-t$ is in $\mathbb N$ and never truncates.
-- source:
--   Fomin, Golovach, Khargeliia, Sagunov, Simonov, Stability Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems, STOC 2027 submission (manuscript sha256 a9d53ab8…), §1, p.3 (= PDF p.3)

import Mathlib

set_option autoImplicit false

namespace LovaszECCKernel

/-- The function `s` of Lovász's bound (Fomin, Golovach, Khargeliia, Sagunov, Simonov, *Stability
Meets Kernelization: Algorithmic Extensions of the Lovász and Erdős–Goodman–Pósa Theorems*, STOC
2027 submission (manuscript sha256 a9d53ab8…), §1, p.3 (= PDF p.3)): "Let s(n) be the maximum
integer t such that t² − t ≤ n."

**Formalization Note** For `x : ℕ` the maximum is taken over `t ∈ {0, …, x + 1}`: every `t ≥ x + 2`
has `t² − t ≥ (x + 2)(x + 1) > x`, and `t = 1` always qualifies, so this is the maximum over all
integers and `sMax x ≥ 1` (`s(0) = s(1) = 1`, `s(2) = 2`). The subtraction `t ^ 2 - t` is in `ℕ`;
it never truncates because `t ≤ t²`. -/
def sMax (x : ℕ) : ℕ := Nat.findGreatest (fun t => t ^ 2 - t ≤ x) (x + 1)

end LovaszECCKernel


