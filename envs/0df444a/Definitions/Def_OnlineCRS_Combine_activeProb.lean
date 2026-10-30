-- Prove2me | Definitions.Def_OnlineCRS_Combine_activeProb
-- name    : OnlineCRS_Combine_activeProb
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:14:49.550707+00:00
-- url     : https://prove2.me/theorems/740f7392-7553-4154-86e5-5adf26b726a3
-- title:
--   Law of the active set $R(x)$
-- statement:
--   For $x\in[0,1]^N$, $R(x)$ is the random subset of $N$ that contains each element $e$ independently with probability $x_e$ (the set of **active** elements). Its law is
--   $$\Pr[R(x)=A]=\prod_{e\in A}x_e\prod_{e\in N\setminus A}(1-x_e),\qquad A\subseteq N .$$
--
--   Every selectability guarantee in the paper is a probability over $R(x)$.
--
--   **Formalization Note** The product formula is defined for all real $x$; it is a probability distribution only for $x\in[0,1]^N$, and every statement using it restricts $x$ to the cube, directly or through $x\in b\cdot P$ with $P\subseteq[0,1]^N$, $b\in[0,1]$.
-- source:
--   Feldman, Svensson, Zenklusen, Online Contention Resolution Schemes, arXiv:1508.00142v2, introduction, p. 2

import Mathlib

namespace OnlineCRS.Combine

/-- **Law of the active set `R(x)`.**
Feldman, Svensson, Zenklusen, *Online Contention Resolution Schemes*, arXiv:1508.00142v2, introduction, p. 2: "the set of all active elements is distributed like a random set that
contains each element `e` independently with probability `x_e`. We denote such a set by `R(x)`."

`activeProb x A = ∏_{e ∈ A} x_e · ∏_{e ∉ A} (1 − x_e)` is `Pr[R(x) = A]`.

**Formalization Note.** The formula is defined for every `x : N → ℝ`; it is a probability
distribution on `Finset N` only for `x ∈ [0,1]^N`, and every statement using it restricts `x`
to the cube (directly, or through `x ∈ b • P` with `P ⊆ [0,1]^N` and `b ∈ [0,1]`). -/
def activeProb {N : Type*} [Fintype N] [DecidableEq N] (x : N → ℝ) (A : Finset N) : ℝ :=
  (∏ e ∈ A, x e) * ∏ e ∈ Aᶜ, (1 - x e)

end OnlineCRS.Combine


