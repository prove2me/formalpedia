-- Prove2me | Definitions.Def_RevisitXor_xorPow
-- name    : RevisitXor_xorPow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:03:31.610024+00:00
-- url     : https://prove2.me/theorems/d653d25a-56c5-4682-8c70-2f1d3bc515e6
-- title:
--   XOR power $f^{\oplus k}$
-- statement:
--   For $f:A\to[2]$ and $k\ge0$, the **XOR of $k$ independent copies** of $f$ is
--
--   $$f^{\oplus k}:A^k\ni(x_1,\dots,x_k)\mapsto f(x_1)\oplus f(x_2)\oplus\cdots\oplus f(x_k)\in[2].$$
--
--   With $A=[2]^n$ this is a function on $[2]^{kn}$. Yao's XOR lemma says that the correlation of $f^{\oplus k}$ with small circuits decays roughly like the $k$-th power of the correlation of $f$.
--
--   **Formalization Note** $\oplus$ is addition in `ZMod 2`. The input $(x_1,\dots,x_k)$ is a function `Fin k → A`. For $k=0$ the empty sum gives the constant $0$.
-- source:
--   Viola, Revisiting the XOR lemma, STOC 2027 submission (manuscript of August 25, 2026, sha256 3b49e10d…716), p.1

import Mathlib

namespace RevisitXor

/-- **XOR power.** Viola, *Revisiting the XOR lemma*, STOC 2027 submission (manuscript of
August 25, 2026, sha256 3b49e10d…716), p.1: "the XOR of k independent copies of f, denoted
f^{⊕k} : [2]^{kn} ∋ (x1, x2, . . . , xk) → f(x1) ⊕ f(x2) ⊕ · · · ⊕ f(xk) ∈ [2]".

**Formalization Note.** `[2]` is `ZMod 2`, so `⊕` is `+` and the XOR of the `k` values is their
sum. The input `(x₁, …, x_k) ∈ [2]^{kn}` is curried as a function `Fin k → α` (with `α = [2]^n`).
For `k = 0` the empty sum gives the constant `0`. -/
def xorPow {α : Type*} (f : α → ZMod 2) (k : ℕ) : (Fin k → α) → ZMod 2 :=
  fun x => ∑ j, f (x j)

end RevisitXor


