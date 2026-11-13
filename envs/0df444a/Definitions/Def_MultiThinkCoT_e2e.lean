-- Prove2me | Definitions.Def_MultiThinkCoT_e2e
-- name    : MultiThinkCoT_e2e
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:40:25.435199+00:00
-- url     : https://prove2.me/theorems/aa323d32-4ac7-4a7c-b8df-9655a1119321
-- title:
--   Next-token generators, the end-to-end map $f^{\mathrm{e2e}\text{-}T}$ and the chain of thought $f^{\mathrm{CoT}\text{-}T}$
-- statement:
--   A **sequence-to-next-token generator** (a *thinker*) is a function $f:\{0,1\}^*\to\{0,1\}$. Its **apply-and-append map** is $\bar f(x)=[x,f(x)]\in\{0,1\}^{|x|+1}$. For a generation length $T$, the **end-to-end map** and the **chain of thought** of $f$ on $x$ are
--
--   $$
--   f^{\mathrm{e2e}\text{-}T}(x)=\big(\bar f^{\,T}(x)\big)[-1],\qquad f^{\mathrm{CoT}\text{-}T}(x)=\big[f^{\mathrm{e2e}\text{-}1}(x),\dots,f^{\mathrm{e2e}\text{-}T}(x)\big]\in\{0,1\}^T,
--   $$
--
--   where $\bar f^{\,T}$ is the $T$-fold iterate and $z[-1]$ is the last bit of the string $z$. Thus $f^{\mathrm{CoT}\text{-}T}(x)$ is the list of the $T$ tokens that autoregressive generation appends to $x$, and $f^{\mathrm{e2e}\text{-}T}(x)$ is the last of them.
--
--   These are the objects of the whole mission: classes of end-to-end maps are what is learned, and CoTs are the supervision.
--
--   **Formalization Note** Strings are lists of Booleans read left to right and a generator is a function on them (`Gen`). The end-to-end map takes the last element of the iterate with default `false`; for $T\ge1$ the iterate is nonempty, and for $T=0$ the map returns the last bit of the input (the paper only uses $T\ge1$). The CoT is the suffix of the iterate after the input.
-- source:
--   Joshi, Magen, Srebro, Tsilivis, Vardi, Learning to Think from Multiple Thinkers: How Chain-of-Thought Heterogeneity Affects Efficient Learnability, arXiv:2604.24737 (held version, sha256 e663a640…), §1.1, eqs. (1)–(2), p.3 (PDF p.3)

import Mathlib

namespace MultiThinkCoT

/-!
# Next-token generators, the end-to-end map (1) and the chain of thought (2)

N. Joshi, R. Magen, N. Srebro, N. Tsilivis, G. Vardi, *Learning to Think from Multiple Thinkers:
How Chain-of-Thought Heterogeneity Affects Efficient Learnability*, arXiv:2604.24737 (held
version, sha256 e663a640…), §1.1, eqs. (1)–(2), p.3 (PDF p.3).

A sequence-to-next-token generator is a function `f : {0,1}* → {0,1}`; the apply-and-append map
is `f̄(x) = [x, f(x)]`. After `T` autoregressive steps the end-to-end output is
`f^{e2e-T}(x) = (f̄^T(x))[−1]`, the last bit, and the chain of thought is
`f^{CoT-T}(x) = [f^{e2e-1}(x), …, f^{e2e-T}(x)] ∈ {0,1}^T`.

**Formalization Note.**
* Strings `{0,1}*` are `List Bool`, read left to right; a generator is `List Bool → Bool`.
* `e2e f T x` is the last element of `(step f)^[T] x`, with `List.getLastD … false`; for `T ≥ 1`
  the iterate is nonempty so the default is never used. `T : ℕ` is unrestricted: at `T = 0` the
  map returns the last bit of the input (or `false` on the empty input) for every `f`, and the
  CoT is empty.
* `cot f T x` is the suffix of `(step f)^[T] x` after the input, i.e. the `T` generated tokens
  `[f^{e2e-1}(x), …, f^{e2e-T}(x)]`.
-/

/-- A sequence-to-next-token generator (a *thinker*) `f : {0,1}* → {0,1}`. -/
abbrev Gen : Type := List Bool → Bool

/-- The apply-and-append map `f̄(x) = [x, f(x)]`. -/
def step (f : Gen) (x : List Bool) : List Bool := x ++ [f x]

/-- (1) The end-to-end map `f^{e2e-T}(x) = (f̄^T(x))[−1]`. -/
def e2e (f : Gen) (T : ℕ) (x : List Bool) : Bool := ((step f)^[T] x).getLastD false

/-- (2) The chain of thought `f^{CoT-T}(x) = [f^{e2e-1}(x), …, f^{e2e-T}(x)]`: the `T` tokens
appended to `x` by `T` autoregressive steps. -/
def cot (f : Gen) (T : ℕ) (x : List Bool) : List Bool := ((step f)^[T] x).drop x.length

end MultiThinkCoT


