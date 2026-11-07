-- Prove2me | Definitions.Def_HypercliqueFalse_rectEval
-- name    : HypercliqueFalse_rectEval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:29:59.398203+00:00
-- url     : https://prove2.me/theorems/c4199b06-17a7-4407-92f3-a11aed09e73f
-- title:
--   Rectangular instances of $H_u = H_{u+1,u}$ (word RAM problem)
-- statement:
--   The problem of evaluating **rectangular instances of $H_u = H_{u+1,u}$**, in which the $u+1$ variables $x_0,\dots,x_u$ range over $[n_0],\dots,[n_u]$ respectively. An instance at scale $s$ consists of sizes $n_0,\dots,n_u \le s$ and, for each $i$, an integer array $A_i$ in the $u$ variables other than $x_i$. The machine must output
--   $$
--   \sum_{x_0 \in [n_0]} \cdots \sum_{x_u \in [n_u]} \ \prod_{i=0}^{u} A_{i;\,\hat x_i},
--   $$
--   where $\hat x_i$ is $x$ with $x_i$ omitted.
--
--   These are the instances of Lemma 4.2 (with $u = h - 1$). For $H_{u+1,u}$ the $u$-element subsets of $[u+1]$ are the complements of single positions, so the array $A_i$ is the array omitting $x_i$.
--
--   **Formalization Note** Variable $j$ of $A_i$ is $x_{i.\mathrm{succAbove}(j)}$ (the variables other than $x_i$, in increasing order). The input lists the sizes and then the arrays $A_0,\dots,A_u$, each in the order of Mathlib's `finPiFinEquiv`.
-- source:
--   Fischer, The Hyperclique Hypothesis is False, arXiv:2611.03880 (held version, sha256 6bd5cf5d…7730), Lemma 4.2, p.11

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM

set_option autoImplicit false

open TrulySubcubicAPSP

namespace HypercliqueFalse

/-- **Rectangular instances of `H_u = H_{u+1,u}`**, as a problem of the published word RAM.
Fischer, *The Hyperclique Hypothesis is False*, arXiv:2611.03880 (held version, sha256
6bd5cf5d…7730), Lemma 4.2, p.11: "every instance of H_{h−1} in which the h variables range over
[n₁], …, [n_h], respectively" (here `u = h − 1`, with `u + 1` variables).

An instance at scale `s` is `⟨ν, _, A⟩`: sizes `ν i ≤ s` for the `u + 1` variables and, for each
`i`, an integer array `A i` in the `u` variables other than `x_i` (variable `j` of `A i` is
`x_{i.succAbove j}`, ranging over `[ν (i.succAbove j)]`). The program must write
`Σ_{x} Π_i A_i(x̂_i)`, the sum over all `x` with `x_i ∈ [ν i]`, into the first cell after the input.

**Formalization Note.** The input lists the `ν i`, then the arrays `A 0, …, A u`, the entries of
each in the order of `finPiFinEquiv.symm`. For `H_u` the `h`-subsets of `[u+1]` are the complements
of single positions, so array `i` is the one omitting `x_i` (the paper's `A_{x̂_i}`). The scale `s`
fixes the word size and the integer bound of `SolvedWithin`. -/
def rectEval (u : ℕ) : Problem where
  Instance s := Σ' (ν : Fin (u + 1) → ℕ) (_ : ∀ i, ν i ≤ s),
    ((i : Fin (u + 1)) → ((j : Fin u) → Fin (ν (i.succAbove j))) → ℤ)
  input x := (List.ofFn fun i => (x.1 i : ℤ)) ++
    (List.ofFn fun i => List.ofFn fun t : Fin (∏ j, x.1 (i.succAbove j)) =>
      x.2.2 i (finPiFinEquiv.symm t)).flatten
  output x f := f 0 = ∑ y : (i : Fin (u + 1)) → Fin (x.1 i), ∏ i, x.2.2 i (fun j => y (i.succAbove j))

end HypercliqueFalse


