-- Prove2me | Definitions.Def_StateSynthNP_warmStart
-- name    : StateSynthNP_warmStart
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:47:37.66267+00:00
-- url     : https://prove2.me/theorems/3b155f6a-398d-4e80-96b6-ed0b6de99961
-- title:
--   Prefix sums $s_y$ and warm-start weights $q_x$
-- statement:
--   Let $B$ be a finite alphabet (one block of qubits), $m\in\mathbb N$ and $p$ a function on strings $x=(x_0,\dots,x_{m-1})\in B^m$.
--
--   1. The **prefix sum** of a word $y$ is $s_y=\sum_{z}p_{yz}$, the sum of $p_x$ over all $x$ whose first $|y|$ symbols are $y$ ($s_y=0$ for $|y|>m$).
--   2. Given estimates $\hat s_y$ of the prefix sums, the **warm-start weight** of $x$ is the product of the normalized conditional ratios along $x$:
--
--   $$
--   q_x=\prod_{j=0}^{m-1}\frac{\hat s_{x_0\cdots x_j}}{\sum_{b\in B}\hat s_{x_0\cdots x_{j-1}b}} .
--   $$
--
--   With exact estimates $q_x=p_x$; this is the Grover–Rudolph chain (1)–(3), batched into blocks as on p.3.
--
--   **Formalization Note** A factor with denominator $0$ is $0$ (Lean's $a/0=0$); with estimates within a factor $1\pm\gamma$, $\gamma<1$, of the true prefix sums this happens only below a prefix of zero mass, where $q_x=p_x=0$.
-- source:
--   A. Sen, State Synthesis with an NP oracle, arXiv:2611.02370 (held version, sha256 1705b965726e24478266bc8bdb695f0c6c6e06e172eff71c247272c116f264d0), proof of Theorem 2.1, p.2 (prefix sums), p.3 (batching), p.4 ("each q_x is obtained through a product of sufficiently good approximate prefix-sums"); proof of Lemma 2.2, p.4

import Mathlib

set_option autoImplicit false

namespace StateSynthNP

/-- The prefix sum `s_y = Σ_z p_{yz}` of a function `p` on strings `x = (x_0, …, x_{m−1})` of `m`
symbols from a finite alphabet `B`: the sum of `p x` over all `x` whose first `|y|` symbols are `y`.
For `|y| > m` it is `0`.

Source: A. Sen, *State Synthesis with an NP oracle*, arXiv:2611.02370 (held version, sha256 1705b965…), proof of Theorem 2.1, p.2: "Let us define the prefix sum s_y := Σ_z p_{yz},
where z consists of all (n−|y|) length bitstrings."

**Formalization Note.** A symbol of `B` is one block of qubits; the paper batches the qubits into
blocks of `log n` qubits (p.3), i.e. `B = {0,1}^{log n}` and `m = n / log n`; `B = Bool` is the
unbatched chain. -/
noncomputable def prefixSum {B : Type} [Fintype B] [DecidableEq B] {m : ℕ}
    (p : (Fin m → B) → ℝ) (y : List B) : ℝ :=
  ∑ x : Fin m → B, if (List.ofFn x).take y.length = y then p x else 0

/-- The warm-start weight `q_x` built from estimates `ŝ_y` of the prefix sums: the product over the
`m` levels of the conditional ratios `ŝ_{y b} / Σ_{b'} ŝ_{y b'}` along `x`, where `y` is the prefix of
`x` before level `j` and `b = x_j`:
`q_x = Π_{j<m} ŝ_{x_0…x_j} / Σ_{b ∈ B} ŝ_{x_0…x_{j−1} b}`.

Source: A. Sen, *State Synthesis with an NP oracle*, arXiv:2611.02370 (held version, sha256 1705b965…), p.4: "each q_x is obtained through a product of sufficiently good approximate
prefix-sums", and proof of Lemma 2.2, p.4: "Each q_x is a product of O(n/ log n) ratios of
approximate prefix sums".

**Formalization Note.** The ratios are normalized by the sum over the siblings, so that the
conditional rotations are unitary and `Σ_x q_x = 1`. When that sum is `0`, Lean's `a / 0 = 0` makes
the factor `0`; with estimates within a factor `1 ± γ` (`γ < 1`) of the true prefix sums this happens
only below a prefix of zero mass, where `q_x = p_x = 0` anyway. -/
noncomputable def warmStart {B : Type} [Fintype B] [DecidableEq B] {m : ℕ}
    (sh : List B → ℝ) (x : Fin m → B) : ℝ :=
  ∏ j : Fin m, sh ((List.ofFn x).take (j.val + 1)) / ∑ b : B, sh ((List.ofFn x).take j.val ++ [b])

end StateSynthNP


