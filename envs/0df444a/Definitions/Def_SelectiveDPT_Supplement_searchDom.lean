-- Prove2me | Definitions.Def_SelectiveDPT_Supplement_searchDom
-- name    : SelectiveDPT_Supplement_searchDom
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:24:49.444592+00:00
-- url     : https://prove2.me/theorems/748031b5-05c8-4422-9790-f2becea41292
-- title:
--   $\mathsf{SEARCH}_n$: weight-one domain, relation and uniform hard distribution
-- statement:
--   Let $n \ge 0$ and identify bits with $\mathbb Z_2$. The **promise domain** of $\mathsf{SEARCH}_n$ is the set of strings of Hamming weight one,
--   $$D_n = \{x \in \{0,1\}^n : |\{i : x_i = 1\}| = 1\},$$
--   and $\mathsf{SEARCH}_n(x)$ is the unique $i \in [n]$ with $x_i = 1$. It is encoded as the relation $\{(x, i) : x_i = 1\}$, which on $D_n$ is the graph of $\mathsf{SEARCH}_n$.
--
--   The **hard distribution** used by the paper's proofs is uniform on $D_n$:
--   $$\mu_{\mathrm{S}}(x) = \begin{cases} 1/n & x \in D_n,\\ 0 & \text{otherwise.}\end{cases}$$
--
--   These objects are the input domain, the correctness relation and the input distribution of the selective and list-decoding direct product theorems for $\mathsf{SEARCH}_n$ (Theorems 1.2, 1.10(i), 5.5).
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, §1, p.4 (definition of SEARCH_n); §4.1.1, p.26 (hard distribution |χ₀⟩)

import Mathlib

namespace SelectiveDPT.Supplement

/-- The promise domain of `SEARCH_n`: the binary strings `x ∈ {0,1}^n` of Hamming weight `1`
(Beame–Kornerup–Whitmeyer, arXiv:2609.26678, §1, p.4: "the promise problem `SEARCH_n` function
which takes as input `x ∈ {0,1}^n` with `|x| = 1` and outputs the unique index `i` such that
`x_i = 1`"; §4.1.1, p.26).

**Formalization Note.** Bits are `ZMod 2`, inputs are `Fin n → ZMod 2` (the base mission's
convention `X = Z_d` with `d = 2`). -/
def searchDom (n : ℕ) : Finset (Fin n → ZMod 2) :=
  Finset.univ.filter fun x => (Finset.univ.filter fun i => x i = 1).card = 1

/-- `SEARCH_n` as a relation: `(x, i)` is correct iff `x_i = 1` (arXiv:2609.26678, p.4). On the
promise domain `searchDom n` this is the graph of the function `x ↦` the unique `i` with
`x_i = 1`; the answer set is `[n] = Fin n`. -/
def searchRel (n : ℕ) (x : Fin n → ZMod 2) (i : Fin n) : Prop :=
  x i = 1

/-- The hard distribution of `SEARCH_n` used by the paper's proofs: uniform on the `n` strings of
Hamming weight `1` (arXiv:2609.26678, §4.1.1, p.26: "`|χ₀⟩ = (1/√n) Σ_{j ∈ [n]} |j⟩` … a uniform
superposition over inputs of Hamming weight 1"), i.e. `μ(x) = 1/n` on `searchDom n` and `0`
elsewhere. -/
noncomputable def searchDist (n : ℕ) (x : Fin n → ZMod 2) : ℝ :=
  if x ∈ searchDom n then 1 / (n : ℝ) else 0

end SelectiveDPT.Supplement


