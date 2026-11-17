-- Prove2me | Definitions.Def_PolyContract_Supplement_almCutCap
-- name    : PolyContract_Supplement_almCutCap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:58:47.968843+00:00
-- url     : https://prove2.me/theorems/6da86faa-59c8-4d2b-ac40-c07cb515e887
-- title:
--   Cut capacity in a two-parameter network of type [ALM22]; $O(n\log n)$ bit budget; characteristic vectors
-- statement:
--   A **network of type [ALM22]** has a source $s$, a sink $s'$ and the nodes $E=[n]$. The arc $s\to j$ has capacity $a_j\lambda+b_j\mu$ for parameters $(\lambda,\mu)$, and the arcs $i\to j$ inside $E$ and $i\to s'$ have constant capacities $u_{ij}$ and $u_{is'}$. The capacity of the cut $\{s\}\cup S$, $S\subseteq E$, at $(\lambda,\mu)$ is
--   $$\sum_{j\notin S}(a_j\lambda+b_j\mu)+\sum_{i\in S,\,j\notin S}u_{ij}+\sum_{i\in S}u_{is'}.$$
--
--   The module also defines the bit budget $n(\lfloor\log_2 n\rfloor+1)$, used to state "$O(n\log n)$ bits" with one absolute constant, and the characteristic bit list $\chi_S$ of a set $S\subseteq[n]$, on which the rank function of Theorem 3.10(i) is evaluated.
--
--   **Formalization Note** Coefficients and constant capacities are integers. Arcs entering $\{s\}\cup S$ and a constant arc $s\to s'$ add the same amount to, or nothing to, every cut, and are omitted.
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), Theorem 3.10(ii), p.9 (PDF p.10); proof of Theorem 3.8, p.26 (PDF p.27); proof of Theorem 3.10, p.43

import Mathlib

set_option autoImplicit false

namespace PolyContract.Supplement

/-- The capacity of the cut `{s} ∪ S` in a **two-parameter network of type [ALM22]** (Klimm,
Lippke, Warode, arXiv:2611.04934, version of November 3, 2026, sha256 18cfc0a5…, Theorem 3.10(ii),
p.9, and proof of Theorem 3.8, p.26): a source `s`, a sink `s′` and the nodes `E = [n]`; the arc
`s → j` has capacity `a_j λ + b_j µ`, the arc `i → j` inside `E` the constant capacity `u_{ij}`, and
the arc `i → s′` the constant capacity `u_{is′}`. The capacity of `{s} ∪ S` at `(λ, µ)` is
`Σ_{j ∉ S} (a_j λ + b_j µ) + Σ_{i ∈ S, j ∉ S} u_{ij} + Σ_{i ∈ S} u_{is′}`.

**Formalization Note** The nodes are `Fin n`; the coefficients and fixed capacities are integers
(`a`, `b`, `u`, `us`). Arcs entering `{s} ∪ S` and a constant arc `s → s′` do not change which cut
is minimum, and they are omitted. -/
def almCutCap {n : ℕ} (a b : Fin n → ℤ) (u : Fin n → Fin n → ℤ) (us : Fin n → ℤ)
    (S : Finset (Fin n)) (lam μ : ℝ) : ℝ :=
  ∑ j ∈ Sᶜ, ((a j : ℝ) * lam + (b j : ℝ) * μ) + ∑ i ∈ S, ∑ j ∈ Sᶜ, (u i j : ℝ) + ∑ i ∈ S, (us i : ℝ)

/-- The bit budget `n (⌊log₂ n⌋ + 1)` of an `O(n log n)`-bit bound (arXiv:2611.04934,
Theorem 3.10, p.9): a quantity has `O(n log n)` bits when it has at most `C · nlogn n` bits for an
absolute constant `C`. -/
def nlogn (n : ℕ) : ℕ := n * (Nat.log 2 n + 1)

/-- The characteristic bit list `χ_S` of `S ⊆ [n]`, of length `n`: its `i`-th entry says whether
`i ∈ S`. It is the input on which the rank function is evaluated in Theorem 3.10(i)
(arXiv:2611.04934, p.9). -/
def charVec {n : ℕ} (S : Finset (Fin n)) : List Bool :=
  (List.finRange n).map fun i => decide (i ∈ S)

end PolyContract.Supplement


