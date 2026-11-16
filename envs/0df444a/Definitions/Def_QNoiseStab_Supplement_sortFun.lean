-- Prove2me | Definitions.Def_QNoiseStab_Supplement_sortFun
-- name    : QNoiseStab_Supplement_sortFun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:20:33.066567+00:00
-- url     : https://prove2.me/theorems/5ec82675-4838-405b-98c2-3f425c7f0083
-- title:
--   The sorting function $\mathrm{SORT}_{n,[m]}$ as a multi-output function $i\mapsto(x_i,r_i)$
-- statement:
--   For $x\in[m]^n$ the **stable rank** of index $i$ is
--
--   $$
--   r_i=\#\{j\in[n]:\ x_j<x_i\ \text{or}\ (x_j=x_i\ \text{and}\ j<i)\},
--   $$
--
--   so $\{r_i\}=[n]$ and $r_i<r_j$ exactly when $x_i<x_j$, or $x_i=x_j$ and $i<j$. The sorting function $\mathrm{SORT}_{n,[m]}$ maps $x$ to the set of triples $\{(i,x_i,r_i)\}_{i\in[n]}$; as a multi-output function it has one output coordinate per input index,
--
--   $$
--   \mathrm{SORT}(x)_i=(x_i,r_i)\in[m]\times[n].
--   $$
--
--   A partial output is a partial function $i\mapsto(v_i,r_i)$, consistent with $\mathrm{SORT}(x)$ when it agrees with these values.
--
--   **Formalization Note** $[m]$ and $[n]$ are $\{0,\dots,m-1\}$ and $\{0,\dots,n-1\}$ with their usual order, so ranks start at $0$.
-- source:
--   Beame–Holman–Kornerup, A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), Definitions 5.2 and 5.3, p.28

import Mathlib

set_option autoImplicit false

namespace QNoiseStab.Supplement

/-- The **sorting function** `SORT_{n,[m]}` as a multi-output function (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), Definition 5.2,
p.28: "SORT_{n,[m]} … mapping input (x_1, …, x_n) ∈ [m]^n to the unique unordered set
{(i, x_i, r_i)}_{i∈[n]} where {r_i}_{i∈[n]} = [n] and r_i < r_j implies that x_i < x_j or both
x_i = x_j and i < j"; Definition 5.3, p.28, partial outputs as partial functions
`i ↦ (v_i, r_i)`). Output coordinate `i` is `(x_i, r_i)`, where the stable rank
`r_i = #{j : x_j < x_i ∨ (x_j = x_i ∧ j < i)}`.

**Formalization Note** `[m]` and `[n]` are `Fin m` and `Fin n` (0-based, order preserved), so
ranks are `0, …, n − 1`. The rank is below `n` because `i` itself is not counted. -/
def sortFun {n m : ℕ} (x : Fin n → Fin m) (i : Fin n) : Fin m × Fin n :=
  (x i, ⟨(Finset.univ.filter fun j => x j < x i ∨ (x j = x i ∧ j < i)).card, by
    calc (Finset.univ.filter fun j => x j < x i ∨ (x j = x i ∧ j < i)).card
        < (Finset.univ : Finset (Fin n)).card :=
          Finset.card_lt_card (Finset.filter_ssubset.2 ⟨i, Finset.mem_univ _, by simp⟩)
      _ = n := by simp⟩)

end QNoiseStab.Supplement


