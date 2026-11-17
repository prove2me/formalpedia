-- Prove2me | Definitions.Def_ErrAmpOV_Supplement_ZPSorts
-- name    : ErrAmpOV_Supplement_ZPSorts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:16:09.335319+00:00
-- url     : https://prove2.me/theorems/380f66e2-42c4-422f-aa95-a69c5d829102
-- title:
--   Zero-error probabilistic circuits for $\mathrm{SORT}_{n,m}$: $\mathrm{ZPSIZE}_\delta[S]$ at one input length
-- statement:
--   Let $w=\lceil\log_2 m\rceil$. $\mathrm{SORT}_{n,m}\in\mathrm{ZPSIZE}_\delta[S]$ (at one input length) holds when there are $p\in\mathbb N$ and a Boolean circuit $C$ with at most $S$ gates, reading the $n\cdot w$ input bits $x$ and $p$ random bits $r$, with $1+n\cdot w$ output wires, such that:
--
--   1. **(zero error)** for every valid $x\in[m]^n$ and every $r\in\{0,1\}^p$, the output $C(x,r)$ is either $0$ followed by the encoding of $\mathrm{SORT}_{n,m}(x)$, or $1$ followed by $n\cdot w$ arbitrary bits (the symbol $\bot$);
--   2. for every valid $x$,
--   $$\Pr_{r\in\{0,1\}^p}\bigl[C(x,r)=0\,\|\,\mathrm{SORT}_{n,m}(x)\bigr]\ge1-\delta .$$
--
--   This is Definition 2.2 specialised to sorting, as the paper does on p.13, and is the circuit class of Theorem 4.1.
--
--   **Formalization Note** The abort convention is that of the published decision-problem class (first output wire true means $\bot$). The probability is a count of random strings divided by $2^p$; $p$ is chosen with the circuit; the size bound is exact.
-- source:
--   Koucký, Mertz, Rajgopal, Efficient Error Amplification for Sorting and Orthogonal Vectors, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3), Definition 2.2, p.6; specialised to SORT on p.13

import Mathlib
import Definitions.Def_ErrAmpOV_Circuit
import Definitions.Def_ErrAmpOV_Supplement_SORT

set_option autoImplicit false

namespace ErrAmpOV.Supplement

open Classical in
/-- `ZPSorts δ S n m` (Definition 2.2 for `SORT_{n,m}`, at one input length): with
`w := Nat.clog 2 m`, some probabilistic circuit with at most `S` gates, reading the `n·w`
input bits `x` and `p` random bits `r`, has `1 + n·w` output wires `(abort, value)` such that

1. (zero error) for **every** valid `x ∈ [m]^n` and **every** `r`, the output is either
   `false :: enc(SORT_{n,m}(x))` (the sorted list) or `true` followed by `n·w` bits (the
   symbol `⊥`);
2. for every valid `x`, the output is `false :: enc(SORT_{n,m}(x))` for at least a `1 − δ`
   fraction of the `2^p` random strings `r`.

At one input length this is "`SORT_{n,m} ∈ ZPSIZE_δ[S]`".

Source: Koucký, Mertz, Rajgopal, *Efficient Error Amplification for Sorting and Orthogonal
Vectors*, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3),
Definition 2.2, p.6 ("`C_n(x, r)` outputs a string in `R(x)` or `⊥` for all `r` and
`Pr_r[C_n(x, r) ∈ R(x)] ≥ 1 − δ`"), specialised to SORT as on p.13 ("`R_{n,m}` outputs
`SORT_{n,m}(x)` with probability at least `1 − ε`, and `R_{n,m}(x) ∈ {SORT_{n,m}(x), ⊥}`").

**Formalization Note.**
* Mirrors the published `ErrAmpOV.ZPDecides`: `⊥` is the first output wire (`abort`) being
  `true` (p.5: "`⊥` … padded with the appropriate number of zeroes"; the padding bits are left
  free). Success counts outputs equal to `false :: enc(SORT(x))`, not merely "not aborted".
* Only valid inputs (every element `< m`) are constrained; the paper's domain is `[m]^n`.
* `p` is chosen with the circuit; the size bound is exact. Definition 2.2's "`1/2 > δ > 0`"
  names the class and is not part of the predicate. -/
def ZPSorts (δ S : ℝ) (n m : ℕ) : Prop :=
  ∃ (p : ℕ) (C : ErrAmpOV.Circuit ((Fin n × Fin (Nat.clog 2 m)) ⊕ Fin p)),
    (C.size : ℝ) ≤ S ∧
    (∀ x : Fin n × Fin (Nat.clog 2 m) → Bool, SortValid n m (Nat.clog 2 m) x →
      ∀ r : Fin p → Bool,
        (∃ y, IsSortOf n (Nat.clog 2 m) x y ∧
            C.eval (Sum.elim x r) = false :: sortEncode n (Nat.clog 2 m) y) ∨
        ∃ v : List Bool, v.length = n * Nat.clog 2 m ∧ C.eval (Sum.elim x r) = true :: v) ∧
    ∀ x : Fin n × Fin (Nat.clog 2 m) → Bool, SortValid n m (Nat.clog 2 m) x →
      (1 - δ) * 2 ^ p ≤
        ((Finset.univ.filter (fun r : Fin p → Bool => ∃ y, IsSortOf n (Nat.clog 2 m) x y ∧
            C.eval (Sum.elim x r) = false :: sortEncode n (Nat.clog 2 m) y)).card : ℝ)

end ErrAmpOV.Supplement


