-- Prove2me | Definitions.Def_ErrAmpOV_Supplement_BPSorts
-- name    : ErrAmpOV_Supplement_BPSorts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:16:29.764699+00:00
-- url     : https://prove2.me/theorems/934f138a-ffbf-498c-af83-e774475eb288
-- title:
--   Bounded-error probabilistic circuits for $\mathrm{SORT}_{n,m}$: $\mathrm{BPSIZE}_\delta[S]$ at one input length
-- statement:
--   Let $w=\lceil\log_2 m\rceil$. $\mathrm{SORT}_{n,m}\in\mathrm{BPSIZE}_\delta[S]$ (at one input length) holds when there are $p\in\mathbb N$ and a Boolean circuit $C$ with at most $S$ gates, reading the $n\cdot w$ input bits $x$ and $p$ random bits $r$, with $n\cdot w$ output wires, such that for every valid $x\in[m]^n$
--   $$\Pr_{r\in\{0,1\}^p}\bigl[C(x,r)=\mathrm{SORT}_{n,m}(x)\bigr]\ge1-\delta .$$
--   On the remaining random strings the output is arbitrary.
--
--   This is Definition 2.3 specialised to sorting (p.13), the circuit class of Theorem 5.1.
--
--   **Formalization Note** No $\bot$ symbol and no condition on every random string. The size bound is exact; $p$ is chosen with the circuit.
-- source:
--   Koucký, Mertz, Rajgopal, Efficient Error Amplification for Sorting and Orthogonal Vectors, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3), Definition 2.3, p.6; specialised to SORT on p.13

import Mathlib
import Definitions.Def_ErrAmpOV_Circuit
import Definitions.Def_ErrAmpOV_Supplement_SORT

set_option autoImplicit false

namespace ErrAmpOV.Supplement

open Classical in
/-- `BPSorts δ S n m` (Definition 2.3 for `SORT_{n,m}`, at one input length): with
`w := Nat.clog 2 m`, some probabilistic circuit with at most `S` gates, reading the `n·w`
input bits `x` and `p` random bits `r`, has `n·w` output wires such that for every valid
`x ∈ [m]^n`, the output is exactly `enc(SORT_{n,m}(x))` for at least a `1 − δ` fraction of the
`2^p` random strings `r`. At one input length this is "`SORT_{n,m} ∈ BPSIZE_δ[S]`".

Source: Koucký, Mertz, Rajgopal, *Efficient Error Amplification for Sorting and Orthogonal
Vectors*, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3),
Definition 2.3, p.6 ("`C_n` has `n` deterministic bits and `p(n)` random bits as inputs, `n`
output bits and has size at most `S(n)`, such that … `Pr_r[C_n(x, r) ∈ R(x)] ≥ 1 − δ`"),
specialised to SORT as on p.13.

**Formalization Note.** No `⊥` and no all-`r` clause: on the failing random strings the output
is arbitrary. Only valid inputs (every element `< m`) are constrained. `p` is chosen with the
circuit; the size bound is exact; "`1/2 > δ > 0`" names the class and is not part of the
predicate. -/
def BPSorts (δ S : ℝ) (n m : ℕ) : Prop :=
  ∃ (p : ℕ) (C : ErrAmpOV.Circuit ((Fin n × Fin (Nat.clog 2 m)) ⊕ Fin p)),
    (C.size : ℝ) ≤ S ∧
    ∀ x : Fin n × Fin (Nat.clog 2 m) → Bool, SortValid n m (Nat.clog 2 m) x →
      (1 - δ) * 2 ^ p ≤
        ((Finset.univ.filter (fun r : Fin p → Bool => ∃ y, IsSortOf n (Nat.clog 2 m) x y ∧
            C.eval (Sum.elim x r) = sortEncode n (Nat.clog 2 m) y)).card : ℝ)

end ErrAmpOV.Supplement


