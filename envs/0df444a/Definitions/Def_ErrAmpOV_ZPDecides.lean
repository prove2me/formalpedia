-- Prove2me | Definitions.Def_ErrAmpOV_ZPDecides
-- name    : ErrAmpOV_ZPDecides
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:38:30.810314+00:00
-- url     : https://prove2.me/theorems/ce615eae-30f3-44e0-8ba7-d1d3b35a716f
-- title:
--   $\mathsf{ZPSIZE}_\delta[S]$ at one input length (Definition 2.1)
-- statement:
--   For real numbers $\delta,S$ and $f:\{0,1\}^\iota\to\{0,1\}$, $f$ is decided with zero error and error $\delta$ in size $S$ when there are $p\in\mathbb N$ and a circuit $C$ with at most $S$ gates, reading $x\in\{0,1\}^\iota$ and random bits $r\in\{0,1\}^p$, such that:
--
--   1. for every $x$ and **every** $r$, $C(x,r)\in\{f(x),\bot\}$;
--   2. for every $x$,
--   $$
--   \Pr_{r\in\{0,1\}^p}\bigl[C(x,r)=f(x)\bigr]\ge 1-\delta .
--   $$
--
--   The first clause is what makes the class zero-error: a wrong value is never output, only an abort. Without it the class would be the bounded-error class of Definition 2.3, and the error amplification of the mission would be a different theorem.
--
--   **Formalization Note** The circuit has two output wires (abort, value). The value $\bot$ is abort $=$ `true`, and a correct output is exactly `[false, f x]`. The probability is the number of good $r$ divided by $2^p$, written without division. The paper's "$1/2>\delta>0$" names the class and is not part of the predicate.
-- source:
--   Koucký, Mertz, Rajgopal, Efficient Error Amplification for Sorting and Orthogonal Vectors, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3), Definition 2.1, p.6

import Mathlib
import Definitions.Def_ErrAmpOV_Circuit

set_option autoImplicit false

namespace ErrAmpOV

/-- `ZPDecides δ S f` (Definition 2.1 at one input length): some probabilistic circuit with at
most `S` gates, reading the input `x` and `p` random bits `r`, has two output wires
`(abort, value)` such that

1. (zero error) for **every** `x` and **every** `r`, the output is either `[false, f x]` (the
   correct answer) or begins with `true` (the symbol `⊥`);
2. for every `x`, the output is `[false, f x]` for at least a `1 - δ` fraction of the `2^p`
   random strings `r`.

Source: Koucký, Mertz, Rajgopal, *Efficient Error Amplification for Sorting and Orthogonal
Vectors*, STOC 2027 submission (manuscript of November 3, 2026, sha256 f31f577a…72fbb9d3),
Definition 2.1, p.6: "`C_n(x, r) ∈ {f_n(x), ⊥}` for all `r ∈ {0,1}^{p(n)}` and
`Pr_r[C_n(x, r) = f_n(x)] ≥ 1 − δ`".

**Formalization Note.**
* `⊥` is a separate symbol (pp.5–6); it is encoded as the first output wire (`abort`) being
  `true`. The probability is the number of `r : Fin p → Bool` with output `[false, f x]`,
  divided by `2^p`.
* The number `p` of random bits is chosen with the circuit. The size bound is exact.
* Definition 2.1's "`1/2 > δ > 0`" names the class `ZPSIZE_δ` and is not part of the predicate.
* A family statement "`f ∈ ZPSIZE_δ[S(n)]`" is `∀ᶠ n in Filter.atTop, ZPDecides δ (S n) (f n)`. -/
def ZPDecides {ι : Type} (δ S : ℝ) (f : (ι → Bool) → Bool) : Prop :=
  ∃ (p : ℕ) (C : Circuit (ι ⊕ Fin p)), (C.size : ℝ) ≤ S ∧
    (∀ x r, C.eval (Sum.elim x r) = [false, f x] ∨ ∃ v, C.eval (Sum.elim x r) = [true, v]) ∧
    ∀ x, (1 - δ) * 2 ^ p ≤
      ((Finset.univ.filter (fun r : Fin p → Bool => C.eval (Sum.elim x r) = [false, f x])).card : ℝ)

end ErrAmpOV


