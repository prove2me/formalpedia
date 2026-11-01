-- Prove2me | Definitions.Def_PacingComplexity_gadgetValue
-- name    : PacingComplexity_gadgetValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:27:18.135173+00:00
-- url     : https://prove2.me/theorems/9d13ecfa-443f-4b38-9ef3-a29fac37acf2
-- title:
--   Values of the gadget game $G(A,B)$
-- statement:
--   Let $(A,B)$ be an $n\times n$ cost bimatrix game, $\nu=1/(16n)$ and $\delta=1/n^7$. The values $V(\cdot,\cdot)$ of the gadget game are:
--
--   1. Buyer $C(p,s)$: $V(C(p,s),N(p,s)_i)=16$ for $i\ne s$; $V(C(p,s),N(p,s)_s)=1$; $V(C(p,s),N(p,t)_s)=1$ for $t\ne s$; $V(C(p,s),T(p,s))=2n^4$; $V(C(p,s),E(p,s)_i)=1$ for all $i$; for $p=1$, $V(C(1,s),E(2,t)_s)=\nu B_{st}$, and for $p=2$, $V(C(2,s),E(1,t)_s)=\nu A_{ts}$, for all $t$.
--   2. Threshold buyer $T$: $V(T,T(p,s))=(1-\delta)n^4$; $V(T,E(1,s)_t)=\nu A_{st}/2$ and $V(T,E(2,s)_t)=\nu B_{ts}/2$ for all $s,t$.
--   3. Dummy buyer $D(p,s)$: $V(D(p,s),N(p,s)_s)=1$.
--
--   All other values are $0$. These are the values of the approximate construction in the appendix, not those of the exact warm-up in §3.1.
--
--   **Formalization Note** $\nu$ and $\delta$ are computed from the bimatrix dimension $n$, not from the number $4n+1$ of buyers. The matrices are real; the lemmas assume their entries lie in $\{0,1\}$.
-- source:
--   Chen, Kroer, Kumar, The Complexity of Pacing for Second-Price Auctions, arXiv:2103.13969v2, Appendix A, p.31

import Mathlib
import Definitions.Def_PacingComplexity_GBuyer
import Definitions.Def_PacingComplexity_GGood

namespace PacingComplexity

/-- **Values of the gadget game** `G` built from an `n × n` cost bimatrix game `(A, B)` (Chen,
Kroer, Kumar, *The Complexity of Pacing for Second-Price Auctions*, arXiv:2103.13969v2,
Appendix A, p.31), with `ν = 1/(16n)` and `δ = 1/n^7` (p.30: `δ = γ = ε/n^6`, `ε = 1/n`):
* `C(p, s)`: `V(C(p, s), N(p, s)_i) = 16` for `i ≠ s`; `V(C(p, s), N(p, s)_s) = 1`;
  `V(C(p, s), N(p, t)_s) = 1` for `t ≠ s`; `V(C(p, s), T(p, s)) = 2n^4`;
  `V(C(p, s), E(p, s)_i) = 1` for all `i`; for `p = 1`, `V(C(1, s), E(2, t)_s) = ν B_st`, and
  for `p = 2`, `V(C(2, s), E(1, t)_s) = ν A_ts`, for all `t`.
* `T`: `V(T, T(p, s)) = (1 − δ)n^4`; `V(T, E(1, s)_t) = ν A_st / 2` and
  `V(T, E(2, s)_t) = ν B_ts / 2` for all `s, t`.
* `D(p, s)`: `V(D(p, s), N(p, s)_s) = 1`.
All values not listed are `0`.

**Formalization Note** These are the appendix's values (16 on the normalization goods, `T`'s
`(1 − δ)n^4`), not those of §3.1's exact warm-up. Player `1` is `p = 0`, player `2` is `p = 1`
(`Fin 2`). `δ = 1/n^7` and `ν = 1/(16n)` use the bimatrix dimension `n`, not the number `4n + 1`
of buyers. The matrices are real; the theorems assume their entries lie in `{0, 1}`. -/
noncomputable def gadgetValue (n : ℕ) (A B : Fin n → Fin n → ℝ) : GBuyer n → GGood n → ℝ
  | .C p s, .N p' s' i =>
      if p' = p ∧ s' = s then (if i = s then 1 else 16)
      else if p' = p ∧ i = s then 1 else 0
  | .C p s, .Th p' s' => if p' = p ∧ s' = s then 2 * (n : ℝ) ^ 4 else 0
  | .C p s, .E p' s' i =>
      if p' = p ∧ s' = s then 1
      else if p = 0 ∧ p' = 1 ∧ i = s then (1 / (16 * (n : ℝ))) * B s s'
      else if p = 1 ∧ p' = 0 ∧ i = s then (1 / (16 * (n : ℝ))) * A s' s
      else 0
  | .T, .Th _ _ => (1 - 1 / (n : ℝ) ^ 7) * (n : ℝ) ^ 4
  | .T, .E p' s t =>
      if p' = 0 then (1 / (16 * (n : ℝ))) * A s t / 2 else (1 / (16 * (n : ℝ))) * B t s / 2
  | .T, .N _ _ _ => 0
  | .D p s, .N p' s' i => if p' = p ∧ s' = s ∧ i = s then 1 else 0
  | .D _ _, .E _ _ _ => 0
  | .D _ _, .Th _ _ => 0

end PacingComplexity


