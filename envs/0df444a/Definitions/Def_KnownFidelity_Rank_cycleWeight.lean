-- Prove2me | Definitions.Def_KnownFidelity_Rank_cycleWeight
-- name    : KnownFidelity_Rank_cycleWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:46:51.776433+00:00
-- url     : https://prove2.me/theorems/a05fa9e2-5b42-4c9f-8781-af5b1b9ab47a
-- title:
--   Cycle weight $\prod_{d\in\mathrm{Cycles}(\pi)}u_{|d|}^2$ of a permutation
-- statement:
--   For $a\in\mathbb R^r$ and a permutation $\pi\in S_m$,
--
--   $$w_a(\pi)=\prod_{d\in\mathrm{Cycles}(\pi)} p_{|d|}(a)^2 ,$$
--
--   the product over all cycles of $\pi$, fixed points included, of the squared power sum indexed by the cycle length. Summing over $S_m$ gives $Z^{(m)}_{bb}$ of Eq. (58).
--
--   **Formalization Note** The multiset of cycle lengths is Mathlib's `π.partition.parts`, which contains a $1$ for each fixed point.
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, §5.5, Eqs. (58)–(59), p. 20 (PDF p. 22)

import Mathlib
import Definitions.Def_KnownFidelity_Rank_powerSum

namespace KnownFidelity.Rank

/-- **The cycle weight `∏_{d ∈ Cycles(π)} u_{b,|d|}²` of a permutation.**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, §5.5, Eqs. (58)–(59), printed p. 20 (PDF p. 22):
"Z^{(m)}_{bc} = Σ_{π∈S_m} ∏_{d∈Cycles(π)} u_{b,|d|} u_{c,|d|}" and "normalize the nonnegative
weights in Z^{(m)}_{bb} to a probability law on S_m".

`cycleWeight a π = ∏_{cycles d of π} (Σ_i a_i^{|d|})²`, the product over **all** cycles of
`π ∈ S_m`, fixed points (1-cycles) included.

**Formalization Note.** The multiset of cycle lengths is Mathlib's `π.partition.parts`, i.e.
`π.cycleType` (lengths `≥ 2`) together with one `1` for each fixed point; `cycleType` alone would
drop the 1-cycles. -/
def cycleWeight {r m : ℕ} (a : Fin r → ℝ) (π : Equiv.Perm (Fin m)) : ℝ :=
  (π.partition.parts.map fun l => powerSum a l ^ 2).prod

end KnownFidelity.Rank


