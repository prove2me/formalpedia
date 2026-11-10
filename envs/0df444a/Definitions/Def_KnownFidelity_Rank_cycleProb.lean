-- Prove2me | Definitions.Def_KnownFidelity_Rank_cycleProb
-- name    : KnownFidelity_Rank_cycleProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:47:40.542428+00:00
-- url     : https://prove2.me/theorems/c3acac82-cd08-404d-8f2f-d5079ec0e6d6
-- title:
--   The cycle-weighted law $\mathbb P_b$ on $S_m$, Eq. (59)
-- statement:
--   For $a\in\mathbb R^r$ the weights $w_a(\pi)$ are normalized to a law on $S_m$:
--
--   $$\mathbb P(\pi)=\frac{1}{Z^{(m)}}\prod_{d\in\mathrm{Cycles}(\pi)}p_{|d|}(a)^2,\qquad Z^{(m)}=\sum_{\pi'\in S_m}\prod_{d\in\mathrm{Cycles}(\pi')}p_{|d|}(a)^2 .$$
--
--   With $a=a^{(b)}$ this is $\mathbb P_b$ of the paper. When $p_1(a)=1$ the identity has weight $1$, so $Z^{(m)}\ge1$.
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, §5.5, Eq. (59), p. 20 (PDF p. 22)

import Mathlib
import Definitions.Def_KnownFidelity_Rank_cycleWeight

namespace KnownFidelity.Rank

/-- **The cycle-weighted law `P_b` on `S_m`, Eq. (59).**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, §5.5, Eq. (59), printed p. 20 (PDF p. 22): "For b ∈ {0, 1}, normalize the
nonnegative weights in Z^{(m)}_{bb} to a probability law on S_m:
P_b(π) = (1/Z^{(m)}_{bb}) ∏_{d∈Cycles(π)} u²_{b,|d|}."

`cycleProb a π = cycleWeight a π / Σ_{π' ∈ S_m} cycleWeight a π'`, the normalizer being
`Z^{(m)}_{bb}` of Eq. (58).

**Formalization Note.** When `u_{b,1} = 1` the identity permutation has weight `1`, so the
normalizer is at least `1`; the statements that use `cycleProb` assume `u_{b,1} = 1`. -/
noncomputable def cycleProb {r m : ℕ} (a : Fin r → ℝ) (π : Equiv.Perm (Fin m)) : ℝ :=
  cycleWeight a π / ∑ π' : Equiv.Perm (Fin m), cycleWeight a π'

end KnownFidelity.Rank


