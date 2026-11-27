-- Prove2me | Definitions.Def_ConvexRMDP_Supplement_SRMDP_tOp
-- name    : ConvexRMDP_Supplement_SRMDP_tOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:53:52.539952+00:00
-- url     : https://prove2.me/theorems/6dda9f3a-4821-4aca-8c02-a39aea541c54
-- title:
--   The s-rectangular operator $\tilde t(x)_s=\min_{P\in\mathcal U_s}\sum_a\omega_b(s,a)\prod_{s'}x_{s'}^{\gamma P_{as'}}$ (6.2)
-- statement:
--   Let $(\mathcal S, \mathcal A, r, \gamma, \mathcal U)$ be an s-rectangular robust MDP and $b > 0$, and write $\omega_b(s,a) = \frac{1}{|\mathcal A|}\exp(b\,r_{sa})$. For $x \in (\mathbb R^*_+)^{\mathcal S}$ and $s \in \mathcal S$,
--
--   $$
--   \tilde t(x)_s = \min_{(P_a)_{a} \in \mathcal U_s} \sum_{a \in \mathcal A} \omega_b(s,a) \prod_{s' \in \mathcal S} x_{s'}^{\gamma P_{as'}} . \tag{6.2}
--   $$
--
--   The convex program (6.3) of Theorem 6.1 has the constraints $1 \le x_s \le \tilde t(x)_s$.
--
--   **Formalization Note** The Lean function is defined for every $x \in \mathbb R^{\mathcal S}$ and agrees with (6.2) for positive $x$; every statement uses it for $x \ge 1$. The minimum is an infimum over the nonempty compact $\mathcal U_s$. $\exp_b$ is the published `ConvexRMDP.expB`.
-- source:
--   Grand-Clément & Petrik, arXiv:2209.10187v2, §6, display (6.2), p.20; ω_b from p.13

import Mathlib
import Definitions.Def_ConvexRMDP_RMDP_tOp
import Definitions.Def_ConvexRMDP_Supplement_SRMDP

namespace ConvexRMDP

namespace Supplement

namespace SRMDP

variable {S A : Type*} [Fintype S] [Fintype A]

/-- The weight `ω_b(s,a) = (1/|A|) exp_b(r_{sa})` for an s-rectangular model (Grand-Clément &
Petrik, arXiv:2209.10187v2, p.13 after (4.5), and §6, p.20). -/
noncomputable def omega (M : SRMDP S A) (b : ℝ) (s : S) (a : A) : ℝ :=
  expB b (M.r s a) / (Fintype.card A : ℝ)

/-- **The operator `t̃` of (6.2)** (Grand-Clément & Petrik, arXiv:2209.10187v2, p.20):
`t̃(x)_s = min_{(P_a)_a ∈ 𝒰_s} ∑_a ω_b(s,a) ∏_{s'} x_{s'}^{γ P_{as'}}`.

**Formalization Note.** The paper defines `t̃` on `(ℝ*₊)^S`; here it is a total function on `S → ℝ`
whose values are the paper's for `x` with positive entries (`Real.rpow`); every statement uses it on
`x ≥ 1`. The minimum is `sInf` over the nonempty compact `𝒰_s`. `exp_b` is the published `expB`. -/
noncomputable def tOp (M : SRMDP S A) (b : ℝ) (x : S → ℝ) : S → ℝ := fun s =>
  sInf ((fun P : A → S → ℝ => ∑ a, M.omega b s a * ∏ s', x s' ^ (M.γ * P a s')) '' M.U s)

end SRMDP

end Supplement

end ConvexRMDP


