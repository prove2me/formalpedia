-- Prove2me | Definitions.Def_ConvexRMDP_Supplement_SRMDP_regOp
-- name    : ConvexRMDP_Supplement_SRMDP_regOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:53:20.468863+00:00
-- url     : https://prove2.me/theorems/c1c63e1a-b878-4b3d-9db7-110ac8f7be8f
-- title:
--   s-rectangular robust Bellman operator $T$ and regularized operator $\tilde T$ (6.1), uniform $\nu$
-- statement:
--   Let $(\mathcal S, \mathcal A, r, \gamma, \mathcal U)$ be an s-rectangular robust MDP and $b > 0$. For $v \in \mathbb R^{\mathcal S}$ and $s \in \mathcal S$, the **s-rectangular robust Bellman operator** and the **regularized robust Bellman operator** with uniform reference policy $\nu_{sa} = 1/|\mathcal A|$ are
--
--   $$
--   T(v)_s = \max_{\pi_s \in \Delta(\mathcal A)} \; \min_{(P_a)_{a} \in \mathcal U_s} \sum_{a \in \mathcal A} \pi_{sa}\left(r_{sa} + \gamma P_a^\top v\right),
--   $$
--
--   $$
--   \tilde T(v)_s = \max_{\pi_s \in \Delta(\mathcal A)} \; \min_{(P_a)_{a} \in \mathcal U_s} \sum_{a \in \mathcal A} \pi_{sa}\left(r_{sa} + \gamma P_a^\top v\right) - \frac1b\, \mathrm{KL}(\pi_s, \nu_s). \tag{6.1}
--   $$
--
--   Theorem 6.1 shows that the fixed point of $\tilde T$ is computed by a convex program and approximates the fixed point of $T$.
--
--   **Formalization Note** The KL term does not depend on $P$ and is written outside the minimum. The minimum over $\mathcal U_s$ is an infimum (attained: $\mathcal U_s$ is nonempty compact) and the maximum over $\Delta(\mathcal A)$ a supremum. Because $\nu_{sa} = 1/|\mathcal A| > 0$, the published real-valued `ConvexRMDP.kl` is the paper's divergence.
-- source:
--   Grand-Clément & Petrik, arXiv:2209.10187v2, §6, p.20: the operator T and display (6.1), with ν_sa = 1/|A|

import Mathlib
import Definitions.Def_ConvexRMDP_kl
import Definitions.Def_ConvexRMDP_Supplement_SRMDP

namespace ConvexRMDP

namespace Supplement

namespace SRMDP

variable {S A : Type*} [Fintype S] [Fintype A]

/-- The one-step value `∑_a π_{sa} (r_{sa} + γ P_aᵀv)` of the policy row `π_s` against the
transition family `P = (P_a)_a ∈ 𝒰_s` (Grand-Clément & Petrik, arXiv:2209.10187v2, §6, p.20). -/
noncomputable def stepVal (M : SRMDP S A) (v : S → ℝ) (s : S) (π : A → ℝ) (P : A → S → ℝ) : ℝ :=
  ∑ a, π a * (M.r s a + M.γ * ∑ s', P a s' * v s')

/-- **The s-rectangular robust Bellman operator** (Grand-Clément & Petrik, arXiv:2209.10187v2, §6,
p.20): `T(v)_s = max_{π_s ∈ Δ(A)} min_{(P_a)_a ∈ 𝒰_s} ∑_a π_{sa} (r_{sa} + γ P_aᵀv)`.

**Formalization Note.** The minimum is `sInf` (over the nonempty compact `𝒰_s`, of a continuous
function, so attained) and the maximum over `Δ(A) = stdSimplex ℝ A` is `sSup` (bounded above; for
nonempty `A` a genuine supremum). -/
noncomputable def robustOp (M : SRMDP S A) (v : S → ℝ) : S → ℝ := fun s =>
  sSup ((fun π : A → ℝ => sInf (M.stepVal v s π '' M.U s)) '' stdSimplex ℝ A)

/-- **The s-rectangular regularized robust Bellman operator** `T̃` of (6.1) with the uniform
reference policy `ν_{sa} = 1/|A|` (Grand-Clément & Petrik, arXiv:2209.10187v2, p.20):
`T̃(v)_s = max_{π_s ∈ Δ(A)} min_{(P_a)_a ∈ 𝒰_s} ∑_a π_{sa} (r_{sa} + γ P_aᵀv) − (1/b) KL(π_s, ν_s)`.

**Formalization Note.** The KL term does not depend on `P`, so it is written outside the minimum.
The minimum is `sInf`, the maximum `sSup`, as in `robustOp`. Since `ν_{sa} = 1/|A| > 0`, every `π_s`
is absolutely continuous with respect to `ν_s` and the real-valued `kl` is the paper's divergence. -/
noncomputable def regOp (M : SRMDP S A) (b : ℝ) (v : S → ℝ) : S → ℝ := fun s =>
  sSup ((fun π : A → ℝ => sInf (M.stepVal v s π '' M.U s)
      - kl π (fun _ => 1 / (Fintype.card A : ℝ)) / b) '' stdSimplex ℝ A)

end SRMDP

end Supplement

end ConvexRMDP


