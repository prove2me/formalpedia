-- Prove2me | Definitions.Def_MSetBandit_IsProjOutput
-- name    : MSetBandit_IsProjOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:42:22.101056+00:00
-- url     : https://prove2.me/theorems/1e2c0a75-9ef4-41dd-a11f-4bcf84e69e8f
-- title:
--   Specification of line 11: the approximate KL projection (65)
-- statement:
--   Fix $\eta>0$ and a horizon $T$, and let $\lambda=128\eta d$, $\varepsilon_{\mathrm p}=\eta/T$, $B_{\mathrm p}=4dT$, $\mathcal D_{\mathrm p}=\{v:\|v\|_1\le B_{\mathrm p}\}$ and $\tau=\varepsilon_{\mathrm p}^2/(2B_{\mathrm p}^2)$ as in (60). A vector $\theta_+$ is an **admissible output of line 11** on input $(\tilde\theta,\eta,T)$ if
--   $$
--   \mathrm{KL}(U\,\|\,p_{\tilde\theta})\le T\ \Longrightarrow\ v=\theta_+-\tilde\theta\in\mathcal D_{\mathrm p}\ \text{ and }\ G_{\tilde\theta}(v)\le G_{\tilde\theta}(u)+\tau\ \text{ for every }u\in\mathcal D_{\mathrm p},
--   $$
--   i.e. $v$ satisfies (65), $G_{\tilde\theta}(v)\le\min_{u\in\mathcal D_{\mathrm p}}G_{\tilde\theta}(u)+\tau$. When $\mathrm{KL}(U\|p_{\tilde\theta})>T$ nothing is required; the paper gives no guarantee there, and Proposition 1 shows that this case does not occur along a run.
--
--   **Formalization Note** The paper's procedure runs the ellipsoid method for a predetermined number of iterations "with a sufficiently large constant" (p.38) and outputs such a $v$ (Lemma 8); every output satisfying (65) is admitted, which includes the paper's and an exact minimizer over $\mathcal D_{\mathrm p}$. The divergence is the finite-sum KL `ConvexRMDP.kl`, whose second argument $p_{\tilde\theta}$ has full support.
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Algorithm 1, line 11, p.12; Appendix D.1, Eqs. (60), (65), pp.33–35

import Mathlib
import Definitions.Def_ConvexRMDP_kl
import Definitions.Def_MSetBandit_uniform
import Definitions.Def_MSetBandit_wdist
import Definitions.Def_MSetBandit_projObj

namespace MSetBandit

/-- **Specification of line 11 of Algorithm 1 (the approximate KL projection).** Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231,
Algorithm 1, line 11, p.12, and Appendix D.1, Eqs. (60), (65), pp.33–35: on input
`(θ̃, η, T)` the procedure returns `θ₊ = θ̃ + v` with `v ∈ D_p` and
`G_θ̃(v) ≤ min_{u∈D_p} G_θ̃(u) + τ`, where `λ = 128ηd`, `ε_p = η/T`, `B_p = 4dT`,
`D_p = {v : ‖v‖₁ ≤ B_p}`, `τ = ε_p²/(2B_p²)`. The page guarantees such an output under the
assumption `KL(U ‖ p_θ̃) ≤ T` (p.34, Lemma 8).

`IsProjOutput m η T θt θn` says: if `KL(U ‖ p_θt) ≤ T`, then `v := θn − θt` satisfies
`‖v‖₁ ≤ 4dT` and `G_θt(v) ≤ G_θt(u) + τ` for every `u` with `‖u‖₁ ≤ 4dT`. When
`KL(U ‖ p_θt) > T` nothing is required (the page gives no guarantee there; Proposition 1 shows
the case does not occur along a run).

**Formalization Note.** The ellipsoid run of p.38 ("with a sufficiently large constant") is not
encoded; every output satisfying (65) is admitted, which covers the paper's procedure (Lemma 8)
and an exact minimizer over `D_p`. `KL` is the finite-sum divergence `ConvexRMDP.kl`; its second
argument `p_θ̃` has full support. `‖·‖₁` is written `Σ_i |v_i|`. -/
def IsProjOutput {d : ℕ} (m : ℕ) (η : ℝ) (T : ℕ) (θt θn : Fin d → ℝ) : Prop :=
  ConvexRMDP.kl (uniform (d := d) (m := m)) (wdist (m := m) θt) ≤ (T : ℝ) →
    (∑ i, |θn i - θt i| ≤ 4 * (d : ℝ) * T ∧
      ∀ u : Fin d → ℝ, ∑ i, |u i| ≤ 4 * (d : ℝ) * T →
        projObj m (128 * η * d) θt (θn - θt) ≤
          projObj m (128 * η * d) θt u + (η / T) ^ 2 / (2 * (4 * (d : ℝ) * T) ^ 2))

end MSetBandit


