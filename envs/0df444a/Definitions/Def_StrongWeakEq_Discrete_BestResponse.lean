-- Prove2me | Definitions.Def_StrongWeakEq_Discrete_BestResponse
-- name    : StrongWeakEq_Discrete_BestResponse
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T22:38:36.556814+00:00
-- url     : https://prove2.me/theorems/158fecea-094f-42ae-97fc-28825d420929
-- title:
--   Proof of Theorem 5.1, p. 27 — the best-response correspondence Φ
-- statement:
--   In the setting of §5 (finite states $S=\{1,\dots,N\}$, admissible rows $\mathcal A_i\subseteq\mathfrak P$, admissible transition matrices $\mathcal A$, payoff $\kappa$), fix a candidate $u\in\mathcal A$ to be used from time $1$ on. The **best-response correspondence** collects the admissible matrices whose rows are simultaneously optimal one-step deviations at time $0$:
--   $$\Phi(u)=\Big\{w\in\mathcal A:\ w\in\operatorname*{arg\,max}_{u'\in\mathcal A}V(i,u'\otimes_1u)\ \ \forall i\in S\Big\},$$
--   that is, $w\in\mathcal A$ and $V(i,u'\otimes_1u)\le V(i,w\otimes_1u)$ for every $i\in S$ and every $u'\in\mathcal A$.
--
--   By Definition 5.1, $u^*$ is an equilibrium exactly when $u^*\in\Phi(u^*)$ (using $V(i,u^*)=V(i,u^*\otimes_1u^*)$), so equilibria are the fixed points of $\Phi$.
--
--   **Formalization Note** $V(i,u'\otimes_1u)$ is `dConcatValue κ u' u i` of the discrete model. The map is defined for every matrix $u$; only $u\in\mathcal A$ is used.
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, p. 27, proof of Theorem 5.1 (Appendix B.1)

import Mathlib
import Definitions.Def_StrongWeakEq_Discrete_DiscreteModel

namespace StrongWeakEq.Discrete

/-- Proof of Theorem 5.1, p. 27: the best-response correspondence
`Φ(u) = {w ∈ 𝒜 : w ∈ argmax_{u' ∈ 𝒜} V(i, u' ⊗₁ u), ∀ i ∈ S}`. -/
def dBestResponse {N : ℕ} (A : Fin N → Set (Fin N → ℝ))
    (κ : ℕ → Fin N → (Fin N → ℝ) → ℝ) (u : Matrix (Fin N) (Fin N) ℝ) :
    Set (Matrix (Fin N) (Fin N) ℝ) :=
  {w | w ∈ DControls A ∧ ∀ i, ∀ u' ∈ DControls A, dConcatValue κ u' u i ≤ dConcatValue κ w u i}

end StrongWeakEq.Discrete


