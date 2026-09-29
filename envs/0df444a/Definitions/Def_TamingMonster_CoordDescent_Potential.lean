-- Prove2me | Definitions.Def_TamingMonster_CoordDescent_Potential
-- name    : TamingMonster_CoordDescent_Potential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T09:16:48.879967+00:00
-- url     : https://prove2.me/theorems/5d864c02-44fd-4a6e-b60c-eaa360fec0ab
-- title:
--   Unnormalized relative entropy and the potential $\Phi_m$ (Eq. (6))
-- statement:
--   This file defines the potential function used to analyse Algorithm 2 (§5 of Agarwal et al., 2014).
--
--   For nonnegative vectors $p,q$ on the action set $A$, the **unnormalized relative entropy** is
--   $$\mathrm{RE}(p\,\|\,q)=\sum_{a\in A}\bigl(p_a\ln(p_a/q_a)+q_a-p_a\bigr).$$
--   Let $\mathcal U_A$ be the uniform distribution on $A$ ($\mathcal U_A(a)=1/K$). For a history $H_\tau$ of length $\tau$, minimum probability $\mu$ and weights $Q$ on $\Pi$, the potential is
--   $$\Phi_m(Q)=\tau\mu\left(\frac{\widehat{\mathbb E}_{x\sim H_\tau}\bigl[\mathrm{RE}(\mathcal U_A\,\|\,Q^\mu(\cdot\mid x))\bigr]}{1-K\mu}+\frac{\sum_{\pi\in\Pi}Q(\pi)b_\pi}{2K}\right)\qquad(6).$$
--
--   The first term measures how far the smoothed action distributions induced by $Q$ are from uniform, the second is a rescaled estimate of the regret of $Q$. Algorithm 2 never increases $\Phi_m$ in its rescaling step and decreases it by a fixed amount in each coordinate step.
--
--   **Formalization Note** $\tau$ is the length $t$ of the history. The paper writes $\Phi_m$ for epoch $m$ with $\tau=\tau_m$, $\mu=\mu_m$; here the history and $\mu$ are explicit arguments. $\ln$ is `Real.log`; for $Q\ge0$ and $0<\mu<1/K$ every argument of $\ln$ is positive, since $Q^\mu(a\mid x)\ge\mu$.
-- source:
--   Agarwal, Hsu, Kale, Langford, Li, Schapire, Taming the Monster: A Fast and Simple Algorithm for Contextual Bandits, arXiv:1402.0555v2, p. 9, §5, Eq. (6) and the definition of RE

import Mathlib
import Definitions.Def_TamingMonster_CoordDescent_Setting

namespace TamingMonster.CoordDescent

variable {X : Type*} {K t : ℕ}

/-- The unnormalized relative entropy between two nonnegative vectors on `A` (§5, p. 9):
`RE(p ‖ q) = ∑_{a ∈ A} (p_a ln(p_a / q_a) + q_a − p_a)`. -/
noncomputable def relEntropy (p q : Fin K → ℝ) : ℝ :=
  ∑ a, (p a * Real.log (p a / q a) + q a - p a)

/-- The uniform distribution `U_A` on `A = Fin K`. -/
noncomputable def uniformA (K : ℕ) : Fin K → ℝ := fun _ => 1 / (K : ℝ)

/-- The potential function, Eq. (6) (p. 9), for the history `H_τ` of length `τ = t` and minimum
probability `μ`:
`Φ(Q) = τμ ( Ê_x[RE(U_A ‖ Q^μ(· | x))] / (1 − Kμ) + ∑_{π ∈ Π} Q(π) b_π / (2K) )`. -/
noncomputable def potential (Pi : Finset (X → Fin K)) (H : History X K t) (μ : ℝ)
    (Q : Pi → ℝ) : ℝ :=
  (t : ℝ) * μ *
    (empExp H (fun x => relEntropy (uniformA K) (smoothedProj Pi μ Q x)) / (1 - (K : ℝ) * μ)
      + (∑ π, Q π * bCoef Pi H μ (π : X → Fin K)) / (2 * (K : ℝ)))

end TamingMonster.CoordDescent


