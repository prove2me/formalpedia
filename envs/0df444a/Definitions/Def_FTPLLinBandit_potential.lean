-- Prove2me | Definitions.Def_FTPLLinBandit_potential
-- name    : FTPLLinBandit_potential
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:01:23.7273+00:00
-- url     : https://prove2.me/theorems/1fc92089-c61f-4b6d-972d-76df18989883
-- title:
--   Potential $\Psi(\Theta)=\mathbb E_{Z\sim\rho}[h(\Theta+Z)]$
-- statement:
--   Let $A\subseteq\mathbb R^d$ and let $h(\Theta)=\max_{a\in A}\langle a,\Theta\rangle$ be its support function. For a perturbation density $\rho$, the **potential** is
--   $$\Psi(\Theta)=\mathbb E_{Z\sim\rho}\big[h(\Theta+Z)\big]=\int_{\mathbb R^d}h(\Theta+z)\,\rho(z)\,dz .$$
--   With $\rho=\rho_t$ it is the paper's $\Psi_t$; the regret decomposition (10) and the stability terms $A_t$, $B_t$ are expressed through it.
--
--   **Formalization Note** $h$ is the platform's support function `DDROFB.supportFn` (a real supremum), which equals the paper's maximum when $A$ is nonempty and bounded and the maximum is attained, as in every statement of the mission. If $z\mapsto h(\Theta+z)\rho(z)$ is not integrable the Lean integral is $0$; for a density with finite first moment and bounded $A$ it is integrable.
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Eq. (1), p.5; §5, p.9; Lemma 18, p.26

import Mathlib
import Definitions.Def_DDROFB_supportFn

open MeasureTheory

namespace FTPLLinBandit

/-- **The potential `Ψ(Θ) = E_{Z∼ρ}[h(Θ + Z)]`.** Wei, arXiv:2610.17818, Eq. (1), p.5 and §5,
p.9: "we denote h(Θ) = max_{a∈A}⟨a, Θ⟩ … Define the potential function by
Ψ_t(Θ) = E_{Z∼ρ_t}[h(Θ + Z)]"; Lemma 18, p.26.

`potential A ρ Θ = ∫ h_A(Θ + z) ρ(z) dz`, where `h_A = DDROFB.supportFn A` is the support function
`h_A(w) = sup_{a∈A} ⟨w, a⟩` and `ρ` is a perturbation density on ℝ^d.

**Formalization Note.** `h_A` is the platform's support function `DDROFB.supportFn` (a real
`sSup`), which is the paper's `max_{a∈A}` whenever the maximum is attained (the linear
optimization oracle) and `A` is nonempty and bounded, as in every statement of the mission. If
`z ↦ h_A(Θ+z) ρ(z)` is not integrable the Bochner integral is `0`; for a density with a finite
first moment and bounded `A` it is integrable. -/
noncomputable def potential {d : ℕ} (A : Set (EuclideanSpace ℝ (Fin d)))
    (ρ : EuclideanSpace ℝ (Fin d) → ℝ) (Θ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ z, DDROFB.supportFn A (Θ + z) * ρ z

end FTPLLinBandit


