-- Prove2me | Definitions.Def_StatComplexityDM_Disagreement_Coefficient
-- name    : StatComplexityDM_Disagreement_Coefficient
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:22:18.87385+00:00
-- url     : https://prove2.me/theorems/e339c98c-ac8a-4528-a773-7926788b59a1
-- title:
--   Definition 6.3, (71), and (70), p. 45 — finitely supported distributions, the disagreement coefficient θ(F, Δ₀, ε₀; ρ), shifted classes and the square-loss DEC objective
-- statement:
--   This file fixes the objects of §6.2 of Foster, Kakade, Qian and Rakhlin.
--
--   1. A function $\mu : X \to \mathbb{R}$ on a finite set $X$ is a **probability distribution** if $\mu(x) \ge 0$ for every $x$ and $\sum_x \mu(x) = 1$.
--   2. A **finitely supported distribution** $\rho$ on the decision space $\Pi$ is given by a finite family of weights $\rho_k \ge 0$ summing to one and atoms $\pi_k \in \Pi$, $\rho = \sum_k \rho_k \delta_{\pi_k}$. Its expectation is $\mathbb{E}_{\pi\sim\rho}[\varphi(\pi)] = \sum_k \rho_k\, \varphi(\pi_k)$ and the probability of an event $A \subseteq \Pi$ is $\mathbb{P}_{\pi\sim\rho}(A) = \sum_k \rho_k\, \mathbb{I}\{\pi_k \in A\}$.
--   3. For a class $\mathcal{F}$ of functions $\Pi \to \mathbb{R}$, scales $\Delta, \varepsilon$ and $\rho$ as above, the **disagreement event** is the set of decisions $\pi$ such that some $f \in \mathcal{F}$ has $|f(\pi)| > \Delta$ while $\mathbb{E}_{\pi'\sim\rho}[f^2(\pi')] \le \varepsilon^2$, the inner expectation being over an independent draw $\pi' \sim \rho$.
--   4. The **disagreement coefficient** (Definition 6.3) is
--   $$
--   \theta(\mathcal{F}, \Delta_0, \varepsilon_0; \rho) = \sup_{\Delta \ge \Delta_0,\ \varepsilon \ge \varepsilon_0} \left\{ \frac{\Delta^2}{\varepsilon^2} \cdot \mathbb{P}_{\pi\sim\rho}\bigl( \exists f \in \mathcal{F} : |f(\pi)| > \Delta,\ \mathbb{E}_{\pi'\sim\rho}[f^2(\pi')] \le \varepsilon^2 \bigr) \right\} \vee 1 .
--   $$
--   5. For a class $\mathcal{F}$ and a function $g$, the **shifted class** is $\mathcal{F} - g = \{ \pi \mapsto f(\pi) - g(\pi) : f \in \mathcal{F} \}$.
--   6. For a finitely supported prior $\mu = \sum_i w_i \delta_{M_i}$ over models, with mean-reward functions $f^{M_i}$ and decisions $\pi_{M_i}$, a reference mean reward $f^{\overline{M}}$, a parameter $\gamma$ and a finitely supported decision distribution $p$, the **square-loss DEC objective** of (70) with $D = D_{\mathrm{Sq}}$, $D_{\mathrm{Sq}}(M(\pi), \overline{M}(\pi)) = (f^M(\pi) - f^{\overline{M}}(\pi))^2$, is
--   $$
--   \mathbb{E}_{M\sim\mu}\, \mathbb{E}_{\pi\sim p}\Bigl[ f^M(\pi_M) - f^M(\pi) - \gamma \cdot \bigl(f^M(\pi) - f^{\overline{M}}(\pi)\bigr)^2 \Bigr] .
--   $$
--   The prior-dependent square-loss DEC $\underline{\mathrm{dec}}^{\mathrm{Sq}}_\gamma(\mu, \overline{M})$ of (70) is the infimum of this objective over $p \in \Delta(\Pi)$.
--
--   The disagreement coefficient measures how much mass a distribution $\rho$ places on decisions where some function of the class is large although it is small in $L_2(\rho)$; it is the complexity parameter of the paper's posterior-sampling bound for structured bandits.
--
--   **Formalization Note** Distributions over decisions and priors over models are finitely supported (the paper's footnote 5 equips the model class with the discrete topology), so expectations are finite sums; the decision space itself is an arbitrary type. On the page, (71) uses the letter $\pi$ both for the outer and the inner random decision; the inner expectation is over an independent copy. The supremum in (71) is Lean's real `sSup`; it is a genuine supremum whenever $\Delta_0 > 0$, $\varepsilon_0 > 0$ and $\mathcal{F}$ is uniformly bounded, which every statement using it assumes. A model enters the square-loss objective only through its mean-reward function and its decision $\pi_M$, so models are represented by these two data.
-- source:
--   arXiv:2112.13487v3, (70) and Definition 6.3 (71), p. 45; D_Sq, §4.3, p. 28

import Mathlib
import Definitions.Def_StatComplexityDM_LowerBound_Core

namespace StatComplexityDM.Disagreement

/-- Expectation `E_{π∼ρ}[φ(π)]` under a finitely supported distribution on the decision space
`Act`, given as a weighted family `ρ = Σ_k ρw k · δ_{ρpt k}` (footnote 5, p. 11). -/
def distExp {κ Act : Type*} [Fintype κ] (ρw : κ → ℝ) (ρpt : κ → Act) (φ : Act → ℝ) : ℝ :=
  ∑ k, ρw k * φ (ρpt k)

open Classical in
/-- Probability `P_{π∼ρ}(A)` of an event `A ⊆ Act` under the weighted family `ρ = Σ_k ρw k · δ_{ρpt k}`. -/
noncomputable def distProb {κ Act : Type*} [Fintype κ] (ρw : κ → ℝ) (ρpt : κ → Act)
    (A : Act → Prop) : ℝ :=
  ∑ k, ρw k * (if A (ρpt k) then 1 else 0)

/-- The disagreement event of Definition 6.3, (71), p. 45, at scales `Δ, ε`:
`∃ f ∈ F, |f(π)| > Δ ∧ E_{π′∼ρ}[f²(π′)] ≤ ε²`. The inner expectation is over an independent copy
`π′ ∼ ρ` of the decision (the page reuses the letter `π`). -/
def disagreeEvent {κ Act : Type*} [Fintype κ] (F : Set (Act → ℝ)) (Δ ε : ℝ)
    (ρw : κ → ℝ) (ρpt : κ → Act) (π : Act) : Prop :=
  ∃ f ∈ F, Δ < |f π| ∧ distExp ρw ρpt (fun π' => f π' ^ 2) ≤ ε ^ 2

/-- The (scale-sensitive) disagreement coefficient, Definition 6.3, (71), p. 45:
`θ(F, Δ₀, ε₀; ρ) = sup_{Δ ≥ Δ₀, ε ≥ ε₀} {(Δ²/ε²) · P_{π∼ρ}(∃ f ∈ F : |f(π)| > Δ, E_{π′∼ρ}[f²(π′)] ≤ ε²)} ∨ 1`.
The supremum is the real `sSup`; it is a genuine supremum (the set is nonempty and bounded above)
whenever `Δ₀ > 0`, `ε₀ > 0` and `F` is uniformly bounded. -/
noncomputable def disagreementCoeff {κ Act : Type*} [Fintype κ] (F : Set (Act → ℝ)) (Δ₀ ε₀ : ℝ)
    (ρw : κ → ℝ) (ρpt : κ → Act) : ℝ :=
  max (sSup {x : ℝ | ∃ Δ ε : ℝ, Δ₀ ≤ Δ ∧ ε₀ ≤ ε ∧
    x = Δ ^ 2 / ε ^ 2 * distProb ρw ρpt (disagreeEvent F Δ ε ρw ρpt)}) 1

/-- The shifted class `F − g = {π ↦ f(π) − g(π) : f ∈ F}` (as in `F_M − f^M`, (72), p. 45). -/
def shiftClass {Act : Type*} (F : Set (Act → ℝ)) (g : Act → ℝ) : Set (Act → ℝ) :=
  (fun f π => f π - g π) '' F

/-- The objective of the prior-dependent square-loss DEC (70), p. 45, with `D = D_Sq`
(`D_Sq(M(π), M̄(π)) = (f^M(π) − f^{M̄}(π))²`, p. 28), for a finitely supported prior
`µ = Σ_i w i · δ_{M_i}` (models entering only through their mean rewards `fM i = f^{M_i}` and
decisions `piM i = π_{M_i}`), a reference mean reward `fbar = f^{M̄}`, and a finitely supported
decision distribution `p = Σ_k pw k · δ_{ppt k}`:
`E_{M∼µ} E_{π∼p}[f^M(π_M) − f^M(π) − γ · (f^M(π) − f^{M̄}(π))²]`. -/
def sqDecObjective {ι κ Act : Type*} [Fintype ι] [Fintype κ] (w : ι → ℝ) (fM : ι → Act → ℝ)
    (piM : ι → Act) (fbar : Act → ℝ) (γ : ℝ) (pw : κ → ℝ) (ppt : κ → Act) : ℝ :=
  ∑ i, w i * ∑ k, pw k * (fM i (piM i) - fM i (ppt k) - γ * (fM i (ppt k) - fbar (ppt k)) ^ 2)

end StatComplexityDM.Disagreement


