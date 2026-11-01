-- Prove2me | Definitions.Def_RockafellianRelax_epsArgmin
-- name    : RockafellianRelax_epsArgmin
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:35:30.776322+00:00
-- url     : https://prove2.me/theorems/ce0136ae-f0ee-4be6-a8d6-efef289a39f1
-- title:
--   $\varepsilon$-argmin of an extended-real-valued function
-- statement:
--   Let $\psi : \alpha \to \overline{\mathbb R}$ and $\varepsilon \in \mathbb R$ (the paper takes $\varepsilon \in [0,\infty)$). With $\inf \psi = \inf\{\psi(x) \mid x \in \alpha\}$ and the effective domain $\operatorname{dom}\psi = \{x \mid \psi(x) < \infty\}$, the **$\varepsilon$-argmin** of $\psi$ is
--
--   $$
--   \varepsilon\text{-}\operatorname{argmin}\psi = \{\bar x \in \operatorname{dom}\psi \mid \psi(\bar x) \le \inf\psi + \varepsilon\}.
--   $$
--
--   Only points where $\psi$ is finite or $-\infty$ qualify: the $\varepsilon$-argmin of the function identically $+\infty$ is empty. If $\inf\psi = -\infty$, then $\inf\psi + \varepsilon = -\infty$ and the set is $\{x \mid \psi(x) = -\infty\}$.
--
--   The approximating problems of the paper are solved to within $\varepsilon^\nu$ in this sense.
--
--   **Formalization Note** Values in `EReal`; $\inf\psi$ is the infimum in the complete lattice `EReal`; $\operatorname{dom}\psi$ is the published `AubinLipschitz.effDom` ($\psi \ne +\infty$). The type $\alpha$ is arbitrary (the paper's are $\mathbb R^n$ and $\mathbb R^m \times \mathbb R^n$).
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, §3, p.6 (notation: inf, dom, ε-argmin)

import Mathlib
import Definitions.Def_AubinLipschitz_effDom

namespace RockafellianRelax

/-- **ε-argmin** `ε-argmin ψ = {x̄ ∈ dom ψ | ψ(x̄) ≤ inf ψ + ε}`.
Royset, Chen & Eckstrand, arXiv:2204.04762v4, §3, p.6: "For ψ : ℝⁿ → R̄ and ε ∈ [0, ∞), we define
inf_x ψ(x) = inf{ψ(x) | x ∈ ℝⁿ}, dom ψ = {x ∈ ℝⁿ | ψ(x) < ∞}, and
ε-argmin_x ψ(x) = {x̄ ∈ dom ψ | ψ(x̄) ≤ inf_x ψ(x) + ε}".

**Formalization Note.** `inf_x ψ(x)` is the infimum `⨅ y, ψ y` in the complete lattice `EReal`.
`dom ψ` is the published `AubinLipschitz.effDom ψ = {x | ψ x ≠ ⊤}` (the same set as `ψ < ⊤`).
Only points of `dom ψ` qualify, so `ε-argmin` of the function `≡ +∞` is empty.
When `inf ψ = −∞`, `inf ψ + ε = −∞` and the set is `{x | ψ x = −∞}`, as in the paper's extended
arithmetic. The paper takes `ε ∈ [0, ∞)`; the definition accepts any real `ε`, and every statement
of the mission that uses it supplies `ε ≥ 0`. -/
noncomputable def epsArgmin {α : Type*} (ψ : α → EReal) (ε : ℝ) : Set α :=
  {x | x ∈ AubinLipschitz.effDom ψ ∧ ψ x ≤ (⨅ y, ψ y) + (ε : EReal)}

end RockafellianRelax


