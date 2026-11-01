-- Prove2me | Definitions.Def_RockafellianRelax_argmin
-- name    : RockafellianRelax_argmin
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:36:22.287932+00:00
-- url     : https://prove2.me/theorems/55cb2ebd-834e-4404-83c6-52cd0e37f4d7
-- title:
--   $\operatorname{argmin}$ of an extended-real-valued function
-- statement:
--   For $\psi : \alpha \to \overline{\mathbb R}$, the **argmin** is the $0$-argmin:
--
--   $$
--   \operatorname{argmin}\psi = \{\bar x \in \operatorname{dom}\psi \mid \psi(\bar x) \le \inf\psi\}.
--   $$
--
--   It contains only points with $\psi(\bar x) < \infty$; the argmin of the function identically $+\infty$ is empty, and if $\inf\psi = -\infty$ it is the set where $\psi = -\infty$.
--
--   **Formalization Note** Defined as `epsArgmin ψ 0`.
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, §3, p.6 ("0-argmin_x ψ(x) simply being written as argmin_x ψ(x)")

import Mathlib
import Definitions.Def_RockafellianRelax_epsArgmin

namespace RockafellianRelax

/-- **argmin** `argmin ψ = 0-argmin ψ = {x̄ ∈ dom ψ | ψ(x̄) ≤ inf ψ}`.
Royset, Chen & Eckstrand, arXiv:2204.04762v4, §3, p.6: "with 0-argmin_x ψ(x) simply being written
as argmin_x ψ(x)".

**Formalization Note.** Only points with `ψ < ⊤` qualify (`argmin` of the function `≡ +∞` is `∅`);
if `inf ψ = −∞` the set is `{x | ψ x = −∞}`. -/
noncomputable def argmin {α : Type*} (ψ : α → EReal) : Set α :=
  epsArgmin ψ 0

end RockafellianRelax


