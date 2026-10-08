-- Prove2me | Definitions.Def_BoundedNV_RareEvent_Logit
-- name    : BoundedNV_RareEvent_Logit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T20:01:12.782325+00:00
-- url     : https://prove2.me/theorems/b1f26003-6217-44ad-8042-00981a0fb253
-- title:
--   §3, p. 571 — the choice distribution Ψ of the continuous logit model
-- statement:
--   For a decision domain $S\subseteq\mathbb R$, a utility $u$ and a bounded-rationality parameter $\beta$, let $\psi$ be the logit choice density (2),
--
--   $$
--   \psi(y)=\mathbf 1_S(y)\frac{e^{u(y)/\beta}}{\int_S e^{u(v)/\beta}\,dv}.
--   $$
--
--   The choice distribution is its distribution function
--
--   $$
--   \Psi(y)=\int_{-\infty}^{y}\psi(v)\,dv .
--   $$
--
--   The behavioral newsvendor of §4 uses $u=\pi$, the expected profit (3), and $S$ the decision domain, giving the density (4) of the behavioral solution $X^\flat$.
--
--   **Formalization Note** Only $\Psi$ is declared here. The density $\psi$, the expectation $\mathbb E\,g(Y)=\int g\psi$, the demand density, $F$, $\mathbb E\min(D,x)$, $\pi$ and the decision domain come from the group's shared definition modules, which this file imports. The logit formula is used only with $\beta>0$ and a positive, finite normalizer.
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4), 2008, p. 571 (PDF 6), eq. (2) and the choice distribution Ψ

import Mathlib
import Definitions.Def_BoundedNV_ExpFam_Logit
import Definitions.Def_BoundedNV_Uniform_Logit

namespace BoundedNV.RareEvent

/-- The logit choice distribution function. -/
noncomputable def logitCDF (S : Set ℝ) (u : ℝ → ℝ) (β : ℝ) (y : ℝ) : ℝ :=
  ∫ v in Set.Iic y, BoundedNV.Uniform.logitDensity S u β v

end BoundedNV.RareEvent


