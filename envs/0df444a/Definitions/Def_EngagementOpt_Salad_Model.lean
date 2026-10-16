-- Prove2me | Definitions.Def_EngagementOpt_Salad_Model
-- name    : EngagementOpt_Salad_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T09:42:13.056944+00:00
-- url     : https://prove2.me/theorems/9e37d944-021b-4bfd-8e8e-4fb39481e9b7
-- title:
--   §2.1, §4, pp. 7–8, 17 — E[S] (1), E[T] (2), and coefficients a, b, using the shared content model
-- statement:
--   This module defines the expected utility, expected session length, and proof coefficients for the two-system user model of Kleinberg, Mullainathan and Raghavan. It imports the shared definitions of the parameter space, $g_S$, $g_T$, and the maximizer predicates.
--
--   A **content distribution** is a triple $\omega=(p,q,\bar v)$ of real numbers: the **moreishness** $p$ (the probability that system 1 is hooked by an item and consumes the next one), the **span** $q$ (the probability that system 2 stays interested after an item) and the **value** $\bar v$ (system 2's mean utility per item). The **parameter space** is
--   $$\Omega=[0,1)\times[0,1)\times\mathbb R_+ ,$$
--   that is, $0\le p<1$, $0\le q<1$ and $\bar v\ge0$. Let $W$ be the per-step outside option of system 2. Define
--   $$g_S(\omega)=\frac{\bar v-W}{1-q}-\frac{pW}{1-p},\qquad g_T(\omega)=\frac{1}{1-q}+\frac{p}{1-p}.$$
--
--   1. System 2's **expected utility** is equation (1): $\mathbb E[S(\omega)]=\max\bigl(g_S(\omega),0\bigr)$.
--   2. The **expected session length** is $\mathbb E[T(\omega)]=0$ when the user does not visit the platform, i.e. when $g_S(\omega)<0$, and otherwise $\mathbb E[T(\omega)]=g_T(\omega)$, equation (2).
--   3. The proof of Theorem 4.2 writes $a=\frac{1}{1-p}$ and $b=\frac{1}{1-q}$.
--   4. For a **content manifold** $\mathcal M\subseteq\Omega$, a point $\omega_S$ is a **utility maximizer** (3) if $\omega_S\in\mathcal M$ and $g_S(\omega)\le g_S(\omega_S)$ for every $\omega\in\mathcal M$.
--   5. A point $\omega_T$ is an **engagement maximizer** (4) if $\omega_T\in\mathcal M$, $g_S(\omega_T)\ge0$, and $g_T(\omega)\le g_T(\omega_T)$ for every $\omega\in\mathcal M$ with $g_S(\omega)\ge0$.
--
--   The shared base model and this module's four definitions are used by every statement of the mission.
--
--   **Formalization Note** A triple is a structure `Params` with real fields `p`, `q`, `v`; membership in $\Omega$ is the separate predicate `InOmega`, which every statement assumes where needed. The maximizer predicates do not pick a maximizer: they hold for every maximizer, so no tie-breaking rule is needed, and closedness of $\mathcal M$ (which the paper uses only to guarantee that maximizers exist) is not part of the model. In Lean $x/0=0$; all denominators $1-p$, $1-q$ are positive on $\Omega$.
-- source:
--   Kleinberg, Mullainathan, Raghavan, The Challenge of Understanding What Users Want, arXiv:2202.11776v3, pp. 7–8, equations (1), (2); p. 17, a_i, b_i; imports the shared model for p. 15, Ω and content manifold, and p. 16, g_S, g_T, (3), (4)

import Mathlib
import Definitions.Def_EngagementOpt_Misalign_Model

/-!
# The engagement-optimization model of Kleinberg, Mullainathan and Raghavan

Kleinberg, Mullainathan, Raghavan, *The Challenge of Understanding What Users Want*,
arXiv:2202.11776v3, §2.1 (pp. 7–8, equations (1), (2)) and §4 (pp. 15–17, Ω, the content
manifold, g_S, g_T, (3), (4), and the notation a_i, b_i of the proof of Theorem 4.2).
-/

namespace EngagementOpt.Salad

/-- System 2's expected utility, equation (1), p. 7: `E[S(ω)] = max(g_S(ω), 0)`. -/
noncomputable def ES (W : ℝ) (ω : EngagementOpt.Misalign.Params) : ℝ :=
  max (EngagementOpt.Misalign.gS W ω) 0

/-- Expected session length, equation (2) and p. 7–8: `T = 0` when the user does not visit the
platform (`g_S(ω) < 0`), and otherwise `E[T(ω)] = 1/(1 − q) + p/(1 − p)`. -/
noncomputable def ET (W : ℝ) (ω : EngagementOpt.Misalign.Params) : ℝ :=
  if EngagementOpt.Misalign.gS W ω < 0 then 0 else EngagementOpt.Misalign.gT ω

/-- `a = 1/(1 − p)` (proof of Theorem 4.2, p. 17). -/
noncomputable def aCoef (ω : EngagementOpt.Misalign.Params) : ℝ :=
  1 / (1 - ω.p)

/-- `b = 1/(1 − q)` (proof of Theorem 4.2, p. 17). -/
noncomputable def bCoef (ω : EngagementOpt.Misalign.Params) : ℝ :=
  1 / (1 - ω.q)

end EngagementOpt.Salad


