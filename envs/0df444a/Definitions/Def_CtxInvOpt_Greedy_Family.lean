-- Prove2me | Definitions.Def_CtxInvOpt_Greedy_Family
-- name    : CtxInvOpt_Greedy_Family
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:29:23.868902+00:00
-- url     : https://prove2.me/theorems/b2086780-f8af-44a1-8c25-0fa07ec4169c
-- title:
--   App-9, proof of Theorem 2, Steps 1–2 — the sets C_{ε,ᾱ}, the true cost c⋆ and nature's instances X_t = {x̄_t, 0}
-- statement:
--   These are the objects of the lower-bound construction in the proof of Theorem 2, in dimension $d=3$. For an angle $\bar\alpha$ and $\varepsilon\ge 0$ put
--
--   $$h_1=(2\sin^2\bar\alpha,\,-\sin 2\bar\alpha,\,\sin 2\bar\alpha),\quad h_2=(2\sin^2\bar\alpha,\,-\sin 2\bar\alpha,\,-\sin 2\bar\alpha),\quad h_3=(-\varepsilon,1,0),$$
--
--   and let
--
--   $$C_{\varepsilon,\bar\alpha}=\{c:h_1'c\ge0\}\cap\{c:h_2'c\ge0\}\cap\{c:h_3'c\ge0\}\cap S^3,$$
--
--   the intersection of a polyhedral cone with the unit sphere. The true cost is $c^\star=(\cos\bar\alpha,\sin\bar\alpha,0)$. For $\varepsilon\in\mathbb R$ write $\bar x(\varepsilon)=(e_2-\varepsilon e_1)/\|e_2-\varepsilon e_1\|$, the unit vector along $(-\varepsilon,1,0)$. Nature's instance for horizon $T$ uses $\varepsilon_1=\tan\bar\alpha/(2T)$, $\varepsilon_t=t\varepsilon_1$, and the two-point feasible sets $\mathcal X_t=\{\bar x(\varepsilon_t),0\}$.
--
--   With these choices the knowledge sets of the greedy circumcenter policy stay inside the family $C_{\varepsilon,\bar\alpha}$ while the policy keeps paying regret bounded away from zero.
--
--   **Formalization Note** The paper's coordinates $1,2,3$ are Lean's `0, 1, 2`. Lean periods are $0$-based, so `instX a T t` is the paper's $\mathcal X_{t+1}=\{\bar x(\varepsilon_{t+1}),0\}$ with $\varepsilon_{t+1}=(t+1)\varepsilon_1$.
-- source:
--   Besbes, Fonseca, Lobel, Contextual Inverse Optimization: Offline and Online Learning, arXiv:2106.14015v3, App-9, proof of Theorem 2, Steps 1–2

import Mathlib
import Definitions.Def_CtxInvOpt_Offline_Geometry

namespace CtxInvOpt.Greedy

open Real

/-- **App-9, proof of Theorem 2, Step 1.** `h₁ = (2 sin² ᾱ, − sin 2ᾱ, sin 2ᾱ)`. -/
noncomputable def h1 (a : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[2 * Real.sin a ^ 2, -Real.sin (2 * a), Real.sin (2 * a)]

/-- **App-9, Step 1.** `h₂ = (2 sin² ᾱ, − sin 2ᾱ, − sin 2ᾱ)`. -/
noncomputable def h2 (a : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[2 * Real.sin a ^ 2, -Real.sin (2 * a), -Real.sin (2 * a)]

/-- **App-9, Step 1.** `h₃ = (−ε, 1, 0)`. -/
def h3 (ε : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[-ε, 1, 0]

/-- **App-9, Step 1.** The family
`C_{ε,ᾱ} = {c : h₁′c ≥ 0} ∩ {c : h₂′c ≥ 0} ∩ {c : h₃′c ≥ 0} ∩ S³` (here `d = 3`);
`Cfam ε a` is `C_{ε,a}`. -/
noncomputable def Cfam (ε a : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {c | 0 ≤ inner ℝ (h1 a) c ∧ 0 ≤ inner ℝ (h2 a) c ∧ 0 ≤ inner ℝ (h3 ε) c} ∩ CtxInvOpt.Offline.unitSphere 3

/-- **App-9, Step 2.** `x̄ = (e₂ − ε e₁)/‖e₂ − ε e₁‖`, i.e. the unit vector along `(−ε, 1, 0)`
(the paper's coordinates `1, 2, 3` are Lean's `0, 1, 2`). -/
noncomputable def xbar (ε : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  ‖(!₂[-ε, 1, 0] : EuclideanSpace ℝ (Fin 3))‖⁻¹ • (!₂[-ε, 1, 0] : EuclideanSpace ℝ (Fin 3))

/-- **App-9, Step 1.** The true cost `c⋆ = g₃ = (cos ᾱ, sin ᾱ, 0)`. -/
noncomputable def cstarFam (a : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[Real.cos a, Real.sin a, 0]

/-- **App-9, Step 2.** `ε₁ = tan ᾱ / (2T)`. -/
noncomputable def eps1 (a : ℝ) (T : ℕ) : ℝ :=
  Real.tan a / (2 * T)

/-- **App-9, Step 2.** Nature's feasible sets `X_t = {x̄_t, 0}` with `x̄_t` built from
`ε_t = t ε₁`. Lean periods are 0-based: `instX a T t` is the paper's `X_{t+1}`, built from
`ε_{t+1} = (t + 1) ε₁`. -/
noncomputable def instX (a : ℝ) (T : ℕ) (t : ℕ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {xbar (((t : ℝ) + 1) * eps1 a T), 0}

end CtxInvOpt.Greedy


