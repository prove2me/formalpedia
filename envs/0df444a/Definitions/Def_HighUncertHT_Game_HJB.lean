-- Prove2me | Definitions.Def_HighUncertHT_Game_HJB
-- name    : HighUncertHT_Game_HJB
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T22:34:35.489538+00:00
-- url     : https://prove2.me/theorems/5fd3cb24-9af9-41ef-8a59-20690f7482d0
-- title:
--   p. 10 — the Hamiltonians H̄, Hˡ, Hˡⁿ and classical solutions of (HJB)
-- statement:
--   For $(v_1,v_2,b,q)\in\mathbb R^4$ let $\bar H(v_1,v_2,b,q)=bv_1+qv_2$ and
--   $$
--   H^\ell(v_1,v_2)=\max_{(b,q)\in\mathrm{ch}(K^\ell)}\bar H(v_1,v_2,b,q),\qquad
--   H^{\ell n}(v_1,v_2)=\max_{(b,q)\in\mathrm{ch}(K^{\ell n})}\bar H(v_1,v_2,b,q),
--   $$
--   where $\mathrm{ch}$ is the closed convex hull. A **classical solution** of the HJB equation
--   $$
--   \sum_{\ell=1}^L H^\ell(u'(w),u''(w))-u(w)+w=0,\qquad w\ge0,
--   $$
--   is a function $u$ that is $C^2$ on $[0,\infty)$, satisfies the equation at every $w\ge0$, and satisfies the boundary conditions $u'(0)=0$ and $\limsup_{w\to\infty}|u(w)|/w<\infty$.
--
--   The HJB equation characterizes the value of the limiting martingale control problem, in which the adversary controls the drift and variance of a reflected diffusion.
--
--   **Formalization Note** $u'$ and $u''$ are one-sided derivatives within $[0,\infty)$ (`derivWithin`), so $u'(0)$ is the right derivative and no junk derivative can satisfy the equation. Linear growth is written $\exists C,\ \forall w\ge0,\ |u(w)|\le C(1+w)$, equivalent to the limsup condition for $u$ continuous on $[0,\infty)$. The maxima are suprema of images of the closed convex hull, attained for the sets of the setting ($K^\ell$ compact; $K^{\ell n}$ nonempty and bounded by Assumption 1.1).
-- source:
--   Atar, Castiel, Shadmi, Scheduling in the High Uncertainty Heavy Traffic Regime, arXiv:2204.05733v1, p. 10, definitions of H̄, Hˡ, Hˡⁿ and (HJB) with its boundary conditions

import Mathlib
import Definitions.Def_HighUncertHT_Game_Setting

namespace HighUncertHT.Game

/-!
Atar, Castiel, Shadmi, arXiv:2204.05733v1, §2.2, p. 10: the Hamiltonians `H̄`, `H^ℓ`, `H^{ℓn}` and
classical solutions of the HJB equation

  `Σ_{ℓ=1}^L H^ℓ(u′(w), u″(w)) - u(w) + w = 0`, `w ≥ 0`,   (HJB)

with `u′(0) = 0` and `limsup_{w→∞} |u(w)|/w < ∞`. `ch` is the closed convex hull (§1.4, p. 4).
-/

variable {L : ℕ}

/-- `H̄(v₁, v₂, b, q) = b v₁ + q v₂` (p. 10). -/
def Hbar (v₁ v₂ b q : ℝ) : ℝ := b * v₁ + q * v₂

/-- `max_{(b, q) ∈ ch(K)} H̄(v₁, v₂, b, q)`, as the supremum of the image of the closed convex hull.
For the sets used here (`K^ℓ` compact, `K^{ℓn}` nonempty and bounded) the closed convex hull is a
nonempty compact set, so the supremum is attained: it is the paper's `max`. -/
noncomputable def maxOverHull (K : Set (ℝ × ℝ)) (v₁ v₂ : ℝ) : ℝ :=
  sSup ((fun p : ℝ × ℝ => Hbar v₁ v₂ p.1 p.2) '' closedConvexHull ℝ K)

/-- `H^ℓ(v₁, v₂) = max_{(b,q) ∈ ch(K^ℓ)} H̄(v₁, v₂, b, q)` (p. 10). -/
noncomputable def Hlim (S : Setting L) (ℓ : Fin L) (v₁ v₂ : ℝ) : ℝ :=
  maxOverHull (S.K ℓ) v₁ v₂

/-- `H^{ℓn}(v₁, v₂) = max_{(b,q) ∈ ch(K^{ℓn})} H̄(v₁, v₂, b, q)` (p. 10). -/
noncomputable def Hpre (S : Setting L) (n : ℕ) (ℓ : Fin L) (v₁ v₂ : ℝ) : ℝ :=
  maxOverHull (S.Kn n ℓ) v₁ v₂

/-- The one-sided first derivative `u′` on `[0, ∞)`. -/
noncomputable def d1 (u : ℝ → ℝ) : ℝ → ℝ := derivWithin u (Set.Ici 0)

/-- The one-sided second derivative `u″` on `[0, ∞)`. -/
noncomputable def d2 (u : ℝ → ℝ) : ℝ → ℝ := derivWithin (derivWithin u (Set.Ici 0)) (Set.Ici 0)

/-- `u` is a **classical solution** of (HJB) (p. 10): `u` is `C²` on `[0, ∞)` (derivatives
one-sided at `0`), satisfies (HJB) at every `w ≥ 0`, `u′(0) = 0`, and has at most linear growth,
`∃ C, ∀ w ≥ 0, |u(w)| ≤ C (1 + w)`, which for `u` continuous on `[0, ∞)` is equivalent to
`limsup_{w→∞} |u(w)|/w < ∞`. Values at negative arguments are irrelevant. -/
def IsClassicalSolution (S : Setting L) (u : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 u (Set.Ici 0) ∧
  (∀ w : ℝ, 0 ≤ w → ∑ ℓ, Hlim S ℓ (d1 u w) (d2 u w) - u w + w = 0) ∧
  d1 u 0 = 0 ∧
  ∃ C : ℝ, ∀ w : ℝ, 0 ≤ w → |u w| ≤ C * (1 + w)

end HighUncertHT.Game


