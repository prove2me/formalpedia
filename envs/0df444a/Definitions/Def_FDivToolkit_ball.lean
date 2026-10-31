-- Prove2me | Definitions.Def_FDivToolkit_ball
-- name    : FDivToolkit_ball
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:22:51.779838+00:00
-- url     : https://prove2.me/theorems/e0ec7b39-1f39-4dd8-ac56-55997a132769
-- title:
--   The divergence ball and its set of means
-- statement:
--   For a radius $\kappa$, the **ball** around $\nu$ is the set of densities $g$ of distributions $\eta$ with $D_F(\eta\,|\,\nu)\le\kappa$. The **worst case** is
--   $$
--   W(\nu,F,\kappa)=\sup_{\eta:\,D_F(\eta|\nu)\le\kappa}\int_{\mathcal S}x\,g(x)\,dx. \tag{4}
--   $$
--
--   This is the optimization problem at the centre of the paper.
--
--   **Formalization Note** `meanSet` is the set of values $\int x\,g(x)\,dx$ over the ball. The mission states facts about $W$ through `BddAbove` and `IsGreatest` of this set, never through a real `sSup`. Membership in the ball imposes no integrability of $x\,g(x)$; that integrability is a conclusion of Proposition 1.
-- source:
--   Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), display (4), §2.2, p.7

import Definitions.Def_FDivToolkit_fDiv
import Definitions.Def_FDivToolkit_Fh

namespace FDivToolkit

/-- The feasible set of the worst-case problem (4), Kruse, Schneider & Schweizer, SSRN 3680475
(Aug 25, 2020), §2.2, p.7: the densities `g` of all distributions η with `D_F(η|ν) ≤ κ`.

**Formalization Note.** Absolute continuity is forced by `fDiv`, which is `⊤` otherwise. No
integrability of `x g(x)` is imposed: that integrability is a conclusion of Proposition 1, so
heavy-tailed members would not be silently dropped. -/
def ball (H f : ℝ → ℝ) (κ : ℝ) : Set (ℝ → ℝ) :=
  {g | IsDensity g ∧ fDiv (Fbar H) f g ≤ ENNReal.ofReal κ}

/-- The set of expected values `E_η[X] = ∫_𝓢 x g(x) dx` over the ball, whose supremum is the worst
case `W(ν, F, κ)` of display (4), Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), §2.2,
p.7.

**Formalization Note.** The worst case is never written as a real `sSup`, which would be `0` for an
unbounded set. Statements use `BddAbove` and `IsGreatest` of this set, together with integrability
of every member. -/
noncomputable def meanSet (H f : ℝ → ℝ) (κ : ℝ) : Set ℝ :=
  (fun g : ℝ → ℝ => ∫ x, x * g x) '' ball H f κ

end FDivToolkit


