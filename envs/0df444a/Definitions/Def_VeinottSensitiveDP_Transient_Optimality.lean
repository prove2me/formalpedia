-- Prove2me | Definitions.Def_VeinottSensitiveDP_Transient_Optimality
-- name    : VeinottSensitiveDP_Transient_Optimality
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:50:30.346828+00:00
-- url     : https://prove2.me/theorems/f6457c9b-82c8-45d2-9a9a-159bd6327b1d
-- title:
--   V* ≡ max_f V(f^∞) and the optimal-return operator ℜV ≡ max_g [r(g) + P(g)V] (4)
-- statement:
--   In the model of §2 of Veinott (1969), with finite nonempty set $F$ of decision rules, define the vector
--
--   $$V^*=\max_{f\in F}V(f^\infty),$$
--
--   the maximum taken coordinatewise: $V^*_s=\max_{f\in F}V(f^\infty)_s$. Veinott defines it provided every stationary policy is transient (Corollary 1 then shows that one $f$ attains every coordinate at once). Define also the **optimal-return operator** $\Re$ mapping $\mathbb R^S$ into itself by (4):
--
--   $$\Re V=\max_{g\in F}\,[\,r(g)+P(g)V\,],\qquad V\in\mathbb R^S,$$
--
--   again coordinatewise: $(\Re V)_s=\max_{g\in F}[\,r(s,g(s))+\sum_t p(t\mid s,g(s))V_t\,]$. The operator $\Re$ is monotone.
--
--   $\Re V$ is the best return obtainable from one period of decisions with terminal value $V$, and $V^*$ is the best stationary total return; Corollary 2 identifies $V^*$ as the unique fixed point of $\Re$.
--
--   **Formalization Note.** Both maxima are finite `Finset.sup'` over the nonempty finite type of decision rules, not real suprema. `vStar` is meaningful when every stationary policy is transient, and every statement that uses it assumes this.
-- source:
--   Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria, Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1637, definition of V* after Corollary 1 and (4)

import Mathlib
import Definitions.Def_VeinottSensitiveDP_Transient_Model

namespace VeinottSensitiveDP.Transient

open Matrix

variable {St : Type} {A : St → Type}

namespace Program

variable [Fintype St] [DecidableEq St] [∀ s, Fintype (A s)] [∀ s, Nonempty (A s)]
  (D : Program St A)

/-- `V* ≡ max_{f ∈ F} V(f^∞)` (p. 1637), taken coordinatewise over the finite nonempty set `F`:
the `s`th coordinate is `max_f V(f^∞)_s`.

**Formalization Note.** Veinott defines `V*` "provided every stationary policy is transient";
each statement using `vStar` assumes this. The coordinatewise maximum is a finite `Finset.sup'`,
not a real supremum. -/
noncomputable def vStar : St → ℝ :=
  fun s => Finset.univ.sup' Finset.univ_nonempty fun f : DecisionRule St A => D.V (stationary f) s

/-- The optimal-return operator (4), p. 1637: `ℜV ≡ max_{g ∈ F} [r(g) + P(g)V]` for `V ∈ E^S`,
the maximum taken coordinatewise over the finite set `F`. -/
noncomputable def optReturn (W : St → ℝ) : St → ℝ :=
  fun s => Finset.univ.sup' Finset.univ_nonempty fun g : DecisionRule St A =>
    D.rvec g s + (D.Pmat g *ᵥ W) s

end Program

end VeinottSensitiveDP.Transient


