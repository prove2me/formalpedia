-- Prove2me | Definitions.Def_DarkKnights_ActiveSellerEquilibrium
-- name    : DarkKnights_ActiveSellerEquilibrium
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:42:45.973383+00:00
-- url     : https://prove2.me/theorems/0c21347c-e407-4d8d-9c10-725dbb9561c4
-- title:
--   Subgame-perfect equilibria of the active-CDS-seller model and their value, hedge ratio, liquidation probability and premium
-- statement:
--   A **subgame-perfect equilibrium** of the model of §2 (timeline Figure 3) consists of
--
--   1. a dealer strategy $\sigma(k,b,h)$ that is optimal (Lemma 3's problem) after every $k,b,h\ge0$;
--   2. a lender strategy $h(k,b)\ge0$ that maximizes the value of debt $M(k,b,h)$ over all $h\ge0$ after every $k,b\ge0$, the dealer playing $\sigma(k,b,h)$ after each $h$;
--   3. an owner choice $(k^*,b^*)$, $k^*,b^*\ge0$, maximizing the firm value (14) $V(k,b,h(k,b))$ given these strategies.
--
--   Its **value** is $V(k^*,b^*,h^*)$ with $h^*=h(k^*,b^*)$; its **probability of liquidation** and **CDS premium** are those of $(k^*,b^*,h^*)$ under $\sigma(k^*,b^*,h^*)$.
--
--   These are the equilibria compared with the active-CDS-buyer model in Proposition 1.
--
--   **Formalization Note** Equilibria are defined by optimality conditions only, never by the closed forms of Lemmas 1–4 or eqs. (13)–(17).
-- source:
--   Danis, Gamba, Dark Knights: The Rise in Firm Intervention by CDS Investors, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023) of Management Science, doi:10.1287/mnsc.2023.4717, §2, pp.14–20 (PDF 16–22), Figure 3; eq. (14), p.20 (PDF 22)

import Mathlib
import Definitions.Def_DarkKnights_Primitives
import Definitions.Def_DarkKnights_ActiveSellerModel

open MeasureTheory

namespace DarkKnights

/-- A subgame-perfect equilibrium of model 2 (active CDS buyer and seller).
Danis, Gamba, *Dark Knights*, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023),
doi:10.1287/mnsc.2023.4717, §2, pp.14–20 (PDF pp.16–22), timeline Figure 3, eq. (14).

* `σ k b h` is the dealer's strategy (state `z ↦` offer `(b_n, θ)`) after `(k, b, h)`; it is
  optimal after every `k, b, h ≥ 0` (p.17, Lemma 3);
* `hfun k b ≥ 0` is the lender's hedge ratio after `(k, b)`; it maximizes the value of debt
  `M(k, b, ·)` over all `h ≥ 0` (p.14: "h ≥ 0"), the dealer playing `σ k b h` after each `h`;
* `(k, b)`, `k, b ≥ 0`, maximizes the owner's firm value (14) given `hfun` and `σ`.

**Formalization Note** Equilibria are defined by these optimality conditions only, never by the
closed forms of Lemmas 1–4 or eqs. (13)–(17). -/
structure Equilibrium2 (α Z τ : ℝ) where
  /-- The dealer's offer at state `z`, after `(k, b, h)`: `σ k b h z = (b_n, θ)`. -/
  σ : ℝ → ℝ → ℝ → ℝ → ℝ × ℝ
  /-- The lender's hedge ratio after the owner's choice `(k, b)`. -/
  hfun : ℝ → ℝ → ℝ
  /-- The owner's capital. -/
  k : ℝ
  /-- The owner's face value of debt. -/
  b : ℝ
  σ_opt : ∀ k' b' h' : ℝ, 0 ≤ k' → 0 ≤ b' → 0 ≤ h' → IsDealerOptimal α Z k' b' h' (σ k' b' h')
  hfun_br : ∀ k' b' : ℝ, 0 ≤ k' → 0 ≤ b' → 0 ≤ hfun k' b' ∧
    ∀ h' : ℝ, 0 ≤ h' → debtValue2 α Z k' b' h' (σ k' b' h')
      ≤ debtValue2 α Z k' b' (hfun k' b') (σ k' b' (hfun k' b'))
  k_nonneg : 0 ≤ k
  b_nonneg : 0 ≤ b
  opt : ∀ k' b' : ℝ, 0 ≤ k' → 0 ≤ b' →
    firmValue2 α Z τ k' b' (hfun k' b') (σ k' b' (hfun k' b'))
      ≤ firmValue2 α Z τ k b (hfun k b) (σ k b (hfun k b))

namespace Equilibrium2

variable {α Z τ : ℝ}

/-- The equilibrium hedge ratio `h* = h(k*, b*)`. -/
def h (E : Equilibrium2 α Z τ) : ℝ := E.hfun E.k E.b

/-- The ex ante firm value of a model-2 equilibrium, `V(k*, b*, h(k*, b*))`, eq. (14). -/
noncomputable def value (E : Equilibrium2 α Z τ) : ℝ :=
  firmValue2 α Z τ E.k E.b E.h (E.σ E.k E.b E.h)

/-- The equilibrium probability of liquidation (the credit event). -/
noncomputable def liqProb (E : Equilibrium2 α Z τ) : ℝ :=
  liqProb2 α Z E.k E.b E.h (E.σ E.k E.b E.h)

/-- The equilibrium (fair, zero-NPV) CDS premium. -/
noncomputable def premium (E : Equilibrium2 α Z τ) : ℝ :=
  premium2 α Z E.k E.b E.h (E.σ E.k E.b E.h)

end Equilibrium2

end DarkKnights


