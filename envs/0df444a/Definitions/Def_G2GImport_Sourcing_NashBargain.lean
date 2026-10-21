-- Prove2me | Definitions.Def_G2GImport_Sourcing_NashBargain
-- name    : G2GImport_Sourcing_NashBargain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:31.54155+00:00
-- url     : https://prove2.me/theorems/abdb2135-0f6d-4617-b5b7-d8d8f24ea8c3
-- title:
--   Generalized Nash bargaining over quantity and payment
-- statement:
--   A buyer and a supplier choose a feasible quantity $q$ and a nonnegative payment $t$. Their gains over disagreement are $g_B(q,t)$ and $g_S(q,t)$, and the buyer's bargaining power is $\gamma$.
--
--   The **Nash product** is
--   $$N_\gamma(g_B,g_S)=g_B^{\gamma}g_S^{1-\gamma}.$$
--   A Nash bargaining solution is an individually rational pair with $q$ in the feasible set, $t\ge0$, and both gains nonnegative, whose Nash product is at least that of every other individually rational feasible pair.
--
--   This general quantity-and-payment solution concept is used for both contracting times in the paper. It does not fix a disagreement point; the model supplies the gain functions for each negotiation.
-- source:
--   Mu, Hu, Reddy & Gavirneni, Negotiating government-to-government food importing contracts: a Nash bargaining framework, accepted manuscript (MSOM, doi:10.1287/msom.2021.1027), PDF pp. 4, 6, 13–14, Nash products in §§3–4 and Appendix B

import Mathlib

namespace G2GImport.Sourcing

/-- The generalized Nash product of nonnegative buyer and supplier gains. -/
noncomputable def nashProd (γ gB gS : ℝ) : ℝ := gB ^ γ * gS ^ (1 - γ)

/-- A quantity and payment maximize the generalized Nash product over all individually
rational feasible quantity-payment pairs. The functions give gains over disagreement. -/
def IsNBS (γ : ℝ) (A : Set ℝ) (gB gS : ℝ → ℝ → ℝ) (q t : ℝ) : Prop :=
  q ∈ A ∧ 0 ≤ t ∧ 0 ≤ gB q t ∧ 0 ≤ gS q t ∧
  ∀ q' ∈ A, ∀ t', 0 ≤ t' → 0 ≤ gB q' t' → 0 ≤ gS q' t' →
    nashProd γ (gB q' t') (gS q' t') ≤ nashProd γ (gB q t) (gS q t)

end G2GImport.Sourcing


