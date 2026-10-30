-- Prove2me | Definitions.Def_SupplyChainCarbon_Necessity_Domains
-- name    : SupplyChainCarbon_Necessity_Domains
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:33:23.288221+00:00
-- url     : https://prove2.me/theorems/2a42b68b-b1bd-46e6-bc8c-7c9a323e5bf8
-- title:
--   Continuous effort boxes and nonnegative footprints
-- statement:
--   There are positive finite numbers $N$ of firms and $I$ of processes. Firm $n$ has $m_n$ real effort coordinates, with $m_n>0$. For a common effort bound $A>0$, the feasible domains are
--
--   $$E=\prod_n[0,A]^{m_n},\qquad E_n=[0,A]^{m_n},\qquad F=\{\phi\in\mathbb R^I:\phi_i\ge0\text{ for all }i\}.$$
--
--   This module transparently reuses the published effort and firm boxes and defines the nonnegative footprint orthant. These domains retain every continuous feasible effort, including boundary points. Positivity of the counts and bound belongs to the technology data, rather than these bare type aliases.
--
--   **Formalization Note** Zero-based finite indices merely reindex the manuscript's one-based sets. Functions are implemented on ambient real vector spaces; all analytic conditions will be restricted to the displayed domains.
-- source:
--   Caro, Corbett, Tan and Zuidwijk, Double-Counting in Supply Chain Carbon Footprinting, working paper dated December 21, 2012, §3.1, p. 8; §3.3, pp. 10–11

import Mathlib
import Definitions.Def_CarbonDoubleCount_Planner_Setting

namespace SupplyChainCarbon.Necessity

abbrev Effort (N : ℕ) (m : Fin N → ℕ) := (n : Fin N) → Fin (m n) → ℝ
abbrev Footprint (I : ℕ) := Fin I → ℝ

/-- Transparent reuse of the published collective effort box. -/
abbrev effortBox {N : ℕ} (m : Fin N → ℕ) (A : ℝ) : Set (Effort N m) :=
  CarbonDoubleCount.Planner.effortBox A

abbrev firmBox {N : ℕ} (m : Fin N → ℕ) (A : ℝ) (n : Fin N) : Set (Fin (m n) → ℝ) :=
  CarbonDoubleCount.Planner.firmBox (act := fun k => Fin (m k)) A n

/-- The source's domain of nonnegative process footprints. -/
def footprintOrthant (I : ℕ) : Set (Footprint I) := {φ | ∀ i, 0 ≤ φ i}

end SupplyChainCarbon.Necessity


