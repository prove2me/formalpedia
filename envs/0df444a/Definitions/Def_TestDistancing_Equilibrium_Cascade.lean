-- Prove2me | Definitions.Def_TestDistancing_Equilibrium_Cascade
-- name    : TestDistancing_Equilibrium_Cascade
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:32:39.580703+00:00
-- url     : https://prove2.me/theorems/c31d41c4-38c6-43bc-b8dd-728a9aee0e3a
-- title:
--   Finite independent cascade with vertex testing
-- statement:
--   Let a source be chosen uniformly among $n$ agents in an undirected contact graph $G$. Each agent receives one independent testing coin. A tested agent transmits along each outgoing contact with probability $\beta p$; an untested agent uses probability $\beta$. Transmission coins are independent across ordered contacts. The infection probability of an agent is the total weight of outcomes in which the source reaches her through live directed contacts.
--
--   $$P_i^{\mathrm{inf}}(G,\alpha_L,\alpha_H)=\Pr\{s\leadsto i\}. $$
--
--   This reusable finite cascade is the infection layer beneath the paper's activity game. Reflexive reachability includes infection of the source.
-- source:
--   Acemoglu, Makhdoumi, Malekian & Ozdaglar, Testing, Voluntary Social Distancing and the Spread of an Infection, NBER Working Paper 27483 (July 2020), https://www.nber.org/papers/w27483, pp. 5–7 (PDF 7–9), §2.2 and Definition 1

import Mathlib
open Classical

namespace TestDistancing.Equilibrium

/-- An independently sampled Bernoulli coin. -/
def bern (q : ℝ) (b : Bool) : ℝ := if b then q else 1 - q

/-- A finite independent cascade with one testing coin per vertex, shared by its out-arcs,
and one transmission coin per ordered arc. The source is uniform. -/
noncomputable def cascadeInf {n : ℕ} (G : SimpleGraph (Fin n))
    (test : Fin n → ℝ) (β p : ℝ) (i : Fin n) : ℝ :=
  ∑ s : Fin n, ∑ Z : Fin n → Bool, ∑ T : Fin n → Fin n → Bool,
    ((1 : ℝ) / n) *
      (∏ k : Fin n, bern (test k) (Z k)) *
      (∏ k : Fin n, ∏ j : Fin n,
        bern (if Z k then β * p else β) (T k j)) *
      (if Relation.ReflTransGen (fun k j => G.Adj k j ∧ T k j = true) s i then 1 else 0)

end TestDistancing.Equilibrium


