-- Prove2me | Definitions.Def_BilatMatch_submarket
-- name    : BilatMatch_submarket
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:08:09.941938+00:00
-- url     : https://prove2.me/theorems/c1deb1fe-2603-4c68-b03f-d3453431b7bb
-- title:
--   Finite submarket $\mathcal I_n$ with $\mathcal F_n=\{M\in\mathcal F: M\subseteq B_n\times S_n\}$
-- statement:
--   For agent sets $B_n\subseteq B$ and $S_n\subseteq S$ the **submarket** $\mathcal I_n$ keeps the agents of $B_n$ and $S_n$ with their priors, the edges between them, and the feasible family
--   $$\mathcal F_n=\{M\in\mathcal F:\ M\subseteq B_n\times S_n\}.$$
--   The module also defines the restriction of a type profile of $\mathcal I$ to the agents of $\mathcal I_n$.
--
--   **Formalization Note** $\mathcal I_n$ is a market on the subtypes of $B_n$, $S_n$; a matching of $\mathcal I_n$ is identified with its image in $B\times S$.
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), Lemma B.9, p.36 (pdf p.38)

import Mathlib
import Definitions.Def_BilatMatch_Market

open MeasureTheory

namespace BilatMatch

/-!
# Finite submarkets of a countable market

Liu, Qin, Wang, *From Bilateral Trade to Matching Markets: Sharp Gains from Trade*,
arXiv:2609.30702 (held version, sha256 ff1490ad…), Lemma B.9, p.36 (pdf p.38).

**Formalization Note** The submarket `I_n` on finite agent sets `B_n ⊆ B`, `S_n ⊆ S` is a market on
the subtypes `↥B_n`, `↥S_n`: its agents keep their priors, its edges are the edges of `I` between
them, and its feasible family is `F_n = {M ∈ F : M ⊆ B_n × S_n}`, a matching of `I_n` being identified
with its image in `B × S`.
-/

variable {B S : Type*}

/-- The submarket `I_n` of `I` on the agent sets `Bn`, `Sn` (Lemma B.9). -/
def Market.restrict (I : Market B S) (Bn : Set B) (Sn : Set S) : Market Bn Sn where
  edges := {e | ((e.1 : B), (e.2 : S)) ∈ I.edges}
  family := {M | Prod.map Subtype.val Subtype.val '' M ∈ I.family}
  buyerLaw := fun i => I.buyerLaw i
  sellerLaw := fun j => I.sellerLaw j

/-- The restriction of a profile of `I` to the agents of the submarket. -/
def restrictProfile {Bn : Set B} {Sn : Set S} (θ : Profile B S) : Profile Bn Sn :=
  (fun i => θ.1 i, fun j => θ.2 j)

end BilatMatch


