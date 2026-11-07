-- Prove2me | Definitions.Def_MulticastPoS_IsGlobalMin
-- name    : MulticastPoS_IsGlobalMin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:38:52.670437+00:00
-- url     : https://prove2.me/theorems/dfc0a1d5-29e4-4989-aa93-9f2d30fde28b
-- title:
--   Global minimizer of the potential
-- statement:
--   A profile $P$ of a congestion game is a **global minimizer of the potential** if it is feasible and
--
--   $$
--   \Phi(P)\le\Phi(R)\quad\text{for every feasible profile } R,
--   $$
--
--   including profiles in which many players change paths at once. Here $\Phi$ is Rosenthal's potential.
--
--   By Corollary 2.1 every global minimizer is a Nash equilibrium; the main theorem bounds the social cost of every global minimizer.
-- source:
--   Huang–Yuan, An O(log log n) Upper Bound on the Price of Stability for Undirected Multicast Shapley Games, STOC 2027 submission (manuscript sha256 dd0e08d0…), Section 1, p.2; Corollary 2.1 and the paragraph after it, p.5

import Mathlib
import Definitions.Def_PriceOfStability_Harmonic_Model

open CongestionPoA.AsymSum PriceOfStability.Harmonic

namespace MulticastPoS

/-- A global minimizer of the potential (Huang–Yuan, *An O(log log n) Upper Bound on the Price of
Stability for Undirected Multicast Shapley Games*, STOC 2027 submission manuscript (sha256
dd0e08d0…f6d4), Section 1, p.2 and Section 2, p.5): `P` is a feasible profile and
`Φ(P) ≤ Φ(R)` for every feasible profile `R`, including profiles in which many players change
paths together.

**Formalization Note** Stated for every congestion game, with the published Rosenthal potential
`PriceOfStability.Harmonic.potential`; for `game G c t s` this is `Φ(P) = Σ_e c_e H_{x_e(P)}`. -/
def IsGlobalMin {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (Γ : CongestionGame ι E) (P : ι → Finset E) : Prop :=
  IsProfile Γ P ∧ ∀ R, IsProfile Γ R → potential Γ P ≤ potential Γ R

end MulticastPoS


