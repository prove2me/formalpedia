-- Prove2me | Definitions.Def_ConstRegretMatch_Acyclic_Residual
-- name    : ConstRegretMatch_Acyclic_Residual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:36:25.846175+00:00
-- url     : https://prove2.me/theorems/33d00aab-0acb-4fc3-8806-e01ce9da6cba
-- title:
--   Definition 5.1, p. 24 — the (SPP)-residual graph and (SPP)-acyclic networks; 𝒰₀ (App. C, p. 44)
-- statement:
--   This file defines the **(SPP)-residual graph**, **(SPP)-acyclicity** and the set $\mathcal U_0$ used in Appendix C.
--
--   Suppose the network satisfies GP and let $(z^*, s^*)$ be the unique optimal solution of (SPP).
--
--   1. **(SPP)-residual graph (Definition 5.1).** It is obtained from the matching network graph $\mathcal G$ by removing every redundant match $m \in \mathcal M_0$ (those with $z^*_m = 0$).
--   2. **(SPP)-acyclic (Definition 5.1).** The network is (SPP)-acyclic if it satisfies GP with witness $(z^*, s^*)$ and the (SPP)-residual graph is acyclic.
--   3. **The set $\mathcal U_0$ (p. 44).**
--   $$\mathcal U_0 := \Big\{ i \in \mathcal Q_0 : \sum_{m\in\mathcal M} M_{im} = 1 \Big\},$$
--   the over-demanded queues that participate in exactly one match.
--
--   (SPP)-acyclicity is the hypothesis under which the paper gives an explicit description of the optimal solution of (SPP) through vectors with entries in $\{-1,0,1\}$.
--
--   **Formalization Note** The removed match vertices are kept as isolated vertices of the residual graph (it is the incidence graph of $\mathcal M_+$ on all of $\mathcal A \sqcup \mathcal M$). Isolated vertices change neither acyclicity, nor the degrees of the type vertices, nor any path between the remaining vertices. Connectedness, where a statement assumes it, is then only meaningful when $\mathcal M_0 = \emptyset$, which is the setting of Appendix C.
-- source:
--   Kerimov, Ashlagi, Gurvich, Dynamic Matching: Characterizing and Achieving Constant Regret, SSRN 3824407 (Sep 14, 2022), p. 24, Definition 5.1; p. 44, App. C (definition of 𝒰₀)

import Mathlib
import Definitions.Def_ConstRegretMatch_Acyclic_Network
import Definitions.Def_ConstRegretMatch_Acyclic_SPP

namespace ConstRegretMatch.Acyclic

variable {n d : ℕ}

/-- The (SPP)-residual graph (Definition 5.1, p. 24): the matching network graph with all redundant
matches `m ∈ ℳ₀` (those with `z_m = 0`) removed. Here the removed match vertices are kept as
isolated vertices, which changes neither acyclicity, nor the degrees of the type vertices, nor the
connections between the remaining vertices. -/
noncomputable def residualGraph (N : MatchingNetwork n d) (z : Fin d → ℝ) : SimpleGraph (Fin n ⊕ Fin d) :=
  incidenceGraph N (ConstRegretMatch.Upper.Mplus z)

/-- (SPP)-acyclic networks (Definition 5.1, p. 24): the network satisfies GP with unique optimal
solution `(z, s)`, and the (SPP)-residual graph is acyclic. -/
def IsSPPAcyclic (N : MatchingNetwork n d) (r : Fin d → ℝ) (lam : Fin n → ℝ) (z : Fin d → ℝ)
    (s : Fin n → ℝ) : Prop :=
  IsGP N r lam z s ∧ (residualGraph N z).IsAcyclic

/-- `𝒰₀ := {i ∈ 𝒬₀ : ∑_{m ∈ ℳ} M_{im} = 1}` (App. C, p. 44): the over-demanded queues that
participate in exactly one match. -/
noncomputable def U0 (N : MatchingNetwork n d) (s : Fin n → ℝ) : Finset (Fin n) :=
  (ConstRegretMatch.Upper.Qzero s).filter (fun i => matchCount N i = 1)

end ConstRegretMatch.Acyclic


