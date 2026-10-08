-- Prove2me | Definitions.Def_YoungConventions_RiskDominance_stochasticPotential
-- name    : YoungConventions_RiskDominance_stochasticPotential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T18:03:49.473167+00:00
-- url     : https://prove2.me/theorems/6ed34629-900f-411c-9dae-de377f6b6806
-- title:
--   Stochastic potential $\gamma_i$, displays (3)–(4)
-- statement:
--   Let $H_1,\dots,H_J$ be the recurrent communication classes of $P^0$ and let $\mathcal G$ be the complete directed graph on these classes in which the edge $(i,j)$ has resistance $r_{ij}$. The **resistance of an $i$-tree** $\tau$ is the sum of the resistances of its edges,
--   $$r(\tau)=\sum_{(i,j)\in\tau}r_{ij},$$
--   and the **stochastic potential** of the class $H_i$ is the least resistance among all $i$-trees:
--   $$\gamma_i=\min_{\tau\in\mathcal T_i}r(\tau).$$
--
--   Theorem 2 identifies the stochastically stable states with the classes of minimum stochastic potential.
--
--   **Formalization Note** The vertices are the classes themselves (sets of states). The minimum is the infimum on $\mathbb N$ of a nonempty set (the star tree is always an $i$-tree). The value is computed from mistake counts only, so it does not depend on $\lambda$ or $q$, and it depends on $p$ only through the classes of $P^0$, which are the same for every best-reply distribution.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §6, p. 69, displays (3)–(4)

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_History
import Definitions.Def_YoungConventions_RiskDominance_unperturbed
import Definitions.Def_YoungConventions_RiskDominance_recurrentClasses
import Definitions.Def_YoungConventions_RiskDominance_classResistance
import Definitions.Def_YoungConventions_RiskDominance_IsInTree

open Classical

namespace YoungConventions.RiskDominance

/-- **Stochastic potential** `γᵢ`, displays (3)–(4). Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §6, p. 69 (PDF p. 14): "define a new
directed graph `𝒢` as follows: there is one vertex `i` for each recurrent communication class `Hᵢ`,
and for every distinct `1 ≤ i, j ≤ J` the directed edge `(i, j)` has weight or resistance `r_ij`."
"The resistance of an `i`-tree `τ` is the sum of the resistances of its edges,
`r(τ) = ∑_{(i,j)∈τ} r_ij`." "The stochastic potential of the recurrent class `Hᵢ` is the least
resistance among all `i`-trees: `γᵢ = min_{τ∈𝒯ᵢ} r(τ)`."

`stochasticPotential u k p C` is the least resistance of an in-tree rooted at `C` on the vertex set
of recurrent communication classes of `P⁰ = unperturbed p`, with edge weights `classResistance`.

**Formalization Note.** Vertices are the classes themselves (sets of states). The minimum is `sInf`
on `ℕ`; the set is nonempty whenever `C` is a recurrent class (the star tree with every parent equal
to `C` is an in-tree). The value depends on `p` only through the classes of `P⁰`, which are the same
for every best-reply distribution (the support of `p` is fixed). -/
noncomputable def stochasticPotential {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] {m : ℕ} [NeZero m]
    (u : ι → ((i : ι) → S i) → ℝ) (k : ℕ) (p : (i : ι) → YoungConventions.AdaptivePlay.History S m → S i → ℝ)
    (C : Set (YoungConventions.AdaptivePlay.History S m)) : ℕ :=
  let V := (Set.toFinite (recurrentClasses (unperturbed p))).toFinset
  sInf {x : ℕ | ∃ par : Set (YoungConventions.AdaptivePlay.History S m) → Set (YoungConventions.AdaptivePlay.History S m), IsInTree V C par ∧
    x = ∑ D ∈ V.erase C, classResistance u k D (par D)}

end YoungConventions.RiskDominance


