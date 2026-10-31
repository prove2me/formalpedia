-- Prove2me | Definitions.Def_HellmanLevy_Bayes_assocPayoff
-- name    : HellmanLevy_Bayes_assocPayoff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:57:06.502523+00:00
-- url     : https://prove2.me/theorems/cbe104f5-eeca-42bd-8da9-80c070f3ccb0
-- title:
--   Payoff $u_T$ of the associated graphical game
-- statement:
--   Let all players share the finite action set $A$. A pure profile of the associated graphical game assigns an action $a(\tau)$ to every type $\tau\in\Omega_T$. The payoff of the vertex $\tau\in T^i$ is player $i$'s conditional payoff given $\tau$ when, at each state $\omega$, every player $j$ plays the action of its type $t^j(\omega)$:
--   $$u_T(\tau,a)=\int_\Omega r^i\big(\omega,(a(t^j(\omega)))_{j\in I}\big)\,d\tau(\omega).$$
--   Its multilinear (product-measure) extension is $u_T(\tau,\sigma)=r^i(\sigma\mid\tau)$ for the induced Bayesian profile.
-- source:
--   Hellman–Levy, Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence Relation Hierarchy, author's manuscript (2020-07-14), §4.2, p.20; eq. (3.1), p.13

import Mathlib
import Definitions.Def_HellmanLevy_Bayes_typeOf

namespace HellmanLevy.Bayes

/-- The **payoff `u_T` of the associated graphical game** (common action set `A`): the vertex
`τ ∈ Tⁱ` receives player `i`'s conditional payoff given the type `τ`. On a pure profile
`a : Ω_T → A` (each type of each player chooses an action) this is
`u_T(τ, a) = ∫ rⁱ(ω, (a(tʲ(ω)))ⱼ) dτ(ω)`: at state `ω` player `j` plays the action chosen by
its type `tʲ(ω)`.
Hellman–Levy, *Equilibria Existence in Bayesian Games: Climbing the Countable Borel Equivalence
Relation Hierarchy*, author's manuscript (2020-07-14), §4.2, p.20 ("uT(τi, σ) = ri(σ | τi)", with (3.1), p.13; "for simplicity, assume all
the players share the same action space").

**Formalization Note** The mixed extension of this pure-profile payoff (`mixedPayoffG`) is
`rⁱ(σ | τ)` for the induced Bayesian profile, because the vertices `tʲ(ω)`, `j ∈ I`, are
distinct. As in (3.1) the sum over the class of `τ` is written as an integral against `τ`. -/
noncomputable def assocPayoff {Ω : Type*} [MeasurableSpace Ω] {I : Type*} {A : Type*}
    (B : BayesianGame Ω I fun _ => A) (τ : TypeSpace B) (a : TypeSpace B → A) : ℝ :=
  ∫ ω, B.r τ.1 ω (fun j => a (typeOf B j ω)) ∂(τ.2 : MeasureTheory.Measure Ω)

end HellmanLevy.Bayes


