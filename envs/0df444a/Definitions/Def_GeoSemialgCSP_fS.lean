-- Prove2me | Definitions.Def_GeoSemialgCSP_fS
-- name    : GeoSemialgCSP_fS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:48:39.44595+00:00
-- url     : https://prove2.me/theorems/1bb2b770-d9f3-47a7-afb5-7696db9a7516
-- title:
--   The predicate on a finite output support
-- statement:
--   A **fractional solution** assigns to each variable a finitely supported distribution on $X$; all of them live on one finite set $\{x_1,\dots,x_n\}\subseteq X$, so $\xi$ is a map into $\mathcal P_n$. Its value on a template $I$,
--   $$\mathrm{val}(\xi,I_P)=\mathbb E_{(z_1,\dots,z_k)\sim I}\ \mathbb E_{X_j\sim\xi(z_j)}P(X_1,\dots,X_k),$$
--   is the value of the finite payoff $(i_1,\dots,i_k)\mapsto P(x_{i_1},\dots,x_{i_k})$ on $[n]^k$ at $\xi$, through the multilinear extension. This definition is that payoff.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §4.4, p.12 (PDF p.13)

import Mathlib
import Definitions.Def_GeoSemialgCSP_E

namespace GeoSemialgCSP

/-- **The predicate on a finite output support.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §4.4, printed p.12 (PDF p.13): a
fractional solution `ξ` assigns to each variable a distribution on one finite set
`{x₁, …, x_n} ⊆ X`, i.e. a vector in `P_n`; its value is the multilinear extension of
`(i₁, …, i_k) ↦ P(x_{i₁}, …, x_{i_k})`. -/
noncomputable def fS {k d n : ℕ} (S : Set (Fin k → E d)) (x : Fin n → E d) :
    (Fin k → Fin n) → ℝ :=
  fun a => S.indicator 1 (x ∘ a)

end GeoSemialgCSP


