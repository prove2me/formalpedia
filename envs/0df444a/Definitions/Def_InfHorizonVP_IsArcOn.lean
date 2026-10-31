-- Prove2me | Definitions.Def_InfHorizonVP_IsArcOn
-- name    : InfHorizonVP_IsArcOn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:20.144916+00:00
-- url     : https://prove2.me/theorems/9720468e-0c91-4d38-a6d8-18eeed2274ef
-- title:
--   Arc on $[a,b]$: the Sobolev space $W^{1,1}([a,b],E)$
-- statement:
--   Let $E$ be a real normed space and $a\le b$. A function $x:[a,b]\to E$ is an **arc** on $[a,b]$, i.e. belongs to $W^{1,1}([a,b],E)$, if
--
--   1. its strong derivative $\dot x(s)=\lim_{h\to0}(x(s+h)-x(s))/h$ exists for almost every $s\in(a,b)$;
--   2. $\dot x$ is Bochner integrable on $[a,b]$;
--   3. $x(s)=x(a)+\int_a^s\dot x(\tau)\,d\tau$ for every $s\in[a,b]$.
--
--   Arcs are the trajectories of the differential inclusions of the paper: every admissible trajectory is an arc on each bounded interval, and Lemmas B.1 and B.2 produce arcs on compact intervals.
--
--   **Formalization Note** Functions on an interval are functions $\mathbb R\to E$ whose values outside the interval are ignored; $\dot x$ is `deriv x`.
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, §3.1, p.7

import Mathlib
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Arc on a compact interval: the Sobolev space `W^{1,1}([a, b], E)`.**
Frankowska, Sagara, arXiv:1801.00400v3, §3.1, p.7: "Denote by W^{1,1}_loc(R+, E) the Sobolev
space, which consists of locally Bochner integrable functions x : R+ → E whose strong derivative
ẋ(t) exists a.e. … with ẋ(·) ∈ L¹_loc(R+, E) and x(t) = ∫_0^t ẋ(s)ds + x(0) … When R+ is replaced
by a compact interval I of R+, the above definition simply leads to that of the Sobolev space
W^{1,1}(I, E)".

`IsArcOn x a b` says that the restriction of `x` to `[a, b]` lies in `W^{1,1}([a, b], E)`: `x` is
strongly differentiable at almost every point of `(a, b)`, its strong derivative is Bochner
integrable on `[a, b]`, and `x(s) = x(a) + ∫_a^s ẋ(τ) dτ` for every `s ∈ [a, b]`.

**Formalization Note.** Functions on an interval are functions `ℝ → E` whose values outside the
interval are ignored. The strong derivative `ẋ(s)` is `deriv x s` (two-sided, at interior points);
where `x` is not differentiable `deriv` returns `0`, which only happens on a null set. Local Bochner
integrability of `x` itself follows from the integral representation (it makes `x` continuous on
`[a, b]`). -/
def IsArcOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : ℝ → E) (a b : ℝ) : Prop :=
  (∀ᵐ s ∂(volume.restrict (Ioo a b)), DifferentiableAt ℝ x s) ∧
  IntegrableOn (deriv x) (Icc a b) ∧
  ∀ s ∈ Icc a b, x s = x a + ∫ τ in a..s, deriv x τ

end InfHorizonVP


