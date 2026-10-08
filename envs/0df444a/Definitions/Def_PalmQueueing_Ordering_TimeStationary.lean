-- Prove2me | Definitions.Def_PalmQueueing_Ordering_TimeStationary
-- name    : PalmQueueing_Ordering_TimeStationary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T03:51:52.769994+00:00
-- url     : https://prove2.me/theorems/a4d7ebec-9258-470d-b24d-07aed80193de
-- title:
--   The S-orders for time-stationary queues
-- statement:
--   §4.4 compares **time-stationary** queues, and its point is that a stochastic order
--   between Palm distributions does not by itself give one between the stationary distributions.
--   Example 4.4.1, "Feller's paradox revisited", exhibits $N$ Poisson of intensity $1$ and $\widetilde
--   N$ renewal with inter-arrival c.d.f. that of $X \vee u$ for $X$ exponential: then
--   $T_1[P^0] \le_i \widetilde T_1[\widetilde P^0]$, and yet
--   $E_{\widetilde P}[\widetilde T_1] < E_P[T_1] = 1$ for $u$ in an interval, so
--   $T_1[P] \le_i \widetilde T_1[\widetilde P]$ fails.
--
--   What survives is a family of orders built from the Palm distributions with the **mean cycle
--   length divided out**. For $\mathcal{L}$ a set of functions on $\mathbb{R}^{n+1}$, $\{I\text{-}\mathcal{L}\}$
--   (p.300, (4.4.4)) is the set of functions $\phi : \mathbb{R}^{n+1}\to\mathbb{R}$ which admit an
--   integral representation
--   $$ \phi(t,x_1,\dots,x_n) = \int_0^t f(u,x_1,\dots,x_n)\,du $$
--   for some locally integrable mapping $f$ in $\mathcal{L}$. The partial semi-order
--   $\le_{S\text{-}\mathcal{L}}$ on $\mathcal{D}(\mathbb{R}^{n+1})$ (p.302) is defined by
--   $F^0 \le_{S\text{-}\mathcal{L}} \widetilde F^0$ if, for all $\phi$ in $\{I\text{-}\mathcal{L}\}$,
--   $$ \frac{\int_{\mathbb{R}^{n+1}}\phi(t,x)F^0(dt,dx)}{\int_{\mathbb{R}} t F^0_T(dt)}
--   \le \frac{\int_{\mathbb{R}^{n+1}}\phi(t,x)\widetilde F^0(dt,dx)}{\int_{\mathbb{R}} t
--   \widetilde F^0_T(dt)} . $$
--   $\le_{S\text{-}i}$ is the case $\mathcal{L} = \{i\}$, the non-decreasing functions.
--
--   "Unlike the integral orders defined in §4.2, $\le_{S\text{-}\mathcal{L}}$ does not apply to all
--   distributions, but only to those of the form $(T,X)[P^0]$ ... In particular, $T[P^0]$ should have
--   its support on $\mathbb{R}_{+,*}$ and have a finite first moment." That restriction is the
--   predicate `SOrderDomain`, a hypothesis of the theorems that use the order.
--
--   **Formalization Note.** The first coordinate of $\mathbb{R}^{n+1}$ is $t$. Local integrability of
--   $f$ is required in $u$ for each fixed $x$, which is what makes the defining integral meaningful;
--   test integrals are taken over functions integrable under both distributions.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, §4.4, pp. 295-302

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess
import Definitions.Def_PalmQueueing_Ordering_IntegralOrders

/-!
# The `S`-orders of §4.4 (pp.295-302)

§4.4 compares **time-stationary** queues, and the point of the section is that the stochastic
order between two Palm distributions does not by itself give the order between the corresponding
stationary ones. Example 4.4.1 — "Feller's paradox revisited" — exhibits two point processes with
`T_n[P⁰] ≤_i T̃_n[P̃⁰]` for all `n` and yet not `T_n[P] ≤_i T̃_n[P̃]`.

What survives is a family of orders built from the Palm distributions with the mean cycle length
divided out. That is `≤_{S-ℒ}`.
-/

namespace PalmQueueing.Ordering

open MeasureTheory
open PalmQueueing.Palm

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `{I-ℒ}` (p.300, (4.4.4)): the functions `φ : ℝ^{n+1} → ℝ` which admit an integral
representation

`φ(t, x₁, …, xₙ) = ∫_0^t f(u, x₁, …, xₙ) du`

for some locally integrable mapping `f` in `ℒ`. The first coordinate of `ℝ^{n+1}` is `t`;
local integrability is required in `u` for every fixed `x`, which is what makes the integral
defined. -/
def classIL {n : ℕ} (L : Set ((Fin (n + 1) → ℝ) → ℝ)) : Set ((Fin (n + 1) → ℝ) → ℝ) :=
  {phi | ∃ f ∈ L,
    (∀ x : Fin n → ℝ, LocallyIntegrable (fun u : ℝ => f (Fin.cons u x))) ∧
    ∀ z : Fin (n + 1) → ℝ, phi z = ∫ u in (0 : ℝ)..(z 0), f (Fin.cons u (Fin.tail z))}

/-- The partial semi-order `≤_{S-ℒ}` on `𝒟(ℝ^{n+1})` (p.302). For distributions of the form
`(T, X)[P⁰]`, `F⁰ ≤_{S-ℒ} F̃⁰` if, for all `φ` in `I-ℒ`,

`( ∫ φ(t,x) F⁰(dt,dx) ) / ( ∫ t F⁰_T(dt) )  ≤  ( ∫ φ(t,x) F̃⁰(dt,dx) ) / ( ∫ t F̃⁰_T(dt) )`.

Each side is a Palm integral **normalised by the mean cycle length**, which is what corrects for
the length-biasing that produces Feller's paradox. The book is explicit that, unlike the integral
orders of §4.2, "`≤_{S-ℒ}` does not apply to all distributions, but only to those of the form
`(T, X)[P⁰]`; in particular `T[P⁰]` should have its support on `ℝ₊,*` and have a finite first
moment"; that restriction is `SOrderDomain`, a hypothesis of the theorems.

The test functions are those of `{I-ℒ}` (`classIL`), not `ℒ` itself; the first coordinate `z 0`
of `ℝ^{n+1}` is `t`. -/
def SLe {n : ℕ} (L : Set ((Fin (n + 1) → ℝ) → ℝ)) (F0 F0' : Measure (Fin (n + 1) → ℝ)) : Prop :=
  ∀ phi ∈ classIL L, Integrable phi F0 → Integrable phi F0' →
    (∫ z, phi z ∂F0) / (∫ z, z 0 ∂F0) ≤ (∫ z, phi z ∂F0') / ∫ z, z 0 ∂F0'

/-- `F⁰ ≤_{S-i} F̃⁰`, the `S`-order generated by the non-decreasing functions. -/
def SILe {n : ℕ} (F0 F0' : Measure (Fin (n + 1) → ℝ)) : Prop := SLe (classI (n + 1)) F0 F0'

/-- The support restriction the `S`-orders require (p.302): `T[P⁰]` is carried by `ℝ₊,*` and has a
finite first moment. -/
def SOrderDomain {n : ℕ} (F0 : Measure (Fin (n + 1) → ℝ)) : Prop :=
  IsProbabilityMeasure F0 ∧
  F0 {z : Fin (n + 1) → ℝ | z 0 ≤ 0} = 0 ∧
  Integrable (fun z : Fin (n + 1) → ℝ => z 0) F0

end PalmQueueing.Ordering


