-- Prove2me | Definitions.Def_MilnorDynamics_Linearization
-- name    : MilnorDynamics_Linearization
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-26T10:40:26.583974+00:00
-- url     : https://prove2.me/theorems/4bb7617f-6329-4854-97d5-f9cfb3ef75ec
-- title:
--   Local linearizability of germs and of maps of the sphere; Diophantine numbers of order κ (Milnor §11)
-- statement:
--   Notions from Milnor's §11 (*Cremer Points and Siegel Disks*).
--
--   1. A holomorphic germ $f$ with $f(0)=0$ is **locally linearizable** with multiplier $\lambda$ if there is a local holomorphic change of coordinate $z=h(w)$, $h(0)=0$, with $f(h(w))=h(\lambda w)$ near $0$.
--   2. The same notion for a self-map $g$ of the Riemann sphere $\hat{\mathbb C}$ at a fixed point $z_0$: a holomorphic injective $h$ from a disk around $0$ into $\hat{\mathbb C}$ with $h(0)=z_0$ and $g(h(w))=h(\lambda w)$.
--   3. An irrational real number $\xi$ is **Diophantine of order $\le\kappa$**, $\xi\in\mathcal D(\kappa)$, if there is $\varepsilon>0$ with $|\xi-p/q|>\varepsilon/q^{\kappa}$ for every rational $p/q$ (equation (11:1), p. 129).
--
--   **Formalization Note** The linearizing coordinate is always parametrized by a round disk $\{|w|<r\}$; this is equivalent to the book's "local change of coordinate'' because the conjugacy is only required near the fixed point.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, ISBN 978-0-691-12488-9, §11, pp. 125–129 (local linearization; Diophantine condition (11:1))

import Mathlib
import Definitions.Def_MilnorDynamics_RationalMaps

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

/-- A holomorphic germ `f` fixing `0` is locally linearizable at `0` with multiplier `μ`:
there is a holomorphic, injective change of coordinate `h` on a disk around `0`, with
`h 0 = 0`, such that `f (h w) = h (μ * w)` on that disk. -/
def IsLocallyLinearizable (f : ℂ → ℂ) (μ : ℂ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.ball 0 r) ∧
    InjOn h (Metric.ball 0 r) ∧ h 0 = 0 ∧ ∀ w ∈ Metric.ball (0 : ℂ) r, f (h w) = h (μ * w)

/-- A self-map `g` of the Riemann sphere is locally linearizable at `p` with multiplier `μ`:
there is a holomorphic, injective map `h` from a disk around `0` into the sphere, with
`h 0 = p`, such that `g (h w) = h (μ * w)` on that disk. -/
def IsLinearizableAt (g : OnePoint ℂ → OnePoint ℂ) (p : OnePoint ℂ) (μ : ℂ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ h : ℂ → OnePoint ℂ, IsHolomorphicOn (Metric.ball 0 r) h ∧
    InjOn h (Metric.ball 0 r) ∧ h 0 = p ∧ ∀ w ∈ Metric.ball (0 : ℂ) r, g (h w) = h (μ * w)

/-- The real number `ξ` is Diophantine of order `≤ κ`: it is irrational and there is `ε > 0`
with `|ξ - p/q| > ε / q^κ` for every rational number `p/q` (`q > 0`). -/
def IsDiophantineOfOrder (ξ : ℝ) (κ : ℝ) : Prop :=
  Irrational ξ ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ p : ℤ, ∀ q : ℕ, 0 < q →
    ε / (q : ℝ) ^ κ < |ξ - (p : ℝ) / (q : ℝ)|

end MilnorDynamics


