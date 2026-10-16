-- Prove2me | Definitions.Def_SpatialPricing_ABC_Setting
-- name    : SpatialPricing_ABC_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T02:43:02.402103+00:00
-- url     : https://prove2.me/theorems/031e4271-2d2b-4769-ab4b-2cf5bc5e9090
-- title:
--   §3 — spatial pricing system, deterministic relaxation, finite demand paths, and loss
-- statement:
--   A spatial pricing instance has finitely many regions, a finite horizon, a travel time for every ordered pair of regions, an initial server count at each region, and an expected revenue function for each period and trip. Within-region trips are included. The control chooses a demand rate in $[0,1]$; its one-period expected revenue is $r_{t,ij}(\lambda)$.
--
--   The standing conditions require at least one region and period, positive integral travel times, at least $N$ initial servers per region, strong concavity of every $r_{t,ij}$, bounded first and second derivatives, nonnegative revenue, and $r_{t,ij}(0)=0$. Scaling by $n$ multiplies the horizon, travel times, and initial server counts by $n$, and repeats each original period's revenue function for $n$ consecutive periods.
--
--   The deterministic program $\mathrm{DCP}(\zeta)$ maximizes total expected revenue over demand rates satisfying the flow-balance constraints and $\zeta\le\lambda_{t,ij}\le1-\zeta$. Its value is $J(\zeta)$, and a selected optimizer is $\lambda^{\zeta,D}$. A finite binary path records realized demand on every arc and period. The probability of a path is the sequential product of Bernoulli factors at the rates posted on that path; finite sums give probabilities and expectations. The normalized loss compares $J(n,0)$ with expected revenue in the scaled system.
--
--   These definitions provide the common model for the ABC theorem and its milestones.
--
--   **Formalization Note** The rate formulation drops the price-only parts A1 and A3(i). It writes A2 and A3(ii) directly for revenue on $[0,1]$, with a twice continuously differentiable extension to $\mathbb R$. Nonnegative revenue and $r(0)=0$ follow from the paper's positive-price model. Periods are 1-based, natural-number subtraction represents $(\cdot)^+$, and $J(\zeta)$ is used at positive $\zeta$ only with feasibility. The chosen optimizer is zero when no optimum exists; strong concavity makes its values on the horizon unique whenever an optimum exists. The path law is a probability law for nonanticipating controls, including ABC.
-- source:
--   Chen, Lei, Jasin, Real-Time Spatial-Intertemporal Pricing and Relocation in a Ride-Hailing Network: Near Optimal Heuristics and The Value of Dynamic Pricing, author accepted manuscript (LBS Research Online eprint 2845; published in Operations Research 72(5):2097–2118, 2024, doi:10.1287/opre.2022.2425), PDF sha256 7310a8a1…480a, pp. 7–12, A2–A3, (2), (4)–(6), (8), (9)

import Mathlib

noncomputable section

namespace SpatialPricing.ABC

/-- Data of a finite spatial pricing system. Arcs include loops. -/
structure Instance where
  N : ℕ
  T : ℕ
  τ : Fin N → Fin N → ℕ
  C : Fin N → ℕ
  r : ℕ → Fin N → Fin N → ℝ → ℝ

/-- The assumptions on the rate formulation of the paper's model. -/
def Instance.Standing (P : Instance) (Ψ3 : ℝ) : Prop :=
  1 ≤ P.N ∧ 1 ≤ P.T ∧
  (∀ i j, 1 ≤ P.τ i j) ∧
  (∀ i, P.N ≤ P.C i) ∧
  0 < Ψ3 ∧
  ∀ t ∈ Finset.Icc 1 P.T, ∀ i j,
    (∃ m : ℝ, 0 < m ∧ StrongConcaveOn (Set.Icc (0 : ℝ) 1) m (P.r t i j)) ∧
    ContDiff ℝ 2 (P.r t i j) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1,
      |deriv (P.r t i j) x| ≤ Ψ3 ∧
      |deriv (deriv (P.r t i j)) x| ≤ Ψ3 ∧
      0 ≤ P.r t i j x) ∧
    P.r t i j 0 = 0

/-- The smallest travel time, denoted by an underlined tau in the manuscript. -/
def Instance.tauMin (P : Instance) : ℕ :=
  ⨅ p : Fin P.N × Fin P.N, P.τ p.1 p.2

/-- Maximum unconstrained one-period arc revenue. -/
def Instance.rmax (P : Instance) : ℝ :=
  sSup {v : ℝ | ∃ t ∈ Finset.Icc 1 P.T, ∃ i j,
    ∃ x ∈ Set.Icc (0 : ℝ) 1, v = P.r t i j x}

/-- The n-th scaled system of (8). -/
def Instance.scale (P : Instance) (n : ℕ) : Instance where
  N := P.N
  T := n * P.T
  τ := fun i j => n * P.τ i j
  C := fun i => n * P.C i
  r := fun t i j x => P.r ((t + n - 1) / n) i j x

/-- The deterministic flow constraints (5) and cushion constraints (6). -/
def Instance.DCPFeasible (P : Instance) (ζ : ℝ)
    (x : ℕ → Fin P.N → Fin P.N → ℝ) : Prop :=
  (∀ t ∈ Finset.Icc 1 P.T, ∀ i,
    0 ≤ (P.C i : ℝ) -
      ∑ j, ∑ s ∈ Finset.Icc 1 t, x s i j +
      ∑ j, ∑ s ∈ Finset.Icc 1 (t - P.τ j i), x s j i) ∧
  (∀ t ∈ Finset.Icc 1 P.T, ∀ i j,
    ζ ≤ x t i j ∧ x t i j ≤ 1 - ζ)

/-- The objective in (4). -/
def Instance.DCPObj (P : Instance)
    (x : ℕ → Fin P.N → Fin P.N → ℝ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 P.T, ∑ i, ∑ j, P.r t i j (x t i j)

/-- Real-valued DCP objective; theorem statements involving a positive cushion ensure feasibility. -/
def Instance.J (P : Instance) (ζ : ℝ) : ℝ :=
  sSup (P.DCPObj '' {x | P.DCPFeasible ζ x})

def Instance.IsDCPOpt (P : Instance) (ζ : ℝ)
    (x : ℕ → Fin P.N → Fin P.N → ℝ) : Prop :=
  P.DCPFeasible ζ x ∧
  ∀ y, P.DCPFeasible ζ y → P.DCPObj y ≤ P.DCPObj x

/-- A DCP optimum, or the zero schedule if there is no optimum. -/
def Instance.lamD (P : Instance) (ζ : ℝ) :
    ℕ → Fin P.N → Fin P.N → ℝ :=
  by
    classical
    exact if h : ∃ x, P.IsDCPOpt ζ x then Classical.choose h else fun _ _ _ => 0

/-- The finite space of binary demand paths. -/
abbrev Instance.Path (P : Instance) := Fin P.T → Fin P.N → Fin P.N → Bool

/-- Realized demand, zero outside the planning horizon. -/
def Instance.D (P : Instance) (t : ℕ) (ω : P.Path) (i j : Fin P.N) : ℝ :=
  if h : 1 ≤ t ∧ t ≤ P.T then
    if ω ⟨t - 1, by omega⟩ i j then 1 else 0
  else 0

/-- Available servers at the beginning of period t. -/
def Instance.avail (P : Instance) (t : ℕ) (ω : P.Path) (i : Fin P.N) : ℝ :=
  (P.C i : ℝ) -
    (∑ j, ∑ s ∈ Finset.Icc 1 (t - 1), P.D s ω i j) +
    (∑ j, ∑ s ∈ Finset.Icc 1 (t - P.τ j i), P.D s ω j i)

/-- Probability of a path under sequential Bernoulli demands at the posted rates. -/
def Instance.pathProb (P : Instance)
    (ρ : ℕ → P.Path → Fin P.N → Fin P.N → ℝ) (ω : P.Path) : ℝ :=
  ∏ t ∈ Finset.Icc 1 P.T, ∏ i, ∏ j,
    if P.D t ω i j = 1 then ρ t ω i j else 1 - ρ t ω i j

/-- Finite-path expectation. -/
def Instance.E (P : Instance)
    (ρ : ℕ → P.Path → Fin P.N → Fin P.N → ℝ)
    (X : P.Path → ℝ) : ℝ :=
  ∑ ω : P.Path, P.pathProb ρ ω * X ω

/-- Probability of an event in the finite path space. -/
def Instance.prob (P : Instance)
    (ρ : ℕ → P.Path → Fin P.N → Fin P.N → ℝ)
    (S : P.Path → Prop) : ℝ :=
  by
    classical
    exact ∑ ω : P.Path, if S ω then P.pathProb ρ ω else 0

/-- Expected revenue expressed in demand-rate coordinates. -/
def Instance.revenue (P : Instance)
    (ρ : ℕ → P.Path → Fin P.N → Fin P.N → ℝ) : ℝ :=
  P.E ρ (fun ω => ∑ t ∈ Finset.Icc 1 P.T, ∑ i, ∑ j,
    P.r t i j (ρ t ω i j))

/-- Minimum scaled travel time. -/
def Instance.tauN (P : Instance) (n : ℕ) : ℝ := (n : ℝ) * P.tauMin

/-- Scaled horizon length. -/
def Instance.TN (P : Instance) (n : ℕ) : ℝ := (n : ℝ) * P.T

end SpatialPricing.ABC


