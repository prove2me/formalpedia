-- Prove2me | Definitions.Def_SensitivityPoA_Continuity_Setting
-- name    : SensitivityPoA_Continuity_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T17:38:30.082928+00:00
-- url     : https://prove2.me/theorems/2c38b3cb-5047-4117-ab0c-08c2e449ee8e
-- title:
--   §2–§3.2 — congestion game model, flows, costs, game space and distance
-- statement:
--   Fix a finite set of arcs $A$, routes $S$, and origin–destination pairs $K$. Each route serves exactly one pair and is represented by a nonempty $0$–$1$ arc-incidence column. Every arc lies on a route, every pair has at least two routes, and $K$ is nonempty. A game $\Gamma=(\tau,d)$ gives each arc $a$ a continuous, nondecreasing, nonnegative cost function $\tau_a$ on $[0,\infty)$ and each pair $k$ a nonnegative demand $d_k$. Write $T(d)=\sum_k d_k$. The game space requires $T(d)>0$ and $\tau_a(x)>0$ for $0<x\le T(d)$.
--
--   A feasible path flow $f$ routes demand $d_k$ on the paths of each pair. Its arc flow is $f_a=\sum_{s\ni a}f_s$, and its total cost is
--   $$C(\Gamma,f)=\sum_{a\in A}f_a\tau_a(f_a).$$
--   A Wardrop equilibrium uses only minimum-cost routes for each pair; a social optimum minimizes $C$ among feasible flows. The definitions also give the variational form of an $\epsilon$-approximate equilibrium, the potential $\Phi(\Gamma,f)=\sum_a\int_0^{f_a}\tau_a(x)\,dx$, the optimum cost $C^*(\Gamma)$, the equilibrium cost $\widetilde C(\Gamma)$, and $\rho(\Gamma)=\widetilde C(\Gamma)/C^*(\Gamma)$.
--
--   Two games are equivalent when demands and costs on their relevant flow interval agree. Their distance is the maximum of the sup norm of demand differences, the largest cost difference on the shared interval $[0,\min\{T(d),T(d')\}]$, and the sup norm of the cost vectors at their respective total demands. This representation supports the continuity and sensitivity results of the paper.
--
--   **Formalization Note** Routes are arbitrary nonempty $0$–$1$ columns, a disclosed generalization of loop-free graph paths. Cost functions are total real functions whose conditions apply only on $[0,\infty)$. The shared Wardrop definition supplies feasible flows, arc flows, the equilibrium condition, and the potential. The extrema are finite-set extrema on valid games; $C^*$ and $\widetilde C$ use an infimum and supremum over the specified flow sets.
-- source:
--   Wu, Möhring, A sensitivity analysis of the PoA in non-atomic congestion games, arXiv:2007.13979v3 (2021), p. 10–16, §2.1–§3.2, (2.1)–(2.7), Conditions 1–2, (3.1)–(3.3)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop

namespace SensitivityPoA.Continuity

open KellyStochasticNetworks

/-- The fixed finite route-incidence data of a nonatomic congestion game. -/
structure Network where
  J : ℕ
  R : ℕ
  Sd : ℕ
  A : Fin J → Fin R → ℝ
  s : Fin R → Fin Sd

/-- The paper's G1–G2 and standing Condition 1. -/
def Network.Standing (N : Network) : Prop :=
  (∀ j r, N.A j r = 0 ∨ N.A j r = 1) ∧
  (∀ r, ∃ j, N.A j r = 1) ∧
  0 < N.Sd ∧
  (∀ j, ∃ r, N.A j r = 1) ∧
  ∀ k, 2 ≤ (Finset.univ.filter (fun r => N.s r = k)).card

/-- A latency vector and a demand vector on the fixed network. -/
structure Game (N : Network) where
  τ : Fin N.J → ℝ → ℝ
  d : Fin N.Sd → ℝ

def totalDemand {N : Network} (d : Fin N.Sd → ℝ) : ℝ := ∑ k, d k

def IsCostFn (h : ℝ → ℝ) : Prop :=
  ContinuousOn h (Set.Ici 0) ∧ MonotoneOn h (Set.Ici 0) ∧
  ∀ x, 0 ≤ x → 0 ≤ h x

def Game.IsGeneralized {N : Network} (Γ : Game N) : Prop :=
  (∀ j, IsCostFn (Γ.τ j)) ∧ ∀ k, 0 ≤ Γ.d k

def Game.Condition2 {N : Network} (Γ : Game N) : Prop :=
  0 < totalDemand Γ.d ∧
  ∀ j x, 0 < x → x ≤ totalDemand Γ.d → 0 < Γ.τ j x

def gameSpace (N : Network) : Set (Game N) :=
  {Γ | Γ.IsGeneralized ∧ Γ.Condition2}

def IsFlow {N : Network} (Γ : Game N) (f : Fin N.R → ℝ) : Prop :=
  f ∈ wardropFeasible N.s Γ.d

def pathCost {N : Network} (Γ : Game N) (f : Fin N.R → ℝ)
    (r : Fin N.R) : ℝ :=
  ∑ j, Γ.τ j (linkFlow N.A f j) * N.A j r

noncomputable def minPathCost {N : Network} (Γ : Game N)
    (f : Fin N.R → ℝ) (k : Fin N.Sd) : ℝ :=
  sInf (pathCost Γ f '' {r | N.s r = k})

def cost {N : Network} (Γ : Game N) (f : Fin N.R → ℝ) : ℝ :=
  ∑ j, linkFlow N.A f j * Γ.τ j (linkFlow N.A f j)

def IsWE {N : Network} (Γ : Game N) (f : Fin N.R → ℝ) : Prop :=
  IsWardropEquilibrium N.A N.s Γ.τ Γ.d f

def IsSO {N : Network} (Γ : Game N) (f : Fin N.R → ℝ) : Prop :=
  IsFlow Γ f ∧ ∀ g, IsFlow Γ g → cost Γ f ≤ cost Γ g

def IsApproxWE {N : Network} (Γ : Game N) (ε : ℝ)
    (f : Fin N.R → ℝ) : Prop :=
  IsFlow Γ f ∧ ∀ g, IsFlow Γ g →
    (∑ j, Γ.τ j (linkFlow N.A f j) *
      (linkFlow N.A f j - linkFlow N.A g j)) ≤ ε

noncomputable def potential {N : Network} (Γ : Game N)
    (f : Fin N.R → ℝ) : ℝ :=
  wardropObjective N.A Γ.τ f

noncomputable def SOCost {N : Network} (Γ : Game N) : ℝ :=
  sInf (cost Γ '' {f | IsFlow Γ f})

noncomputable def WECost {N : Network} (Γ : Game N) : ℝ :=
  sSup (cost Γ '' {f | IsWE Γ f})

noncomputable def PoA {N : Network} (Γ : Game N) : ℝ :=
  WECost Γ / SOCost Γ

def Game.Equiv {N : Network} (Γ Γ' : Game N) : Prop :=
  Γ.d = Γ'.d ∧
  ∀ j, ∀ x ∈ Set.Icc 0 (totalDemand Γ.d), Γ.τ j x = Γ'.τ j x

noncomputable def gameDist {N : Network} (Γ Γ' : Game N) : ℝ :=
  max ‖Γ.d - Γ'.d‖
    (max
      (sSup ((fun p : Fin N.J × ℝ => |Γ.τ p.1 p.2 - Γ'.τ p.1 p.2|) ''
        (Set.univ ×ˢ Set.Icc 0 (min (totalDemand Γ.d) (totalDemand Γ'.d)))))
      ‖(fun j => Γ.τ j (totalDemand Γ.d) -
        Γ'.τ j (totalDemand Γ'.d))‖)

def LipOnIcc (h : ℝ → ℝ) (T M : ℝ) : Prop :=
  ∀ x ∈ Set.Icc 0 T, ∀ y ∈ Set.Icc 0 T,
    |h x - h y| ≤ M * |x - y|

noncomputable def minArc {N : Network} (Γ : Game N) (x : ℝ) : ℝ :=
  sInf (Set.range (fun j : Fin N.J => Γ.τ j x))

noncomputable def maxArc {N : Network} (Γ : Game N) (x : ℝ) : ℝ :=
  sSup (Set.range (fun j : Fin N.J => Γ.τ j x))

end SensitivityPoA.Continuity


