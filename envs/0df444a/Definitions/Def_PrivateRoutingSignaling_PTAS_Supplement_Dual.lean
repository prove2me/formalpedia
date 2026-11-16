-- Prove2me | Definitions.Def_PrivateRoutingSignaling_PTAS_Supplement_Dual
-- name    : PrivateRoutingSignaling_PTAS_Supplement_Dual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:42:09.782198+00:00
-- url     : https://prove2.me/theorems/d1d7b78a-9cfe-4093-91c8-46ffa4bf07dd
-- title:
--   Statewise dual function $D^\theta(y)$, $\ell^1$ distance, maximum row sum and the continuous setting
-- statement:
--   Let a routing network have the set $P$ of simple source–sink paths, and let one state of nature have arc latency functions $c_i$. For a flow $s\in\Delta_P$ write $c_p(s)=\sum_{i\in p}c_i(x_i(s))$ for the path latency at the arc loads $x_i(s)=\sum_{p\ni i}s_p$. A **dual matrix** is a family $y=(y_{p,q})_{p\neq q}$ of reals indexed by ordered pairs of distinct paths; it is **nonnegative** when every $y_{p,q}\ge0$. The statewise dual function of §2.2 is
--
--   $$
--   D(y,s)=\sum_{p\in P}s_pc_p(s)-\sum_{p\neq q}y_{p,q}\,s_p\bigl[c_q(s)-c_p(s)\bigr],\qquad D(y)=\inf_{s\in\Delta_P}D(y,s),
--   $$
--
--   the infimum running over all real unit-demand flows. For an instance, $D^\theta$ uses the latencies of state $\theta$. The **entrywise $\ell^1$ distance** of two dual matrices is $\|y-y'\|_1=\sum_{p\neq q}|y_{p,q}-y'_{p,q}|$, and the **maximum row sum** is $\max_{p\in P}\sum_{q\neq p}y_{p,q}$.
--
--   The **continuous setting** collects the standing assumptions of §2.1 without any Lipschitz bound: a valid network with at least one path, a nonempty finite set of states with a probability prior, and arc latencies that are nonnegative, nondecreasing and continuous on $[0,1]$. A function on $[0,1]$ has **at most three linear pieces** if there are breakpoints $0\le t_1\le t_2\le1$ such that it is affine on $[0,t_1]$, on $[t_1,t_2]$ and on $[t_2,1]$.
--
--   These objects state the relaxed-IC dual bound (Lemma 2.1), the optimum bounds of the three hardness constructions, and the smoothing bounds of Remark 6.6.
--
--   **Formalization Note** Diagonal entries of a dual matrix are never read: every sum ranges over $q\neq p$. $D(y)$ is a real infimum over the subtype of flows; on every instance of this mission the latencies are bounded on $[0,1]$, so the set of values is bounded below and nonempty. The latencies enter through the published path-latency and cost functions, exactly as in the base mission's `pathCost` and `flowCost`.
-- source:
--   Yu Cheng, Tianle Jiang, The Complexity of Private Signaling in Nonatomic Routing Games, STOC 2027 submission #439 (October 2026), §2.1 p. 5, §2.2 p. 7 (definition of D^θ(y,s), D^θ(y), ‖y−y′‖₁), Lemma 2.1 p. 8, Remark 6.6 p. 37; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/439.pdf; SHA-256 766b4afa05d6c7c4c106ed83a73221ca4d951eeca5cce863930177ed26fd4e61

import Mathlib
import Definitions.Def_PrivateRoutingSignaling_PTAS_Signaling

set_option autoImplicit false
open scoped BigOperators

namespace PrivateRoutingSignaling.PTAS.Supplement

open PrivateRoutingSignaling.PTAS

/-- A dual matrix `y = (y_{p,q})_{p ≠ q}` indexed by the paths of a network. Diagonal entries are
never read: every sum below ranges over `q ≠ p` only (§2.2, p. 7, dummy zero diagonal). -/
abbrev DualMatrix (N : RoutingNetwork) := Path N → Path N → ℝ

/-- `y ≥ 0`: every off-diagonal dual variable is nonnegative. -/
def DualNonneg {N : RoutingNetwork} (y : DualMatrix N) : Prop :=
  ∀ p q, p ≠ q → 0 ≤ y p q

/-- `D(y, s)` of §2.2, p. 7, for one state's arc latency functions `c`:
`∑_p s_p c_p(s) − ∑_{p ≠ q} y_{p,q} s_p (c_q(s) − c_p(s))`. -/
def dualFlowValueL (N : RoutingNetwork) (c : Fin N.arcs → ℝ → ℝ) (y : DualMatrix N)
    (s : Path N → ℝ) : ℝ :=
  SelfishRouting.Bicriteria.cost (incidence N) c s -
    ∑ p, ∑ q ∈ Finset.univ.erase p,
      y p q * s p * (SelfishRouting.Bicriteria.pathLatency (incidence N) c s q -
        SelfishRouting.Bicriteria.pathLatency (incidence N) c s p)

/-- `D(y) = inf_{s ∈ Δ_P} D(y, s)` (§2.2, p. 7), an infimum over all real unit-demand flows.
This is the infimum convention of §6.2 (p. 33); for continuous latencies it is a minimum. -/
noncomputable def dualValueL (N : RoutingNetwork) (c : Fin N.arcs → ℝ → ℝ) (y : DualMatrix N) : ℝ :=
  ⨅ s : Flow N, dualFlowValueL N c y s.val

/-- `D^θ(y, s)` for state `θ` of an instance (§2.2, p. 7). -/
def dualFlowValue (I : Instance) (θ : Fin I.states) (y : DualMatrix I.network)
    (s : Path I.network → ℝ) : ℝ :=
  dualFlowValueL I.network (I.latency θ) y s

/-- `D^θ(y) = inf_{s ∈ Δ_P} D^θ(y, s)` (§2.2, p. 7). -/
noncomputable def dualValue (I : Instance) (θ : Fin I.states) (y : DualMatrix I.network) : ℝ :=
  dualValueL I.network (I.latency θ) y

/-- The entrywise ℓ¹ distance `‖y − y'‖₁ = ∑_{p ≠ q} |y_{p,q} − y'_{p,q}|` (§2.2, p. 7). -/
def l1Dist {N : RoutingNetwork} (y y' : DualMatrix N) : ℝ :=
  ∑ p, ∑ q ∈ Finset.univ.erase p, |y p q - y' p q|

/-- The largest off-diagonal row sum `max_{p ∈ P} ∑_{q ≠ p} y_{p,q}` (Lemma 2.1, p. 8). -/
noncomputable def maxRowSum {N : RoutingNetwork} (y : DualMatrix N) : ℝ :=
  ⨆ p : Path N, ∑ q ∈ Finset.univ.erase p, y p q

/-- The standing assumptions of §2.1 (p. 5) without any Lipschitz bound: a valid network, a
nonempty finite state set with a probability prior, and arc latencies that are nonnegative,
nondecreasing and continuous on the relevant range `[0,1]`. -/
def ContinuousSetting (I : Instance) : Prop :=
  NetworkValid I.network ∧ 0 < I.states ∧ FiniteLaw I.prior ∧
  ∀ θ i, (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ I.latency θ i x) ∧
    MonotoneOn (I.latency θ i) (Set.Icc 0 1) ∧
    ContinuousOn (I.latency θ i) (Set.Icc 0 1)

/-- A real function on `[0,1]` that is piecewise linear with at most three linear pieces: there are
breakpoints `0 ≤ t₁ ≤ t₂ ≤ 1` such that it is affine on `[0,t₁]`, on `[t₁,t₂]` and on `[t₂,1]`
(a piece may be degenerate). -/
def AtMostThreePieces (f : ℝ → ℝ) : Prop :=
  ∃ t₁ t₂ : ℝ, 0 ≤ t₁ ∧ t₁ ≤ t₂ ∧ t₂ ≤ 1 ∧
    (∃ a b : ℝ, ∀ x ∈ Set.Icc 0 t₁, f x = a * x + b) ∧
    (∃ a b : ℝ, ∀ x ∈ Set.Icc t₁ t₂, f x = a * x + b) ∧
    (∃ a b : ℝ, ∀ x ∈ Set.Icc t₂ 1, f x = a * x + b)

end PrivateRoutingSignaling.PTAS.Supplement


