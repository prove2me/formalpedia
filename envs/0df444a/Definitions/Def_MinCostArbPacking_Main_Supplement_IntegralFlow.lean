-- Prove2me | Definitions.Def_MinCostArbPacking_Main_Supplement_IntegralFlow
-- name    : MinCostArbPacking_Main_Supplement_IntegralFlow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:46:07.625204+00:00
-- url     : https://prove2.me/theorems/963e43fb-d3ab-41f9-a672-d484dbe8113e
-- title:
--   Integral minimum-cost maximum flow with an executed-program runtime contract
-- statement:
--   A finite network consists of a directed multigraph, distinct source s and sink t, nonnegative integer capacities u(e), and integer costs c(e). An integral flow f satisfies 0≤f(e)≤u(e) and conservation away from s,t. Its value is net outgoing flow at s. The required output maximizes that value, then minimizes
--
--   $$\sum_e c(e)f(e)$$
--
--   among all integral flows of the maximum value, including flows containing cycles. One output integer per arc encodes the flow. The input consists only of the dimensions, terminals, endpoint arrays, capacities and costs; real input is empty.
--
--   For a fixed degree d≥1, capacities and absolute costs are at most (N+M+2)^d. MCF(N,M) is a monotone worst-case envelope at least N+M+1 for a fixed correct deterministic program Q. Its contract requires actual halting of Q in the published interpreter within MCF steps, for every sufficiently large polynomial word bound. This is a precise interpretation of the source's flow-runtime parameter, with no extra instruction or uncharged flow oracle. The reduction needs only degree one because all its integer costs and capacities are at most the current edge count.
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), Theorem 1.2, flow-time convention and §6.2.2, p. 2,28,31–32

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_Graph
import Definitions.Def_MinCostArbPacking_Main_Machine
set_option autoImplicit false
noncomputable section
open Classical

namespace MinCostArbPacking.Main.Supplement

/-! Integral minimum-cost maximum flow, the parameter in Zhou's Theorem 1.2, p.2 and pp.28,31–32.
A general network is separate from the paper's graph reduction. The solver contract measures
actual instructions in the immutable published machine; it supplies no oracle instruction. -/

/-- Finite directed multigraph network with integer costs and nonnegative integer capacities. -/
structure IntegralNetwork where
  n : ℕ
  m : ℕ
  G : Digraph (Fin n) (Fin m)
  src : Fin n
  snk : Fin n
  cap : Fin m → ℕ
  c : Fin m → ℤ

/-- Graph-size parameter; the polynomial degree is fixed separately, independently of the input. -/
def IntegralNetwork.size (N : IntegralNetwork) : ℕ := N.n + N.m

/-- Polynomial integer magnitude bound, including distinct terminals. -/
def IntegralNetwork.Admissible (N : IntegralNetwork) (d : ℕ) : Prop :=
  N.src ≠ N.snk ∧ ∀ e, N.cap e ≤ (N.size + 2) ^ d ∧ |N.c e| ≤ ((N.size + 2 : ℕ) : ℤ) ^ d

/-- Net outgoing integral flow at v. Loops cancel in the two sums. -/
def IntegralNetwork.net (N : IntegralNetwork) (f : Fin N.m → ℤ) (v : Fin N.n) : ℤ :=
  (∑ e ∈ Finset.univ.filter (fun e => N.G.tail e = v), f e) -
    ∑ e ∈ Finset.univ.filter (fun e => N.G.head e = v), f e

/-- Capacity constraints and conservation away from the two terminals. -/
def IntegralNetwork.Feasible (N : IntegralNetwork) (f : Fin N.m → ℤ) : Prop :=
  (∀ e, 0 ≤ f e ∧ f e ≤ (N.cap e : ℤ)) ∧
    ∀ v, v ≠ N.src → v ≠ N.snk → N.net f v = 0

/-- Maximum value first; minimum integer cost among all flows of maximum value. -/
def IntegralNetwork.Optimal (N : IntegralNetwork) (f : Fin N.m → ℤ) : Prop :=
  N.Feasible f ∧ ∀ g, N.Feasible g →
    N.net g N.src ≤ N.net f N.src ∧
      (N.net g N.src = N.net f N.src → (∑ e, N.c e * f e) ≤ ∑ e, N.c e * g e)

/-- Integer input only: n,m,s,t, tails, heads, capacities, costs. -/
def IntegralNetwork.inI (N : IntegralNetwork) : List ℤ :=
  [(N.n : ℤ), N.m, N.src.val, N.snk.val] ++
    (List.finRange N.m).map (fun e => ((N.G.tail e).val : ℤ)) ++
    (List.finRange N.m).map (fun e => ((N.G.head e).val : ℤ)) ++
    (List.finRange N.m).map (fun e => (N.cap e : ℤ)) ++ (List.finRange N.m).map N.c

/-- Flow value per original arc in integer output cells, charged by the interpreter. -/
def IntegralNetwork.Output (N : IntegralNetwork) (o : ℕ → ℤ) : Prop :=
  N.Optimal (fun e => o e.val)

/-- A monotone worst-case envelope, at least linear in represented input size. -/
def RuntimeEnvelope (T : ℕ → ℕ → ℝ) : Prop :=
  (∀ n m, (n + m + 1 : ℕ) ≤ T n m) ∧
    (∀ n n' m, n ≤ n' → T n m ≤ T n' m) ∧
    ∀ n m m', m ≤ m' → T n m ≤ T n m'

/-- Runtime of a fixed correct deterministic integral min-cost maximum-flow subprogram,
for every sufficiently large polynomial word bound. d is fixed before all networks.
The source reduction only needs d=1, since all costs/capacities are at most the edge count. -/
def MCFContract (Q : Machine.Program) (cw d : ℕ) (T : ℕ → ℕ → ℝ) : Prop :=
  1 ≤ d ∧ RuntimeEnvelope T ∧
    ∀ N : IntegralNetwork, N.Admissible d → ∀ W : ℤ,
      ((N.size + 2 : ℕ) : ℤ) ^ cw ≤ W →
        Machine.HaltsWithin Q W N.inI [] (T N.n N.m) (fun o _ => N.Output o)

end MinCostArbPacking.Main.Supplement


