-- Prove2me | Definitions.Def_CollectiveTreeExploration_Async_ElectricalNetwork
-- name    : CollectiveTreeExploration_Async_ElectricalNetwork
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:08:47.88027+00:00
-- url     : https://prove2.me/theorems/0a29f0c1-d40d-494a-89ce-d7a5e0ed1047
-- title:
--   Tree electrical currents and wired-subtree effective resistance
-- statement:
--   A resistive network on a finite rooted tree assigns a resistance $r_u$ to each non-root edge. Currents $i_u$ are oriented from the parent to the child and satisfy Kirchhoff's conservation law at internal vertices; at the root the outgoing currents sum to zero. Prescribed leaf voltages are enforced by a potential $V$ satisfying
--   $$V_{p_u}-V_u=r_ui_u.$$
--
--   For a vertex $u$ that is not a leaf, a unit flow sends one unit from $u$ toward its descendant leaves, conserving flow at every strict internal descendant. Its energy is the sum of $r_v\theta_v^2$ on the strict descendant edges. The wired-subtree effective resistance is
--   $$R_u=\inf_{\theta\text{ a unit flow from }u\text{ to }L_u}\sum_{v\prec u}r_v\theta_v^2.$$
--   At a leaf it is zero. This definition is independent of any power regularizer or asserted resistance formula. On a valid finite tree with positive resistances, the flow set is nonempty and its energy is bounded below by zero. On malformed data the real infimum retains Lean's total convention; no theorem uses that case.
--
--   These are the Ohm–Kirchhoff and Thomson formulations used by the source in §2.1 and Lemma 3.6.
--
--   The voltage itself is chosen from the Dirichlet problem: prescribed leaf values and zero net current at internal nodes, with currents determined by voltage differences divided by resistance. Values outside the vertex set are zero. The zero fallback is used only when this boundary problem has no solution; no theorem identity is part of the defining problem.
-- source:
--   Romain Cosson, Laurent Massoulié, STOC 2027 submission #263 (October 2026), §2.1, p.5 (Electrical networks); Lemma 3.6, pp.9–10

import Mathlib
import Definitions.Def_CollectiveTreeExploration_Async_WeightedTree

namespace CollectiveTreeExploration.Async
open scoped BigOperators
noncomputable section
open Classical
namespace WTree
variable (T : WTree)

/-! ## Resistive networks on a tree (§2.1, p.5; Lemma 3.6, p.9)

Each edge `(p_u, u)`, `u ≠ r`, carries a resistance `res u`; the leaves are the terminals. A
current is described by the value `i u` on each edge `(p_u, u)`, positive when it flows from `p_u`
down to `u`. -/

/-- `i` is an electrical current in the network with resistances `res` and leaf voltages `bv`:
Kirchhoff's law holds at every non-leaf vertex (at the root, the currents into its children sum
to zero; at a non-root internal vertex `u`, `i_u = ∑_{c ∈ C_u} i_c`), and there is a potential
`V` with `V_ℓ = bv ℓ` at every leaf satisfying Ohm's law `V_{p_u} - V_u = res_u · i_u` on every
edge. -/
def IsCurrent (res : ℕ → ℝ) (bv : ℕ → ℝ) (i : ℕ → ℝ) : Prop :=
  (T.root ∉ T.leaves → ∑ c ∈ T.children T.root, i c = 0) ∧
  (∀ u ∈ T.V, u ≠ T.root → u ∉ T.leaves → i u = ∑ c ∈ T.children u, i c) ∧
  ∃ V : ℕ → ℝ, (∀ ℓ ∈ T.leaves, V ℓ = bv ℓ) ∧
    ∀ u ∈ T.V, u ≠ T.root → V (T.par u) - V u = res u * i u

/-- The Dirichlet problem with prescribed leaf voltages: zero extension outside
vertices, boundary values, and Kirchhoff's harmonicity law at internal vertices.
It depends on resistances and boundary data, not on a claimed current or voltage identity. -/
def IsVoltage (res bv V : ℕ → ℝ) : Prop :=
  (∀ u, u ∉ T.V → V u = 0) ∧
  (∀ ℓ ∈ T.leaves, V ℓ = bv ℓ) ∧
  ∀ u ∈ T.V, u ∉ T.leaves →
    (∑ c ∈ T.children u, (V u - V c) / res c) =
      (if u = T.root then 0 else (V (T.par u) - V u) / res u)

/-- The voltage computed from the Dirichlet problem. On a finite positive tree the
solution exists and is unique. Zero is only the total extension if no solution exists. -/
def voltage (res bv : ℕ → ℝ) : ℕ → ℝ :=
  if h : ∃ V, T.IsVoltage res bv V then Classical.choose h else fun _ => 0

/-- `θ` is a unit flow from `u` to the leaves `L_u` of its subtree: one unit enters the edges to
the children of `u`, and Kirchhoff's law holds at every internal strict descendant of `u` (the
leaves absorb the flow). Only the values on strict descendants of `u` matter. -/
def IsUnitFlowToLeaves (u : ℕ) (θ : ℕ → ℝ) : Prop :=
  ∑ c ∈ T.children u, θ c = 1 ∧
  ∀ v ∈ T.V, T.Desc v u → v ≠ u → v ∉ T.leaves → θ v = ∑ c ∈ T.children v, θ c

/-- The effective resistance `R_u` between `u` and `L_u` in the subtree of `u` with edge
resistances `res`, by Thomson's principle: the least energy `∑_{v ≺ u} res_v θ_v²` of a unit flow
from `u` to `L_u`. A leaf has effective resistance `0` (`L_u = {u}`). -/
def effRes (res : ℕ → ℝ) (u : ℕ) : ℝ :=
  if u ∈ T.leaves then 0 else
    sInf ((fun θ : ℕ → ℝ =>
        ∑ v ∈ T.V.filter (fun v => T.Desc v u ∧ v ≠ u), res v * θ v ^ 2) ''
      {θ | T.IsUnitFlowToLeaves u θ})

end WTree
end
end CollectiveTreeExploration.Async


