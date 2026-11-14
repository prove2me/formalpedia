-- Prove2me | Definitions.Def_DvorakNorin2018_SplitNetwork
-- name    : DvorakNorin2018_SplitNetwork
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-13T17:06:55.127966+00:00
-- url     : https://prove2.me/theorems/4893b61d-481b-4988-a9bf-472adaba13c3
-- title:
--   Finite split-vertex network for bounded-congestion clouds
-- statement:
--   For a finite graph $G$ with sinks $W$, split each vertex into an input and an output node, and add a source and a sink. Source-to-input capacities are $1$; input-to-output capacities are $\alpha$; graph edges give output-to-input arcs of capacity $M$ unless their tail belongs to $W$; outputs of vertices in $W$ connect to the sink with capacity $M$. Other capacities are zero. Cut capacity sums capacities from the cut to its complement. Finite $M$ is chosen above the supply threshold of interest.
-- source:
--   Dvorak and Norin, Treewidth of graphs with balanced separations, https://arxiv.org/pdf/1408.3869v2, Section 2.2, construction before Observation 5 (PDF p. 4). Finite M replaces infinite capacities for cuts below M.

import Definitions.Def_TreewidthApprox_Pushed_Setting
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
open scoped Classical BigOperators
namespace StableMSR.Recovery.SplitNetwork
abbrev Node (V : Type) := Unit ⊕ (Unit ⊕ (V ⊕ V))
abbrev source {V : Type} : Node V := Sum.inl ()
abbrev sink {V : Type} : Node V := Sum.inr (Sum.inl ())
abbrev input {V : Type} (v : V) : Node V := Sum.inr (Sum.inr (Sum.inl v))
abbrev output {V : Type} (v : V) : Node V := Sum.inr (Sum.inr (Sum.inr v))
noncomputable def capacity {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (W : Finset V) (α M : ℝ) : Node V → Node V → ℝ
  | .inl _, .inr (.inr (.inl _)) => 1
  | .inr (.inr (.inl v)), .inr (.inr (.inr w)) => if v = w then α else 0
  | .inr (.inr (.inr v)), .inr (.inr (.inl w)) => if G.Adj v w ∧ v ∉ W then M else 0
  | .inr (.inr (.inr v)), .inr (.inl _) => if v ∈ W then M else 0
  | _, _ => 0
noncomputable def row {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (α M : ℝ) (C : Finset (Node V)) (x : Node V) : ℝ :=
  if x ∈ C then ∑ y, if y ∉ C then capacity G W α M x y else 0 else 0
noncomputable def cut {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (α M : ℝ) (C : Finset (Node V)) : ℝ :=
  ∑ x, row G W α M C x

end StableMSR.Recovery.SplitNetwork


