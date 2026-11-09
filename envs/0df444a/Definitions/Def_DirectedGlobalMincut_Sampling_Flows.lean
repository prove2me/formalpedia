-- Prove2me | Definitions.Def_DirectedGlobalMincut_Sampling_Flows
-- name    : DirectedGlobalMincut_Sampling_Flows
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:59:41.388696+00:00
-- url     : https://prove2.me/theorems/2d01ecec-cd6c-40c5-8ed9-d39860e7856b
-- title:
--   Nonnegative demand flows and the warmup auxiliary network
-- statement:
--   A finite network consists of a digraph, capacities in $[0,+\infty]$, and integer vertex demands. A nonnegative demand flow $g$ is zero outside its arc set and obeys
--
--   $$\sum_{e:\operatorname{head}(e)=v}g_e-\sum_{e:\operatorname{tail}(e)=v}g_e=d(v).$$
--
--   Capacity feasibility is a separate predicate. It adds $g_e\le c_e$, allowing the capacity-free predicate to apply after rounding.
--
--   For a rooted spanning tree $T$, the warmup network has sources $s_v$ for $v\ne r$, edge nodes $y_e$, and one sink $t_f$ for each tree arc. It contains $s_v\to y_e$ of capacity $q_e$ when $\operatorname{head}(e)=v\ne r$, and $y_e\to t_f$ of infinite capacity exactly when $f$ lies on the undirected tree path between the endpoints of $e$. Demands are $-1,0,+1$ on these three node classes. Projection reads the first kind of arc.
--
--   The source's undefined $s_r$ is completed by omitting the corresponding auxiliary arcs and defining their original-edge projections to be zero. Root-entering arcs remain present in the original graph. This changes no arborescence or cut instance.
-- source:
--   Henry Fleischmann, Jason Li, Thatchaphol Saranurak, Benyu Wang, STOC 2027 submission #504 (October 2026), §4.1 and §4.2, pp.5–6, p. 5 (PDF p. 5); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/504.pdf

import Mathlib
import Definitions.Def_DirectedGlobalMincut_Sampling_Cuts

open scoped ENNReal NNReal

namespace DirectedGlobalMincut.Sampling

open BasicPackArb.Main

/-- A finite network with separate capacities and integer demands. Positive demand means net inflow. -/
structure Network (V A : Type) where
  graph : Digraph V A
  capacity : A → ℝ≥0∞
  demand : V → ℤ

noncomputable def balance {V A : Type} [DecidableEq V] (H : Network V A)
    (g : A → ℝ) (v : V) : ℝ :=
  (∑ e ∈ H.graph.arcs.filter (fun e => H.graph.head e = v), g e) -
    ∑ e ∈ H.graph.arcs.filter (fun e => H.graph.tail e = v), g e

/-- Nonnegativity and conservation are independent of capacity restrictions. -/
def DemandFlow {V A : Type} [DecidableEq V] (H : Network V A) (g : A → ℝ) : Prop :=
  (∀ e, 0 ≤ g e) ∧ (∀ e, e ∉ H.graph.arcs → g e = 0) ∧
    ∀ v, balance H g v = (H.demand v : ℝ)

def FeasibleFlow {V A : Type} [DecidableEq V] (H : Network V A) (g : A → ℝ) : Prop :=
  DemandFlow H g ∧ ∀ e ∈ H.graph.arcs, ENNReal.ofReal (g e) ≤ H.capacity e

abbrev WarmNode {n m : ℕ} (r : Fin n) (T : Finset (Fin m)) :=
  {v : Fin n // v ≠ r} ⊕ (Fin m ⊕ {f : Fin m // f ∈ T})

/-- §4.1, p.5. The nonexistent source s_r is omitted; its projection is zero. -/
noncomputable def warmAdj {n m : ℕ} (G : Graph n m) (r : Fin n) (T : Finset (Fin m)) :
    WarmNode r T → WarmNode r T → Prop
  | .inl v, .inr (.inl e) => e ∈ G.arcs ∧ G.head e = v.val
  | .inr (.inl e), .inr (.inr f) => e ∈ G.arcs ∧ f.val ∈ pathEdges G T e
  | _, _ => False

noncomputable def warmNetwork {n m : ℕ} (G : Graph n m) (r : Fin n)
    (T : Finset (Fin m)) (q : Fin m → ℝ) : Network (WarmNode r T) (WarmNode r T × WarmNode r T) := by
  classical
  exact {
    graph := ⟨Prod.fst, Prod.snd, Finset.univ.filter (fun a => warmAdj G r T a.1 a.2)⟩
    capacity := fun a => match a with
      | (.inl _, .inr (.inl e)) => ENNReal.ofReal (q e)
      | _ => ⊤
    demand := fun v => match v with
      | .inl _ => -1
      | .inr (.inl _) => 0
      | .inr (.inr _) => 1 }

noncomputable def warmProjection {n m : ℕ} (G : Graph n m) (r : Fin n) (T : Finset (Fin m))
    (g : (WarmNode r T × WarmNode r T) → ℝ) (e : Fin m) : ℝ :=
  if h : G.head e ≠ r then g (.inl ⟨G.head e, h⟩, .inr (.inl e)) else 0

end DirectedGlobalMincut.Sampling


