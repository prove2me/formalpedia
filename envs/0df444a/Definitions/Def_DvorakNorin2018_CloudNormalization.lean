-- Prove2me | Definitions.Def_DvorakNorin2018_CloudNormalization
-- name    : DvorakNorin2018_CloudNormalization
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-13T17:35:46.896083+00:00
-- url     : https://prove2.me/theorems/c3f9c0e6-c7f5-4950-98df-7443c8d58226
-- title:
--   Clouds, tameness and lexicographic flow minimization
-- statement:
--   A cloud is a finite nonnegative supply/flow pair supported on graph edges, with supply at most one, no outgoing flow from designated sinks, conservation elsewhere, and congestion at most $\alpha$. A vertex is saturated if its supply is one, and hungry if its supply is less than one and it has positive congestion or is a sink. Tameness means no incoming flow at hungry vertices, at most one hungry predecessor at each saturated vertex, and, when $\alpha\le1$, zero edge flow with active vertices exactly the sinks.
--
--   The primary objective is total edge flow. The secondary objective is the support size plus the number of unsaturated vertices; for a fixed graph this differs from the source's support-size-minus-saturation-size objective by the constant number of vertices. A lexicographic minimizer first minimizes total edge flow among clouds of the prescribed total supply, then minimizes this secondary objective. The rerouting conclusion records the first two structural tameness properties.
-- source:
--   Dvorak–Norin, Treewidth of graphs with balanced separations, https://arxiv.org/pdf/1408.3869v2, Section 2.2, definitions preceding Lemma 6 and its proof (PDF pp. 5–6).

import Definitions.Def_TreewidthApprox_Pushed_Setting
import Mathlib.Data.Real.Basic

set_option autoImplicit false
open scoped Classical BigOperators
namespace StableMSR.Recovery.TameCloud
abbrev Data (V : Type) := (V → ℝ) × (V × V → ℝ)
noncomputable def incoming {V : Type} [Fintype V] (p : Data V) (v : V) : ℝ := ∑ u, p.2 (u,v)
noncomputable def congestion {V : Type} [Fintype V] (p : Data V) (v : V) : ℝ := p.1 v + incoming p v
noncomputable def volume {V : Type} [Fintype V] (p : Data V) : ℝ := ∑ a, p.2 a
noncomputable def total {V : Type} [Fintype V] (p : Data V) : ℝ := ∑ v, p.1 v
structure Cloud {V : Type} [Fintype V] (G : SimpleGraph V) (W : Finset V) (α : ℝ) (p : Data V) : Prop where
  supply : ∀ v, 0 ≤ p.1 v ∧ p.1 v ≤ 1
  flow : ∀ a, 0 ≤ p.2 a
  support : ∀ u v, ¬ G.Adj u v → p.2 (u,v) = 0
  sinks : ∀ u ∈ W, ∀ v, p.2 (u,v) = 0
  conserve : ∀ v ∉ W, congestion p v = ∑ u, p.2 (v,u)
  bound : ∀ v, congestion p v ≤ α

def Hungry {V : Type} [Fintype V] (W : Finset V) (p : Data V) (v : V) : Prop :=
  p.1 v < 1 ∧ (0 < congestion p v ∨ v ∈ W)
def Tame {V : Type} [Fintype V] (W : Finset V) (α : ℝ) (p : Data V) : Prop :=
  (∀ v, Hungry W p v → ∀ u, p.2 (u,v) = 0) ∧
  (∀ z, p.1 z = 1 → ∀ u v, Hungry W p u → Hungry W p v →
    0 < p.2 (u,z) → 0 < p.2 (v,z) → u = v) ∧
  (α ≤ 1 → (∀ a, p.2 a = 0) ∧
    ∀ v, (p.1 v = 1 ∨ Hungry W p v) ↔ v ∈ W)


noncomputable def penalty {V : Type} [Fintype V] (p : Data V) : ℕ :=
  (Finset.univ.filter (fun a => p.2 a ≠ 0)).card +
    (Finset.univ.filter (fun v => p.1 v ≠ 1)).card

def IsLexMinimum {V : Type} [Fintype V] (G : SimpleGraph V) (W : Finset V)
    (α s : ℝ) (p : Data V) : Prop :=
  Cloud G W α p ∧ total p = s ∧ ∀ q : Data V, Cloud G W α q → total q = s →
    volume p ≤ volume q ∧ (volume q = volume p → penalty p ≤ penalty q)


def ReroutingConclusion {V : Type} [Fintype V] (W : Finset V) (p : Data V) : Prop :=
  (∀ v, Hungry W p v → ∀ u, p.2 (u,v) = 0) ∧
  (∀ z, p.1 z = 1 → ∀ u v, Hungry W p u → Hungry W p v →
    0 < p.2 (u,z) → 0 < p.2 (v,z) → u = v)


end StableMSR.Recovery.TameCloud


