-- Prove2me | Definitions.Def_SkewMatching_SkewGraph_IsFlow
-- name    : SkewMatching_SkewGraph_IsFlow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:08:33.963911+00:00
-- url     : https://prove2.me/theorems/3dfdf503-eda0-430f-8777-1e20bb0e21b0
-- title:
--   Definition 4 — integral symmetric flows and their value
-- statement:
--   Let $G$ be a finite skew-symmetric graph, $s$ a vertex and $s'=\sigma(s)$. An **integral symmetric flow** from $s$ to $s'$ at unit capacity is a function $f:E\to\mathbb N$ with $f_e\le 1$, $f_{\sigma(e)}=f_e$, and equal inflow and outflow at every vertex other than $s$ and $s'$.
--
--   Its **value** $|f|$ is the net flow out of $s$, an integer. A pair of symmetric $s$–$s'$ paths has value $2$. A flow is **maximum** if no flow has larger value.
--
--   **Formalization Note** Value counts both symmetric paths, as in Observation 6 ("twice the matching size"), so the constant in Lemma 15 is the paper's $-2|f|$.
-- source:
--   Li, Li, Zhang, Maximum Cardinality Matching in n^{2+o(1)} Time, STOC 2027 submission (manuscript sha256 3fc151f5…), Definition 4, p.3; Observation 6, p.3

import Mathlib
import Definitions.Def_SkewMatching_SkewGraph

namespace SkewMatching

namespace SkewGraph

open scoped Classical

variable {V E : Type*} (G : SkewGraph V E)

/-- The total flow out of `v`. -/
noncomputable def outSum [Fintype E] (f : E → ℕ) (v : V) : ℕ :=
  ∑ e ∈ Finset.univ.filter (fun e => G.tail e = v), f e

/-- The total flow into `v`. -/
noncomputable def inSum [Fintype E] (f : E → ℕ) (v : V) : ℕ :=
  ∑ e ∈ Finset.univ.filter (fun e => G.head e = v), f e

/-- An **integral symmetric flow** from `s` to `s′ = σ s` (Definition 4, p.3) at unit capacity: integer
values at most `1`, `f (σ e) = f e`, and conservation at every vertex other than `s`, `s′`.

Li, Li, Zhang, *Maximum Cardinality Matching in n^{2+o(1)} Time*, STOC 2027 submission (manuscript
sha256 3fc151f5…), Definition 4, p.3.

**Formalization Note.** A flow is an honest `E → ℕ`; `f e ≤ 1` is the capacity constraint. -/
structure IsFlow [Fintype E] (s : V) (f : E → ℕ) : Prop where
  le_one : ∀ e, f e ≤ 1
  symm : ∀ e, f (G.σE e) = f e
  conserve : ∀ v, v ≠ s → v ≠ G.σV s → G.outSum f v = G.inSum f v

/-- The **value** of `f`: net flow out of `s`. A pair of symmetric paths has value `2` (Observation 6, p.3:
"twice the matching size"). It is an integer, because a flow in a residual graph may have negative value in
the sense of §3.5, p.9 ("this path contributes −1"). -/
noncomputable def value [Fintype E] (s : V) (f : E → ℕ) : ℤ :=
  (G.outSum f s : ℤ) - (G.inSum f s : ℤ)

/-- A **maximum** integral symmetric flow (Definition 4, p.3). -/
def IsMaxFlow [Fintype E] (s : V) (f : E → ℕ) : Prop :=
  G.IsFlow s f ∧ ∀ f', G.IsFlow s f' → G.value s f' ≤ G.value s f

end SkewGraph

end SkewMatching


