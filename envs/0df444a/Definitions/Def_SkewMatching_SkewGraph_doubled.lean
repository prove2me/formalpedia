-- Prove2me | Definitions.Def_SkewMatching_SkewGraph_doubled
-- name    : SkewMatching_SkewGraph_doubled
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:08:33.852853+00:00
-- url     : https://prove2.me/theorems/c72b0186-74dd-445e-ba24-fcd0da655c85
-- title:
--   Residual graphs: forward and reverse edges, active edges, augmentation
-- statement:
--   For a skew-symmetric graph $G$, the **doubled graph** has for each edge $e$ a forward copy $(e,\mathrm{true})$ running as $e$ does, and a reverse copy $(e,\mathrm{false})$ running against it; $\sigma$ keeps the direction. It is again skew-symmetric.
--
--   For a flow $f$, a forward copy is **active** when $f_e=0$ and a reverse copy is active when $f_e=1$. The active edges form the **residual graph** of $f$, a sub-multigraph of the doubled graph.
--
--   **Augmenting** $f$ along a residual path $p$ flips $f$ on every edge used by $p$ or by its symmetric path.
--
--   **Formalization Note** The doubled graph does not depend on $f$, so the variables $x_e$ and the charges can be kept on one fixed edge type while the residual graph changes.
-- source:
--   Li, Li, Zhang, Maximum Cardinality Matching in n^{2+o(1)} Time, STOC 2027 submission (manuscript sha256 3fc151f5…), §2.3, p.5; Theorem 10, p.4

import Mathlib
import Definitions.Def_SkewMatching_SkewGraph

namespace SkewMatching

namespace SkewGraph

open scoped Classical

variable {V E : Type*} (G : SkewGraph V E)

/-- All forward and reverse edges of `G`: `(e, true)` runs as `e` does and `(e, false)` runs against it.
`σ` keeps the direction. The **residual graph** of a flow `f` is the sub-multigraph `G.active f` of this
graph.

Li, Li, Zhang, *Maximum Cardinality Matching in n^{2+o(1)} Time*, STOC 2027 submission (manuscript
sha256 3fc151f5…), §2.3, p.5 ("including their corresponding reverse edges that may appear during
augmentation"), Theorem 10, p.4. -/
def doubled : SkewGraph V (E × Bool) where
  tail a := if a.2 then G.tail a.1 else G.head a.1
  head a := if a.2 then G.head a.1 else G.tail a.1
  σV := G.σV
  σE a := (G.σE a.1, a.2)
  σV_invol := G.σV_invol
  σV_ne := G.σV_ne
  σE_invol := fun a => by simp [G.σE_invol a.1]
  σE_ne := fun a h => G.σE_ne a.1 (congrArg Prod.fst h)
  tail_σE := fun a => by cases a.2 <;> simp [*, G.tail_σE, G.head_σE]
  head_σE := fun a => by cases a.2 <;> simp [*, G.tail_σE, G.head_σE]

/-- An edge is **active** (§2.3, p.5) if its capacity in the residual graph of `f` is `1`: a forward edge
with `f e = 0`, or a reverse edge with `f e = 1`. -/
def Active (f : E → ℕ) (a : E × Bool) : Prop := if a.2 then f a.1 = 0 else f a.1 = 1

/-- The **residual graph** of `f`: its active edges, as a sub-multigraph of `G.doubled`. -/
noncomputable def active [Fintype E] (f : E → ℕ) : Finset (E × Bool) :=
  Finset.univ.filter (Active f)

/-- **Augmenting** along the residual path `p` and its symmetric path (Theorem 10, p.4): the value of `f` is
flipped on every edge used by `p` or by its symmetric path.

**Formalization Note.** A regular path in the residual graph of a symmetric `f` cannot use `(e, b)` together
with `(σ e, b)` (regularity), nor `(e, b)` together with `(σ e, !b)` or `(e, !b)` (only one direction of a
symmetric pair is active), so each edge is flipped once. -/
noncomputable def augment (f : E → ℕ) (p : List (E × Bool)) : E → ℕ := fun e =>
  if ∃ b, (e, b) ∈ p ∨ (G.σE e, b) ∈ p then 1 - f e else f e

end SkewGraph

end SkewMatching


