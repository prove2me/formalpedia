-- Prove2me | Definitions.Def_BauerleRiederMDP_Contracting_IsClosedInIBb
-- name    : BauerleRiederMDP_Contracting_IsClosedInIBb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:27:51.316396+00:00
-- url     : https://prove2.me/theorems/01dec194-e586-472d-a302-3e61617c35c2
-- title:
--   Closed subsets of the weighted function space $(\mathbb B_b,\|\cdot\|_b)$
-- statement:
--   Let $b:E\to\mathbb R_+$ be measurable. The space $\mathbb B_b$ consists of the measurable functions $v:E\to\mathbb R$ with finite weighted supremum norm
--
--   $$\|v\|_b=\sup_{x\in E}\frac{|v(x)|}{b(x)}\qquad(\text{with } 0/0:=0),$$
--
--   equivalently with $|v(x)|\le c\,b(x)$ for all $x$ and some $c\ge0$.
--
--   A set $S\subset\mathbb B_b$ is **closed in $(\mathbb B_b,\|\cdot\|_b)$** if for every sequence $v_n\in S$ and every $v\in\mathbb B_b$ with $\|v_n-v\|_b\to0$ we have $v\in S$.
--
--   This is the closedness of the set $\mathbb M$ in the Structure Theorem 7.3.5 for contracting models: closedness for the weighted norm, not for pointwise convergence.
--
--   **Formalization Note** $\mathbb B_b$ and $\|\cdot\|_b$ are the published `MDPFinance.Contracting.IBb` and `normb`; Lean's $x/0=0$ agrees with the book's convention because functions in $\mathbb B_b$ vanish where $b$ does. Since $(\mathbb B_b,\|\cdot\|_b)$ is a normed space, sequential closedness is closedness.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Springer Universitext, DOI 10.1007/978-3-642-18324-9, Definition 7.3.1 and Theorem 7.3.5, pp.205–207 (PDF pp.216–218); weighted supremum norm §2.4, p.28 (PDF p.43)

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Bounding

open MeasureTheory Filter Topology

namespace BauerleRiederMDP.Contracting

open MDPFinance.Contracting

variable {E : Type*} [MeasurableSpace E]

/-- A set `S ⊂ IB_b` is **closed in `(IB_b, ‖·‖_b)`** (Bäuerle & Rieder, *Markov Decision Processes
with Applications to Finance* (2011), Theorem 7.3.5, p.207, PDF p.218, "a closed subset
`IM ⊂ IB_b`"; the normed space `(IB_b, ‖·‖_b)` of Definition 7.3.1, p.205, PDF p.216): whenever
`v_n ∈ S` and `v ∈ IB_b` satisfy `‖v_n − v‖_b → 0`, then `v ∈ S`.

**Formalization Note.** `IB_b` and the weighted supremum norm `‖v‖_b = sup_x |v(x)|/b(x)` are the
published `MDPFinance.Contracting.IBb` and `normb`. `(IB_b, ‖·‖_b)` is a normed space, so a
subset is closed iff it is sequentially closed; closedness is taken in the `‖·‖_b` metric, not
pointwise. Differences of elements of `IB_b` lie in `IB_b`, so every `normb` here is a supremum
of a bounded family (no junk value). -/
def IsClosedInIBb (b : E → ℝ) (S : Set (E → ℝ)) : Prop :=
  ∀ (vn : ℕ → E → ℝ) (v : E → ℝ), (∀ n, vn n ∈ S) → v ∈ IBb b →
    Tendsto (fun n => normb b (fun x => vn n x - v x)) atTop (𝓝 0) → v ∈ S

end BauerleRiederMDP.Contracting


