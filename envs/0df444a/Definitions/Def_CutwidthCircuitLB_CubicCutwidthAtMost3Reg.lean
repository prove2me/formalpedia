-- Prove2me | Definitions.Def_CutwidthCircuitLB_CubicCutwidthAtMost3Reg
-- name    : CutwidthCircuitLB_CubicCutwidthAtMost3Reg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:26:53.860423+00:00
-- url     : https://prove2.me/theorems/65aab9ba-43ac-41b3-b8a2-c6411a75632a
-- title:
--   The cubic cutwidth constant restricted to simple 3-regular graphs is at most $a$
-- statement:
--   The cubic cutwidth constant **restricted to simple 3-regular graphs** is at most $a$ if for every $\beta > a$ there is a function $r(N) = o(N)$ such that every connected simple 3-regular graph $H$ with $N$ vertices and $M$ edges has
--   $$
--   \mathrm{cw}(H) \le \beta (M - N) + r(N).
--   $$
--   For such graphs $M - N = N/2$. Section 4.3 states that this restriction does not change the constant.
--
--   **Formalization Note** Same reading as for the cubic cutwidth constant ("every $\beta > a$ is admissible"); the graphs are Mathlib simple graphs that are regular of degree $3$ and connected.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Section 4.3, p.13

import Mathlib
import Definitions.Def_CutwidthCircuitLB_cutSize
import Definitions.Def_CutwidthCircuitLB_CutwidthLE

namespace CutwidthCircuitLB

/-- The cubic cutwidth constant **restricted to simple 3-regular graphs** is at most `a` (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), §4.3,
p.13): every `β > a` admits `r(N) = o(N)` such that every connected simple 3-regular graph with `N`
vertices and `M` edges has cutwidth at most `β(M − N) + r(N)`.

**Formalization Note** Same reading as `CubicCutwidthAtMost`, with the class of graphs replaced by
connected `SimpleGraph`s on `Fin N` that are regular of degree 3 (for which `M − N = N/2`). -/
def CubicCutwidthAtMost3Reg (a : ℝ) : Prop :=
  ∀ β : ℝ, a < β → ∃ r : ℕ → ℝ, r =o[Filter.atTop] (fun N : ℕ => (N : ℝ)) ∧
    ∀ (N : ℕ) (H : SimpleGraph (Fin N)) [DecidableRel H.Adj],
      H.Connected → H.IsRegularOfDegree 3 →
        CutwidthLE H.edgeFinset.val (β * ((H.edgeFinset.card : ℝ) - N) + r N)

end CutwidthCircuitLB


