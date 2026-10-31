-- Prove2me | Definitions.Def_LeGallBrownianMap_pseudoQuotientGH
-- name    : LeGallBrownianMap_pseudoQuotientGH
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:36:50.581397+00:00
-- url     : https://prove2.me/theorems/64482110-125d-4af0-b06e-86ac2fd73505
-- title:
--   The compact metric space $X/\{d=0\}$ as a point of $\mathbb K$
-- statement:
--   Let $X$ be a set and $d : X\times X\to\mathbb R$ a **pseudometric** ($d(x,x)=0$, $d(x,y)=d(y,x)$, $d(x,z)\le d(x,y)+d(y,z)$). Identify points at $d$-distance $0$; the quotient $X/\{d=0\}$ with the induced distance is a metric space. When it is compact and nonempty, its isometry class is a point of $\mathbb K$.
--
--   The paper uses this construction for the Brownian map $(m_\infty, D^*)$ (the quotient of $[0,1]$ by $\{D^*=0\}$), for the subsequential limits $([0,1]/\!\approx, D)$ of Theorem 2.3, and for finite vertex sets with a multiple of the graph distance.
--
--   **Formalization Note** The quotient is Mathlib's `SeparationQuotient` of the pseudometric space $(X,d)$. The function is total: if $d$ is not a pseudometric, or the quotient is not compact or empty, the value is `default` (a one-point space). The mission only applies it to continuous pseudometrics on $[0,1]$ and to scaled graph distances on finite connected graphs, where the quotient is compact and nonempty.
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §1, pp.2–4; Theorem 2.3, p.17 (m∞ = [0,1]/≈ with the distance induced by D)

import Mathlib
import Definitions.Def_LeGallBrownianMap_PseudoCarrier

open GromovHausdorff

namespace LeGallBrownianMap

/-- The metric space associated with a pseudometric, as a point of the space K of isometry
classes of compact metric spaces (Le Gall, arXiv:1105.4842v2, §1, p.2: "the space K of
isometry classes of compact metric spaces", with the Gromov–Hausdorff distance). Given a set `X`
and a function `d : X → X → ℝ` that is a pseudometric (`d x x = 0`, symmetric, triangle
inequality), identify the points at `d`-distance `0` and equip the quotient `X / {d = 0}` with
the distance induced by `d`. If this metric space is compact and nonempty, return its isometry
class.

The paper uses this construction twice: `m∞ = T_e/≃` with the distance `D∗` of eq. (1), p.4
(here applied to `D∗` viewed on `[0,1]`, p.15), and `m∞ = [0,1]/≈` with the distance induced by
`D` (Theorem 2.3, p.17). For a finite connected graph with a positive multiple of its graph
distance, `d` is already a metric and the quotient is the vertex set itself.

**Formalization Note.** The quotient is Mathlib's `SeparationQuotient` of the pseudometric
space `(X, d)`, whose `MetricSpace` instance is the induced distance. The function is total:
when `d` is not a pseudometric, or the quotient is not compact or is empty, it returns
`default` (a one-point space). Every use in this mission applies it to a pseudometric whose
quotient is compact and nonempty (a continuous pseudometric on `[0,1]`, or a scaled graph
distance on a finite connected vertex set), so the `default` branch is never reached on the
paper's objects. -/
noncomputable def pseudoQuotientGH (X : Type) (d : X → X → ℝ) : GHSpace := by
  classical
  exact
    if h : (∀ x, d x x = 0) ∧ (∀ x y, d x y = d y x) ∧ (∀ x y z, d x z ≤ d x y + d y z) then
      letI : PseudoMetricSpace (PseudoCarrier X d) :=
        { dist := d
          dist_self := h.1
          dist_comm := h.2.1
          dist_triangle := h.2.2 }
      if hc : CompactSpace (SeparationQuotient (PseudoCarrier X d)) ∧
          Nonempty (SeparationQuotient (PseudoCarrier X d)) then
        haveI := hc.1
        haveI := hc.2
        toGHSpace (SeparationQuotient (PseudoCarrier X d))
      else default
    else default

end LeGallBrownianMap


