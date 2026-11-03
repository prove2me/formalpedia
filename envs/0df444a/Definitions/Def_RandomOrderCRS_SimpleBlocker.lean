-- Prove2me | Definitions.Def_RandomOrderCRS_SimpleBlocker
-- name    : RandomOrderCRS_SimpleBlocker
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:22:06.247831+00:00
-- url     : https://prove2.me/theorems/a3732202-f96d-4b6e-a612-91a47e886ee4
-- title:
--   Simple-blockers and the pair $f^c$
-- statement:
--   Fix $e=(u,v)\in E$, and suppose that $f\in\partial(e)$ has vertex $w$ not in $e$. If $f=(w,u)$ (or $f=(w,v)$), the **pair** of $f$ is $f^c:=(w,v)$ (respectively $f^c:=(w,u)$), the other side of the triangle on $\{u,v,w\}$.
--
--   An edge $h\in\partial(w)\setminus\{(u,w),(v,w)\}$ is a **simple-blocker** for $f$, an event written $\mathrm{sbl}_f(h)$, if
--
--   1. $h$ is relevant for $f$, i.e. $S_h=1$ and $Y_h<Y_f$;
--   2. each $h'\in\partial(h)\setminus\partial(e)$ is irrelevant for $h$.
--
--   The event that $f$ has some simple-blocker is written $\mathrm{sbl}_f$. A simple-blocker of $f$ is selected before $f$ arrives, so $f$ cannot block $e$. This is what allows the analysis to go beyond the event $\mathcal R_e=\emptyset$.
--
--   **Formalization Note** The pair $f^c$ is the image of $f$ under the transposition of $u$ and $v$, as a pair of vertices that need not be an edge; so $x_{f^c}$ is `x (pair e f)`, which is $0$ when $f^c$ is not an edge. If $f^c$ is not an edge, its exclusion from the candidates is vacuous. The set difference $\partial(h)\setminus\partial(e)$ is kept exactly, because the independence of Proposition 6 depends on it.
-- source:
--   MacRury, Ma & Grammel, On (Random-order) Online Contention Resolution Schemes for the Matching Polytope of (Bipartite) Graphs, arXiv:2209.07520v2, Definition 5, p.18 (simple-blocker); p.19 (fᶜ)

import Mathlib
import Definitions.Def_RandomOrderCRS_ArrivalModel

open Finset

namespace RandomOrderCRS

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The pair `fᶜ` of `f` with respect to `e = (u, v)`: "if f = (w, u) (or f = (w, v)), then we define
f^c := (w, v) (respectively, f^c := (w, u)) to be the pair of f in the triangle
{(u, v), (w, v), (w, u)}", arXiv:2209.07520v2, p.19.

**Formalization Note.** It is the image of `f` under the transposition of `u` and `v`, so it depends
only on the unordered pair `e`. It is a pair of vertices that need not be an edge. Then `x (pair e f)`
is `x_{fᶜ}`, which is `0` when `fᶜ` is not an edge (p.23 uses this for triangle-free graphs). -/
def pair (e f : Sym2 V) : Sym2 V :=
  Sym2.lift ⟨fun u v => Sym2.map (Equiv.swap u v), fun u v => by
    show Sym2.map _ = Sym2.map _
    rw [Equiv.swap_comm]⟩ e f

/-- The candidates for simple-blockers of `f`, arXiv:2209.07520v2, Definition 5, p.18: "suppose that
f ∈ ∂(e) has vertex w not in e", and `h ∈ ∂(w) \ {(u, w), (v, w)}`.

**Formalization Note.** `{(u, w), (v, w)}` is `{f, fᶜ}`. If `fᶜ` is not an edge, its exclusion is
vacuous. For `f ∈ ∂(e)` the vertex `w` is unique, since `f ≠ e` and the graph is simple. -/
noncomputable def blockerCandidates (G : SimpleGraph V) [DecidableRel G.Adj] (e f : G.edgeSet) :
    Finset G.edgeSet := by
  classical
  exact univ.filter fun h => h ≠ f ∧ (h : Sym2 V) ≠ pair (e : Sym2 V) (f : Sym2 V) ∧
    ∃ w, w ∈ (f : Sym2 V) ∧ w ∉ (e : Sym2 V) ∧ w ∈ (h : Sym2 V)

/-- The event `sbl_f(h)` that `h` is a simple-blocker for `f`, arXiv:2209.07520v2, Definition 5,
p.18: "1. h is relevant for f (i.e., S_h = X_h · A_h = 1, and Y_h < Y_f). 2. Each h′ ∈ ∂(h) \ ∂(e) is
irrelevant for h."

**Formalization Note.** `h ∈ ∂(f)` follows from `h ∈ blockerCandidates G e f`, so condition 1 is
`IsRelevant G Y S f h`. The set difference `∂(h) \ ∂(e)` is kept exactly. -/
def IsSimpleBlocker (G : SimpleGraph V) [DecidableRel G.Adj] (Y : G.edgeSet → ℝ)
    (S : G.edgeSet → Bool) (e f h : G.edgeSet) : Prop :=
  h ∈ blockerCandidates G e f ∧ IsRelevant G Y S f h ∧
    ∀ h' ∈ edgeNbrs G h \ edgeNbrs G e, ¬ IsRelevant G Y S h h'

/-- The event `sbl_f`: "the event in which f has some simple-blocker", arXiv:2209.07520v2,
Definition 5, p.18. -/
def HasSimpleBlocker (G : SimpleGraph V) [DecidableRel G.Adj] (Y : G.edgeSet → ℝ)
    (S : G.edgeSet → Bool) (e f : G.edgeSet) : Prop :=
  ∃ h, IsSimpleBlocker G Y S e f h

end RandomOrderCRS


