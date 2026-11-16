-- Prove2me | Definitions.Def_IntervalExplore_KT1_Supplement_Model
-- name    : IntervalExplore_KT1_Supplement_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T11:59:53.448204+00:00
-- url     : https://prove2.me/theorems/61e101ca-593d-4713-baa4-b5bdf4855bb1
-- title:
--   KT0 algorithms, ∞-interval connectivity, the gadget $K_n(u,v)$ and $f(m,n)$
-- statement:
--   These definitions extend the published fixed-port model of online exploration on a dynamic graph $\mathcal G=(G_t)_{t\ge0}$ with underlying graph $G=(V,E)$.
--
--   1. **KT0 algorithms.** In the KT0 model the agent at time $t$ receives only the identifier of its current node $\nu(t)$, the set $P(\nu(t),t)$ of currently available local ports, and the incoming port $p_{\mathrm{in}}(t)$. The KT0 view of a KT1 observation is the same observation with the list of (neighbour identifier, port) pairs erased. A deterministic algorithm is a KT0 algorithm when every decision it takes on an observation history coincides with its decision on the history of KT0 views.
--   2. **∞-interval connectivity.** The dynamic graph is ∞-interval-connected when the graph of edges present at every time,
--   $$
--   \Big(V,\ \bigcap_{t\in\mathbb N}E(t)\Big),
--   $$
--   is connected.
--   3. **The gadget.** For distinct $u,v\in V$, $K_n(u,v)$ is the complete graph on $V$ ($|V|=n$) with the single edge $\{u,v\}$ removed. The nodes $u,v$ are its gates; the other nodes are traps.
--   4. **The function of Lemma 11.** For reals $n,m$,
--   $$
--   f(m,n)=\frac{m\ln n}{1+\ln m-\ln n},
--   $$
--   which equals $\xi(n,m)\cdot m$ at natural arguments; it is used only for $3\le n\le m$, where the denominator is at least $1$.
--
--   These objects state the KT0 upper bound, the window-size lower bound and the two exploration-time lower bounds of the paper on the published execution semantics, without introducing a second execution model.
--
--   **Formalization Note** KT0 is a restriction on the published algorithm type (decisions invariant under erasing neighbour identifiers), so the run, termination and invalid-port semantics are exactly the published ones.
-- source:
--   Yuichi Sudo, Naoki Kitamura, Masahiro Shibata, Junya Nakamura, Sébastien Tixeuil, Toshimitsu Masuzawa, Koichi Wada, STOC 2027 submission #1589 (October 2026), §1.2, p.3 (PDF p.4) (KT0, ∞-interval connectivity); §3, p.13 (PDF p.14) (gadget K_n(u,v)); Appendix A, Lemma 11, p.18 (PDF p.19) (f(m,n))

import Definitions.Def_IntervalExplore_KT1_Execution

set_option autoImplicit false

namespace IntervalExplore.KT1.Supplement

open IntervalExplore.KT1

/-- §1.2, p.3 (PDF p.4): in KT0 the agent receives only (id(ν(t)), P(ν(t),t), p_in(t)).
The KT0 view of a published KT1 observation forgets the neighbour identifiers. -/
def kt0View (o : Obs) : Obs := {o with neighbors := ∅}

/-- A KT0 algorithm is a published algorithm whose every decision depends only on the
KT0 views of its observation history. The published execution semantics are unchanged. -/
def IsKT0 (A : Alg) : Prop := ∀ h : List Obs, A h = A (h.map kt0View)

/-- §1.2, p.3 (PDF p.4): ∞-interval connectivity, the intersection of all snapshots is
connected. -/
def InfIntervalConnected {V : Type} {G : SimpleGraph V} (D : DynamicGraph G) : Prop :=
  (⨅ t : ℕ, D.snapshot t).Connected

/-- §3, p.13 (PDF p.14): the gadget K_n(u,v), the complete graph on the vertex type with
the single edge {u,v} removed. Used only with u ≠ v. -/
def gadget {V : Type} (u v : V) : SimpleGraph V :=
  (⊤ : SimpleGraph V).deleteEdges {s(u, v)}

/-- Appendix A, Lemma 11, p.18 (PDF p.19): f(m,n) = m ln n / (1 + ln m − ln n),
over the reals, natural logarithms. Used only with 3 ≤ n ≤ m, where the denominator
is at least 1. -/
noncomputable def lemma11F (m n : ℝ) : ℝ :=
  m * Real.log n / (1 + Real.log m - Real.log n)

end IntervalExplore.KT1.Supplement


