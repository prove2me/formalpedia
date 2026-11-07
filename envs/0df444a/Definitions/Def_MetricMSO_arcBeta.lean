-- Prove2me | Definitions.Def_MetricMSO_arcBeta
-- name    : MetricMSO_arcBeta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:42:16.617205+00:00
-- url     : https://prove2.me/theorems/3c990f0f-8ace-47cb-bbe2-e6ebceeeb3ec
-- title:
--   Arcs of a cycle, the signs $\varepsilon_P$ and the differences $\beta^\pm_{P,Q}$
-- statement:
--   An $a$-$b$ **arc** of $C$ is a path subgraph of $G[C]$ with endpoints $a,b$; when $a=b$ the stationary arc is allowed. For an oriented edge $(r,z)$, the sign $\varepsilon_P(r,z)$ is $1$ if the traversal of $P$ uses the edge from $r$ to $z$, $-1$ if it uses it in the opposite direction, and $0$ otherwise. For two arcs $P,Q$,
--   $$\beta^+_{P,Q}(r,z):=\varepsilon_P(r,z)-\varepsilon_Q(r,z),\qquad\beta^-_{P,Q}(r,z):=\varepsilon_P(r,z)+\varepsilon_Q(r,z).$$
--
--   **Formalization Note** An arc is a walk with `Walk.IsPath` and all vertices in `C`; `Walk.nil` is the stationary arc. Either of the two arcs between distinct endpoints qualifies, as on the page. The sign $\eta\in\{+,-\}$ is a `Bool` with `true` for $+$.
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c586330b037548a2b4a977081284996698f39c1b55c17b91cb81a536d3dd9), §4.1, p.25 (PDF 27)

import Mathlib

namespace MetricMSO

/-- **An arc of the vertex set `C`** (§4.1, p.25 (PDF 27)): "An a-b arc of C is a path subgraph of
G[C] with endpoints a and b, and when a = b, we allow the stationary arc consisting only of a". For a
walk `p` from `a` to `b`: `p` is a path (`Walk.nil` is the stationary arc) all of whose vertices lie
in `C`.

**Formalization Note** Used for `C` with `G[C]` a cycle, so either of the two arcs between distinct
endpoints qualifies, as on the page. -/
def IsArc {V : Type} {G : SimpleGraph V} (C : Finset V) {a b : V} (p : G.Walk a b) : Prop :=
  p.IsPath ∧ ∀ x ∈ p.support, x ∈ C

open Classical in
/-- **The traversal sign `ε_P(r, z)`** of an arc, §4.1, p.25 (PDF 27): "We define εP(r, z) to be 1
if the traversal of P from s to t uses the edge from r to z, to be −1 if it uses that edge in the
opposite direction, and to be 0 if it does not use the edge."

For a walk `p` from `s` to `t`, `arcEps p r z` is `1` if `p` traverses the dart `(r, z)`, `−1` if it
traverses `(z, r)`, and `0` otherwise.

**Formalization Note** For a path (the only case used) an edge is traversed at most once, so the
cases are exclusive; a stationary arc (`Walk.nil`) has all signs `0`. -/
noncomputable def arcEps {V : Type} {G : SimpleGraph V} {s t : V} (p : G.Walk s t) (r z : V) : ℤ :=
  if (r, z) ∈ p.darts.map (·.toProd) then 1
  else if (z, r) ∈ p.darts.map (·.toProd) then -1 else 0

/-- **The arc differences `β^±_{P,Q}`**, §4.1, p.25 (PDF 27): "β+_{P,Q}(r, z) := εP(r, z) − εQ(r, z),
and β−_{P,Q}(r, z) := εP(r, z) + εQ(r, z)."

`arcBeta true p q r z = β⁺_{P,Q}(r, z)` and `arcBeta false p q r z = β⁻_{P,Q}(r, z)`, where `p` is
the traversal of `P` from `s` to `t` and `q` that of `Q` from `u` to `v`.

**Formalization Note** `η ∈ {+, −}` is a `Bool`: `true` is `+`, `false` is `−`. -/
noncomputable def arcBeta {V : Type} {G : SimpleGraph V} {s t u v : V} (η : Bool) (p : G.Walk s t)
    (q : G.Walk u v) (r z : V) : ℤ :=
  if η then arcEps p r z - arcEps q r z else arcEps p r z + arcEps q r z

end MetricMSO


