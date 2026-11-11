-- Prove2me | Definitions.Def_EuclidKSteiner_TermTree
-- name    : EuclidKSteiner_TermTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:44.953515+00:00
-- url     : https://prove2.me/theorems/18b94cd7-5101-405b-b889-0116d4873b04
-- title:
--   Trees on the terminals, bottleneck lengths $\ell$ and the attachment value $\Phi$
-- statement:
--   A **terminal tree** is a finite set $P$ with a tree $M$ spanning $P$ and edge weights $w\ge0$ on $M$. In §§3–4 it is the fixed minimum spanning tree of $G[P]$; in §3.4 and §5 any tree with nonnegative weights.
--
--   1. For $u,v\in P$ let $M[u,v]$ be the unique path from $u$ to $v$ in $M$. The **bottleneck length** is
--   $$\ell(u,v)=\max_{e\in M[u,v]}w(e),\qquad \ell(u,u)=0 .$$
--   2. For $A\subseteq P$ the **attachment value** is the minimum spanning tree weight of the complete graph on $A$ with edge weights $\ell$,
--   $$\Phi(A)=w\bigl(\mathrm{MST}(A,\ell)\bigr),$$
--   with $\Phi(\emptyset)=0$ and $\Phi(A)=0$ when $|A|=1$.
--
--   $\Phi(A)$ is the backbone weight saved by joining the terminals of $A$ into one component; the completion formula and the representative-family machinery of the paper are stated in terms of $\Phi$.
--
--   **Formalization Note** $\ell(u,v)$ is the maximum of the path maxima in the two directions; since the path from $v$ to $u$ is the reverse path, both are equal, and the maximum only makes the symmetry of $\ell$ hold by definition.
-- source:
--   Bhore, Kisfaludi-Bak, Marx, Odak, Parameterized Tractability of Euclidean k-Steiner Tree, STOC 2027 submission (manuscript sha256 75361687…), §3.2, p.9 (PDF p.11), (3.1) p.10 (PDF p.12); §3.4 p.13 (PDF p.15); Theorem 3.8 p.12 (PDF p.14)

import Mathlib
import Definitions.Def_EuclidKSteiner_SpanningTree

namespace EuclidKSteiner

open Classical

/-!
# A weighted tree on the terminals, bottleneck lengths ℓ and the attachment value Φ

Bhore, Kisfaludi-Bak, Marx, Odak, *Parameterized Tractability of Euclidean k-Steiner Tree*,
STOC 2027 submission (manuscript sha256 75361687…), §3, pp.8–10 (PDF pp.10–12):
"For u, v ∈ P, write M[u, v] for the unique path in M from u to v." "For u, v ∈ P, define the
bottleneck length ℓ(u, v) = max_{e∈M[u,v]} w(e), ℓ(u, u) = 0." "For a nonempty set A ⊆ P, define
Φ(A) = w(MST(A, ℓ)). (3.1) Here (A, ℓ) is the complete graph on A with edge weights ℓ. Set Φ(∅) = 0;
also Φ(A) = 0 when |A| = 1."

**Formalization Note**
* A `TermTree V` is a tree `M` (a set of unordered pairs) spanning the finite set `P ⊆ V` with
  nonnegative edge weights `w`. In §§3–4 it is the fixed minimum spanning tree of `G[P]`; §3.4 and
  §5 allow any tree with nonnegative weights ("The construction also applies when M is any tree with
  nonnegative edge weights", p.13; Theorem 3.8).
* `pathMax M w u v` is the largest weight on the path from `u` to `v` in `M` (any walk reduced to a
  path; in a tree the path is unique), `0` for `u = v`. `ℓ u v` is `max (pathMax u v) (pathMax v u)`:
  the path from `v` to `u` is the reverse path with the same edges, so the two agree and the max only
  makes the symmetry of `ℓ` hold by definition. Outside `P` the value is irrelevant.
-/

/-- A **tree on the terminal set** `P`: a set `M` of unordered pairs forming a spanning tree of `P`
(in the complete graph on `P`), with edge weights `w`, nonnegative on `M`.
Source: Bhore, Kisfaludi-Bak, Marx, Odak, §3 p.8 (PDF p.10), §3.4 p.13 (PDF p.15), Theorem 3.8 p.12
(PDF p.14): "Let M be a tree on a set P of n vertices where edges have non-negative weights." -/
structure TermTree (V : Type*) [DecidableEq V] where
  /-- The terminal set. -/
  P : Finset V
  /-- The tree edges. -/
  M : Finset (Sym2 V)
  /-- Edge weights. -/
  w : Sym2 V → ℝ
  /-- `M` is a spanning tree of `P`. -/
  isTree : IsSpanningTree P id M M
  /-- The weights of tree edges are nonnegative. -/
  w_nonneg : ∀ e ∈ M, 0 ≤ w e

variable {V : Type*} [DecidableEq V]

/-- The largest edge weight on the path `M[u, v]` of the tree `M`, and `0` when `u = v` or when `u`
and `v` are not joined in `M`. -/
noncomputable def TermTree.pathMax (T : TermTree V) (u v : V) : ℝ :=
  if u = v then 0 else
  if h : (SimpleGraph.fromEdgeSet (T.M : Set (Sym2 V))).Reachable u v then
    ((h.some.toPath : (SimpleGraph.fromEdgeSet (T.M : Set (Sym2 V))).Path u v).1.edges.map
      T.w).foldr max 0
  else 0

/-- The **bottleneck length** `ℓ(u, v) = max_{e ∈ M[u,v]} w(e)`, `ℓ(u, u) = 0`.
Source: Bhore, Kisfaludi-Bak, Marx, Odak, §3.2, p.9 (PDF p.11). -/
noncomputable def TermTree.ell (T : TermTree V) (u v : V) : ℝ :=
  max (T.pathMax u v) (T.pathMax v u)

/-- `ℓ` as a function of an unordered pair. -/
noncomputable def TermTree.ellSym (T : TermTree V) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u v => T.ell u v, fun u v => by simp [TermTree.ell, max_comm]⟩

/-- The **attachment value** `Φ(A) = w(MST(A, ℓ))`: the minimum spanning tree weight of the complete
graph on `A` with edge weights `ℓ` (3.1); `Φ(∅) = 0` and `Φ(A) = 0` when `|A| = 1`.
Source: Bhore, Kisfaludi-Bak, Marx, Odak, §3.2, (3.1), p.10 (PDF p.12). -/
noncomputable def TermTree.Phi (T : TermTree V) (A : Finset V) : ℝ :=
  mstWeightOn A id (completeEdges A) T.ellSym

end EuclidKSteiner


