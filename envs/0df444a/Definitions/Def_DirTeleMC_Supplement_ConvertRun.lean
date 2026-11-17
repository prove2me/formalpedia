-- Prove2me | Definitions.Def_DirTeleMC_Supplement_ConvertRun
-- name    : DirTeleMC_Supplement_ConvertRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:38:29.195796+00:00
-- url     : https://prove2.me/theorems/c3c12c90-a8fe-4b5d-8774-20a04ff0acbe
-- title:
--   CONVERT: reading a schedule off an arborescence of $G_\theta$
-- statement:
--   Let $A'$ be an out-arborescence of $G_\theta$ rooted at $(s,0)$ that contains all sinks. For every vertex $v$ of $G$ with a state node in $A'$ let
--   $$\tau(v)=\min\{t:(v,t)\in A'\},$$
--   and for $v\neq s$ let $p(v)$ be the vertex $u$ such that the call node $c(u,\tau(v)-1)$ is the parent of $(v,\tau(v))$ in $A'$. The arcs $(p(v),v)$ form an out-arborescence $T'$ of $G$ rooted at $s$.
--
--   **CONVERT** returns the schedule in which every vertex $v$ calls the vertices $w$ with $p(w)=v$ in non-decreasing order of $\tau(w)$, one per round, starting in the round after $v$ is informed. The relation $\mathrm{ConvertRun}(I,\theta,A',S)$ holds when $S$ is such a schedule for some order of the children with equal $\tau$.
--
--   For the running-time claim of Theorem B.8(ii), the input $(G,\theta,A')$ is encoded as the instance, $\theta$ in binary, and for every node of $G_\theta$ (in a fixed order) one membership bit and the encoding of its parent.
--
--   **Formalization Note** The schedule along $T'$ with a child order is the published busy schedule `Arb.arbSchedule`. The source names no encoding; the length of the chosen one is polynomial in the size of $G_\theta$ and conversely.
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), Algorithm 3, lines 1–9, pp.33–34 (PDF pp.34–35); proof of Theorem B.8(ii), p.35 (PDF p.36)

import Mathlib
import Definitions.Def_DirTeleMC_Supplement_TEArb
import Definitions.Def_DirTeleMC_arbSchedule
import Definitions.Def_DirTeleMC_encInst

namespace DirTeleMC.Supplement

open DirTeleMC OnlineCRS.Combine

/-- `τ(v)` of CONVERT (Algorithm 3, line 3, p.34): the least `t` with `(v, t) ∈ A′`, for a vertex `v` that has a
state node in `A′` (`0` otherwise; such vertices are not used). -/
noncomputable def convTau {n : ℕ} (A : TEArb n) (v : Fin n) : ℕ := by
  classical
  exact if h : ∃ t, TENode.state v t ∈ A.verts then Nat.find h else 0

/-- `p(v)` of CONVERT (Algorithm 3, line 6, p.34): "the vertex u such that c(u, τ(v) − 1) is the parent of
(v, τ(v)) in A′". If the parent of `(v, τ(v))` is not a call node (which happens only for `v = s`), the value is `v`
itself (not used). -/
noncomputable def convParent {n : ℕ} (A : TEArb n) (v : Fin n) : Fin n :=
  match A.parent (TENode.state v (convTau A v)) with
  | .call u _ => u
  | _ => v

/-- The out-arborescence `T′` of `G` read off by CONVERT (proof of Theorem B.8(ii), p.35: "the arcs (p(v), v) form
an out-arborescence T′ of G rooted at s"): root `s`, vertices the `v` with a state node in `A′`, parent `p(v)` for
`v ≠ s` (and `s` for `s`). -/
noncomputable def convTree (I : Inst) (A : TEArb I.n) : Arb I.n := by
  classical
  exact { root := I.s
          verts := Finset.univ.filter fun v => ∃ t, TENode.state v t ∈ A.verts
          parent := fun v => if v = I.s then I.s else convParent A v }

/-- **CONVERT** (Algorithm 3, lines 1–9, pp.33–34).
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), Algorithm 3, line 8, p.34: "return the schedule in which every vertex v of G calls
the vertices w with p(w) = v in non-decreasing order of τ(w), one per round, starting in the round after it is
informed".

`ConvertRun I θ A S`: for some child order `ord` of the tree `T′ = convTree I A` that lists the children of every
vertex in non-decreasing order of `τ`, `S` is the schedule along `T′` with the child order `ord` (every vertex calls
its children consecutively in that order, starting in the round after it is informed in `S`).

**Formalization Note.** CONVERT leaves the order among children with equal `τ` open; the relation contains every
such order. The schedule along an arborescence is the published `Arb.arbSchedule`. `θ` is not used by CONVERT
itself; it is kept so that the relation names the digraph `G_θ` whose arborescence is converted. -/
def ConvertRun (I : Inst) (_θ : ℕ) (A : TEArb I.n) (S : Schedule I.n) : Prop :=
  ∃ ord : Fin I.n → List (Fin I.n),
    (convTree I A).IsChildOrder ord ∧
    (∀ u, (ord u).Pairwise fun a b => convTau A a ≤ convTau A b) ∧
    S = (convTree I A).arbSchedule ord

/-- The input of CONVERT as one object: an instance, a horizon `θ`, and an arborescence of `G_θ`. -/
structure ConvInput where
  I : Inst
  θ : ℕ
  A : TEArb I.n

/-- The nodes of `G_θ` in a fixed order: the state nodes `(v, t)` (`v` ascending, then `t = 0, …, θ`), the call nodes
`c(v, t)` (`t = 0, …, θ − 1`), and the sinks `x̂` (`x ∈ K` ascending). -/
def teNodes (I : Inst) (θ : ℕ) : List (TENode I.n) :=
  ((List.finRange I.n).flatMap fun v => (List.range (θ + 1)).map fun t => TENode.state v t) ++
    ((List.finRange I.n).flatMap fun v => (List.range θ).map fun t => TENode.call v t) ++
    (((List.finRange I.n).filter fun x => x ∈ I.K).map TENode.sink)

/-- Encoding of a node: its kind (`0` state, `1` call, `2` sink), its vertex and its time, in binary, each followed by
the separator `3`. -/
def encNode {n : ℕ} : TENode n → List Sym
  | .state v t => encNat 0 ++ [3] ++ encNat v.val ++ [3] ++ encNat t ++ [3]
  | .call v t => encNat 1 ++ [3] ++ encNat v.val ++ [3] ++ encNat t ++ [3]
  | .sink x => encNat 2 ++ [3] ++ encNat x.val ++ [3] ++ encNat 0 ++ [3]

/-- **Encoding of the input of CONVERT** (Theorem B.8(ii), p.34: "computed in polynomial time"): the instance
(`encInst`), `θ` in binary, and then, for every node `z` of `G_θ` in the order of `teNodes`, one bit saying whether
`z ∈ A′` and the encoding of the parent of `z`.

**Formalization Note.** The source names no machine or encoding. The input length is polynomial in the size of
`G_θ` (it has `O(n θ)` nodes, plus the `n²` bits of the adjacency matrix), and the size of `G_θ` is polynomial in the
input length, so "polynomial in the size of `G_θ`" and "polynomial in the input length" agree. -/
def encConv (X : ConvInput) : List Sym :=
  encInst X.I ++ encNat X.θ ++ [3] ++
    (teNodes X.I X.θ).flatMap fun z => [bit (decide (z ∈ X.A.verts)), 3] ++ encNode (X.A.parent z)

end DirTeleMC.Supplement


