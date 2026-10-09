-- Prove2me | Definitions.Def_OneTwoThree_Weighting_STFlow
-- name    : OneTwoThree_Weighting_STFlow
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:54:23.625609+00:00
-- url     : https://prove2.me/theorems/f4815a21-4a9c-454f-9209-859b749a5875
-- title:
--   Integral $s$-$t$-flows on a finite directed multigraph with capacities
-- statement:
--   Let $\mathcal N$ be a finite directed multigraph network: a set of nodes, a finite set $A$ of arcs, each arc $a$ having a tail $\mathrm{tail}(a)$, a head $\mathrm{head}(a)$ and a capacity $c(a)\in\mathbb N$, together with a source node $s$ and a sink node $t$. Parallel arcs are allowed, since arcs are elements of $A$ and not pairs of nodes.
--
--   An *integral $s$-$t$-flow* is a function $\varphi:A\to\mathbb N$ such that
--
--   1. $\varphi(a)\le c(a)$ for every arc $a$ (capacity constraints), and
--   2. for every node $x\ne s,t$, flow conservation holds:
--   $$\sum_{a:\ \mathrm{head}(a)=x}\varphi(a)=\sum_{a:\ \mathrm{tail}(a)=x}\varphi(a).$$
--
--   The *value* of $\varphi$ is the net flow out of the source,
--   $$|\varphi|=\sum_{a:\ \mathrm{tail}(a)=s}\varphi(a)-\sum_{a:\ \mathrm{head}(a)=s}\varphi(a),$$
--   an integer.
--
--   This is the general notion of flow used in Lemma 4 of Keusch's paper, where it is applied to the auxiliary network $G_{C,F,\sigma}$.
--
--   **Formalization Note** Flows are integral (values in $\mathbb N$); this is the form in which the paper uses the flow of Lemma 4 ("As all edges have capacity 1, there are $|F|$ edge-disjoint $s$-$t$-paths", p. 5), and with integer capacities an integral maximum flow exists by the integrality theorem. The value is computed in $\mathbb Z$ so that no truncated subtraction occurs.
-- source:
--   Keusch, A Solution to the 1-2-3 Conjecture, arXiv:2303.02611v4, p. 4, Lemma 4 (the notion of s-t-flow in a directed multigraph network with capacities)

import Mathlib

namespace OneTwoThree.Weighting

open Finset

variable {N α : Type*} [Fintype α] [DecidableEq N]

/-- An integral `s`-`t`-flow on a finite directed multigraph whose arcs are indexed by `α`, with
tail and head maps `tail head : α → N` and capacities `cap : α → ℕ`: `φ` respects every capacity,
and at every node other than `s` and `t` the total flow on entering arcs equals the total flow on
leaving arcs. -/
def IsSTFlow (tail head : α → N) (cap : α → ℕ) (s t : N) (φ : α → ℕ) : Prop :=
  (∀ a, φ a ≤ cap a) ∧
    ∀ x, x ≠ s → x ≠ t →
      ∑ a ∈ univ.filter (fun a => head a = x), φ a = ∑ a ∈ univ.filter (fun a => tail a = x), φ a

/-- The value of a flow `φ`: the net flow out of the source `s`, as an integer. -/
def flowValue (tail head : α → N) (s : N) (φ : α → ℕ) : ℤ :=
  (∑ a ∈ univ.filter (fun a => tail a = s), (φ a : ℤ)) -
    ∑ a ∈ univ.filter (fun a => head a = s), (φ a : ℤ)

end OneTwoThree.Weighting


