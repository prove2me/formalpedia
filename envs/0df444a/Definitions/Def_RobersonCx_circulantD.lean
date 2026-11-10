-- Prove2me | Definitions.Def_RobersonCx_circulantD
-- name    : RobersonCx_circulantD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:40.706443+00:00
-- url     : https://prove2.me/theorems/a860587d-aecd-4795-8f51-b52df3908243
-- title:
--   The circulant $D^{(r)}_n=C_n(\{1,r\})$ and its split $B^{(r)}_n$
-- statement:
--   Fix integers $r\ge 2$ and $n>2r$. $D^{(r)}_n$ is the graph on $\mathbb Z_n$ with edges
--   $$\{i,i+1\}\ \text{(short edges)}\quad\text{and}\quad\{i,i+r\}\ \text{(long edges)}\qquad(i\in\mathbb Z_n),$$
--   the circulant graph $C_n(\{1,r\})$.
--
--   $B^{(r)}_n$ is obtained by splitting every vertex of $D^{(r)}_n$: its vertices are $\{u_i,v_i: i\in\mathbb Z_n\}$ and its edges are
--   $$v_iu_i\ \text{(spokes)},\qquad v_iu_{i+1}\ \text{(short edges)},\qquad v_iu_{i+r}\ \text{(long edges)}\qquad(i\in\mathbb Z_n).$$
--
--   For suitable $r,q$ (e.g. $r=5$, $q=91$), $D^{(r)}_q$ and $B^{(r)}_q$ are the graphs $H$, $H'$ of the counterexamples, and $D^{(r)}_{qm}$, $B^{(r)}_{qm}$ the source graphs whose rotations have them as orbit quotients.
--
--   **Formalization Note** $D^{(r)}_n$ is Mathlib's `circulantGraph {1, r}` on `ZMod n`; $B^{(r)}_n$ is `SimpleGraph.fromRel` of the relation $v_i\sim u_i,u_{i+1},u_{i+r}$ on `ZMod n ⊕ ZMod n` with `Sum.inl i` $=u_i$ and `Sum.inr i` $=v_i$. The definitions accept every $n,r$; every statement using them assumes $r\ge2$ and $n>2r$ (which also excludes `ZMod 0 = ℤ`).
-- source:
--   Kristjánsson, Counterexamples to the Strong Roberson Conjecture, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), §4.1, p.8 (PDF p.10), eq. (3)

import Mathlib

set_option autoImplicit false

namespace RobersonCx

/-- `D^(r)_n`, the graph on `ℤ_n` with short edges `{i, i + 1}` and long edges `{i, i + r}` (`i ∈ ℤ_n`)
(Kristjánsson, *Counterexamples to the Strong Roberson Conjecture*, arXiv:2610.03550 (version of 2 November 2026, sha256 1b70a7c6…), §4.1, p.8 (PDF p.10)); the circulant `C_n({1, r})`.

**Formalization Note** Mathlib's `circulantGraph {1, r}` on `ZMod n`: `u ~ v` iff `u ≠ v` and `u − v` or `v − u`
lies in `{1, r}`. The paper fixes `r ≥ 2` and `n > 2r`; every statement using `D^(r)_n` carries these
hypotheses (which also exclude `ZMod 0 = ℤ`). -/
def circulantD (n r : ℕ) : SimpleGraph (ZMod n) :=
  SimpleGraph.circulantGraph ({1, (r : ZMod n)} : Set (ZMod n))

/-- The generating relation of `B^(r)_n`: `v_i` (`Sum.inr i`) is related to `u_i`, `u_{i+1}` and `u_{i+r}`
(`Sum.inl`), eq. (3), p.8. -/
def splitRel (n r : ℕ) : ZMod n ⊕ ZMod n → ZMod n ⊕ ZMod n → Prop
  | Sum.inr i, Sum.inl j => j = i ∨ j = i + 1 ∨ j = i + (r : ZMod n)
  | _, _ => False

/-- `B^(r)_n` (§4.1, p.8 (PDF p.10)): vertices `{u_i, v_i : i ∈ ℤ_n}` and edges `v_iu_i`, `v_iu_{i+1}`, `v_iu_{i+r}`
(`i ∈ ℤ_n`), eq. (3): spokes, short edges and long edges.

**Formalization Note** The vertex type is `ZMod n ⊕ ZMod n` with `Sum.inl i = u_i` and `Sum.inr i = v_i`; the
graph is `SimpleGraph.fromRel` of `splitRel` (symmetrized). Every statement using `B^(r)_n` carries `r ≥ 2` and
`n > 2r`. -/
def splitB (n r : ℕ) : SimpleGraph (ZMod n ⊕ ZMod n) :=
  SimpleGraph.fromRel (splitRel n r)

end RobersonCx


