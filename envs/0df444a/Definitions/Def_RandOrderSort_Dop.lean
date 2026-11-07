-- Prove2me | Definitions.Def_RandOrderSort_Dop
-- name    : RandOrderSort_Dop
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:05:29.941149+00:00
-- url     : https://prove2.me/theorems/f5189b5f-2139-4f6c-8082-7e452b970eb4
-- title:
--   Replacement charges, top marks and local overflow
-- statement:
--   Fix a cut $\beta$ on keys, with $\beta(-\infty)=0$ and $\beta(+\infty)=1$. An operation is a phase's arrivals or its old-cell reassignments, and each request $o$ has a key or label $y(o)$ before and $z(o)$ after replacement. This module defines
--   $$\chi(o)=2|\beta(z(o))-\beta(y(o))|,\qquad D_{\mathrm{op}}=\sum_{o}\chi(o).$$
--   The placing node of a request is the least common ancestor of its canonical and destination leaves. A marked node is top-marked if it has no marked proper ancestor; a request is charged to the top-marked ancestor of its placing node, and $\Gamma(v)$ sums the charges assigned to $v$. $N_{\mathrm{op}}(v)$ counts requests with canonical leaf below $v$, $\mathrm{cap}(v)$ is the total capacity below $v$, and $v$ locally overflows when $N_{\mathrm{op}}(v)>\mathrm{cap}(v)$. Finally $\kappa=2048$, and $E_s$ is the event that a child, with $s$ leaves, of the selected $2s$-leaf parent locally overflows.
--
--   These are the objects of the deterministic accounting in Lemmas 4.1 and 4.2 and display (22).
--
--   **Formalization Note** An operation is a list of logged requests, and a node's capacity is computed from the phase's bucket capacities, which equal the initially available cells or assignment slots.
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), §4.1.1, p.20; §4.1.2, pp.21–22

import Mathlib
import Definitions.Def_RandOrderSort_empiricalSort

namespace RandOrderSort

/-! # Replacement charges, top marks and local overflow (§4.1, pp.20–22)

Kang, Fan, arXiv:2610.15438 (version of 2026-11-01), §4.1.1, p.20: "Fix a cut q distinct from every
key, and encode its two sides by β_q(x) = 1[x > q], β_q(−∞) = 0, β_q(+∞) = 1. … An operation
consists of a phase's arrivals or its old-cell reassignments. Each request o is one arrival or old
empty cell, respectively. Let y(o), z(o) be the cell's key or label before and after replacement.
Define χ_q(o) = 2|β_q(z(o)) − β_q(y(o))|, D_op(q) = ∑_{o∈O_op} χ_q(o)". §4.1.2, p.21: "Capacities
count initially available cells for arrivals, or initially unused assignment slots for
reallocation. Write cap(v) for the total capacity below node v … Let N_op(v) count requests whose
canonical leaves lie below v. The subtree locally overflows when N_op(v) > cap(v). … Mark each
request's placing node: the least common ancestor of its canonical and destination leaves, or that
leaf when they coincide. After the operation, a marked node is top-marked if it has no marked
proper ancestor. … Assign each request to its placing node's highest marked ancestor, possibly the
node itself. Let Γ_q(v) sum the charges assigned to v". p.22: "Set κ = 2048. … At each scale s,
let v be the selected parent with 2s leaves and u_1, u_2 its children, each with s leaves. Define
E_s(q) = {N_op(u_1) > cap(u_1) or N_op(u_2) > cap(u_2)}."

**Formalization Note.**
* An operation is the list `reqs` of its requests (from the run's log, `opReqs`); its tree has
  leaves `0, …, b − 1` and the capacity of leaf `ℓ` is `cap ℓ` (`phaseCap n p ℓ`: a phase's bucket
  sizes after its reallocation equal its assignment capacities).
* Nodes are pairs `(h, idx)` (see `mkTree`). `isAnc v w`: `w` lies below `v` (or `w = v`).
* `β` is the cut on keys (`rankCut` for a cut in the strict key order; `q < value` for a numerical
  threshold). Charges `χ` are natural numbers (`0` or `2`).
-/

/-- `χ_q(o) = 2|β_q(z(o)) − β_q(y(o))|`. -/
def chi (β : ℕ → Bool) (r : Req) : ℕ := if betaE β r.z = betaE β r.y then 0 else 2

/-- `D_op(q) = ∑_{o ∈ O_op} χ_q(o)`. -/
def Dop (β : ℕ → Bool) (reqs : List Req) : ℕ := (reqs.map (chi β)).sum

/-- The placing node of a request: the least common ancestor of its canonical and destination
leaves. -/
def placingNode (r : Req) : ℕ × ℕ := (lcaH r.canon r.dest, r.canon / 2 ^ lcaH r.canon r.dest)

/-- `isAnc v w`: node `w` lies below node `v` (possibly `w = v`). -/
def isAnc (v w : ℕ × ℕ) : Prop := w.1 ≤ v.1 ∧ w.2 / 2 ^ (v.1 - w.1) = v.2

/-- A node is marked when it is the placing node of some request of the operation. -/
def Marked (reqs : List Req) (v : ℕ × ℕ) : Prop := ∃ r ∈ reqs, placingNode r = v

/-- A marked node without a marked proper ancestor. -/
def TopMarked (reqs : List Req) (v : ℕ × ℕ) : Prop :=
  Marked reqs v ∧ ∀ u, isAnc u v → u ≠ v → ¬ Marked reqs u

/-- Request `r` is charged to `v`: `v` is the highest marked ancestor of `r`'s placing node. -/
def ChargedTo (reqs : List Req) (r : Req) (v : ℕ × ℕ) : Prop :=
  TopMarked reqs v ∧ isAnc v (placingNode r)

/-- `Γ_q(v)`: the sum of the charges of the requests assigned to `v`. -/
noncomputable def Gamma (β : ℕ → Bool) (reqs : List Req) (v : ℕ × ℕ) : ℕ :=
  by classical exact ((reqs.filter (fun r => decide (ChargedTo reqs r v))).map (chi β)).sum

/-- `N_op(v)`: the number of requests whose canonical leaf lies below node `(h, idx)`. -/
def Nop (reqs : List Req) (h idx : ℕ) : ℕ :=
  (reqs.filter (fun r => decide (r.canon / 2 ^ h = idx))).length

/-- `cap(v)`: the total capacity of the leaves below node `(h, idx)` of a `b`-leaf tree. -/
def capNode (b : ℕ) (cap : ℕ → ℕ) (h idx : ℕ) : ℕ :=
  ∑ ℓ ∈ (Finset.range b).filter (fun ℓ => ℓ / 2 ^ h = idx), cap ℓ

/-- Node `(h, idx)` locally overflows: `N_op(v) > cap(v)`. -/
def Overflows (reqs : List Req) (b : ℕ) (cap : ℕ → ℕ) (h idx : ℕ) : Prop :=
  capNode b cap h idx < Nop reqs h idx

/-- `κ = 2048`. -/
def kappa : ℕ := 2048

/-- `E_s(q)` at scale `s = 2^h`: a child (height `h`) of the selected parent (height `h + 1`, the
node containing the cut) locally overflows. `tr` is the operation's tree. -/
def Es (β : ℕ → Bool) (tr : Tree) (reqs : List Req) (cap : ℕ → ℕ) (h : ℕ) : Prop :=
  Overflows reqs tr.leaves cap h (2 * (cutLeaf β tr / 2 ^ (h + 1))) ∨
    Overflows reqs tr.leaves cap h (2 * (cutLeaf β tr / 2 ^ (h + 1)) + 1)

/-- The number of requests charged to `v`. -/
noncomputable def nCharged (reqs : List Req) (v : ℕ × ℕ) : ℕ :=
  by classical exact (reqs.filter (fun r => decide (ChargedTo reqs r v))).length

end RandOrderSort


