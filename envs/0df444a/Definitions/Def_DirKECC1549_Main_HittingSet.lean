-- Prove2me | Definitions.Def_DirKECC1549_Main_HittingSet
-- name    : DirKECC1549_Main_HittingSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:42:16.820824+00:00
-- url     : https://prove2.me/theorems/70e878b6-0ca3-4bd4-8c2a-949f5e530abf
-- title:
--   §3.2.1 — spanning in-trees and Algorithm 2 (HittingSet)
-- statement:
--   Let $D$ be a directed multigraph on $V=\{0,\dots,n-1\}$ and $r\in V$. A parent map $\mathrm{par}:V\to V$ describes a spanning tree $T$ of $D$ directed towards $r$ when $\mathrm{par}(r)=r$, every $v\ne r$ has an edge $v\to\mathrm{par}(v)$ of $D$, and iterating $\mathrm{par}$ from any vertex reaches $r$. The children of $v$ are the vertices $u\ne r$ with $\mathrm{par}(u)=v$.
--
--   Algorithm 2, $\mathrm{HittingSet}(T,(\deg^+(v))_{v},b)$, processes the vertices $v\ne r$ from the leaves towards the root and computes
--   $$q(v)=\deg^+(v)+\sum_{u\ \text{child of}\ v}\rho(u),\qquad \rho(v)=\begin{cases}0,& q(v)>b,\\ q(v),& q(v)\le b,\end{cases}$$
--   and returns $Z=\{v\ne r: q(v)>b\}$. The values do not depend on which postorder is used.
--
--   This is the deterministic hitting-set construction of Section 3.2.1, used for Lemma 2.
--
--   **Formalization Note** The recursion is evaluated by $n$ rounds of propagation from the leaves: after $t$ rounds the value $\rho$ is exact at every vertex whose subtree has height below $t$, and every tree on $n$ vertices has height below $n$.
-- source:
--   Loukas Georgiadis, Evangelos Kipouridis, Evangelos Kosinas, Charis Papadopoulos, Christos Pergaminelis, STOC 2027 submission #1549 (October 2026), Section 3.2.1, p.13 and Algorithm 2, p.14

import Mathlib
import Definitions.Def_DirKECC1549_Main_Graph

set_option autoImplicit false

noncomputable section

open Classical Finset

namespace DirKECC1549.Main

/-!
# Spanning in-trees and Algorithm 2 (HittingSet), §3.2.1, pp.13–14
-/

variable {n m : ℕ}

/-- `par` describes a spanning tree `T` of `D` directed towards the root `r`: `par r = r`; every
other vertex `v` has a tree edge `v → par v` that is an edge of `D`; and following parents from
any vertex reaches `r` (so `T` is acyclic and spans `V`). -/
def IsSpanningInTree (D : Fin m → Fin n × Fin n) (r : Fin n) (par : Fin n → Fin n) : Prop :=
  par r = r ∧ (∀ v, v ≠ r → ∃ e, D e = (v, par v)) ∧ ∀ v, ∃ j : ℕ, par^[j] v = r

/-- The children of `v` in the tree `par` rooted at `r`. -/
def treeChildren (r : Fin n) (par : Fin n → Fin n) (v : Fin n) : Finset (Fin n) :=
  univ.filter (fun u => u ≠ r ∧ par u = v)

/-- The values `ρ` of Algorithm 2 computed with `t` rounds of propagation from the leaves:
`q(v) = deg(v) + ∑_{u child of v} ρ(u)`, and `ρ(v) = 0` if `q(v) > b`, else `ρ(v) = q(v)`.
For a tree of height `< t` these are the values of Algorithm 2 (any postorder). -/
def alg2Rho (r : Fin n) (par : Fin n → Fin n) (deg : Fin n → ℕ) (b : ℕ) : ℕ → Fin n → ℕ
  | 0 => fun _ => 0
  | t + 1 => fun v =>
      let q := deg v + ∑ u ∈ treeChildren r par v, alg2Rho r par deg b t u
      if b < q then 0 else q

/-- The value `q(v)` of Algorithm 2, line 4 (with `n` rounds, more than the tree height). -/
def alg2Q (r : Fin n) (par : Fin n → Fin n) (deg : Fin n → ℕ) (b : ℕ) (v : Fin n) : ℕ :=
  deg v + ∑ u ∈ treeChildren r par v, alg2Rho r par deg b n u

/-- Algorithm 2, `HittingSet(T, (deg⁺(v))_v, b)`: the set of non-root vertices `v` with
`q(v) > b`. -/
def hittingSet (r : Fin n) (par : Fin n → Fin n) (deg : Fin n → ℕ) (b : ℕ) : Finset (Fin n) :=
  univ.filter (fun v => v ≠ r ∧ b < alg2Q r par deg b v)

end DirKECC1549.Main


