-- Prove2me | Definitions.Def_MetricTSPSublinear_fragments
-- name    : MetricTSPSublinear_fragments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-27T06:04:42.205943+00:00
-- url     : https://prove2.me/theorems/8ce1b431-07c7-56b9-96fd-efb2589eba04
-- title:
--   Split set and MST fragments of a rooted forest
-- statement:
--   Let a rooted forest on $V=\{0,\dots,n-1\}$ be given by a parent map $\mathrm{par}$ (roots are fixed points).
--
--   1. `Anc par u v`: $v$ is an ancestor-or-self of $u$ ($v=\mathrm{par}^k(u)$ for some $k$); `sub par v` is the subtree of $v$, the set of its descendants including $v$.
--   2. `Fsplit par R S` is the split set $F_{\mathrm{split}}$: the roots $R$ together with all ancestors-or-self of the sampled vertices $S$, i.e. the vertices of the paths from the sampled vertices to their roots.
--   3. `frag par F u` is the fragment of $u$: the connected piece containing $u$ of the vertices outside $F$, connected through parent edges whose both endpoints are outside $F$.
--
--   In the sublinear metric TSP algorithm, $F_{\mathrm{root}}$ is the rooted MSF for the sampled roots $S_{\mathrm{root}}$, $S=S_{\mathrm{split}}$ is a further uniform sample, and the fragments are the small pieces of the MST the algorithm explores locally.
-- source:
--   Azarmehr–Behnezhad 2026, Metric TSP in Sublinear Time: Breaking Two Approximation, https://arxiv.org/abs/2611.04283, §5.1, p.15 (PDF p.17): definition of F_split and the fragments.

import Mathlib

open Classical

namespace MetricTSPSublinear.Fragments

open Finset

noncomputable section

variable {n : ℕ}


/-- `v` is an ancestor-or-self of `u`. -/
def Anc (par : Fin n → Fin n) (u v : Fin n) : Prop := ∃ k, par^[k] u = v

/-- The subtree of `v`: all `u` having `v` as ancestor-or-self. -/
def sub (par : Fin n → Fin n) (v : Fin n) : Finset (Fin n) := univ.filter (fun u => Anc par u v)

/-- `Fsplit = R ∪ {ancestors-or-self of vertices in S}`. -/
def Fsplit (par : Fin n → Fin n) (R S : Finset (Fin n)) : Finset (Fin n) :=
  R ∪ univ.filter (fun v => ∃ x ∈ S, Anc par x v)

/-- Parent edges between two non-`F` vertices. -/
def FragRel (par : Fin n → Fin n) (F : Finset (Fin n)) (a b : Fin n) : Prop :=
  a ∉ F ∧ b ∉ F ∧ par a = b

/-- The fragment of `u`: its class under the equivalence closure of `FragRel`
(meaningful for `u ∉ F`). -/
def frag (par : Fin n → Fin n) (F : Finset (Fin n)) (u : Fin n) : Finset (Fin n) :=
  univ.filter (fun w => Relation.EqvGen (FragRel par F) u w)


end

end MetricTSPSublinear.Fragments


