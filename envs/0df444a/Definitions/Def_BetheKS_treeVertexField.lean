-- Prove2me | Definitions.Def_BetheKS_treeVertexField
-- name    : BetheKS_treeVertexField
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:36:24.069598+00:00
-- url     : https://prove2.me/theorems/cfd671c6-b6ac-4800-be30-ad276dfce79c
-- title:
--   Limit messages $b_u$, messages $b_{u\to v}$ on all edges and the vertex field $V$ on the tree
-- statement:
--   On the labelled Galton–Watson tree $(T,o)\sim\widetilde\nu$, with $X_u=\phi(\sigma(u))$:
--
--   1. $b_u$ is the $L^2(\widetilde\nu)$ limit of $b^{(L)}_u=b^{(L)}_{u\to p(u)}$ as $L\to\infty$ (Proposition 5.3);
--   2. the messages on all directed edges (Definition C.1) are $b_{u\to p(u)}=b_u$, $b_{o\to v}=\Gamma^{(v)}_o\sum_{w\in\operatorname{ch}(o),w\ne v}b_{w\to o}$ and, for $u\ne o$ and a child $v$ of $u$, $b_{u\to v}=\Gamma^{(v)}_u\big(b_{p(u)\to u}+\sum_{w\in\operatorname{ch}(u),w\ne v}b_{w\to u}\big)$;
--   3. the **vertex field** (Definition 6.1, (6.1)) is
--   $$
--   V(u):=\frac{t\sum_{v\sim u}b_{v\to u}}{t^2+\deg(u)-1+\delta-t\sum_{v\sim u}\Gamma^{(u)}_v}.
--   $$
--
--   **Formalization Note** $b_u$ is defined by choice of an $L^2$ limit, which Proposition 5.3 (a milestone) asserts exists; it is unique up to null sets. The sign $s$ acts as in the graph definitions ($s=-1$: $-\Gamma$ and $-t$, as in the proof of Theorem 2.2).
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), Proposition 5.3, p.9; Definition C.1, p.19; Definition 6.1 (6.1), p.9

import Mathlib
import Definitions.Def_BetheKS_vertexFieldGraph
import Definitions.Def_BetheKS_multitypeGW

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace BetheKS

open Classical

variable {r : ℕ}

/-- The labelled tree `(T, o)` of the data `ω`, as a rooted labelled graph (root `[]`). -/
noncomputable def treeRL (ω : LTData r) : RLGraph r :=
  { V := List ℕ, G := treeGraph ω.1, lab := label ω, root := [] }

/-- `b^{(L)}_u = b^{(L)}_{u→p(u)}` on the labelled tree (Definition 5.2, p.9), for a non-root word
`u` (its parent is `u.tail`). -/
noncomputable def treeMsgUp (ϕ : Fin r → ℝ) (s t δ : ℝ) (L : ℕ) (u : List ℕ) (ω : LTData r) : ℝ :=
  msg (treeGraph ω.1) (label ω) ϕ s t δ L u u.tail

/-- **The limit message `b_u`** (Proposition 5.3, p.9, PDF p.10): the `L²(ν̃)` limit of `b^{(L)}_u`
as `L → ∞`.

**Formalization Note.** Defined by choice: a function `g ∈ L²(ν̃)` (`MemLp g 2`) with
`‖b^{(L)}_u − g‖_{L²(ν̃)} → 0`, if one exists (it is then unique up to `ν̃`-null sets), and `0`
otherwise. Membership in `L²` is part of the choice because `eLpNorm` of a non-measurable function
is a lower integral: without it the choice could add junk on a set of inner measure `0`. Proposition 5.3 (a milestone)
asserts that it exists. -/
noncomputable def bLim (p : SBMParams r) (ϕ : Fin r → ℝ) (s t δ : ℝ) (u : List ℕ) : LTData r → ℝ :=
  if h : ∃ g : LTData r → ℝ, MemLp g 2 (mgwLaw p) ∧ Tendsto (fun L : ℕ =>
      eLpNorm (fun ω => treeMsgUp ϕ s t δ L u ω - g ω) 2 (mgwLaw p)) atTop (𝓝 0)
  then h.choose else fun _ => 0

/-- The downward messages `b_{w→v}`, `v = k :: w` a child of `w` (Definition C.1, p.19, PDF p.20):
`b_{o→v} = Γ_o^{(v)} ∑_{w ∈ ch(o), w ≠ v} b_{w→o}` and, for `u ≠ o`,
`b_{u→v} = Γ_u^{(v)} (b_{p(u)→u} + ∑_{w ∈ ch(u), w ≠ v} b_{w→u})`, where `b_{w→p(w)} = b_w`
(sign `s` on the weights, as in `msg`). -/
noncomputable def bDown (p : SBMParams r) (ϕ : Fin r → ℝ) (s t δ : ℝ) (ω : LTData r) :
    List ℕ → ℕ → ℝ
  | [], k => s * cav (treeGraph ω.1) t δ [] [k] *
      ∑ j ∈ (Finset.range (ω.1 [])).erase k, bLim p ϕ s t δ [j] ω
  | j :: w, k => s * cav (treeGraph ω.1) t δ (j :: w) (k :: j :: w) *
      (bDown p ϕ s t δ ω w j +
        ∑ i ∈ (Finset.range (ω.1 (j :: w))).erase k, bLim p ϕ s t δ (i :: j :: w) ω)

/-- **The messages `b_{u→v}` on all directed edges** (Definition C.1, p.19): `b_u` if `v = p(u)`, and
the downward message if `v` is a child of `u`; `0` for non-edges. -/
noncomputable def bFull (p : SBMParams r) (ϕ : Fin r → ℝ) (s t δ : ℝ) (u v : List ℕ)
    (ω : LTData r) : ℝ :=
  if u ≠ [] ∧ v = u.tail then bLim p ϕ s t δ u ω
  else if v ≠ [] ∧ v.tail = u then bDown p ϕ s t δ ω u (v.headD 0)
  else 0

/-- **The vertex field `V`** — Dong, McKenzie, arXiv:2610.41802 (held version, sha256 4da41e16…),
Definition 6.1, p.9 (PDF p.10), (6.1): on the Galton–Watson tree,
`V(u) := t ∑_{v∼u} b_{v→u} / (t² + deg(u) − 1 + δ − t ∑_{v∼u} Γ_v^{(u)})`, with `b_{v→u}` from
Definition C.1.

**Formalization Note.** `Vtree p ϕ s t δ u ω` is `V(u)` on the labelled tree of `ω`; the planted
function is `X = ϕ ∘ σ`. With `s = −1` it is the negative-sign field of the proof of Theorem 2.2
(p.12: `−Γ_δ` for `Γ_δ`, `−t` for `t`, same denominator). -/
noncomputable def Vtree (p : SBMParams r) (ϕ : Fin r → ℝ) (s t δ : ℝ) (u : List ℕ)
    (ω : LTData r) : ℝ :=
  s * t * (∑ v ∈ (treeGraph ω.1).neighborFinset u, bFull p ϕ s t δ v u ω) /
    (t ^ 2 + ((treeGraph ω.1).degree u : ℝ) - 1 + δ -
      t * ∑ v ∈ (treeGraph ω.1).neighborFinset u, cav (treeGraph ω.1) t δ v u)

end BetheKS


