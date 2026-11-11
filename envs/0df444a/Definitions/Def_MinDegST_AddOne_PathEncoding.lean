-- Prove2me | Definitions.Def_MinDegST_AddOne_PathEncoding
-- name    : MinDegST_AddOne_PathEncoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:53:05.3004+00:00
-- url     : https://prove2.me/theorems/e6ab63cb-87aa-414e-90a1-bb620929d13a
-- title:
--   The path-encoding graph G^enc (§16.1), its s–t flows, and the chain read off an s–t path (§16.2)
-- statement:
--   Fix $G$, $F$, $k$, $\theta$, a molecular decomposition $M$ and its regions $\mathcal R$; $L$ is the set of junctions and roots of normal molecules. The directed graph $G^{enc}$ has vertices $s,t$, minus vertices $u^-$ ($u\in L$ or internal) and $R^-$ ($R\in\mathcal R$), and plus vertices $u^+$ ($u$ slack) and $R^+$ ($R\in\mathcal R$). Arcs (capacity 1 unless stated):
--   1. entry $s\to R^-$ for the region $R$ containing the root of a special molecule;
--   2. tree-descending $X^-\to Y^-$ for $X\in L$ and $Y$ a child of $X$ in the rooted molecular structure after contracting regions;
--   3. transition, for $R\in\mathcal R$, $w\in R$, $z\notin R$, $(w,z)\in E$: $R^-\to z^-$; $R^-\to L'^+$ if $z$ lies in region $L'$ and is saturated; $R^-\to z^+$ if $z$ is slack;
--   4. termination $R^+\to t$ with capacity $2\theta$, and $u^+\to t$ with capacity $\max\{k+1-\deg_F(u),2\theta\}$ for $M$-covered slack $u$ and $k+1-\deg_F(u)$ for $M$-free slack $u$.
--
--   An **$s$–$t$ flow** is $\varphi\ge0$ below the capacities with conservation at all vertices other than $s,t$; its value is the net flow out of $s$. A **simple $s$–$t$ path** repeats no vertex. A chain is **read off** a path as in the proof of Lemma 16.5: if $R_0^-,\dots,R_{\ell-1}^-$ are the region vertices of the path in order, $w_i\in R_i$ and $z_{i+1}\notin R_i$ with $(w_i,z_{i+1})\in E$ create the arc leaving $R_i^-$ on the path.
--
--   **Formalization Note.** Two readings of §16.1: the arc $R^-\to z^-$ is added only when $z^-$ exists (the paper creates no minus vertex for a node inside a region); "$Y\in B\cup R$" in item 2 is read as $Y\in L\cup\mathcal R$ ($B$ is not defined in Part III). Capacities are a function `encCap` (0 = no arc), so parallel arcs collapse into one, as in an edge set. Flows are real-valued.
--
--   The finite vertex set now contains exactly the vertex classes listed above; node vertices outside those classes are excluded. Flow conservation and flow value sum over this set.
-- source:
--   Bhattacharya, Farokhnejad, Saranurak, Wang, Faster Algorithms for Minimum Degree Spanning Tree, STOC 2027 submission (manuscript sha256 7d985d3b…), p. 40–42, §16.1 and §16.2

import Mathlib
import Definitions.Def_MinDegST_AddOne_Molecules

open Classical

namespace MinDegST.AddOne

/-! # The path-encoding graph `G^enc`, its `s`–`t` flows, and the chain read off an `s`–`t` path

Part III, §16.1–16.2 (pp. 40–42). Fix `G`, a forest `F`, the threshold `k` (`Δ⋆` in the paper),
`θ`, a molecular decomposition `M` and its region collection `𝓡`. `L` is the set of junctions and
roots of normal `M`-molecules. -/

variable {n : ℕ}

/-- Vertices of `G^enc`: `s`, `t`, minus vertices `u⁻` (nodes) and `R⁻` (regions), plus vertices
`u⁺` (nodes) and `R⁺` (regions). Only those listed in `encVerts` occur, and a node or region whose
vertex the paper does not create carries no arc. -/
inductive EncVtx (n : ℕ) where
  | s
  | t
  | minusNode (u : Fin n)
  | minusRegion (R : Finset (Fin n))
  | plusNode (u : Fin n)
  | plusRegion (R : Finset (Fin n))
  deriving DecidableEq

/-- `u ∈ L`: a junction or the root of a normal `M`-molecule. -/
def InL (F : SimpleGraph (Fin n)) (M : Finset (Molecule n)) (𝓡 : Finset (Finset (Fin n)))
    (u : Fin n) : Prop :=
  Junction F M 𝓡 u ∨ IsNormalRoot M u

/-- `c` is a child of `X` in the rooted structure of the molecules: `(X, c) ∈ E(F)` and `c` lies
below `X` (in the molecule of `c`, on the side away from its root). -/
def IsChild (F : SimpleGraph (Fin n)) (M : Finset (Molecule n)) (X c : Fin n) : Prop :=
  F.Adj X c ∧ Below F M c X

/-- Arc capacities of `G^enc` (`0` = no arc), §16.1:
1. entry `s → R⁻`, capacity 1, for the region `R` containing the root of a special molecule;
2. tree-descending `X⁻ → Y⁻`, capacity 1, for `X ∈ L` and `Y` a child of `X` after contracting the
   regions: `Y = c⁻` for a child `c` in no region, `Y = R⁻` for the region `R` containing a child;
3. transition, capacity 1, for `R ∈ 𝓡`, `w ∈ R`, `z ∉ R`, `(w, z) ∈ E`: (a) `R⁻ → z⁻` (when `z⁻`
   exists, i.e. `z` is in no region); (b) `R⁻ → L⁺` when `z` is in the region `L` and saturated, and
   `R⁻ → z⁺` when `z` is slack;
4. termination: `R⁺ → t` with capacity `2θ`; `u⁺ → t` for slack `u` with capacity
   `max{k + 1 − deg_F(u), 2θ}` if `u` is `M`-covered and `k + 1 − deg_F(u)` if `u` is `M`-free. -/
noncomputable def encCap (G F : SimpleGraph (Fin n)) (k θ : ℕ) (M : Finset (Molecule n))
    (𝓡 : Finset (Finset (Fin n))) : EncVtx n → EncVtx n → ℕ
  | .s, .minusRegion R =>
      if R ∈ 𝓡 ∧ ∃ r, Molecule.special r ∈ M ∧ r ∈ R then 1 else 0
  | .minusNode X, .minusNode c =>
      if InL F M 𝓡 X ∧ ¬ RCovered 𝓡 c ∧ IsChild F M X c then 1 else 0
  | .minusNode X, .minusRegion R =>
      if InL F M 𝓡 X ∧ R ∈ 𝓡 ∧ ∃ c ∈ R, IsChild F M X c then 1 else 0
  | .minusRegion R, .minusNode z =>
      if R ∈ 𝓡 ∧ ¬ RCovered 𝓡 z ∧ ∃ w ∈ R, z ∉ R ∧ G.Adj w z then 1 else 0
  | .minusRegion R, .plusRegion L =>
      if R ∈ 𝓡 ∧ L ∈ 𝓡 ∧ ∃ w ∈ R, ∃ z ∈ L, z ∉ R ∧ G.Adj w z ∧ Saturated k F z then 1 else 0
  | .minusRegion R, .plusNode z =>
      if R ∈ 𝓡 ∧ ∃ w ∈ R, z ∉ R ∧ G.Adj w z ∧ Slack k F z then 1 else 0
  | .plusRegion R, .t => if R ∈ 𝓡 then 2 * θ else 0
  | .plusNode u, .t =>
      if Slack k F u then
        (if Covered F M u then max (k + 1 - deg F u) (2 * θ) else k + 1 - deg F u)
      else 0
  | _, _ => 0

/-- The (finite) vertex set of `G^enc`, exactly as in §16.1: minus node vertices only for
`L` and internal nodes, and plus node vertices only for slack nodes. -/
noncomputable def encVerts (F : SimpleGraph (Fin n)) (k : ℕ) (M : Finset (Molecule n))
    (𝓡 : Finset (Finset (Fin n))) : Finset (EncVtx n) :=
  {EncVtx.s, EncVtx.t} ∪
    (Finset.univ.filter fun u => InL F M 𝓡 u ∨ Internal F M u).image EncVtx.minusNode ∪
    𝓡.image EncVtx.minusRegion ∪
    (Finset.univ.filter fun u => Slack k F u).image EncVtx.plusNode ∪ 𝓡.image EncVtx.plusRegion

/-- `φ` is an `s`–`t` flow of `G^enc`: `0 ≤ φ ≤ capacity` on every ordered pair (so `φ` vanishes
off the arcs) and flow conservation at every vertex other than `s` and `t`. -/
def IsEncFlow (G F : SimpleGraph (Fin n)) (k θ : ℕ) (M : Finset (Molecule n))
    (𝓡 : Finset (Finset (Fin n))) (φ : EncVtx n → EncVtx n → ℝ) : Prop :=
  (∀ a b, 0 ≤ φ a b ∧ φ a b ≤ (encCap G F k θ M 𝓡 a b : ℝ)) ∧
  ∀ v ∈ encVerts F k M 𝓡, v ≠ EncVtx.s → v ≠ EncVtx.t →
    ∑ u ∈ encVerts F k M 𝓡, φ u v = ∑ u ∈ encVerts F k M 𝓡, φ v u

/-- The value of a flow: net flow out of `s`. -/
noncomputable def encFlowValue (F : SimpleGraph (Fin n)) (k : ℕ) (M : Finset (Molecule n))
    (𝓡 : Finset (Finset (Fin n))) (φ : EncVtx n → EncVtx n → ℝ) : ℝ :=
  ∑ u ∈ encVerts F k M 𝓡, φ EncVtx.s u - ∑ u ∈ encVerts F k M 𝓡, φ u EncVtx.s

/-- A simple `s`–`t` path of `G^enc`: a vertex list from `s` to `t`, no vertex repeated, every
consecutive pair an arc (positive capacity). -/
def IsSimpleSTPath (G F : SimpleGraph (Fin n)) (k θ : ℕ) (M : Finset (Molecule n))
    (𝓡 : Finset (Finset (Fin n))) (p : List (EncVtx n)) : Prop :=
  p.head? = some EncVtx.s ∧ p.getLast? = some EncVtx.t ∧ p.Nodup ∧
    p.IsChain fun a b => 0 < encCap G F k θ M 𝓡 a b

/-- The transitions of a vertex list: for each region minus vertex `R⁻` of `p`, in order, the pair
`(R, the vertex following R⁻ in p)`. -/
def transitions (p : List (EncVtx n)) : List (Finset (Fin n) × EncVtx n) :=
  (p.zip p.tail).filterMap fun ab =>
    match ab.1 with
    | .minusRegion R => some (R, ab.2)
    | _ => none

/-- The chain `A = (w₀, z₁, …, w_{ℓ−1}, z_ℓ)` is read off the `s`–`t` path `p` as in the proof of
Lemma 16.5 (p. 42): if `R₀⁻, …, R_{ℓ−1}⁻` are the region minus vertices of `p` in order, then
`w_i ∈ R_i` is an endpoint of an edge `(w_i, z_{i+1}) ∈ E` with `z_{i+1} ∉ R_i` that creates the arc
leaving `R_i⁻` on `p`: that arc goes to `z_{i+1}⁻` or `z_{i+1}⁺`, or to `L⁺` for the region `L`
containing the saturated node `z_{i+1}`. -/
def ReadOff (G F : SimpleGraph (Fin n)) (k : ℕ) (p : List (EncVtx n)) (A : Chain n) : Prop :=
  A.ws.length = (transitions p).length ∧ A.zs.length = (transitions p).length ∧
  ∀ (i : ℕ) (R : Finset (Fin n)) (b : EncVtx n) (w z : Fin n),
    (transitions p)[i]? = some (R, b) → A.ws[i]? = some w → A.zs[i]? = some z →
    w ∈ R ∧ z ∉ R ∧ G.Adj w z ∧
    (b = EncVtx.minusNode z ∨ b = EncVtx.plusNode z ∨
      ∃ L, b = EncVtx.plusRegion L ∧ z ∈ L ∧ Saturated k F z)

end MinDegST.AddOne


