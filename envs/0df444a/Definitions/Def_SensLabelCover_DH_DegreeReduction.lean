-- Prove2me | Definitions.Def_SensLabelCover_DH_DegreeReduction
-- name    : SensLabelCover_DH_DegreeReduction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:36:32.718211+00:00
-- url     : https://prove2.me/theorems/406486c9-277c-4463-b331-53b61e5d201f
-- title:
--   Expanders (Definition 4.1), the right-degree reduction $T_{DR}$ (Algorithm 1) and its recovery $R_{DR}$
-- statement:
--   An **$[n,d,\lambda]$-expander** is an undirected $d$-regular multigraph on $[n]$, given by its neighbour function $\Gamma:[n]\times[d]\to[n]$ ($\Gamma(i,k)$ is the $k$-th neighbour of $i$, parallel edges and both incidences of a loop listed with multiplicity), whose normalized adjacency operator has norm at most $\lambda$ on $\mathbf 1^\perp$.
--
--   Let $G=(U,V,E)$ be a bipartite multigraph, $D_v$ the degree of $v\in V$, and fix an even $d$, for each $v$ an $[D_v,d,\lambda]$-expander $H_v$ and an ordering $e_G(v,1),\dots,e_G(v,D_v)$ of the edges at $v$, with left endpoints $u_G(v,j)$. The **right-degree reduction** $T_{DR}(I;d)$ replaces each $v$ by the cloud $\{(v,i):i\in[D_v]\}$ and, for each $i\in[D_v]$, $k\in[d]$ and $j=\Gamma_{H_v}(i,k)$, adds an edge from $u_G(v,j)$ to $(v,i)$ carrying the projection $f_{e_G(v,j)}$; left vertices, predicates and both alphabets are unchanged. Every cloud vertex has degree $d$.
--
--   The **recovery** $R_{DR}$ maps an assignment $\pi'$ of $T_{DR}(I;d)$ to a random assignment of $I$: it copies the left labels and, independently for each $v\in V$, draws $i_v$ uniformly from $[D_v]$ and sets $\pi_V(v)=\pi'_V(v,i_v)$. It needs $D_v\ge1$ for all $v$.
--
--   Degree reduction makes every right degree equal to $d$ while losing at most $\lambda$ in value under recovery.
--
--   **Formalization Note** `IsExpander Γ λ` is the published `SmallBiasPRF.IsUndirected Γ ∧ SmallBiasPRF.IsSpectralExpander Γ λ`: undirected means symmetric incidence counts, and $\|E_\Gamma-U\|\le\lambda$ (Euclidean operator norm, $U$ the averaging matrix) is the norm on $\mathbf 1^\perp$ of the symmetric $E_\Gamma$. Symmetric incidence counts also admit an odd number of loop incidences at a vertex, so this class contains Definition 4.1's expanders. `DRData G d` holds the neighbour functions `nb v : Fin D_v → Fin d → Fin D_v` and the orderings `ord v : Fin D_v ≃ {e // right e = v}` ($[D_v]$ is 0-based). The new graph has right vertices `Σ v, Fin D_v` and edges `Σ v, Fin D_v × Fin d`. `recoverDR G hD π'` takes the proof `hD` that no right vertex is isolated, and it does not depend on $I$.
-- source:
--   Fleming, Hopkins, Yoshida, Sensitivity and Locality Lower Bounds via Low-Soundness Label Cover, STOC 2027 submission (manuscript sha256 5bfe95ad…), pp. 21–23 (PDF 24–26), Definition 4.1, Algorithm 1 and the recovery R_DR

import Mathlib
import Definitions.Def_SmallBiasPRF_IsSpectralExpander
import Definitions.Def_SensLabelCover_DH_LabelCover

open scoped BigOperators

namespace SensLabelCover.DH

/-! Fleming, Hopkins, Yoshida, *Sensitivity and Locality Lower Bounds via Low-Soundness Label
Cover*, STOC 2027 submission (manuscript sha256 5bfe95ad…), §4 (pp. 21–23, PDF pp. 24–26):
Definition 4.1 (expanders), the right-degree reduction `T_DR` (Algorithm 1) and its recovery
`R_DR`.

An `[n, d, λ]`-expander on `[n] = Fin n` is a neighbour function `Γ : Fin n → Fin d → Fin n`
(`Γ i k` is the `k`-th neighbour of `i`, parallel edges and both incidences of a loop listed
with multiplicity) that is undirected and has `‖E_Γ − U‖ ≤ λ`, using the published
`SmallBiasPRF.IsUndirected` and `SmallBiasPRF.IsSpectralExpander`. -/

noncomputable section

variable {U V E SU SV : Type}

/-- `Γ : Fin n → Fin d → Fin n` is an `[n, d, λ]`-expander (Definition 4.1): an undirected
`d`-regular multigraph whose normalized adjacency operator has norm at most `λ` on `1^⊥`
(equivalently `‖E_Γ − U‖ ≤ λ`, `U` the averaging operator). -/
def IsExpander {n d : ℕ} (Γ : Fin n → Fin d → Fin n) (lam : ℝ) : Prop :=
  SmallBiasPRF.IsUndirected Γ ∧ SmallBiasPRF.IsSpectralExpander Γ lam

/-- The data of the right-degree reduction for a graph `G` and target degree `d`: for each right
vertex `v` of degree `D_v`, a neighbour function `nb v : [D_v] × [d] → [D_v]` (the chosen
expander `H_v`) and an ordering `ord v : [D_v] ≃ {edges at v}` of the edge incidences at `v`
(`ord v j` is `e_G(v, j)`; its left endpoint is `u_G(v, j)`). -/
structure DRData [Fintype E] [DecidableEq V] (G : BGraph U V E) (d : ℕ) where
  nb : ∀ v : V, Fin (G.rdeg v) → Fin d → Fin (G.rdeg v)
  ord : ∀ v : V, Fin (G.rdeg v) ≃ {e : E // G.right e = v}

/-- Right vertices of `T_DR(I; d)`: the cloud `{(v, i) : i ∈ [D_v]}` of each `v ∈ V`. -/
abbrev DRV [Fintype E] [DecidableEq V] (G : BGraph U V E) : Type :=
  Σ v : V, Fin (G.rdeg v)

/-- Edges of `T_DR(I; d)`: one edge `(v, i, k)` for each cloud vertex `(v, i)` and `k ∈ [d]`. -/
abbrev DRE [Fintype E] [DecidableEq V] (G : BGraph U V E) (d : ℕ) : Type :=
  Σ v : V, Fin (G.rdeg v) × Fin d

/-- The edge of `G` copied to the edge `(v, i, k)`: `e_G(v, Γ_{H_v}(i, k))`. -/
def DRData.src [Fintype E] [DecidableEq V] {G : BGraph U V E} {d : ℕ} (dr : DRData G d)
    (x : DRE G d) : E :=
  (dr.ord x.1 (dr.nb x.1 x.2.1 x.2.2)).1

/-- The graph of `T_DR(I; d)` (Algorithm 1): edge `(v, i, k)` joins `u_G(v, j)` to `(v, i)`
with `j = Γ_{H_v}(i, k)`. -/
def drGraph [Fintype E] [DecidableEq V] {G : BGraph U V E} {d : ℕ} (dr : DRData G d) :
    BGraph U (DRV G) (DRE G d) where
  left x := G.left (dr.src x)
  right x := ⟨x.1, x.2.1⟩

/-- `T_DR(I; d)` (Algorithm 1): left vertices, predicates and both alphabets unchanged; the edge
`(v, i, k)` carries the projection `f_{e_G(v, j)}`, `j = Γ_{H_v}(i, k)`. -/
def tdr [Fintype E] [DecidableEq V] {G : BGraph U V E} {d : ℕ} (dr : DRData G d)
    (I : LCInst U E SU SV) : LCInst U (DRE G d) SU SV where
  P := I.P
  F x := I.F (dr.src x)

/-- The recovery `R_DR,I` (p. 22–23): copy the left labels, and for each `v ∈ V` set
`π_V(v) := π'_V(v, i_v)` with `i_v` uniform in `[D_v]`, independently over `v`. It needs every
right vertex to have positive degree (no isolated right vertices). It does not depend on the
projections or predicates of `I`. -/
def recoverDR [Fintype E] [DecidableEq V] [Fintype V] (G : BGraph U V E)
    (hD : ∀ v, 0 < G.rdeg v) (π' : Assignment U (DRV G) SU SV) :
    PMF (Assignment U V SU SV) :=
  haveI : Nonempty (∀ v : V, Fin (G.rdeg v)) := ⟨fun v => ⟨0, hD v⟩⟩
  (PMF.uniformOfFintype (∀ v : V, Fin (G.rdeg v))).map
    (fun idx => (π'.1, fun v => π'.2 ⟨v, idx v⟩))

end

end SensLabelCover.DH


