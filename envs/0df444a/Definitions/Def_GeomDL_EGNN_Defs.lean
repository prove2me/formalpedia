-- Prove2me | Definitions.Def_GeomDL_EGNN_Defs
-- name    : GeomDL_EGNN_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T18:13:32.23018+00:00
-- url     : https://prove2.me/theorems/34a6f420-d4cc-4566-a57e-7cc565c8c2e5
-- title:
--   §5.3, §5.5, pp. 78–84 — neighbourhoods, the three GNN flavours (33)–(35), the E(3) action and the Satorras et al. equivariant layer
-- statement:
--   This file fixes the objects of §5.3 and §5.5 of Bronstein, Bruna, Cohen and Veličković's *Geometric Deep Learning*.
--
--   **Graphs and permutations.** A graph on the nodes $V = \{1,\dots,n\}$ is given by an adjacency matrix $\mathbf A \in \mathbb R^{n\times n}$, with edge set $E = \{(u,v) : a_{uv} \neq 0\}$. The neighbourhood of a node $u$ is (11)
--   $$\mathcal N_u = \{v : (u,v) \in E \text{ or } (v,u) \in E\}.$$
--   Node features are a family $\mathbf x_u$, $u \in V$, with values in an arbitrary feature type; for features in $\mathbb R^d$ this is the book's feature matrix $\mathbf X \in \mathbb R^{n\times d}$ with rows $\mathbf x_u$. A permutation $\sigma$ of the nodes acts by its permutation matrix $\mathbf P$: row $u$ of $\mathbf{PX}$ is row $\sigma^{-1}(u)$ of $\mathbf X$, and $(\mathbf{PAP}^\top)_{uv} = a_{\sigma^{-1}(u)\sigma^{-1}(v)}$.
--
--   **The three flavours of GNN layer** (p. 79). A permutation-invariant aggregator $\bigoplus$ is a function of a multiset, so its invariance to the order of the neighbours holds by construction. With an update function $\phi$:
--   1. convolutional (33): $\mathbf h_u = \phi\big(\mathbf x_u, \bigoplus_{v\in\mathcal N_u} c_{uv}\psi(\mathbf x_v)\big)$, with fixed coefficients $c_{uv}$;
--   2. attentional (34): $\mathbf h_u = \phi\big(\mathbf x_u, \bigoplus_{v\in\mathcal N_u} a(\mathbf x_u,\mathbf x_v)\psi(\mathbf x_v)\big)$, with an attention mechanism $a$;
--   3. message passing (35): $\mathbf h_u = \phi\big(\mathbf x_u, \bigoplus_{v\in\mathcal N_u} \psi(\mathbf x_u,\mathbf x_v)\big)$, with a message function $\psi$.
--
--   Also defined is the adjacency matrix of the complete graph without self-loops ($a_{uv} = 1$ for $u \neq v$, $a_{uu} = 0$), whose neighbourhoods are $\mathcal N_u = \{v : v \neq u\}$.
--
--   **E(3) and the equivariant layer** (pp. 83–84). An element $g$ of the Euclidean group $\mathrm E(3)$ acts on $\mathbb R^3$ by $\rho(g)\mathbf x = \mathbf R\mathbf x + \mathbf b$, where $\mathbf R$ is a $3\times 3$ orthogonal matrix (a rotation or a reflection) and $\mathbf b \in \mathbb R^3$ a translation. Each node carries features $\mathbf f_u \in \mathbb R^d$ and spatial coordinates $\mathbf x_u \in \mathbb R^3$. The layer of Satorras et al. (2021) outputs
--   $$\mathbf f'_u = \phi\Big(\mathbf f_u, \bigoplus_{v\in\mathcal N_u}\psi_{\mathrm f}(\mathbf f_u,\mathbf f_v,\|\mathbf x_u-\mathbf x_v\|^2)\Big), \qquad \mathbf x'_u = \mathbf x_u + \sum_{v\neq u}(\mathbf x_u-\mathbf x_v)\,\psi_{\mathrm c}(\mathbf f_u,\mathbf f_v,\|\mathbf x_u-\mathbf x_v\|^2),$$
--   where $\psi_{\mathrm f}$ and $\psi_{\mathrm c}$ are arbitrary functions, $\psi_{\mathrm c}$ real-valued.
--
--   These objects are the common ground of the mission: the permutation equivariance of (35), the containment of the three flavours, and the E(3) equivariance of the layer are all stated on them.
--
--   **Formalization Note** The node set is `Fin n`; $\mathbb R^3$ is `EuclideanSpace ℝ (Fin 3)`; $\mathbf R$ ranges over `Matrix.orthogonalGroup (Fin 3) ℝ` (all of $O(3)$, reflections included) and acts through `Matrix.toEuclideanLin`. The aggregator $\bigoplus$ is an arbitrary function `agg : Multiset M → M'`; the update $\phi$, the messages and the output types are arbitrary. The feature update aggregates over $\mathcal N_u$, while the coordinate update sums over all $v \neq u$, as printed on p. 84.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §4.1, eq. (11), p. 34; §5.3, eqs. (33)–(35), pp. 78–79; §5.5, pp. 83–84

import Mathlib
import Definitions.Def_GeomDL_Sets_Defs

namespace GeomDL.EGNN

open Matrix

noncomputable section

/-! ### §5.3, pp. 78–80: graphs, permutations and the three flavours of GNN layer

A graph on the node set `Fin n` is given by its adjacency matrix `A : Matrix (Fin n) (Fin n) ℝ`.
Node features are a family `X : Fin n → α`, `u ↦ x_u`; for `α = Fin d → ℝ` this is exactly the
book's feature matrix `X ∈ ℝ^{n×d}` with rows `x_u` (`Matrix (Fin n) (Fin d) ℝ` unfolds to
`Fin n → Fin d → ℝ`). The feature type is left general so that a node may carry a pair
(features, coordinates), as in §5.5. -/

/-- §4.1, eq. (11), p. 34: the neighbourhood `N_u = {v : (u,v) ∈ E or (v,u) ∈ E}`, where the edge
set of an adjacency matrix `A` is `E = {(u,v) : a_{uv} ≠ 0}`. -/
def nbhd {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (u : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => A u v ≠ 0 ∨ A v u ≠ 0)

/-- §4.1, p. 32: the action of a permutation `σ ∈ Σₙ` on node features by the permutation
matrix `P`, `X ↦ PX`. Convention: row `u` of `PX` is row `σ⁻¹(u)` of `X`. -/
def permRows {n : ℕ} {α : Type*} (σ : Equiv.Perm (Fin n)) (X : Fin n → α) : Fin n → α :=
  fun u => X (σ.symm u)

/-- §5.3, eq. (33), p. 79: the convolutional flavour
`h_u = φ(x_u, ⊕_{v ∈ N_u} c_{uv} ψ(x_v))` with fixed coefficients `c_{uv}`. The
permutation-invariant aggregator `⊕` is a function `agg` of the multiset
`{{c_{uv} ψ(x_v) : v ∈ N_u}}`. -/
def convLayer {n : ℕ} {α M M' β : Type*} [SMul ℝ M] (φ : α → M' → β) (agg : Multiset M → M')
    (c : Matrix (Fin n) (Fin n) ℝ) (ψ : α → M) (X : Fin n → α) (A : Matrix (Fin n) (Fin n) ℝ) :
    Fin n → β :=
  fun u => φ (X u) (agg ((nbhd A u).val.map (fun v => c u v • ψ (X v))))

/-- §5.3, eq. (34), p. 79: the attentional flavour
`h_u = φ(x_u, ⊕_{v ∈ N_u} a(x_u, x_v) ψ(x_v))` with an attention mechanism `a` of the features. -/
def attLayer {n : ℕ} {α M M' β : Type*} [SMul ℝ M] (φ : α → M' → β) (agg : Multiset M → M')
    (a : α → α → ℝ) (ψ : α → M) (X : Fin n → α) (A : Matrix (Fin n) (Fin n) ℝ) : Fin n → β :=
  fun u => φ (X u) (agg ((nbhd A u).val.map (fun v => a (X u) (X v) • ψ (X v))))

/-- §5.3, eq. (35), p. 79: the message-passing flavour
`h_u = φ(x_u, ⊕_{v ∈ N_u} ψ(x_u, x_v))` with a message function `ψ` of receiver and sender. -/
def mpLayer {n : ℕ} {α M M' β : Type*} (φ : α → M' → β) (agg : Multiset M → M')
    (ψ : α → α → M) (X : Fin n → α) (A : Matrix (Fin n) (Fin n) ℝ) : Fin n → β :=
  fun u => φ (X u) (agg ((nbhd A u).val.map (fun v => ψ (X u) (X v))))

/-- The adjacency matrix of the complete graph without self-loops: `a_{uv} = 1` for `u ≠ v`
and `a_{uu} = 0`, so that `N_u = {v : v ≠ u}`. -/
def completeAdj (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun u v => if u = v then 0 else 1

/-! ### §5.5, pp. 83–84: E(3) and the equivariant message-passing layer -/

/-- Three-dimensional Euclidean space `ℝ³` with the Euclidean norm, home of the node spatial
coordinates `x_u`. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- §5.5, p. 83: the action `ρ(g)x = Rx + b` of an element `g ∈ E(3)` on `ℝ³`, where
`R ∈ O(3)` is an orthogonal matrix (rotations and reflections) and `b ∈ ℝ³` a translation. -/
def rigid (R : Matrix.orthogonalGroup (Fin 3) ℝ) (b : E3) (x : E3) : E3 :=
  Matrix.toEuclideanLin R.1 x + b

/-- §5.5, p. 84: the feature update of the Satorras et al. (2021) layer,
`f'_u = φ(f_u, ⊕_{v ∈ N_u} ψ_f(f_u, f_v, ‖x_u − x_v‖²))`, with node features `f_u ∈ ℝ^d`
(rows of `f`), coordinates `x_u ∈ ℝ³` and the aggregator `⊕` a function of a multiset. -/
def egnnFeat {n d : ℕ} {M M' F' : Type*} (φ : (Fin d → ℝ) → M' → F') (agg : Multiset M → M')
    (ψf : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → M) (A : Matrix (Fin n) (Fin n) ℝ)
    (f : Matrix (Fin n) (Fin d) ℝ) (x : Fin n → E3) : Fin n → F' :=
  fun u => φ (f u) (agg ((nbhd A u).val.map (fun v => ψf (f u) (f v) (‖x u - x v‖ ^ 2))))

/-- §5.5, p. 84: the coordinate update of the Satorras et al. (2021) layer,
`x'_u = x_u + Σ_{v ≠ u} (x_u − x_v) ψ_c(f_u, f_v, ‖x_u − x_v‖²)`, with a scalar-valued `ψ_c`;
the sum runs over all nodes `v ≠ u`, not over `N_u`. -/
def egnnCoord {n d : ℕ} (ψc : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (f : Matrix (Fin n) (Fin d) ℝ) (x : Fin n → E3) : Fin n → E3 :=
  fun u => x u + ∑ v ∈ Finset.univ.filter (fun v => v ≠ u),
    ψc (f u) (f v) (‖x u - x v‖ ^ 2) • (x u - x v)

/-- §5.5, p. 84: the equivariant message-passing layer `(f, x) ↦ (f', x')`. -/
def egnnLayer {n d : ℕ} {M M' F' : Type*} (φ : (Fin d → ℝ) → M' → F') (agg : Multiset M → M')
    (ψf : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → M) (ψc : (Fin d → ℝ) → (Fin d → ℝ) → ℝ → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (f : Matrix (Fin n) (Fin d) ℝ) (x : Fin n → E3) :
    (Fin n → F') × (Fin n → E3) :=
  (egnnFeat φ agg ψf A f x, egnnCoord ψc f x)

end

end GeomDL.EGNN


