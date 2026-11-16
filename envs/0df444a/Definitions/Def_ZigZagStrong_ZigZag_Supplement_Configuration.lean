-- Prove2me | Definitions.Def_ZigZagStrong_ZigZag_Supplement_Configuration
-- name    : ZigZagStrong_ZigZag_Supplement_Configuration
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:13:34.642211+00:00
-- url     : https://prove2.me/theorems/d1e0f312-c5e6-4ece-9eef-191e4a136e7f
-- title:
--   Configuration multigraph, normalized adjacency and rooted neighbourhoods
-- statement:
--   Let $d=(d_1,\dots,d_n)$ be a degree sequence. Vertex $i$ owns $d_i$ **half-edges**; a **pairing** is a perfect matching of all half-edges, encoded as a fixed-point-free involution $\tau$. The **configuration multigraph** of $\tau$ keeps loops and multiple edges: its adjacency matrix is
--   $$A(i,j)=\#\{x\ \text{a half-edge of } i : \tau(x)\ \text{is a half-edge of } j\},$$
--   so a loop at $i$ adds $2$ to $A(i,i)$ and the row sums are the degrees. With $D_n=\operatorname{diag}(d_1,\dots,d_n)$ the **symmetric normalized adjacency** is
--   $$W=D_n^{-1/2}AD_n^{-1/2},\qquad W(i,j)=\frac{A(i,j)}{\sqrt{d_id_j}}.$$
--   Its eigenvalues with multiplicity are listed as $\omega_1\ge\omega_2\ge\dots\ge\omega_n$; the file records $\omega_2$, the number $\#\{i:\omega_i>t\}$ of eigenvalues above a threshold $t$, and the empirical average $\frac1n\sum_i f(\omega_i)=\int f\,d\mu_W$ against the empirical spectral measure $\mu_W=\frac1n\sum_i\delta_{\omega_i}$.
--
--   A **rooted multigraph** is a vertex type with adjacency counts and a root; a **rooted isomorphism** is a bijection preserving every adjacency count and the root. The **radius-$R$ neighbourhood** of a vertex $v$ is the sub-multigraph induced by the vertices at graph distance at most $R$ from $v$, rooted at $v$.
--
--   These are the objects of §4 of the paper, reusable for any work on configuration models with arbitrary bounded degrees.
--
--   **Formalization Note** Eigenvalues are the roots of the characteristic polynomial of the real symmetric matrix $W$; $\omega_2$ is read off the sorted list and is only meaningful for $n\ge2$.
-- source:
--   Gal Maor, Alon Dogon, STOC 2027 submission #371 (October 2026), §4, p. 16 (configuration model, $A_n$, $D_n$, $W_n$, $\omega_i$) and p. 17 (radius-$R$ neighbourhoods).

import Mathlib

set_option autoImplicit false
noncomputable section

namespace ZigZagStrong.ZigZag.Supplement
open scoped BigOperators

/-- Half-edges of a degree sequence `deg` on `n` vertices: vertex `i` owns `deg i` of them.
Source: submission #371, §4, p. 16. -/
abbrev HalfEdge {n : ℕ} (deg : Fin n → ℕ) := Σ i : Fin n, Fin (deg i)

/-- Perfect matchings of a finite set, as fixed-point-free involutions. -/
abbrev Pairing (X : Type) := {τ : Equiv.Perm X // (∀ x, τ (τ x) = x) ∧ ∀ x, τ x ≠ x}

instance (X : Type) [Fintype X] [DecidableEq X] : Fintype (Pairing X) := Fintype.ofFinite _

section Configuration
variable {n : ℕ} {deg : Fin n → ℕ}

/-- Adjacency of the configuration multigraph of a pairing: `A i j` counts the half-edges of `i`
paired with a half-edge of `j`. A loop at `i` is counted twice on the diagonal (once from each of
its two half-edges), parallel edges are counted with multiplicity, so the row sums are the degrees. -/
def configAdj (τ : Pairing (HalfEdge deg)) : Matrix (Fin n) (Fin n) ℕ :=
  fun i j => Fintype.card {x : HalfEdge deg // x.1 = i ∧ (τ.1 x).1 = j}

/-- The symmetric normalized adjacency `W = D^{-1/2} A D^{-1/2}`. -/
def normalizedAdj (τ : Pairing (HalfEdge deg)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (configAdj τ i j : ℝ) / Real.sqrt ((deg i : ℝ) * (deg j : ℝ))

/-- The eigenvalues of `W`, with multiplicity (the roots of its characteristic polynomial; `W` is
real symmetric, so this multiset has `n` elements). -/
def normEigenvalues (τ : Pairing (HalfEdge deg)) : Multiset ℝ :=
  (normalizedAdj τ).charpoly.roots

/-- `ω₂(W)`: the second entry of the eigenvalues listed in nonincreasing order
`ω₁ ≥ ω₂ ≥ ⋯ ≥ ωₙ` (only meaningful for `n ≥ 2`). -/
def secondEig (τ : Pairing (HalfEdge deg)) : ℝ :=
  ((normEigenvalues τ).sort (· ≤ ·)).reverse.getD 1 0

/-- `#{i : ωᵢ > t}`, eigenvalues counted with multiplicity. -/
def eigCountAbove (τ : Pairing (HalfEdge deg)) (t : ℝ) : ℕ := by
  classical exact ((normEigenvalues τ).filter (fun x => t < x)).card

/-- `∫ f dμ_W = (1/n) ∑ᵢ f(ωᵢ)` for the empirical spectral measure `μ_W = (1/n) ∑ᵢ δ_{ωᵢ}`. -/
def spectralAverage (τ : Pairing (HalfEdge deg)) (f : ℝ → ℝ) : ℝ :=
  ((normEigenvalues τ).map f).sum / (n : ℝ)

end Configuration

/-- A rooted multigraph: an adjacency count between every pair of vertices (a loop counted
twice on the diagonal) and a root. -/
structure RootedMultigraph where
  V : Type
  adj : V → V → ℕ
  root : V

/-- Rooted isomorphism: a bijection of vertices preserving every adjacency count and the root. -/
def RootedIso (G K : RootedMultigraph) : Prop :=
  ∃ e : G.V ≃ K.V, e G.root = K.root ∧ ∀ u w, K.adj (e u) (e w) = G.adj u w

/-- The vertices at graph distance at most `R` from `v` in the multigraph with adjacency `A`. -/
def ball {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ) (v : Fin n) : ℕ → Set (Fin n)
  | 0 => {v}
  | R + 1 => ball A v R ∪ {w | ∃ u ∈ ball A v R, 0 < A u w}

theorem mem_ball_self {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ) (v : Fin n) :
    ∀ R, v ∈ ball A v R
  | 0 => rfl
  | R + 1 => Or.inl (mem_ball_self A v R)

/-- The radius-`R` neighbourhood of `v`: the sub-multigraph induced by `ball A v R` (with its loops,
parallel edges and the edges between vertices at distance `R`), rooted at `v`. -/
def nbhd {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ) (v : Fin n) (R : ℕ) : RootedMultigraph where
  V := ball A v R
  adj u w := A u.1 w.1
  root := ⟨v, mem_ball_self A v R⟩

end ZigZagStrong.ZigZag.Supplement


