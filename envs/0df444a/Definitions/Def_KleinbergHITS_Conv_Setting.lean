-- Prove2me | Definitions.Def_KleinbergHITS_Conv_Setting
-- name    : KleinbergHITS_Conv_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:16:38.139259+00:00
-- url     : https://prove2.me/theorems/41f2811c-03c1-40a7-806f-f105045270a5
-- title:
--   §2–§3, pp. 4–10 — link graph, adjacency matrix, the I and O operations, Iterate(G,k), Assumption (†) and principal eigenvectors
-- statement:
--   This module fixes the objects of §2–§3 of Kleinberg, *Authoritative sources in a hyperlinked environment* (1999).
--
--   **The link graph.** A collection of $n$ hyperlinked pages is a directed graph $G=(V,E)$ with $V=\{p_1,\dots,p_n\}$; a directed edge $(p,q)\in E$ means that page $p$ links to page $q$. The **adjacency matrix** $A$ is the $n\times n$ matrix whose $(i,j)$ entry is $1$ if $(p_i,p_j)\in E$ and $0$ otherwise. Self-links are not excluded.
--
--   **Weights and the two operations.** Each page $p$ carries an authority weight $x^{\langle p\rangle}$ and a hub weight $y^{\langle p\rangle}$, collected into vectors $x,y\in\mathbb R^n$. The $\mathcal I$ operation replaces the authority weights by the sums of the hub weights of the pages pointing in, and the $\mathcal O$ operation replaces the hub weights by the sums of the authority weights of the pages pointed to:
--   $$x^{\langle p\rangle}\leftarrow\sum_{q:(q,p)\in E}y^{\langle q\rangle},\qquad y^{\langle p\rangle}\leftarrow\sum_{q:(p,q)\in E}x^{\langle q\rangle}.$$
--   **Normalization** rescales a vector $v$ so that its squares sum to $1$: $v\mapsto v/\sqrt{\sum_i v_i^2}$.
--
--   **The procedure Iterate$(G,k)$.** Let $z=(1,1,\dots,1)\in\mathbb R^n$ and set $x_0=y_0=z$. For $i=1,\dots,k$: apply $\mathcal I$ to $(x_{i-1},y_{i-1})$, obtaining $x_i'$; apply $\mathcal O$ to $(x_i',y_{i-1})$, obtaining $y_i'$; normalize $x_i'$ to get $x_i$ and $y_i'$ to get $y_i$. The procedure returns $(x_k,y_k)$.
--
--   **Eigen-notions and Assumption (†).** For a symmetric $n\times n$ matrix $M$, list its eigenvalues $\lambda_1(M),\dots,\lambda_n(M)$ with multiplicity in order of decreasing absolute value. Assumption (†) is
--   $$|\lambda_1(M)|>|\lambda_2(M)|,$$
--   that is, the eigenvalue of largest absolute value is simple (its eigenspace is a line) and every other eigenvalue is strictly smaller in absolute value. Under (†), a **principal eigenvector** $\omega_1(M)$ is a unit vector (squares summing to $1$) spanning the eigenspace of $\lambda_1(M)$.
--
--   These objects are shared by every statement of the mission: Theorem 3.1 (the iterates converge), Theorem 3.2 (the limits are the principal eigenvectors of $A^{\top}A$ and $AA^{\top}$), and the steps of their proof.
--
--   **Formalization Note** Pages are `Fin n` and the link relation is a decidable relation `E` on them; `adjMatrix E` is a real matrix (Mathlib's `SimpleGraph.adjMatrix` is undirected and loopless, so it is not used). The operations $\mathcal I$, $\mathcal O$ are defined as neighbour sums, not as matrix products; that they equal $A^{\top}y$ and $Ax$ is a milestone. `normalize` sends the zero vector to itself (a junk value; no statement relies on it). `hitsIter E i` is the pair $(x_i,y_i)$, with the $\mathcal O$ step applied to the unnormalized $x_i'$ as on the page. Assumption (†) is `Dagger M`: there is an eigenvalue $\lambda_1$ whose eigenspace has dimension $1$, every eigenvalue $\mu\ne\lambda_1$ has $|\mu|<|\lambda_1|$, and $\lambda_1\ne0$. The clause $\lambda_1\ne0$ is the paper's own reading, "if $\lambda_1(A^{\top}A)\ne0$ (as dictated by Assumption (†))" (p. 11): for $n\ge2$ it follows from the rest, and for $n=1$ it is what $|\lambda_1|>|\lambda_2|$ means with $\lambda_2:=0$; without it the one-page graph with no link would satisfy (†) and Theorem 3.2 would fail. Because the paper fixes $\omega_1(M)$ only by a choice of orthonormal basis, "principal eigenvector" is a predicate (`IsPrincipalEigenvector`), which determines the vector up to sign.
-- source:
--   Kleinberg, Authoritative sources in a hyperlinked environment, J. ACM 46(5) (1999), author's copy, p. 4 (§2, graph G = (V, E)); pp. 8–9 (§3, weights, normalization, the I and O operations, Iterate(G,k)); p. 10 (§3, eigen-notions, Assumption (†), principal eigenvector; adjacency matrix in the proof of Theorem 3.1); p. 11 (λ₁ ≠ 0 as dictated by (†))

import Mathlib

namespace KleinbergHITS.Conv

open Matrix

/-- Kleinberg (1999), §3, proof of Theorem 3.1, p. 10: the adjacency matrix of the link graph
`G = (V, E)` on the pages `Fin n`; its `(i, j)` entry is `1` if `(pᵢ, pⱼ)` is an edge (a link from
`pᵢ` to `pⱼ`) and `0` otherwise. Self-links are allowed. -/
def adjMatrix {n : ℕ} (E : Fin n → Fin n → Prop) [DecidableRel E] : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if E i j then 1 else 0

/-- §3, p. 9: the vector `z = (1, 1, …, 1) ∈ ℝⁿ`. -/
def allOnes (n : ℕ) : Fin n → ℝ := fun _ => 1

/-- §3, p. 8: the `I` operation, `x⟨p⟩ ← Σ_{q : (q,p) ∈ E} y⟨q⟩` (sum of the hub weights of the
pages linking to `p`). -/
def opI {n : ℕ} (E : Fin n → Fin n → Prop) [DecidableRel E] (y : Fin n → ℝ) : Fin n → ℝ :=
  fun p => ∑ q ∈ Finset.univ.filter (fun q => E q p), y q

/-- §3, p. 8: the `O` operation, `y⟨p⟩ ← Σ_{q : (p,q) ∈ E} x⟨q⟩` (sum of the authority weights of
the pages `p` links to). -/
def opO {n : ℕ} (E : Fin n → Fin n → Prop) [DecidableRel E] (x : Fin n → ℝ) : Fin n → ℝ :=
  fun p => ∑ q ∈ Finset.univ.filter (fun q => E p q), x q

/-- §3, p. 8: normalization "so their squares sum to 1", `v ↦ v / √(Σᵢ vᵢ²)`. (Junk value: the
zero vector is sent to itself.) -/
noncomputable def normalize {n : ℕ} (v : Fin n → ℝ) : Fin n → ℝ :=
  (Real.sqrt (∑ i, v i ^ 2))⁻¹ • v

/-- §3, p. 9: the procedure `Iterate(G, k)`. `hitsIter E i = (xᵢ, yᵢ)`, with `x₀ = y₀ = z` and, for
`i ≥ 1`: `x′ᵢ := I(yᵢ₋₁)`, `y′ᵢ := O(x′ᵢ)` (the O operation applied to the unnormalized `x′ᵢ`),
`xᵢ := normalize x′ᵢ`, `yᵢ := normalize y′ᵢ`. `Iterate(G, k)` returns `hitsIter E k`. -/
noncomputable def hitsIter {n : ℕ} (E : Fin n → Fin n → Prop) [DecidableRel E] :
    ℕ → (Fin n → ℝ) × (Fin n → ℝ)
  | 0 => (allOnes n, allOnes n)
  | i + 1 =>
    let x' := opI E (hitsIter E i).2
    let y' := opO E x'
    (normalize x', normalize y')

/-- §3, p. 10: `l₁` is the principal eigenvalue `λ₁(M)` of `M` under Assumption (†): it is an
eigenvalue, it is simple (its eigenspace is one-dimensional), and every other eigenvalue is strictly
smaller in absolute value, `|λ₁(M)| > |λ₂(M)|`. -/
def IsPrincipalEigenvalue {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (l₁ : ℝ) : Prop :=
  Module.End.HasEigenvalue (Matrix.toLin' M) l₁ ∧
    Module.finrank ℝ (Module.End.eigenspace (Matrix.toLin' M) l₁) = 1 ∧
    ∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' M) μ → μ ≠ l₁ → |μ| < |l₁|

/-- §3, p. 10, Assumption (†), `|λ₁(M)| > |λ₂(M)|`, together with `λ₁(M) ≠ 0` ("as dictated by
Assumption (†)", p. 11). -/
def Dagger {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ l₁ : ℝ, IsPrincipalEigenvalue M l₁ ∧ l₁ ≠ 0

/-- §3, p. 10: `ω` is a principal eigenvector `ω₁(M)`: a unit vector (squares summing to 1) in the
eigenspace of the principal eigenvalue. Under (†) this determines `ω` up to sign. -/
def IsPrincipalEigenvector {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (ω : Fin n → ℝ) : Prop :=
  ∃ l₁ : ℝ, IsPrincipalEigenvalue M l₁ ∧ M *ᵥ ω = l₁ • ω ∧ ∑ i, ω i ^ 2 = 1

end KleinbergHITS.Conv


