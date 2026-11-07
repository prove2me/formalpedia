-- Prove2me | Definitions.Def_DetANN_Multigraph
-- name    : DetANN_Multigraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:25:47.970892+00:00
-- url     : https://prove2.me/theorems/717317b5-2f3e-406f-8077-685277267eaf
-- title:
--   Regular multigraphs, normalized adjacency, walks, and $\theta_0=5\sqrt2/8$
-- statement:
--   A **$\Delta$-regular multigraph** on a finite vertex set $V$ is given by neighbor lists $\mathrm{nbr}(u,k)$, $k=0,\dots,\Delta-1$; loops and parallel edges are allowed and every occurrence counts in the degree. It is **undirected** if $v$ occurs among the neighbors of $u$ exactly as often as $u$ among those of $v$. Its **normalized adjacency matrix** is $W_{uv}=\#\{k:\mathrm{nbr}(u,k)=v\}/\Delta$. A **walk** of length $\ell$ from $v$ is a word $w\in[\Delta]^\ell$ of neighbor choices, with endpoint obtained by following them. $W$ **contracts the mean-zero subspace by $\theta$** if $\|Wf\|_2\le\theta\|f\|_2$ for every $f$ with $\sum_vf(v)=0$.
--
--   The constant $\theta_0=5\sqrt2/8$ is the one fixed in the proof of Lemma 7.1.
--
--   These are the objects of Lemma 7.1 and Lemma 7.2.
--
--   **Formalization Note** The contraction is stated squared, $\sum_u(Wf)_u^2\le\theta^2\sum_vf(v)^2$, which is equivalent for $\theta\ge0$. Mathlib's simple graphs are not used because they cannot carry loops or multiplicities.
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), Lemma 7.1, p.17; §7.1–7.2, p.17; Appendix B, p.20

import Mathlib

namespace DetANN

/-!
# Regular multigraphs, normalized adjacency matrices, walks, and the walk family

Y. Feng, P. Indyk, *Deterministic Approximate Nearest Neighbors in High Dimensions*, STOC 2027
submission (manuscript sha256 96f0ad57…), Lemma 7.1 and §7.1–7.2, p.17; Appendix B, p.20.

**Formalization Note.**
* A `Δ`-regular multigraph on a finite vertex type `V` is a neighbor list `nbr : V → Fin Δ → V`:
  `nbr u k` is the `k`th neighbor occurrence of `u`. Loops and repeated neighbors are allowed and
  each occurrence counts in the degree (p.17). Mathlib's `SimpleGraph` cannot carry loops or
  multiplicities and is not used.
* Undirected means that `v` occurs among the neighbors of `u` exactly as often as `u` occurs among
  the neighbors of `v`.
* The normalized adjacency matrix is `W u v = #{k : nbr u k = v} / Δ`.
* The spectral condition `‖W f‖₂ ≤ θ ‖f‖₂` for mean-zero `f` is stated squared,
  `∑_u (W f)_u² ≤ θ² ∑_v f_v²`; for `θ ≥ 0` the two forms are equivalent.
* A walk of length `ℓ` is a word `w : Fin ℓ → Fin Δ` of neighbor choices; the paper's "fixed
  ordering of these walks" is the order of these words.
-/

/-- The constant `θ₀ = 5√2/8` of Lemma 7.1 (p.20). -/
noncomputable def theta0 : ℝ := 5 * Real.sqrt 2 / 8

variable {V : Type} [Fintype V] [DecidableEq V] {Δ : ℕ}

/-- The number of neighbor occurrences of `u` equal to `v`. -/
def edgeCount (nbr : V → Fin Δ → V) (u v : V) : ℕ :=
  (Finset.univ.filter fun k : Fin Δ => nbr u k = v).card

/-- The multigraph is undirected: `#{k : nbr u k = v} = #{k : nbr v k = u}` for all `u, v`. -/
def IsUndirected (nbr : V → Fin Δ → V) : Prop :=
  ∀ u v : V, edgeCount nbr u v = edgeCount nbr v u

/-- The normalized adjacency matrix `W u v = #{k : nbr u k = v} / Δ`. -/
noncomputable def adjMatrix (nbr : V → Fin Δ → V) : Matrix V V ℝ :=
  fun u v => (edgeCount nbr u v : ℝ) / Δ

/-- `W` contracts the mean-zero subspace by `θ`: `∑_u (W f)_u² ≤ θ² ∑_v f_v²` whenever
`∑_v f_v = 0`. -/
def ContractsMeanZero (W : Matrix V V ℝ) (θ : ℝ) : Prop :=
  ∀ f : V → ℝ, ∑ v, f v = 0 → ∑ u, (Matrix.mulVec W f) u ^ 2 ≤ θ ^ 2 * ∑ v, f v ^ 2

/-- The endpoint of the walk from `v` that follows the neighbor choices `w 0, w 1, …, w (ℓ−1)`. -/
def walkEnd (nbr : V → Fin Δ → V) : (ℓ : ℕ) → V → (Fin ℓ → Fin Δ) → V
  | 0, v, _ => v
  | ℓ + 1, v, w => walkEnd nbr ℓ (nbr v (w 0)) (Fin.tail w)

end DetANN


