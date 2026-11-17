-- Prove2me | Definitions.Def_ClusterDecomp_Supplement_lam
-- name    : ClusterDecomp_Supplement_lam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:57:34.685193+00:00
-- url     : https://prove2.me/theorems/dd7c987b-035d-4f2b-bc50-7f39756f2edc
-- title:
--   Induced subgraphs and normalized-Laplacian eigenvalues
-- statement:
--   For a weighted graph $G$ and a vertex set $S$, the **ordinary induced subgraph** $G[S]$ restricts the weight function to $S\times S$ and adds no loops. Thus its degrees count only edges internal to $S$; this is different from the published degree-preserving graph $G\{S\}$.
--
--   If every degree is positive, the **normalized Laplacian** is
--
--   $$
--   L_G=I-D_G^{-1/2}A_GD_G^{-1/2},
--   $$
--
--   where $A_G(u,v)=w(u,v)$. Its eigenvalues, counted with multiplicity, are ordered increasingly as $\lambda_1(L_G)\le\cdots\le\lambda_n(L_G)$, and $\lambda_k(L_G)$ denotes the one-indexed $k$th value.
--
--   These definitions supply the spectral language of Appendix B and, crucially, keep $G[S]$ separate from $G\{S\}$: the paper's counterexample applies only to the former.
--
--   **Formalization Note** The eigenvalues are the ascending real roots of the characteristic polynomial. The normalized Laplacian is real symmetric, so all roots are real and multiplicities agree. Every theorem restricts eigenvalue indices to their meaningful range and assumes positive degrees, excluding total-function junk values.
-- source:
--   Sun, Zhang, Zhou, Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee, STOC 2027 submission (manuscript sha256 ba091f54…), §1.1 p.1 (PDF p.3) and §2.1 p.7 (PDF p.9)

import Mathlib
import Definitions.Def_ClusterDecomp_WGraph

open Finset

namespace ClusterDecomp.Supplement

/-!
# The induced subgraph `G[S]`, the normalized Laplacian and its `k`-th smallest eigenvalue

Sun, Zhang, Zhou, *Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee*, STOC 2027
submission (manuscript sha256 ba091f54…), §1, p.1 (PDF p.3: `G[S]`, "the subgraph induced by `S`") and
§2.1, p.7 (PDF p.9: `L_G = I − D_G^{−1/2} A_G D_G^{−1/2}`, `0 = λ_1(L_G) ≤ ⋯ ≤ λ_n(L_G) ≤ 2`).

**Formalization Note.**
* `induced G S` is the ordinary induced subgraph `G[S]`: vertex type `↥S`, weights `w` restricted to
  `S × S`, no loop added. It differs from the published `degPres G S` (`G{S}`), which adds a loop of weight
  `w(v, V ∖ S)` at each `v ∈ S`; degrees in `G[S]` are those inside `S`.
* `normLap G` is the matrix `L_G(u, v) = [u = v] − w(u, v)/(√deg(u)·√deg(v))`, i.e. `I − D^{−1/2} A D^{−1/2}`
  with `A(u, v) = w(u, v)`. It is the paper's matrix whenever every degree is positive; at a vertex of degree
  `0` the division by `0` gives `0` (a junk value), so every theorem using it assumes positive degrees.
* `lam G k` is `λ_k(L_G)`, the `k`-th **smallest** eigenvalue counted with multiplicity, 1-indexed: the
  `(k−1)`-th entry (0-based) of the ascending sort of the multiset of real roots of the characteristic
  polynomial of `L_G`. Since `L_G` is real symmetric its characteristic polynomial splits over `ℝ`, so that
  multiset is exactly the spectrum with multiplicities, of size `|V|`. Mathlib's
  `Matrix.IsHermitian.eigenvalues₀` is sorted decreasingly and is not used. `lam G k` is meaningful for
  `1 ≤ k ≤ |V|`; outside that range it is a junk value (`0` for `k > |V|`, `λ_1` at `k = 0` by truncated
  subtraction), and every statement using it restricts `k` to `1 ≤ k ≤ |V|`.
* `IsUnweighted G`: every weight is `0` or `1` and there are no loops, i.e. `G` is a simple unweighted
  graph.
-/

open ClusterDecomp

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The induced subgraph `G[S]` (p.1): the weights of `G` restricted to `S × S`. -/
def induced (G : WGraph V) (S : Finset V) : WGraph ↥S where
  w u v := G.w u v
  symm u v := G.symm u v
  nonneg u v := G.nonneg u v

/-- The normalized Laplacian `L_G = I − D_G^{−1/2} A_G D_G^{−1/2}` (§2.1, p.7). -/
noncomputable def normLap (G : WGraph V) : Matrix V V ℝ :=
  fun u v => (if u = v then 1 else 0) - G.w u v / (Real.sqrt (G.deg u) * Real.sqrt (G.deg v))

/-- The eigenvalues of `L_G` with multiplicity, in ascending order: the sorted real roots of its
characteristic polynomial. -/
noncomputable def lapSpectrum (G : WGraph V) : List ℝ :=
  (normLap G).charpoly.roots.sort (· ≤ ·)

/-- `λ_k(L_G)`, the `k`-th smallest eigenvalue of `L_G` (1-indexed, with multiplicity), for
`1 ≤ k ≤ |V|`. -/
noncomputable def lam (G : WGraph V) (k : ℕ) : ℝ :=
  (lapSpectrum G).getD (k - 1) 0

/-- `G` is a simple unweighted graph: weights in `{0, 1}` and no loops. -/
def IsUnweighted (G : WGraph V) : Prop :=
  (∀ u v, G.w u v = 0 ∨ G.w u v = 1) ∧ ∀ v, G.w v v = 0

end ClusterDecomp.Supplement


