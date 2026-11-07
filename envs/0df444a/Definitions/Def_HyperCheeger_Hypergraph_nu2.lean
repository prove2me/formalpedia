-- Prove2me | Definitions.Def_HyperCheeger_Hypergraph_nu2
-- name    : HyperCheeger_Hypergraph_nu2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:02:35.28104+00:00
-- url     : https://prove2.me/theorems/da4e7997-6b7f-4c0b-91fa-6c643a4573b7
-- title:
--   Matrices $A_H$, $D_H$, $L_H$, $\mathcal L_H$ and the eigenvalue $\nu_2(H)$
-- statement:
--   The **adjacency matrix** of $H$ is
--
--   $$A_H[u,v]=\sum_{e\in E_H:\,\{u,v\}\subseteq e}\frac{w_H(e)}{|e|-1}\quad(u\ne v),\qquad A_H[u,u]=0.$$
--
--   The **degree matrix** $D_H$ is diagonal with $D_H[u,u]=d_H(u)$, the **Laplacian** is $L_H=D_H-A_H$, and the **normalized Laplacian** is $\mathcal L_H=D_H^{-1/2}L_HD_H^{-1/2}$. With $\nu_1(H)\le\nu_2(H)\le\dots\le\nu_n(H)$ the eigenvalues of $\mathcal L_H$ in ascending order, counted with multiplicity, $\nu_2(H)$ is the second smallest one. This is the spectral side of the Cheeger inequality.
--
--   **Formalization Note.** $D_H^{-1/2}$ has diagonal entries $1/\sqrt{d_H(u)}$, which is $0$ at a zero-degree vertex in Lean. $\nu_2$ is the published `AlonMilman.PropertyT.lambda1`, the second-smallest eigenvalue with multiplicity of a real symmetric matrix, whose junk value $0$ is reached here only with fewer than two vertices, since $\mathcal L_H$ is always symmetric.
-- source:
--   Kamal, Bagchi, A Cheeger Inequality for Hypergraphs and Its Applications, STOC 2027 submission, arXiv:2609.16286 (manuscript sha256 e0942b89…), §3.1, eq. (3), pp.7–8

import Mathlib
import Definitions.Def_HyperCheeger_Hypergraph
import Definitions.Def_AlonMilman_PropertyT_lambda1

namespace HyperCheeger

namespace Hypergraph

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The adjacency matrix (3): `A_H[u, v] = ∑_{e ∈ E_H : {u, v} ⊆ e} w_H(e)/(|e|−1)` when `u ≠ v`, and
`0` otherwise (§3.1, p.7). `|e| − 1` is a real subtraction. -/
noncomputable def adj (H : Hypergraph V) : Matrix V V ℝ :=
  Matrix.of fun u v =>
    if u = v then 0 else ∑ e ∈ H.edges with {u, v} ⊆ e, H.w e / ((e.card : ℝ) - 1)

/-- The diagonal degree matrix `D_H`, `D_H[u, u] = d_H(u)` (§3.1, p.7). -/
noncomputable def degMat (H : Hypergraph V) : Matrix V V ℝ :=
  Matrix.diagonal H.degree

/-- The Laplacian `L_H = D_H − A_H` (§3.1, p.7). -/
noncomputable def lap (H : Hypergraph V) : Matrix V V ℝ :=
  H.degMat - H.adj

/-- `D_H^{−1/2}`: the diagonal matrix with entries `1/√(d_H(u))`.

**Formalization Note.** The entry is `0` at a zero-degree vertex (`(√0)⁻¹ = 0` in Lean), where the
paper's expression is undefined. -/
noncomputable def degInvSqrt (H : Hypergraph V) : Matrix V V ℝ :=
  Matrix.diagonal fun u => (Real.sqrt (H.degree u))⁻¹

/-- The normalized Laplacian `𝓛_H = D_H^{−1/2} L_H D_H^{−1/2}` (§3.1, p.8). -/
noncomputable def normLap (H : Hypergraph V) : Matrix V V ℝ :=
  H.degInvSqrt * H.lap * H.degInvSqrt

/-- `ν₂(H)`, the second smallest eigenvalue of `𝓛_H`, counted with multiplicity: `ν₂` in
`ν₁(H) ≤ ν₂(H) ≤ ⋯ ≤ ν_n(H)` (Kamal, Bagchi, *A Cheeger Inequality for Hypergraphs and Its
Applications*, STOC 2027 submission, arXiv:2609.16286 (manuscript sha256 e0942b89…), §3.1, p.8).

**Formalization Note.** This is the published `AlonMilman.PropertyT.lambda1`: `eigenvalues₀` at index
`card V − 2`, since Mathlib lists eigenvalues in decreasing order. Its junk value `0` applies only when
`card V < 2`: `𝓛_H` is always symmetric. -/
noncomputable def nu2 (H : Hypergraph V) : ℝ :=
  AlonMilman.PropertyT.lambda1 H.normLap

end Hypergraph

end HyperCheeger


