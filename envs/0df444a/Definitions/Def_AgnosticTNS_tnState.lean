-- Prove2me | Definitions.Def_AgnosticTNS_tnState
-- name    : AgnosticTNS_tnState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:33:09.414607+00:00
-- url     : https://prove2.me/theorems/be1296b7-394e-49fe-8d2d-66fa48c4e098
-- title:
--   Contraction of a tensor network on $(G,w)$
-- statement:
--   Let $G=([n],E)$ be a graph and $w:E\to\mathbb N$ bond dimensions. A tensor $\varphi[v]$ at each vertex $v$ has one physical index $i_v\in[d]$ and one virtual index $j_e\in[w(e)]$ for each edge $e$ incident to $v$. Contracting the network gives the vector with coefficients
--   $$
--   \psi_{i_1,\dots,i_n}=\sum_{(j_e)_{e\in E}\in\prod_{e\in E}[w(e)]}\ \prod_{v\in[n]}\varphi[v]_{i_v}\big((j_e)_{e\ni v}\big),
--   $$
--   each virtual index being shared by the tensors at the two endpoints of its edge.
--
--   **Formalization Note** A vector on $(\mathbb C^d)^{\otimes n}$ is a function `(Fin n → Fin d) → ℂ`; the virtual indices of $\varphi[v]$ are indexed by the incidence set of $v$.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Section 2.1, Eq. (2.2), p.12

import Mathlib

namespace AgnosticTNS

/-- **Contraction of a tensor network**, Eq. (2.2), p.12 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)).
Given a graph `G` on `[n]`, bond dimensions `w : E → ℕ` and at each vertex `v` a tensor `φ[v]` with
one physical index `i_v ∈ [d]` and one virtual index for each incident edge `e` (of dimension `w e`),
the contracted vector has coefficients
`ψ_{i_1, …, i_n} = Σ_{(j_e)_{e∈E} ∈ Π_e [w(e)]} Π_{v ∈ [n]} φ[v]_{i_v}((j_e)_{e ∋ v})`.
Each virtual index `j_e` is shared by the tensors at the two endpoints of `e`.

**Formalization Note** Vertices are `Fin n`, physical labels `Fin d` (0-based), a vector is a function
`(Fin n → Fin d) → ℂ`. The virtual indices of `φ v` are indexed by the edges incident to `v`
(`G.incidenceSet v`), and `j` assigns to every edge a value in `Fin (w e)`. -/
noncomputable def tnState {n d : ℕ} (G : SimpleGraph (Fin n)) (w : G.edgeSet → ℕ)
    (φ : (v : Fin n) → Fin d → ((e : G.incidenceSet v) →
      Fin (w ⟨e.1, G.incidenceSet_subset v e.2⟩)) → ℂ) :
    (Fin n → Fin d) → ℂ := by
  classical
  exact fun i => ∑ j : (e : G.edgeSet) → Fin (w e),
    ∏ v : Fin n, φ v (i v) (fun e => j ⟨e.1, G.incidenceSet_subset v e.2⟩)

end AgnosticTNS


