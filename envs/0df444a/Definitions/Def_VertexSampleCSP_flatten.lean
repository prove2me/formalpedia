-- Prove2me | Definitions.Def_VertexSampleCSP_flatten
-- name    : VertexSampleCSP_flatten
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:55:41.421598+00:00
-- url     : https://prove2.me/theorems/d9b58589-e0d1-4cf1-b901-22699170ea38
-- title:
--   The flattening $M$ of the payoff tensor and elementary tensors $w_2\otimes\dots\otimes w_r$
-- statement:
--   The **flattening** $M:\mathbb R^{V\times[q]}\to(\mathbb R^{V\times[q]})^{\otimes(r-1)}$ is defined by
--
--   $$\langle Mz,w_2\otimes\dots\otimes w_r\rangle=T[z,w_2,\dots,w_r].$$
--
--   Explicitly, $(Mz)_{c'}=\sum_p T_{(p,c')}z_p$ at an index tuple $c'\in(V\times[q])^{r-1}$.
--
--   **Formalization Note** The tensor power is identified with the Euclidean space of functions on index tuples `Fin (r - 1) → V × Fin q`, so its norm is the Hilbert–Schmidt norm, and $w_2\otimes\dots\otimes w_r$ is the function $c'\mapsto\prod_j w_{j+2}(c'_j)$.
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), Appendix A, "The encoding", p.13 (PDF p.15)

import Mathlib
import Definitions.Def_VertexSampleCSP_Instance
import Definitions.Def_VertexSampleCSP_tensorEntry

namespace VertexSampleCSP

/-- The tuple `(p, c'_1, …, c'_{r−1})` of length `r` obtained by putting `p` in front of a tuple
`c'` of length `r − 1`. -/
def consIdx {α : Type*} {r : ℕ} (p : α) (c' : Fin (r - 1) → α) : Fin r → α :=
  fun j => if h : j.val = 0 then p else c' ⟨j.val - 1, by have := j.isLt; omega⟩

/-- **The flattening `M`.** Chang, *Optimal Vertex Sampling for Constraint Satisfaction Problems*,
STOC 2027 submission (manuscript sha256 1e0edd23…), Appendix A, "The encoding", p.13 (PDF p.15):
"The flattening M : ℝ^{V×[q]} → (ℝ^{V×[q]})^{⊗(r−1)} is defined by
⟨Mz, w2 ⊗ · · · ⊗ wr⟩ = T[z, w2, . . . , wr]."

`flatten I z` is the vector with entry `(Mz)_{c'} = Σ_p T_{(p, c')} z_p` at each index tuple
`c' ∈ (V × [q])^{r−1}`.

**Formalization Note.** The tensor power `(ℝ^{V×[q]})^{⊗(r−1)}` is identified with the Euclidean space
of functions on index tuples `Fin (r − 1) → V × Fin q`; its Euclidean norm is the Hilbert–Schmidt norm
of the tensor, and `w_2 ⊗ ⋯ ⊗ w_r` is the function `c' ↦ Π_j w_{j+2}(c'_j)`. -/
noncomputable def flatten {V : Type*} [Fintype V] [DecidableEq V] {r q : ℕ}
    (I : Instance V r q) (z : EuclideanSpace ℝ (V × Fin q)) :
    EuclideanSpace ℝ (Fin (r - 1) → V × Fin q) :=
  WithLp.toLp 2 (fun c' => ∑ p : V × Fin q, tensorEntry I (consIdx p c') * z p)

/-- **Elementary tensor `w_2 ⊗ ⋯ ⊗ w_r`.** Chang, STOC 2027 submission (manuscript sha256
1e0edd23…), Appendix A, p.13: the vector of `(ℝ^{V×[q]})^{⊗(r−1)}` with entry `Π_j w_j(c'_j)` at the
index tuple `c'`. -/
noncomputable def tensorVec {V : Type*} [Fintype V] {r q : ℕ}
    (w : Fin (r - 1) → EuclideanSpace ℝ (V × Fin q)) :
    EuclideanSpace ℝ (Fin (r - 1) → V × Fin q) :=
  WithLp.toLp 2 (fun c' => ∏ j, w j (c' j))

end VertexSampleCSP


