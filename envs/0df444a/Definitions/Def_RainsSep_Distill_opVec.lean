-- Prove2me | Definitions.Def_RainsSep_Distill_opVec
-- name    : RainsSep_Distill_opVec
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:56:17.833044+00:00
-- url     : https://prove2.me/theorems/3456dbd3-c3a2-40c0-870e-dbe2a4b22722
-- title:
--   The vector $|A\rangle=\sum_i|i\rangle\otimes A|i\rangle$ of a linear map
-- statement:
--   Let $V,W$ be finite-dimensional Hilbert spaces and $A:V\to W$ a linear map. Its **vector** $|A\rangle\in V\otimes W$ is
--
--   $$
--   |A\rangle=\sum_i |i\rangle\otimes A|i\rangle=\sqrt{\dim V}\,\big(\mathrm{Id}(V)\otimes A\big)\phi^+(V),
--   $$
--
--   whose $(v,w)$ component is the matrix entry $A_{wv}$. It identifies linear maps with bipartite vectors and is used to rewrite fidelities of superoperators as traces of products of positive operators.
--
--   **Formalization Note** $A$ is a $W\times V$ matrix, and the basis $|i\rangle$ is the computational basis of $V$.
-- source:
--   Rains, Entanglement purification via separable superoperators, arXiv:quant-ph/9707002v3, Eq. (7), p. 2

import Mathlib

namespace RainsSep.Distill

/-- **The vector `|A⟩` of a linear map `A : V → W`.**
Rains, *Entanglement purification via separable superoperators*, arXiv:quant-ph/9707002v3, Eq. (7), p. 2: "If |i⟩ is an orthonormal basis of V, and A is a linear transformation
from V to W, then we define a vector |A⟩ = Σ_i |i⟩ ⊗ A|i⟩ = √dim(V)(Id(V) ⊗ A)φ+(V). (7)"

`|A⟩ ∈ V ⊗ W` has components `|A⟩_{(v,w)} = A_{w v}`.

**Formalization Note.** `A : Matrix W V ℂ` (rows indexed by `W`); the basis `|i⟩` is the
computational basis of `V`. -/
noncomputable def opVec {V W : Type*} (A : Matrix W V ℂ) : EuclideanSpace ℂ (V × W) :=
  WithLp.toLp 2 fun p => A p.2 p.1

end RainsSep.Distill


