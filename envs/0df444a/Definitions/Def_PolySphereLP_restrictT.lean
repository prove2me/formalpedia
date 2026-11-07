-- Prove2me | Definitions.Def_PolySphereLP_restrictT
-- name    : PolySphereLP_restrictT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:57:29.419068+00:00
-- url     : https://prove2.me/theorems/aac6dab0-5e9f-420b-927f-d96821d42f81
-- title:
--   The restriction $R_VT=(V^\top)^{\otimes k}T$
-- statement:
--   For an $n\times m$ complex matrix $V$ (a map $\mathbb C^m\to\mathbb C^n$) and an order-$k$ tensor $T$ on $\mathbb C^n$,
--   $$(R_VT)_{j_1\dots j_k}=\sum_{i_1,\dots,i_k}V_{i_1j_1}\cdots V_{i_kj_k}\,T_{i_1\dots i_k},$$
--   an order-$k$ tensor on $\mathbb C^m$. For $T=T_G$ it is the coefficient tensor of $z\mapsto G(Vz)$.
--
--   **Formalization Note** $V^\top$ is the transpose, not the conjugate transpose.
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), §A.6, p.28

import Mathlib
import Definitions.Def_PolySphereLP_Tensor

namespace PolySphereLP

/-- **The restriction `R_V T = (Vᵀ)^{⊗k} T`.** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), §A.6, p.28: "For a symmetric complex tensor `T`
of order `k`, write `R_V T =def (Vᵀ)^{⊗k} T`."

For `V : ℂ^m → ℂⁿ` (an `n × m` complex matrix), `(R_V T)_{j₁…j_k} = ∑_{i} V_{i₁j₁}⋯V_{i_kj_k}
T_{i₁…i_k}`, an order-`k` tensor on `ℂ^m`.

**Formalization Note.** `(Vᵀ)_{j i} = V_{i j}`: a transpose, not a conjugate transpose. For `T = T_G`
this is the coefficient tensor of `z ↦ G(Vz)`. -/
noncomputable def restrictT {n m : ℕ} (k : ℕ) (V : Matrix (Fin n) (Fin m) ℂ) (T : Tensor n k) :
    Tensor m k :=
  fun j => ∑ i : Fin k → Fin n, (∏ s, V (i s) (j s)) * T i

end PolySphereLP


