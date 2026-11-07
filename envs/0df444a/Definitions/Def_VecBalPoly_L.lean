-- Prove2me | Definitions.Def_VecBalPoly_L
-- name    : VecBalPoly_L
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T23:13:54.876739+00:00
-- url     : https://prove2.me/theorems/623a2918-65fe-49b1-a40a-f002f345fdc2
-- title:
--   The largest eigenvalue $L=\lambda_{\max}(M)$
-- statement:
--   $L=\lambda_{\max}(M)$ when $V\neq\varnothing$, and $L=0$ when $V=\varnothing$, where $M$ is the matrix (2.6) on $\mathbb R^V$.
--
--   **Formalization Note** For $V\ne\varnothing$, $L$ is the supremum of $v^{\mathsf T}Mv$ over unit vectors $v$ supported on $V$. The set is nonempty and bounded, and its supremum is the largest eigenvalue of the symmetric $V\times V$ block of $M$.
-- source:
--   S. Guo, E. X. Fang, J. Lu, Vector Balancing in Polynomial Time, arXiv:2609.23540 (held file sha256 b777ade4…), §2.3, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_VecBalPoly_M

namespace VecBalPoly

open Matrix

variable {m n : ℕ}

/-- **The largest eigenvalue `L = λmax(M)`**, with `L = 0` when `V = ∅`.
Source: Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), §2.3, p.5 (PDF p.6): "We write L = λmax(M) when V ≠ ∅, and set L = 0 when V = ∅."

**Formalization Note** For `V ≠ ∅`, `L` is the supremum of the Rayleigh quotient `vᵀMv` over unit
vectors `v` supported on `V`, which is the largest eigenvalue of the symmetric `V × V` block of
`M`. The set is nonempty (a coordinate vector of `V`) and bounded (a quadratic form on the unit
sphere), so `sSup` is the true supremum. -/
noncomputable def L (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n) : ℝ :=
  if st.V = ∅ then 0 else
    sSup {ρ : ℝ | ∃ v : Fin n → ℝ, (∀ j, j ∉ st.V → v j = 0) ∧ ∑ j, v j ^ 2 = 1 ∧
      ρ = v ⬝ᵥ (M A st *ᵥ v)}

end VecBalPoly


