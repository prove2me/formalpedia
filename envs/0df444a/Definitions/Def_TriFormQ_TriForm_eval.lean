-- Prove2me | Definitions.Def_TriFormQ_TriForm_eval
-- name    : TriFormQ_TriForm_eval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:45:27.840558+00:00
-- url     : https://prove2.me/theorems/c8dc1899-ed42-4adf-9c9c-abff2798f0ff
-- title:
--   Value $f(x,y,z)$ of a trilinear form
-- statement:
--   For a coefficient tensor $\theta$ on $[n]^3$ and vectors $x,y,z\in\mathbb F^n$, the value of the trilinear form is
--
--   $$f(x,y,z)=\sum_{i=1}^n\sum_{j=1}^n\sum_{k=1}^n\theta_{ijk}\,x_i\,y_j\,z_k .$$
--
--   This is the function the evaluation oracle computes; all statements about the hidden form refer to it.
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), §1, p.2 (PDF p.5)

import Definitions.Def_TriFormQ_TriForm

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), §1, p.2 (PDF p.5): the value
`f(x, y, z) = Σ_{i,j,k} θ_{ijk} x_i y_j z_k` of the trilinear form with coefficient tensor `θ`. -/
def TriForm.eval {F : Type} [Field F] {n : ℕ} (θ : TriForm F n) (x y z : Vec F n) : F :=
  ∑ i, ∑ j, ∑ k, θ i j k * x i * y j * z k

end TriFormQ


