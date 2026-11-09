-- Prove2me | Definitions.Def_TriFormQ_sliceU
-- name    : TriFormQ_sliceU
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:45:44.469529+00:00
-- url     : https://prove2.me/theorems/a6a8ef59-6bfa-455e-8e59-ea850421e6ef
-- title:
--   Bilinear slice $f[u]$
-- statement:
--   For a trilinear form $f$ with coefficients $\theta_{ijk}$ and $u\in\mathbb F^n$, the **bilinear slice at $u$** is the bilinear form $f[u](y,z)=f(u,y,z)$, represented by the $n\times n$ matrix
--
--   $$f[u]_{jk}=\sum_{i}\theta_{ijk}u_i ,\qquad f(u,y,z)=y^\top f[u]\,z .$$
--
--   Its rank $\mathrm{rk}\,f[u]$ is the rank of this matrix.
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), §2.2.1, p.13 (PDF p.16)

import Definitions.Def_TriFormQ_TriForm

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), §2.2.1, p.13 (PDF p.16): "For
any u ∈ U, we write f[u] for the bilinear form f[u] : V × W → 𝔽_q obtained from f by fixing the U
coordinate", viewed as a matrix: entry `(j, k)` is `Σ_i θ_{ijk} u_i`, so that
`f(u, y, z) = yᵀ f[u] z`. Its rank is `Matrix.rank`. -/
def sliceU {F : Type} [Field F] {n : ℕ} (θ : TriForm F n) (u : Vec F n) :
    Matrix (Fin n) (Fin n) F :=
  Matrix.of fun j k => ∑ i, θ i j k * u i

end TriFormQ


