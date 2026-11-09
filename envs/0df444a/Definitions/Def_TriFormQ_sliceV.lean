-- Prove2me | Definitions.Def_TriFormQ_sliceV
-- name    : TriFormQ_sliceV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:45:39.200183+00:00
-- url     : https://prove2.me/theorems/289d7f47-a02c-4a1e-8e06-8572b3b20f04
-- title:
--   Bilinear slice $f\langle v\rangle$
-- statement:
--   For a trilinear form $f$ with coefficients $\theta_{ijk}$ and $v\in\mathbb F^n$, the **bilinear slice at $v$** is the bilinear form $f\langle v\rangle(x,z)=f(x,v,z)$, represented by the $n\times n$ matrix
--
--   $$f\langle v\rangle_{ik}=\sum_{j}\theta_{ijk}v_j ,\qquad f(x,v,z)=x^\top f\langle v\rangle\, z .$$
--
--   Its rank $\mathrm{rk}\,f\langle v\rangle$ equals the codimension of the fiber $Z_v$.
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), §2.2.1, p.13 (PDF p.16)

import Definitions.Def_TriFormQ_TriForm

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), §2.2.1, p.13 (PDF p.16):
"Similarly, for every v ∈ V, define a bilinear form f⟨v⟩ : U × W → 𝔽_q", viewed as a matrix:
entry `(i, k)` is `Σ_j θ_{ijk} v_j`, so that `f(x, v, z) = xᵀ f⟨v⟩ z`. -/
def sliceV {F : Type} [Field F] {n : ℕ} (θ : TriForm F n) (v : Vec F n) :
    Matrix (Fin n) (Fin n) F :=
  Matrix.of fun i k => ∑ j, θ i j k * v j

end TriFormQ


