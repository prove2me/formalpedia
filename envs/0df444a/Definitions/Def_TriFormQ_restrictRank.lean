-- Prove2me | Definitions.Def_TriFormQ_restrictRank
-- name    : TriFormQ_restrictRank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:44:13.932229+00:00
-- url     : https://prove2.me/theorems/13dd2d53-bc83-4e2b-afe8-89fd2d40ad04
-- title:
--   Restricted rank $\mathrm{rk}(B|_{\mathrm{coker} A\times\ker A})$
-- statement:
--   Let $K$ be a field and $A,B\in M_{m\times n}(K)$. Let $\ker A=\{x\in K^n: Ax=0\}$ and $\operatorname{coker}A=\{y\in K^m: y^\top A=0\}$ (the left kernel). The **rank of $B$ restricted to $\operatorname{coker}A\times\ker A$** is the rank of the bilinear form
--
--   $$\operatorname{coker}A\times\ker A\to K,\qquad (y,x)\mapsto y^\top B x,$$
--
--   that is, the dimension of the image of the induced linear map $\ker A\to(\operatorname{coker}A)^*$. It is the rank of the matrix of the restricted form in any bases of the two subspaces, not the rank of a coordinate submatrix of $B$. When $A=0$ it equals $\mathrm{rk}\,B$ (proved sanity check).
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Lemma 11, p.31 (PDF p.34); §6.2, p.32 (PDF p.35)

import Mathlib
open Matrix

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Lemma 11, p.31 (PDF p.34) and §2,
p.11: `rk(B|_{coker A × ker A})`, the rank of the bilinear form `(y, x) ↦ yᵀ B x` restricted to
`coker A × ker A`, where `ker A = {x ∈ Kⁿ | A x = 0}` and `coker A = {y ∈ Kᵐ | yᵀ A = 0}` (the
left kernel; "restricting every matrix in M₀ the product of subspaces coker A × ker A", p.32).

**Formalization Note.** The rank of a bilinear form on `Y × X` is the dimension of the range of
the induced linear map `X → Y*`; here `X = ker A`, `Y = coker A`, and the map sends `x` to
`y ↦ y ⬝ᵥ (B *ᵥ x)`. It is the rank of the matrix of the restricted form in any bases of
`coker A` and `ker A`, not the rank of a coordinate submatrix of `B`. -/
noncomputable def restrictRank {K : Type} [Field K] {m n : ℕ} (B A : Matrix (Fin m) (Fin n) K) :
    ℕ :=
  Module.finrank K (LinearMap.range (LinearMap.mk₂ K
    (fun (x : LinearMap.ker A.mulVecLin) (y : LinearMap.ker A.vecMulLinear) =>
      (y : Fin m → K) ⬝ᵥ (B *ᵥ (x : Fin n → K)))
    (by intro x₁ x₂ y; simp [Matrix.mulVec_add, dotProduct_add])
    (by intro c x y; simp [Matrix.mulVec_smul, dotProduct_smul])
    (by intro x y₁ y₂; simp [add_dotProduct])
    (by intro c x y; simp [smul_dotProduct])))

end TriFormQ


