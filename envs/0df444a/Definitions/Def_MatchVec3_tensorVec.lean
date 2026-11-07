-- Prove2me | Definitions.Def_MatchVec3_tensorVec
-- name    : MatchVec3_tensorVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:40:56.320968+00:00
-- url     : https://prove2.me/theorems/b296bf08-6e9d-4a7c-bb92-323972f20b48
-- title:
--   Tensor product of $h$ vectors of $F^R$
-- statement:
--   For vectors $w^{(1)},\dots,w^{(h)}\in F^R$, this is $\bigotimes_{\ell=1}^h w^{(\ell)}$ as a vector of the $R^h$-dimensional space indexed by $h$-tuples of indices: its coordinate at $(j_1,\dots,j_h)$ is $\prod_\ell w^{(\ell)}_{j_\ell}$.
--
--   It gives the tensor representation of products of indicator values, and $\langle\bigotimes_\ell x^{(\ell)},\bigotimes_\ell y^{(\ell)}\rangle=\prod_\ell\langle x^{(\ell)},y^{(\ell)}\rangle$.
-- source:
--   Aggarwal, Obremski, Subexponential Upper Bounds for 3-Restricted Matching Vector Families, STOC 2027 submission (manuscript sha256 44199413…), Lemma 4.1, p.11

import Mathlib

namespace MatchVec3

/-- **The tensor product** `⊗_{ℓ=1}^h w^{(ℓ)}` of `h` vectors of `F^R` (Aggarwal, Obremski, STOC 2027
submission (manuscript sha256 44199413…), Lemma 4.1, p.11), as a vector of the `R^h`-dimensional
space indexed by `Fin h → Fin R`: its coordinate at `idx` is `∏_ℓ w^{(ℓ)}_{idx ℓ}`. -/
def tensorVec {F : Type*} [CommMonoid F] {h R : ℕ} (w : Fin h → Fin R → F) :
    (Fin h → Fin R) → F :=
  fun idx => ∏ ℓ, w ℓ (idx ℓ)

end MatchVec3


