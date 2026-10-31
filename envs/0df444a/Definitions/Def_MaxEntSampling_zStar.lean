-- Prove2me | Definitions.Def_MaxEntSampling_zStar
-- name    : MaxEntSampling_zStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:56:49.199662+00:00
-- url     : https://prove2.me/theorems/26a2f5d3-cc53-4bb3-9a0e-e59540058c9c
-- title:
--   The MESP optimal value $z^*=\max_{|S|=s}\log\det(C_{S,S})$ (MESP (1))
-- statement:
--   Let $C=V^\top V\in\mathbb R^{n\times n}$ be a covariance matrix written through a factor $V\in\mathbb R^{d\times n}$. The **maximum entropy sampling problem** asks for the size-$s$ principal submatrix with the largest log-determinant:
--
--   $$
--   z^* := \max_{S}\bigl\{\log\det(C_{S,S}) : S\subseteq[n],\ |S|=s\bigr\},
--   $$
--
--   where $C_{S,S}$ has rows and columns indexed by $S$.
--
--   **Formalization Note** The value lies in the extended reals with $\log 0=-\infty$ (the paper's convention, Appendix A.4); the logarithm is `ENNReal.log ∘ ENNReal.ofReal`. The maximum is a supremum over the finite family of size-$s$ subsets.
-- source:
--   Li, Xie, Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem, arXiv:2001.08537v3, eq. (1), p.2 (PDF p.2); §2.1, pp.5–6

import Mathlib

open Matrix Finset

namespace MaxEntSampling

/-- **The MESP optimal value `z*` (MESP (1)).**
Li, Xie, *Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem*,
arXiv:2001.08537v3, eq. (1), p.2 (PDF p.2): "z∗ := max_S {log det(C_{S,S}) : S ⊆ [n], |S| = s}",
with the covariance matrix `C = VᵀV` written through its factorization `V ∈ ℝ^{d×n}` (§2.1,
pp.5–6).

`zStar V s` is the largest value of `log det(C_{S,S})` over the size-`s` subsets `S ⊆ [n]`, where
`C = VᵀV` and `C_{S,S}` is the principal submatrix with rows and columns in `S`.

**Formalization Note.** The value lies in `EReal`, with `log 0 = −∞` (the paper uses this
convention, e.g. Appendix A.4, p.45): `log` is `ENNReal.log ∘ ENNReal.ofReal`, which is the real
logarithm on positive reals and `⊥` at `0`. The maximum over the finite family of subsets is a
supremum (`⨆`), equal to the maximum when `s ≤ n`. -/
noncomputable def zStar {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ) (s : ℕ) : EReal :=
  ⨆ S ∈ (univ : Finset (Fin n)).powersetCard s,
    ENNReal.log (ENNReal.ofReal ((Vᵀ * V).submatrix (Subtype.val : S → Fin n) Subtype.val).det)

end MaxEntSampling


