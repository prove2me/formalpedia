-- Prove2me | Definitions.Def_DerandSq_permMat
-- name    : DerandSq_permMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:53:02.571968+00:00
-- url     : https://prove2.me/theorems/dd6541da-09f3-48d6-a6b9-d7a91106530d
-- title:
--   Permutation matrix $\lambda(\sigma)$
-- statement:
--   For a permutation $\sigma$ of $[N]$, the **permutation matrix** $\lambda(\sigma) \in \mathbb R^{N \times N}$ is the matrix of the linear map $\delta_v \mapsto \delta_{\sigma(v)}$ on the standard basis:
--   $$
--   \lambda(\sigma)_{w,v} = \mathbf 1[\sigma(v) = w].
--   $$
--   This is the orientation of the left-regular representation, $\lambda(\sigma)\delta_v = \delta_{\sigma v}$, used in the decomposition $A_G = \sum_j \lambda(\pi_j)$ of (4.1).
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), (4.1), p.18, and Example 2.4, p.8

import Mathlib

namespace DerandSq

/-- The permutation matrix `λ(σ)` of `σ ∈ S_N`, with the paper's orientation `λ(σ) δ_v = δ_{σ v}`
(Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), (4.1), p.18: "λ(•) as before denotes the left-regular representation", and Example 2.4,
p.8): the entry in row `w`, column `v` is `1` if `σ v = w` and `0` otherwise. -/
def permMat {N : ℕ} (σ : Equiv.Perm (Fin N)) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun w v => if σ v = w then 1 else 0

end DerandSq


