-- Prove2me | Definitions.Def_DerandSq_permOp
-- name    : DerandSq_permOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:53:22.137173+00:00
-- url     : https://prove2.me/theorems/97040dd2-7e74-4375-873d-cdf8b9fcfcbc
-- title:
--   Permutation matrices as operators on $\mathbb C^N$
-- statement:
--   For $\sigma \in S_N$, the permutation matrix of $\sigma$ acts on $\mathbb C^N$ by $e_v \mapsto e_{\sigma(v)}$ on the standard basis (the orientation $\lambda(\sigma)\delta_v = \delta_{\sigma v}$ used throughout the paper). It is unitary, and fixes the all-ones vector.
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), §2.5, p.12

import Mathlib

namespace DerandSq

/-- The permutation matrix of `σ ∈ S_N` as an operator on `ℂ^N`, `e_v ↦ e_{σ v}` (Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), §2.5,
p.12, and the orientation `λ(σ) δ_v = δ_{σ v}` of (4.1), p.18). -/
noncomputable def permOp {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ).toContinuousLinearEquiv.toContinuousLinearMap

end DerandSq


