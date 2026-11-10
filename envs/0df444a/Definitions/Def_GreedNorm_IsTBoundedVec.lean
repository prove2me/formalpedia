-- Prove2me | Definitions.Def_GreedNorm_IsTBoundedVec
-- name    : GreedNorm_IsTBoundedVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:44:34.527491+00:00
-- url     : https://prove2.me/theorems/f489d9b3-0453-4065-961e-9f4b85c8ec6e
-- title:
--   $t$-bounded vector
-- statement:
--   A vector $v\in\mathbb R^m$ is **$t$-bounded** if for every $\ell\in\mathrm{POS}$ the number of entries of $v$ larger than $t_\ell$ is at most $\ell-1$.
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Definition 2.2, p.5 (PDF 7)

import Mathlib
import Definitions.Def_GreedNorm_POS

namespace GreedNorm

/-- **`t`-bounded vector**: for every `ℓ ∈ POS`, at most `ℓ − 1` entries of `v` exceed `t_ℓ`.
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Definition 2.2, p.5 (PDF 7): "A vector v is t-bounded if for every ℓ∈POS, the number of
entries in v that are larger than tℓ is at most ℓ−1."

**Formalization Note** `v : Fin m → ℝ`, POS is `POS m ε` (1-based indices). For `m ≥ 1` every
`ℓ ∈ POS` is `≥ 1`, so the natural subtraction `ℓ - 1` is exact. -/
def IsTBoundedVec {m : ℕ} (ε : ℝ) (t : ℕ → ℝ) (v : Fin m → ℝ) : Prop :=
  ∀ ℓ ∈ POS m ε, (Finset.univ.filter (fun i => t ℓ < v i)).card ≤ ℓ - 1

end GreedNorm


