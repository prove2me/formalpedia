-- Prove2me | Definitions.Def_MasulloGRH_ApproximationNumbers
-- name    : MasulloGRH_ApproximationNumbers
-- status  : Definition
-- author  : @marozols
-- created : 2026-11-21T01:57:28.10738+00:00
-- url     : https://prove2.me/theorems/f50de8bf-2a20-4d8e-8dc1-9aac8db38be6
-- title:
--   Approximation numbers of bounded linear operators
-- statement:
--   For a bounded linear operator $T:E\to F$ between normed spaces and an integer $n\ge1$, the $n$-th approximation number is
--   $$\sigma_n(T)=\inf\{\,\lVert T-R\rVert:\ \operatorname{rank}R<n\,\}.$$
--   The rank condition uses finite-dimensional range, and the norm is the operator norm. This is Masullo’s definition (C.3.6.2).
-- source:
--   Alessandro Maria Masullo, The Music of the Primes, 20 November 2026 draft, p. 704, Eq. (C.3.6.2) and Lemma C.3.6.3. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. The same-index sum estimate is disproved at https://prove2.me/theorems/ac4831ba-e3dc-4ba2-afeb-0049ab739c30.

import Mathlib

/-!
# Approximation-number inequalities

The index is one-based, as in Masullo (C.3.6.2). The sum inequality
in Lemma C.3.6.3(1) uses index `m + n - 1`. Part (2) is a same-index
Lipschitz estimate. For part (3), the usual product argument gives
the stronger index `m + n - 1`.
-/

open Set

namespace MasulloGRH

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- An approximant admissible for the one-based index `n`.
The finite-dimensionality condition distinguishes infinite-dimensional
ranges, whose natural-valued finrank also equals zero in Lean. -/
def ApproximationRankBelow (n : ℕ) (T : E →L[𝕜] F) : Prop :=
  FiniteDimensional 𝕜 (LinearMap.range (T : E →ₗ[𝕜] F)) ∧
  Module.finrank 𝕜 (LinearMap.range (T : E →ₗ[𝕜] F)) < n

/-- The set of possible operator-norm errors at a fixed index. -/
def approximationErrors (n : ℕ) (T : E →L[𝕜] F) : Set ℝ :=
  {r | ∃ R : E →L[𝕜] F, ApproximationRankBelow n R ∧ r = ‖T - R‖}

/-- The approximation number `σₙ(T)`, where the meaningful indices start at one. -/
noncomputable def approxNumber (n : ℕ) (T : E →L[𝕜] F) : ℝ :=
  sInf (approximationErrors n T)

end MasulloGRH


