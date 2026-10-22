-- Prove2me | Definitions.Def_HiddenDirection
-- name    : HiddenDirection
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-09T05:17:16.255999+00:00
-- url     : https://prove2.me/theorems/fb92dbf6-0be9-4468-9311-5bf07234f7d9
-- title:
--   Hidden direction: a vector orthogonal to all queries with vanishing first N coordinates
-- statement:
--   This module constructs the hidden direction $u$ of §24 that the Theorem B extremizer is built on. Given the $N$ seed-determined random-search queries $q_1, \dots, q_N \in \mathbb R^{2N+1}$, the source asks for a nonzero vector $v$ with
--
--   $$v_1 = \cdots = v_N = 0, \qquad \langle v, q_i \rangle = 0 \;\; (i = 1, \dots, N),$$
--
--   and proves that such a $v$ necessarily exists, after which $u = v/\|v\|$ is a unit hidden direction. Formally, `firstBlockProj N` is the linear map reading off the first $N$ coordinates of $\mathbb R^{2N+1}$ and `vanishingFirstBlock N` is its kernel — the subspace cut out by the conditions $v_1 = \cdots = v_N = 0$, equivalently the last $N+1$ coordinate directions. The abstract dimension argument is isolated and proved rather than assumed: a subspace of dimension $N+1$ cut by $N$ homogeneous linear constraints has dimension at least $(N+1) - N = 1$. Finally `normalizeVec v = \|v\|^{-1} \cdot v` realises the normalisation $u = v/\|v\|$ (scalar division spelled as multiplication by $\|v\|^{-1}$).
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §24 Lemma 24.1 and eq. (24.1)-(24.5), source lines ~2175-2251; Lean: FullFormalization.HiddenDirection lines 1-117

-- Generated from F:/20261008/FullFormalization\FullFormalization\HiddenDirection.lean by skeleton subtraction (Phase 3-4):
-- every unselected declaration deleted, project imports rewritten.
/-
  FullFormalization.HiddenDirection

  Source: `auditable_full_proof_nag_and_five_algorithm_cn.md`, section 24
  (lines ~2175-2251), Lemma 24.1 and equations (24.1)-(24.5).

  The source document fixes the dimension

      D = 2 N + 1                                              (23.1)

  and, after fixing the seed, obtains `N` query points `q_1, ..., q_N ∈ ℝ^D`
  which are completely determined by `N`, `D` and the public sampling rule;
  in particular the query positions do not depend on function values.  It then
  asks for a *nonzero* vector `v` with

      v_1 = ... = v_N = 0,                                     (24.1)
      ⟨v, q_i⟩ = 0        for i = 1, ..., N,                   (24.2)

  and proves (Lemma 24.1) that such a `v` necessarily exists.

  Formalisation notes.

  * `Fin N` is the Lean index type for `i = 1, ..., N`; the source index `i`
    corresponds to `Fin` value `i - 1`.  Accordingly (24.1) -- `v_1 = ... = v_N = 0`
    -- says that the first `N` coordinates `v 0, ..., v (N-1)` vanish, which is
    encoded as `∀ i : Fin N, v (Fin.castLE _ i) = 0`; the map
    `Fin.castLE (by omega : N ≤ 2 * N + 1)` is the inclusion of the first `N`
    coordinates into `Fin (2 * N + 1)`.

  * The ambient space is `EuclideanSpace ℝ (Fin (2 * N + 1))`, i.e. `Fin D → ℝ`
    with the Pi inner product, exactly as in the source.

  * Lemma 24.1 is *proved*, not assumed: `exists_nonzero_orthogonal_of_finrank_succ`
    below isolates the pure dimension argument of the source ("the last `N + 1`
    coordinates span a subspace of dimension `N + 1`; the `N` homogeneous
    orthogonality conditions impose at most `N` independent linear constraints;
    hence the common kernel has dimension at least `(N + 1) - N = 1`"), and
    `finrank_vanishingFirstBlock` computes the dimension of the constrained
    subspace.  No axiom, `sorry` or `unsafe` is used anywhere in this file.

  * (24.3) writes `u = v / ‖v‖`.  This Mathlib revision has no scalar-division
    instance on `EuclideanSpace`, so the division is written as multiplication
    by `‖v‖⁻¹` (`normalizeVec`); `normalizeVec_eq` records the equality with the
    source's `v / ‖v‖`.
-/

import Mathlib
import Definitions.Def_Coefficients

open scoped Gradient RealInnerProductSpace

set_option linter.unusedSectionVars false

namespace FullFormalization

noncomputable section

variable {N : ℕ}

/-! ## Lemma 24.1, abstract dimension argument

The source's proof only uses: a subspace of dimension `N + 1` in a real inner
product space, and `N` homogeneous linear constraints `⟨·, q i⟩ = 0`.  We prove
that abstract statement first, so that the dimension count is auditable on its
own, independently of the concrete coordinates in `Fin (2 * N + 1)`. -/



/-! ## The concrete subspace of (24.1)

`firstBlockProj N` is the linear map `v ↦ (v 0, ..., v (N-1))` that reads off the
first `N` coordinates of a vector of `EuclideanSpace ℝ (Fin (2 * N + 1))`; its
kernel is the subspace cut out by the conditions (24.1). -/

/-- The projection onto the first `N` coordinates of `EuclideanSpace ℝ (Fin (2*N+1))`. -/
def firstBlockProj (N : ℕ) : EuclideanSpace ℝ (Fin (2 * N + 1)) →ₗ[ℝ] (Fin N → ℝ) :=
  { toFun := fun v i => v (Fin.castLE (by omega) i)
    map_add' := by intro v w; funext i; simp
    map_smul' := by intro c v; funext i; simp }

/-- The subspace of vectors satisfying (24.1): `v 0 = ... = v (N-1) = 0`.

This is the source's "the subspace of the last `N + 1` coordinates", expressed as
the kernel of the complementary projection (the two descriptions are equivalent,
and this one is the one used in the dimension count). -/
def vanishingFirstBlock (N : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin (2 * N + 1))) :=
  (firstBlockProj N).ker





/-! ## Lemma 24.1 for the source's query points -/



/-! ## The unit vector `u = v / ‖v‖` of (24.3)-(24.5) -/

/-- (24.3): `u = v / ‖v‖`.  The source's scalar division is spelled here as
multiplication by `‖v‖⁻¹`, because this Mathlib revision does not equip
`EuclideanSpace` with a scalar-division instance; `normalizeVec_eq` shows this is
exactly the source's quotient. -/
def normalizeVec {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (v : E) : E :=
  ‖v‖⁻¹ • v







end

end FullFormalization


