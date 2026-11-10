-- Prove2me | Definitions.Def_DualCoppersmith_Recovery_Geometry
-- name    : DualCoppersmith_Recovery_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T02:54:05.461124+00:00
-- url     : https://prove2.me/theorems/6cb1c59f-8621-403d-855b-08b4831a3100
-- title:
--   Second successive minimum and certified lattice reduction
-- statement:
--   For a full-rank Euclidean lattice $L\subseteq\mathbb R^n$, its second successive minimum is
--
--   $$\lambda_2(L)=\inf\{R\ge0:\exists v_1,v_2\in L\text{ real-linearly independent},\ \|v_1\|,\|v_2\|\le R\}.$$
--
--   The published Regev definition supplies $\lambda_1(L)$, the infimum of norms of nonzero lattice vectors. The published LLL setting supplies Euclidean vectors, integer spans, genuine real-linearly-independent lattice bases, and Gram–Schmidt data. On full-rank lattices in dimension at least two these minima are positive, finite and attained; none is a heuristic length prediction.
--
--   A reduction call returns a genuine basis of the same lattice and size-reduces its coefficients to absolute value at most $1/2$. Its quality certificate at $\delta\ge1$ either checks the adjacent squared Gram–Schmidt ratios against $\delta^4$, or records the subroutine’s established approximation law against every nonzero vector of the same lattice. The latter option preserves every valid certified factor, even when the sufficient Gram–Schmidt certificate is conservative. No root, root line, collinearity or recovery condition occurs in either certificate.
--
--   The input-only basis selector returns a chosen full basis if one exists and failure otherwise. It tests basis geometry alone. No shortest-vector or recovery theorem is hidden in the selection operation. This is a mathematical subroutine interface without a runtime claim.
-- source:
--   Taehun Kang, Jebin Kim, Changmin Lee, JeongHwan Lee, STOC 2027 submission #1253 (October 2026), p. 3, Definition 2.1 and Lemma 2.2 (PDF p. 4); p. 1, valid approximation factor (PDF p. 2); p. 9, Algorithm 2 (PDF p. 10)

import Mathlib
import Definitions.Def_LLLFactor_RedBasis_Setting
import Definitions.Def_RegevLWE_SmoothingLB_Lattice

set_option autoImplicit false

namespace DualCoppersmith.Recovery

open LLLFactor.RedBasis

/-- Definition 2.1 at i = 2, used only on rank at least two.
    The already published Regev definition is used directly for i = 1. -/
noncomputable def secondMinimum {n : ℕ} (L : Submodule ℤ (Vec n)) : ℝ :=
  sInf {R : ℝ | 0 ≤ R ∧ ∃ v : Fin 2 → Vec n,
    LinearIndependent ℝ v ∧ ∀ j, v j ∈ L ∧ ‖v j‖ ≤ R}

/-- A root-free Gram--Schmidt quality certificate. For standard 3/4-LLL,
    the squared adjacent ratio is at most 2, giving δ = 2^(1/4).
    No successive minimum or shortest-vector conclusion occurs in this certificate. -/
def GSQuality {n : ℕ} (delta : ℝ) (b : Fin n → Vec n) : Prop :=
  ∀ (i : ℕ) (hi : i + 1 < n),
    ‖gs b ⟨i, by omega⟩‖ ^ 2 ≤ delta ^ 4 * ‖gs b ⟨i + 1, hi⟩‖ ^ 2

/-- External subroutine specification against every nonzero lattice vector.
    This is a certified approximation law, not a measured determinant ratio.
    It contains neither a target root nor a successive minimum. -/
def PointwiseQuality {n : ℕ} (delta : ℝ) (b : Fin n → Vec n) : Prop :=
  ∀ (hn : 0 < n) (x : Vec n), x ∈ latticeOf b → x ≠ 0 →
    ‖b ⟨0, hn⟩‖ ≤ delta ^ (2 * (n - 1)) * ‖x‖

/-- A call preserves a genuine basis and is size-reduced. Quality may be
    independently checked in Gram--Schmidt geometry or supplied by the
    subroutine's external approximation contract. The second route retains
    every valid approximation factor, even if the GS test is conservative. -/
def IsLLLCall {n : ℕ} (delta : ℝ) (input output : Fin n → Vec n) : Prop :=
  IsBasisFor output (latticeOf input) ∧
    (∀ i j : Fin n, j < i → |mu output i j| ≤ (1 / 2 : ℝ)) ∧
    (GSQuality delta output ∨ PointwiseQuality delta output)

abbrev Reduction (n : ℕ) := (Fin n → Vec n) → (Fin n → Vec n)

/-- Input-only mathematical basis selection, with failure precisely when no full
    basis exists. For the modular kernel, existence follows from p^m Z^n ⊆ K. -/
noncomputable def selectBasis {n : ℕ} (L : Submodule ℤ (Vec n)) :
    Option (Fin n → Vec n) := by
  classical
  exact if h : ∃ b : Fin n → Vec n, IsBasisFor b L then some h.choose else none

end DualCoppersmith.Recovery


