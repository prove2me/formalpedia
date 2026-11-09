-- Prove2me | Definitions.Def_ChapterFockWeightedSchurEsaPromoted
-- name    : ChapterFockWeightedSchurEsaPromoted
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-08T08:51:20.56793+00:00
-- url     : https://prove2.me/theorems/d860b53f-b232-4182-a300-260b933d50fa
-- title:
--   Symbol-weighted Schur gates for the second quantization of an unbounded one-particle operator
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterFockWeightedSchurEsa.lean`): the symbol-weighted Schur layer for `dΓ(A)` when the one-particle operator is unbounded.  The platform's served `Def_ChapterFockWeightedSchurEsa` copy is a skeleton (no declarations), so every consumer statement that says `open BookProof.FockWeightedSchur` dies with `unknown namespace`; published bundles are immutable, so this bundle re-carries the chapter's DEFINITIONS (wdeg, wSym, wgt, the three weighted Schur gates and the oscillator column matrix) in the original namespace.  Its theorem facts remain separate problem nodes.  Consumers add a single `import Definitions.Def_ChapterFockWeightedSchurEsaPromoted`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFockWeightedSchurEsa.lean

-- §2.13 new-name route (Session 40): the platform's served `Def_ChapterFockWeightedSchurEsa` copy is a
-- skeleton (no declarations at all), so `open BookProof.FockWeightedSchur` in every consumer statement
-- dies with `unknown namespace`.  `submit-definition` cannot update an existing
-- name, so this bundle carries the chapter's DEFINITIONS in the original
-- namespace; its theorem facts stay problem nodes.  Consumers add a single
-- `import Definitions.Def_ChapterFockWeightedSchurEsaPromoted`.
-- Left to the problem nodes on purpose (theorem facts):
--   wdeg_eq_sum
--   wdeg_nonneg
--   wSym_nonneg
--   wSym_pos
--   ndeg_le_wdeg
--   wdeg_up
--   wSym_up
--   wgt_apply
--   support_wgt_subset
--   annA_wgt
--   inner_wgt_symm
--   re_inner_wgt
--   sum_wsq_normSq_annA
--   sum_le_of_vanishing
--   w_pos
--   wrow_le
--   wcol_le
--   wcomm_nonneg
--   wcomm_row_le
--   wcomm_col_le
--   normSq_dGamma_le_of_sector
--   normSq_dGamma_le_w
--   im_inner_dGamma_wgt_bound
--   normSq_toLp_wgt
--   dGammaOp_coreRelBound_w
--   dGammaOp_commForm_bound_w
--   sqrt_le_of_one_le
--   oscW_ge_one
--   oscW_pos
--   oscCol_apply
--   norm_oscCol_apply
--   isHermCol_oscCol
--   support_oscCol_subset
--   sum_pair_le
--   norm_oscCol_le
--   norm_oscCol_le_col
--   wRow_oscCol
--   wCol_oscCol
--   oscComm_term_le
--   wComm_oscCol
--   oscCol_not_schurBound
--   osc_stone_flow
import Definitions.Def_ChapterFockSchurEsa
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterCoreBoundsEsa
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterStoneBridge
import Mathlib



namespace BookProof.FockWeightedSchur

open BookProof.FockSecondQuantization BookProof.CoreBounds BookProof.FockSchur
open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section


/-- The **weighted particle number** `∑_k w_k² α_k` of a configuration. -/
def wdeg (w : ℕ → ℝ) (α : Conf) : ℝ := α.sum fun k n => w k ^ 2 * n

/-- The comparison symbol `σ(α) = ∑_k w_k² α_k + 1`. -/
def wSym (w : ℕ → ℝ) (α : Conf) : ℝ := wdeg w α + 1

variable {w : ℕ → ℝ}


/-- The comparison operator `𝒩_w + 1` applied to a finitely supported state. -/
def wgt (w : ℕ → ℝ) (u : FockAlg) : FockAlg :=
  Finsupp.onFinset u.support (fun α => (wSym w α : ℂ) * u α) (by
    intro α hα
    by_contra hc
    have hz : u α = 0 := Finsupp.notMem_support_iff.mp hc
    simp only [hz, mul_zero, ne_eq, not_true_eq_false] at hα)

/-! ## 3. The weighted Schur gates -/

variable {col : ℕ → (ℕ →₀ ℂ)} {K B : ℝ}

/-- The **row gate**: the rows of the one-particle matrix grow at most like the symbol. -/
def WRowBound (w : ℕ → ℝ) (col : ℕ → (ℕ →₀ ℂ)) (K : ℝ) : Prop :=
  ∀ k, ∑ j ∈ (col k).support, ‖(col k) j‖ ≤ K * w k

/-- The **column gate**: the columns, weighted by the reciprocal symbol, are summable. -/
def WColBound (w : ℕ → ℝ) (col : ℕ → (ℕ →₀ ℂ)) (K : ℝ) : Prop :=
  ∀ j, ∑ k ∈ (col j).support, ‖(col j) k‖ / w k ≤ K

/-- The **commutator gate**: the matrix of `[A, diag w²]`, weighted by `1/(w_k w_j)`, has
bounded rows. -/
def WCommBound (w : ℕ → ℝ) (col : ℕ → (ℕ →₀ ℂ)) (B : ℝ) : Prop :=
  ∀ k, ∑ j ∈ (col k).support, ‖(col k) j‖ * |w j ^ 2 - w k ^ 2| / (w k * w j) ≤ B

/-- The one-particle matrix `A_{k,k+1} = A_{k+1,k} = √(k+1)`, presented by its columns: the
position operator of a harmonic oscillator in the occupation basis.  It is Hermitian,
column-finite and **unbounded**. -/
def oscCol (k : ℕ) : ℕ →₀ ℂ :=
  if k = 0 then Finsupp.single 1 ((Real.sqrt 1 : ℝ) : ℂ)
  else Finsupp.single (k + 1) ((Real.sqrt ((k : ℝ) + 1) : ℝ) : ℂ)
      + Finsupp.single (k - 1) ((Real.sqrt (k : ℝ) : ℝ) : ℂ)

/-- The one-particle symbol `w_k = k + 1`. -/
def oscW (k : ℕ) : ℝ := (k : ℝ) + 1

end

end BookProof.FockWeightedSchur


