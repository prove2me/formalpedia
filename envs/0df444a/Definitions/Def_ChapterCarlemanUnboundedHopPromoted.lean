-- Prove2me | Definitions.Def_ChapterCarlemanUnboundedHopPromoted
-- name    : ChapterCarlemanUnboundedHopPromoted
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-03T12:25:21.44299+00:00
-- url     : https://prove2.me/theorems/b3ef6407-b3ce-4821-bc9b-cee77c2aaaf0
-- title:
--   Carleman flux criterion: the unbounded-hop kernel layer
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterCarlemanUnboundedHop.lean`): the `geoHop` kernel layer (geoHop_herm, geoHop_norm_off, geoHop_col, geoHop_isL2Kernel) carved out of ChapterCarlemanUnboundedHop under the §2.13 new-name route: the served copy stops at `geoHop`, so the `geoHop_essentiallySelfAdjoint`, `kernelOp_symmetric` and `ladderRec_of_deficiency` statements, which carry `geoHop_isL2Kernel` as a term, die server-side with `Unknown identifier`. Published bundles are immutable, so the fix is this auxiliary bundle, which re-carries exactly that cluster in its original namespace. Consumers add a single `import Definitions.Def_ChapterCarlemanUnboundedHopPromoted`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterCarlemanUnboundedHop.lean

-- Generated from ChapterCarlemanUnboundedHop.lean — the `geoHop` kernel layer that
-- the platform's served ChapterCarlemanUnboundedHop copy predates (§2.13 new-name
-- route: submit-definition rejects an existing name, so the decls live here instead).
-- The served bundle stops at `geoHop`; these four facts are what the
-- `geoHop_essentiallySelfAdjoint` / `kernelOp_symmetric` / `ladderRec_of_deficiency`
-- statements cite as `geoHop_isL2Kernel`.
import Definitions.Def_ChapterCarlemanUnboundedHop
import Mathlib

namespace BookProof.CarlemanUnboundedHop

open Finset
open BookProof BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine

noncomputable section

theorem geoHop_herm (b : ℕ → ℝ) (rho : ℝ) : IsHermitianKernel (geoHop b rho) := by
  intro n k
  by_cases h : n = k
  · subst h; simp [geoHop]
  · rw [geoHop, geoHop, if_neg (Ne.symm h), if_neg h, min_comm k n, max_comm k n,
      Complex.conj_ofReal]

theorem geoHop_norm_off {b : ℕ → ℝ} {rho : ℝ} (hrho : 0 ≤ rho) {n k : ℕ} (h : n ≠ k) :
    ‖geoHop b rho n k‖ = (1 + ((min n k : ℕ) : ℝ)) * rho ^ (max n k - min n k) := by
  rw [geoHop, if_neg h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem geoHop_col {b : ℕ → ℝ} {rho : ℝ} (hrho : 0 ≤ rho) (hrho1 : rho < 1) (k : ℕ) :
    Memℓp (fun n => geoHop b rho n k) 2 := by
  refine memLpTwo_of_summable_normSq ?_
  refine (summable_nat_add_iff (k + 1)).mp ?_
  have heq : ∀ m : ℕ, ‖geoHop b rho (m + (k + 1)) k‖ ^ 2
      = (1 + (k : ℝ)) ^ 2 * ((rho ^ 2) ^ (m + 1)) := by
    intro m
    have hne : m + (k + 1) ≠ k := by omega
    have hmin : min (m + (k + 1)) k = k := by omega
    have hmax : max (m + (k + 1)) k = m + (k + 1) := by omega
    have hsub : m + (k + 1) - k = m + 1 := by omega
    rw [geoHop_norm_off hrho hne, hmin, hmax, hsub, mul_pow, ← pow_mul, ← pow_mul]
    ring_nf
  have hgeo : Summable (fun m : ℕ => (1 + (k : ℝ)) ^ 2 * ((rho ^ 2) ^ (m + 1))) := by
    have hlt : rho ^ 2 < 1 := by nlinarith
    have hsum : Summable (fun m : ℕ => (rho ^ 2) ^ m) :=
      (hasSum_geometric_of_lt_one (by positivity) hlt).summable
    have := (hsum.mul_left (rho ^ 2)).mul_left ((1 + (k : ℝ)) ^ 2)
    refine this.congr fun m => ?_
    rw [pow_succ]
    ring
  exact hgeo.congr fun m => (heq m).symm

/-- The kernel data of `geoHop`: Hermitian, with every column square-summable. -/
theorem geoHop_isL2Kernel (b : ℕ → ℝ) {rho : ℝ} (hrho : 0 ≤ rho) (hrho1 : rho < 1) :
    IsL2Kernel (geoHop b rho) :=
  ⟨geoHop_herm b rho, fun k => geoHop_col hrho hrho1 k⟩

end

end BookProof.CarlemanUnboundedHop


