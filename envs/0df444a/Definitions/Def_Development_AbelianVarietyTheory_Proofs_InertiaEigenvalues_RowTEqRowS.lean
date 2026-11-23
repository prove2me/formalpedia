-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:31:57.216105+00:00
-- url     : https://prove2.me/theorems/94a3d5bd-458a-4f77-a6c6-d9be871d0d85
-- title:
--   Row TEq Row S
-- statement:
--   Definitions and structural lemmas for Row TEq Row S, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/RowTEqRowS.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PMonE
open Finset
variable {F : Type*} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]
def rowS {h : ℕ} (ϖ : F) (lam : Fin h → F) (L U : ℕ) (x : Fin h → F) (r : Fin h) : F :=
  ∑ j, ∑ n ∈ Icc (-(L : ℤ)) U, term p ϖ lam x r j n
def winPt {h : ℕ} (π : Fin h → F) (L : ℕ) (z : Fin h → F) : Fin h → F :=
  fun j => π j * z j ^ (p ^ h) ^ (L - 1)
def coefB {h : ℕ} (ϖ : F) (lam π : Fin h → F) (L U m : ℕ) : Matrix (Fin h) (Fin h) F :=
  Matrix.of fun r j => if m ≤ L + U then
    (term p ϖ lam π r j ((m : ℤ) - L) / (lam r * π r ^ p ^ (r : ℕ))) ^ p ^ (h - (r : ℕ)) else 0
end GlobalTheory.PMonE


