-- Prove2me | Definitions.Def_Formalism_BranchSandwichDivisors_NormLog
-- name    : Formalism_BranchSandwichDivisors_NormLog
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:52:54.038856+00:00
-- url     : https://prove2.me/theorems/1490c16b-45a7-40c1-a8cd-7690e6e125f5
-- title:
--   Norm Log
-- statement:
--   Definitions and structural lemmas for Norm Log, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/NormLog.lean

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.BranchingDeterminantCap
def NormLog : Prop :=
  ∀ (Pl : Type) [Fintype Pl] (T : ℝ) (nτ c xi nrm : Pl → ℝ), 0 < T → (∀ τ, c τ ≠ 0) →
    (∀ τ, 0 < xi τ) → (∀ τ, nrm τ = (T ^ (nτ τ / 2))⁻¹ * (|c τ| * xi τ)) →
      Real.log ((∏ τ, nrm τ) ^ 2) =
        -(∑ τ, nτ τ * Real.log T) + ∑ τ, (2 * Real.log |c τ| + Real.log (xi τ ^ 2))
def CapLog : Prop :=
  ∀ (n : ℕ) (lam : Fin (n + 1) → ℤ) (sg : Fin n → ℤ) (a : ℝ), Interlace lam sg →
    ((lam 0 - lam (Fin.last n) : ℤ) : ℝ) + ((n : ℝ) + 1) ≤ 2 * a →
      Real.log |((cCap lam sg : ℤ) : ℝ)| ≤
        (((n : ℝ) + 1) - 1) * ((d1 lam sg : ℤ) : ℝ) * Real.log (2 * a)
def WeylLog : Prop :=
  ∀ (n : ℕ) (nu : Fin (n + 1) → ℤ) (a : ℝ), Antitone nu →
    ((nu 0 - nu (Fin.last n) : ℤ) : ℝ) + ((n : ℝ) + 1) ≤ 2 * a →
      Real.log (∏ p ∈ (Finset.univ : Finset (Fin (n + 1) × Fin (n + 1))).filter (fun p => p.1 < p.2),
        (((nu p.1 - nu p.2 : ℤ) : ℝ) + ((p.2 : ℕ) : ℝ) - ((p.1 : ℕ) : ℝ)) /
          (((p.2 : ℕ) : ℝ) - ((p.1 : ℕ) : ℝ))) ≤
        ((n : ℝ) + 1) * (((n : ℝ) + 1) - 1) / 2 * Real.log (2 * a)
end Formalism.BranchingDeterminantCap


