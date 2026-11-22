-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DiagonalMonomialFactorial
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DiagonalMonomialFactorial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:12:05.737723+00:00
-- url     : https://prove2.me/theorems/5b8bbab4-bb9c-4dcb-91ac-6890924654c3
-- title:
--   Diagonal Monomial Factorial
-- statement:
--   Definitions and structural lemmas for Diagonal Monomial Factorial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HookLengthBound/DiagonalMonomialFactorial.lean

import Definitions.Def_Formalism_PeriodIntegrals_HookBound
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
namespace PI.HookLower
def diagHom (N : ℕ) : MvPolynomial (Fin N × Fin N) ℚ →ₐ[ℚ] MvPolynomial (Fin N × Fin N) ℚ :=
  aeval fun v => if v.1 = v.2 then X v else 0
def IsDiag {N : ℕ} (m : Fin N × Fin N →₀ ℕ) : Prop := ∀ v : Fin N × Fin N, v.1 ≠ v.2 → m v = 0
def diagMono {N : ℕ} (s : ℕ) (h : s ≤ N) : Fin N × Fin N →₀ ℕ :=
  ∑ p : Fin s, Finsupp.single (Fin.castLE h p, Fin.castLE h p) 1
def M0 {N : ℕ} (ν : Fin N → ℕ) : Fin N × Fin N →₀ ℕ :=
  ∑ s : Fin N, (ν s - nuNext ν s) • diagMono (s.val + 1) s.isLt
end PI.HookLower


