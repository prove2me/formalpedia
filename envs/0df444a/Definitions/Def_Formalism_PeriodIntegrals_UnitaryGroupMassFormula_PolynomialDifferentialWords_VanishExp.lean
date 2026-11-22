-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_VanishExp
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_VanishExp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:19.412575+00:00
-- url     : https://prove2.me/theorems/f7d42ff6-339a-45fc-9173-22c7fdfc54ac
-- title:
--   Vanish Exp
-- statement:
--   Definitions and structural lemmas for Vanish Exp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialDifferentialWords/VanishExp.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace PI.OpWords
variable {K : Type} [Field K] [CharZero K] {k : ℕ}
def shiftPt (a b : Fin k) (s : K) (p : Fin k ⊕ Fin k → K) : Fin k ⊕ Fin k → K :=
  fun i => p i + s * eval p (Rop K k a b (X i))
def ExpFormula (a b : Fin k) (s : K) (g : Pol K k) : Prop :=
  ∃ N : ℕ, (∀ n, N < n → (Rop K k a b)^[n] g = 0) ∧
    ∀ M, N ≤ M → ∀ p : Fin k ⊕ Fin k → K,
      eval (shiftPt a b s p) g =
        ∑ n ∈ Finset.range (M + 1), s ^ n / (n.factorial : K) * eval p ((Rop K k a b)^[n] g)
end PI.OpWords


