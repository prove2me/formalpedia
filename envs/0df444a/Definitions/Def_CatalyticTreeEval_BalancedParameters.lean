-- Prove2me | Definitions.Def_CatalyticTreeEval_BalancedParameters
-- name    : CatalyticTreeEval_BalancedParameters
-- status  : Definition
-- author  : @sragavan
-- created : 2026-11-14T02:22:55.351512+00:00
-- url     : https://prove2.me/theorems/070749ef-503d-49ad-98eb-a99585e6f71e
-- title:
--   Computable balanced prime-power parameters
-- statement:
--   Choose the integer root of m times w, where m is the product of t distinct primes, and select each exponent by an integer logarithm in its prime base. The construction is fully computable. Product, degree and dimension bounds are separate theorems establishing the parameters required for Theorem 3.10.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Theorem 3.10 and Appendix B.

import Definitions.Def_CatalyticTreeEval_Main_Polynomials
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

set_option autoImplicit false

namespace CatalyticTreeEval.Main

/-- The integer root used by the uniform prime-power parameter algorithm. -/
def balancedRoot {t : ℕ} (p : Fin t → ℕ) (w : ℕ) : ℕ :=
  Nat.nthRoot t (modulus p * w)

/-- Largest powers of the individual primes below the common integer root. -/
def balancedExponents {t : ℕ} (p : Fin t → ℕ) (w : ℕ) : Fin t → ℕ :=
  fun i => Nat.log (p i) (balancedRoot p w)

end CatalyticTreeEval.Main


