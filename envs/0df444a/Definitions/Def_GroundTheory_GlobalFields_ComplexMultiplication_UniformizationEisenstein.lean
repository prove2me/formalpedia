-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationEisenstein
-- name    : GroundTheory_GlobalFields_ComplexMultiplication_UniformizationEisenstein
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T05:53:02.248142+00:00
-- url     : https://prove2.me/theorems/c3eff499-dc0c-4bc0-aaa7-fd763e59d4dd
-- title:
--   Uniformization Eisenstein
-- statement:
--   Definitions and structural lemmas for Uniformization Eisenstein, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationEisenstein.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
open scoped PeriodPair Nat
noncomputable section
namespace GroundTheory.Global
namespace Elliptic
def weierstrassCoeff {R : Type*} [CommRing R] [Algebra ℚ R] (a b : R) : ℕ → R
  | 0 => 0
  | 1 => (1 / 20 : ℚ) • a
  | 2 => (1 / 28 : ℚ) • b
  | n + 3 => (3 / ((2 * ((n : ℚ) + 3) + 3) * ((n : ℚ) + 1)) : ℚ) •
      ∑ i : Fin (n + 1), weierstrassCoeff a b (i + 1) * weierstrassCoeff a b (n + 1 - i)
decreasing_by
  all_goals (have := i.isLt; omega)
section Recursion
variable {R S : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S]
end Recursion
def eisensteinPoly (n : ℕ) : MvPolynomial (Fin 2) ℚ :=
  (1 / (2 * (n : ℚ) + 1)) • weierstrassCoeff (MvPolynomial.X 0) (MvPolynomial.X 1) n
variable {L : PeriodPair}
variable (L) in

def weierstrassLaurentCoeff (j : ℕ) : ℂ := if j = 0 then 0 else (j + 1) * L.G (j + 2)
end Elliptic
end GroundTheory.Global


